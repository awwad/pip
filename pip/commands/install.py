from __future__ import absolute_import

import logging
import operator
import os
import tempfile
import shutil
import warnings
try:
    import wheel
except ImportError:
    wheel = None

from pip.req import RequirementSet
from pip.basecommand import RequirementCommand
from pip.locations import virtualenv_no_global, distutils_scheme
from pip.exceptions import (
    InstallationError, CommandError, PreviousBuildDirError,
)
from pip import cmdoptions
from pip.utils import ensure_dir
from pip.utils.build import BuildDirectory
from pip.utils.deprecation import RemovedInPip10Warning
from pip.utils.filesystem import check_path_owner
from pip.wheel import WheelCache, WheelBuilder


logger = logging.getLogger(__name__)


class InstallCommand(RequirementCommand):
    """
    Install packages from:

    - PyPI (and other indexes) using requirement specifiers.
    - VCS project urls.
    - Local project directories.
    - Local or remote source archives.

    pip also supports installing from "requirements files", which provide
    an easy way to specify a whole environment to be installed.
    """
    name = 'install'

    usage = """
      %prog [options] <requirement specifier> [package-index-options] ...
      %prog [options] -r <requirements file> [package-index-options] ...
      %prog [options] [-e] <vcs project url> ...
      %prog [options] [-e] <local project path> ...
      %prog [options] <archive url/path> ..."""

    summary = 'Install packages.'

    def __init__(self, *args, **kw):
        super(InstallCommand, self).__init__(*args, **kw)

        cmd_opts = self.cmd_opts

        cmd_opts.add_option(cmdoptions.constraints())
        cmd_opts.add_option(cmdoptions.editable())
        cmd_opts.add_option(cmdoptions.requirements())
        cmd_opts.add_option(cmdoptions.build_dir())

        # <~> Adding an option to check for dependency conflicts instead of installing.
        #     Conflict models 1, 2, or 3 indicated by the integer value of --find-dep-conflicts
        cmd_opts.add_option(
            '--find-dep-conflicts',
            dest='find_dep_conflicts',
            type='int',
            default=0,
            help='<~> Instead of installing, simply check for dependency conflicts '
                 'and raise an error if a conflict is detected. Value given is '
                 'interpreted as an integer 1, 2, or 3, corresponding to these '
                 'conflict models: '
                 'Model 1: '
                 'defining a conflict as a scenario in which different constraints '
                 'for the same package exist, those constraints not being identical. '
                 'Model 2: '
                 'defining a conflict as a scenario in which different constraints '
                 'would lead to the installation of different packages based on pip '
                 'dist selection policies.'
                 'Model 3: '
                 'defining a conflict as a scenario in which pip chooses a set of '
                 'packages to install that does not actually meet all constraints of '
                 'those selected packages.')
        # <~> These options go with the above (--find-dep-conflicts).
        cmd_opts.add_option(
            '--dependencies-db-file',
            dest='dependencies_db_file',
            help='<~> For use with --find-dep-conflicts. Specify the filename for the '
                 'json file where dependency information for discovered packages will '
                 'be saved.')
        cmd_opts.add_option(
            '--conflicts-db-file',
            dest='conflicts_db_file',
            help='<~> For use with --find-dep-conflicts. Specify the filename for the '
                 'json file where conflict information for packages with discovered '
                 'conflicts will be saved.')
        # <~> end

        cmd_opts.add_option(
            '-t', '--target',
            dest='target_dir',
            metavar='dir',
            default=None,
            help='Install packages into <dir>. '
                 'By default this will not replace existing files/folders in '
                 '<dir>. Use --upgrade to replace existing packages in <dir> '
                 'with new versions.'
        )

        cmd_opts.add_option(
            '-d', '--download', '--download-dir', '--download-directory',
            dest='download_dir',
            metavar='dir',
            default=None,
            help=("Download packages into <dir> instead of installing them, "
                  "regardless of what's already installed."),
        )

        cmd_opts.add_option(cmdoptions.src())

        cmd_opts.add_option(
            '-U', '--upgrade',
            dest='upgrade',
            action='store_true',
            help='Upgrade all specified packages to the newest available '
                 'version. This process is recursive regardless of whether '
                 'a dependency is already satisfied.'
        )

        cmd_opts.add_option(
            '--force-reinstall',
            dest='force_reinstall',
            action='store_true',
            help='When upgrading, reinstall all packages even if they are '
                 'already up-to-date.')

        cmd_opts.add_option(
            '-I', '--ignore-installed',
            dest='ignore_installed',
            action='store_true',
            help='Ignore the installed packages (reinstalling instead).')

        cmd_opts.add_option(cmdoptions.no_deps())

        cmd_opts.add_option(cmdoptions.install_options())
        cmd_opts.add_option(cmdoptions.global_options())

        cmd_opts.add_option(
            '--user',
            dest='use_user_site',
            action='store_true',
            help="Install to the Python user install directory for your "
                 "platform. Typically ~/.local/, or %APPDATA%\Python on "
                 "Windows. (See the Python documentation for site.USER_BASE "
                 "for full details.)")

        cmd_opts.add_option(
            '--egg',
            dest='as_egg',
            action='store_true',
            help="Install packages as eggs, not 'flat', like pip normally "
                 "does. This option is not about installing *from* eggs. "
                 "(WARNING: Because this option overrides pip's normal install"
                 " logic, requirements files may not behave as expected.)")

        cmd_opts.add_option(
            '--root',
            dest='root_path',
            metavar='dir',
            default=None,
            help="Install everything relative to this alternate root "
                 "directory.")

        cmd_opts.add_option(
            '--prefix',
            dest='prefix_path',
            metavar='dir',
            default=None,
            help="Installation prefix where lib, bin and other top-level "
                 "folders are placed")

        cmd_opts.add_option(
            "--compile",
            action="store_true",
            dest="compile",
            default=True,
            help="Compile py files to pyc",
        )

        cmd_opts.add_option(
            "--no-compile",
            action="store_false",
            dest="compile",
            help="Do not compile py files to pyc",
        )

        cmd_opts.add_option(cmdoptions.use_wheel())
        cmd_opts.add_option(cmdoptions.no_use_wheel())
        cmd_opts.add_option(cmdoptions.no_binary())
        cmd_opts.add_option(cmdoptions.only_binary())
        cmd_opts.add_option(cmdoptions.pre())
        cmd_opts.add_option(cmdoptions.no_clean())
        cmd_opts.add_option(cmdoptions.require_hashes())

        index_opts = cmdoptions.make_option_group(
            cmdoptions.index_group,
            self.parser,
        )

        self.parser.insert_option_group(0, index_opts)
        self.parser.insert_option_group(0, cmd_opts)

    def run(self, options, args):
        cmdoptions.resolve_wheel_no_use_binary(options)
        cmdoptions.check_install_build_global(options)

        if options.allow_external:
            warnings.warn(
                "--allow-external has been deprecated and will be removed in "
                "the future. Due to changes in the repository protocol, it no "
                "longer has any effect.",
                RemovedInPip10Warning,
            )

        if options.allow_all_external:
            warnings.warn(
                "--allow-all-external has been deprecated and will be removed "
                "in the future. Due to changes in the repository protocol, it "
                "no longer has any effect.",
                RemovedInPip10Warning,
            )

        if options.allow_unverified:
            warnings.warn(
                "--allow-unverified has been deprecated and will be removed "
                "in the future. Due to changes in the repository protocol, it "
                "no longer has any effect.",
                RemovedInPip10Warning,
            )

        if options.download_dir:
            # <~> Shutting this up to reduce spam for now.
            #warnings.warn(
            #    "pip install --download has been deprecated and will be "
            #    "removed in the future. Pip now has a download command that "
            #    "should be used instead.",
            #    RemovedInPip10Warning,
            #)
            options.ignore_installed = True

        if options.build_dir:
            options.build_dir = os.path.abspath(options.build_dir)

        options.src_dir = os.path.abspath(options.src_dir)
        install_options = options.install_options or []
        if options.use_user_site:
            if options.prefix_path:
                raise CommandError(
                    "Can not combine '--user' and '--prefix' as they imply "
                    "different installation locations"
                )
            if virtualenv_no_global():
                raise InstallationError(
                    "Can not perform a '--user' install. User site-packages "
                    "are not visible in this virtualenv."
                )
            install_options.append('--user')
            install_options.append('--prefix=')

        temp_target_dir = None
        if options.target_dir:
            options.ignore_installed = True
            temp_target_dir = tempfile.mkdtemp()
            options.target_dir = os.path.abspath(options.target_dir)
            if (os.path.exists(options.target_dir) and not
                    os.path.isdir(options.target_dir)):
                raise CommandError(
                    "Target path exists but is not a directory, will not "
                    "continue."
                )
            install_options.append('--home=' + temp_target_dir)

        global_options = options.global_options or []

        with self._build_session(options) as session:

            finder = self._build_package_finder(options, session)
            build_delete = (not (options.no_clean or options.build_dir))
            wheel_cache = WheelCache(options.cache_dir, options.format_control)
            if options.cache_dir and not check_path_owner(options.cache_dir):
                logger.warning(
                    "The directory '%s' or its parent directory is not owned "
                    "by the current user and caching wheels has been "
                    "disabled. check the permissions and owner of that "
                    "directory. If executing pip with sudo, you may want "
                    "sudo's -H flag.",
                    options.cache_dir,
                )
                options.cache_dir = None

            with BuildDirectory(options.build_dir,
                                delete=build_delete) as build_dir:
                requirement_set = RequirementSet(
                    build_dir=build_dir,
                    src_dir=options.src_dir,
                    download_dir=options.download_dir,
                    upgrade=options.upgrade,
                    as_egg=options.as_egg,
                    ignore_installed=options.ignore_installed,
                    ignore_dependencies=options.ignore_dependencies,
                    force_reinstall=options.force_reinstall,
                    use_user_site=options.use_user_site,
                    target_dir=temp_target_dir,
                    session=session,
                    pycompile=options.compile,
                    isolated=options.isolated_mode,
                    wheel_cache=wheel_cache,
                    require_hashes=options.require_hashes,
                    find_dep_conflicts=options.find_dep_conflicts, # <~>
                    dependencies_db_file=options.dependencies_db_file, # <~>
                    conflicts_db_file=options.conflicts_db_file, # <~>
                )

                self.populate_requirement_set(
                    requirement_set, args, options, finder, session, self.name,
                    wheel_cache
                )

                if not requirement_set.has_requirements:
                    return

                try:
                    if (options.download_dir or not wheel or not
                            options.cache_dir):
                        # on -d don't do complex things like building
                        # wheels, and don't try to build wheels when wheel is
                        # not installed.
                        requirement_set.prepare_files(finder)
                    else:
                        # build wheels before install.
                        wb = WheelBuilder(
                            requirement_set,
                            finder,
                            build_options=[],
                            global_options=[],
                        )
                        # Ignore the result: a failed wheel will be
                        # installed from the sdist/vcs whatever.
                        wb.build(autobuilding=True)

                    if not options.download_dir:
                        requirement_set.install(
                            install_options,
                            global_options,
                            root=options.root_path,
                            prefix=options.prefix_path,
                        )
                        reqs = sorted(
                            requirement_set.successfully_installed,
                            key=operator.attrgetter('name'))
                        items = []
                        for req in reqs:
                            item = req.name
                            try:
                                if hasattr(req, 'installed_version'):
                                    if req.installed_version:
                                        item += '-' + req.installed_version
                            except Exception:
                                pass
                            items.append(item)
                        installed = ' '.join(items)
                        if installed:
                            logger.info('Successfully installed %s', installed)
                    else:
                        downloaded = ' '.join([
                            req.name
                            for req in requirement_set.successfully_downloaded
                        ])
                        if downloaded:
                            logger.info(
                                'Successfully downloaded %s', downloaded
                            )
                except PreviousBuildDirError:
                    options.no_clean = True
                    raise
                finally:
                    # Clean up
                    if not options.no_clean:
                        requirement_set.cleanup_files()

        if options.target_dir:
            ensure_dir(options.target_dir)

            lib_dir = distutils_scheme('', home=temp_target_dir)['purelib']

            for item in os.listdir(lib_dir):
                target_item_dir = os.path.join(options.target_dir, item)
                if os.path.exists(target_item_dir):
                    if not options.upgrade:
                        logger.warning(
                            'Target directory %s already exists. Specify '
                            '--upgrade to force replacement.',
                            target_item_dir
                        )
                        continue
                    if os.path.islink(target_item_dir):
                        logger.warning(
                            'Target directory %s already exists and is '
                            'a link. Pip will not automatically replace '
                            'links, please remove if replacement is '
                            'desired.',
                            target_item_dir
                        )
                        continue
                    if os.path.isdir(target_item_dir):
                        shutil.rmtree(target_item_dir)
                    else:
                        os.remove(target_item_dir)

                shutil.move(
                    os.path.join(lib_dir, item),
                    target_item_dir
                )
            shutil.rmtree(temp_target_dir)
        return requirement_set
