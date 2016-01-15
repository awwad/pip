from __future__ import absolute_import

from collections import defaultdict
from itertools import chain
import logging
import os

from pip._vendor import pkg_resources
from pip._vendor import requests

from pip.compat import expanduser
from pip.download import (is_file_url, is_dir_url, is_vcs_url, url_to_path,
                          unpack_url)
from pip.exceptions import (InstallationError, BestVersionAlreadyInstalled,
                            DistributionNotFound, PreviousBuildDirError,
                            HashError, HashErrors, HashUnpinned,
                            DirectoryUrlHashUnsupported, VcsHashUnsupported,
                            DependencyConflictError) # <~>
from pip.req.req_install import InstallRequirement
from pip.utils import (
    display_path, dist_in_usersite, ensure_dir, normalize_path)
from pip.utils.hashes import MissingHashes
from pip.utils.logging import indent_log
from pip.vcs import vcs

import pip._vendor.packaging.specifiers # <~> for SpecifierSet, for conflict model 3 code
import json # <~>
# <~> Except for the log filename, will now be taking these from pip install arguments instead.
#_S_DEPENDENCIES_DB_FILENAME = "/Users/s/w/git/pypi-depresolve/dependencies_db.json"
#_S_DEPENDENCY_CONFLICTS_DB_FILENAME = "/Users/s/w/git/pypi-depresolve/conflicts_db.json"
#_S_DEPENDENCY_CONFLICTS2_DB_FILENAME = "/Users/s/w/git/pypi-depresolve/conflicts_2_db.json"
#_S_DEPENDENCY_CONFLICTS3_DB_FILENAME = "/Users/s/w/git/pypi-depresolve/conflicts_3_db.json"
#_S_DEPENDENCIES_LOG_FILENAME = "/Users/s/w/git/pypi-depresolve/_s_deps_from_pip.json"
_S_DEPENDENCIES_CONFLICT_LOG_FILENAME = "/Users/s/w/git/pypi-depresolve/conflicts_db.log"

logger = logging.getLogger(__name__)


class Requirements(object):

    def __init__(self):
        self._keys = []
        self._dict = {}

    def keys(self):
        return self._keys

    def values(self):
        return [self._dict[key] for key in self._keys]

    def __contains__(self, item):
        return item in self._keys

    def __setitem__(self, key, value):
        if key not in self._keys:
            self._keys.append(key)
        self._dict[key] = value

    def __getitem__(self, key):
        return self._dict[key]

    def __repr__(self):
        values = ['%s: %s' % (repr(k), repr(self[k])) for k in self.keys()]
        return 'Requirements({%s})' % ', '.join(values)


class DistAbstraction(object):
    """Abstracts out the wheel vs non-wheel prepare_files logic.

    The requirements for anything installable are as follows:
     - we must be able to determine the requirement name
       (or we can't correctly handle the non-upgrade case).
     - we must be able to generate a list of run-time dependencies
       without installing any additional packages (or we would
       have to either burn time by doing temporary isolated installs
       or alternatively violate pips 'don't start installing unless
       all requirements are available' rule - neither of which are
       desirable).
     - for packages with setup requirements, we must also be able
       to determine their requirements without installing additional
       packages (for the same reason as run-time dependencies)
     - we must be able to create a Distribution object exposing the
       above metadata.
    """

    def __init__(self, req_to_install):
        self.req_to_install = req_to_install

    def dist(self, finder):
        """Return a setuptools Dist object."""
        raise NotImplementedError(self.dist)

    def prep_for_dist(self):
        """Ensure that we can get a Dist for this requirement."""
        raise NotImplementedError(self.dist)


def make_abstract_dist(req_to_install):
    """Factory to make an abstract dist object.

    Preconditions: Either an editable req with a source_dir, or satisfied_by or
    a wheel link, or a non-editable req with a source_dir.

    :return: A concrete DistAbstraction.
    """
    if req_to_install.editable:
        return IsSDist(req_to_install)
    elif req_to_install.link and req_to_install.link.is_wheel:
        return IsWheel(req_to_install)
    else:
        return IsSDist(req_to_install)


class IsWheel(DistAbstraction):

    def dist(self, finder):
        return list(pkg_resources.find_distributions(
            self.req_to_install.source_dir))[0]

    def prep_for_dist(self):
        # FIXME:https://github.com/pypa/pip/issues/1112
        pass


class IsSDist(DistAbstraction):

    def dist(self, finder):
        dist = self.req_to_install.get_dist()
        # FIXME: shouldn't be globally added:
        if dist.has_metadata('dependency_links.txt'):
            finder.add_dependency_links(
                dist.get_metadata_lines('dependency_links.txt')
            )
        return dist

    def prep_for_dist(self):
        self.req_to_install.run_egg_info()
        self.req_to_install.assert_source_matches_version()


class Installed(DistAbstraction):

    def dist(self, finder):
        return self.req_to_install.satisfied_by

    def prep_for_dist(self):
        pass


class RequirementSet(object):

    def __init__(self, build_dir, src_dir, download_dir, upgrade=False,
                 ignore_installed=False, as_egg=False, target_dir=None,
                 ignore_dependencies=False, force_reinstall=False,
                 use_user_site=False, session=None, pycompile=True,
                 isolated=False, wheel_download_dir=None,
                 wheel_cache=None, require_hashes=False,
                 find_dep_conflicts=0, conflicts_db_file=None, dependencies_db_file=None): # <~>
        """Create a RequirementSet.

        :param wheel_download_dir: Where still-packed .whl files should be
            written to. If None they are written to the download_dir parameter.
            Separate to download_dir to permit only keeping wheel archives for
            pip wheel.
        :param download_dir: Where still packed archives should be written to.
            If None they are not saved, and are deleted immediately after
            unpacking.
        :param wheel_cache: The pip wheel cache, for passing to
            InstallRequirement.
        """
        if session is None:
            raise TypeError(
                "RequirementSet() missing 1 required keyword argument: "
                "'session'"
            )

        self.build_dir = build_dir
        self.src_dir = src_dir
        # XXX: download_dir and wheel_download_dir overlap semantically and may
        # be combined if we're willing to have non-wheel archives present in
        # the wheelhouse output by 'pip wheel'.
        self.download_dir = download_dir
        self.upgrade = upgrade
        self.ignore_installed = ignore_installed
        self.force_reinstall = force_reinstall
        self.requirements = Requirements()
        # Mapping of alias: real_name
        self.requirement_aliases = {}
        self.unnamed_requirements = []
        self.ignore_dependencies = ignore_dependencies
        self.successfully_downloaded = []
        self.successfully_installed = []
        self.reqs_to_cleanup = []
        self.as_egg = as_egg
        self.use_user_site = use_user_site
        self.target_dir = target_dir  # set from --target option
        self.session = session
        self.pycompile = pycompile
        self.isolated = isolated
        if wheel_download_dir:
            wheel_download_dir = normalize_path(wheel_download_dir)
        self.wheel_download_dir = wheel_download_dir
        self._wheel_cache = wheel_cache
        self.require_hashes = require_hashes
        # Maps from install_req -> dependencies_of_install_req
        self._dependencies = defaultdict(list)
        self.find_dep_conflicts = find_dep_conflicts # <~>
        self.conflicts_db_file = conflicts_db_file # <~>
        self.dependencies_db_file = dependencies_db_file # <~>



    def __str__(self):
        reqs = [req for req in self.requirements.values()
                if not req.comes_from]
        reqs.sort(key=lambda req: req.name.lower())
        return ' '.join([str(req.req) for req in reqs])

    def __repr__(self):
        reqs = [req for req in self.requirements.values()]
        reqs.sort(key=lambda req: req.name.lower())
        reqs_str = ', '.join([str(req.req) for req in reqs])
        return ('<%s object; %d requirement(s): %s>'
                % (self.__class__.__name__, len(reqs), reqs_str))

    def add_requirement(self, install_req, parent_req_name=None):
        """Add install_req as a requirement to install.

        :param parent_req_name: The name of the requirement that needed this
            added. The name is used because when multiple unnamed requirements
            resolve to the same name, we could otherwise end up with dependency
            links that point outside the Requirements set. parent_req must
            already be added. Note that None implies that this is a user
            supplied requirement, vs an inferred one.
        :return: Additional requirements to scan. That is either [] if
            the requirement is not applicable, or [install_req] if the
            requirement is applicable and has just been added.
        """
        name = install_req.name
        if not install_req.match_markers():
            logger.warning("Ignoring %s: markers %r don't match your "
                           "environment", install_req.name,
                           install_req.markers)
            return []

        install_req.as_egg = self.as_egg
        install_req.use_user_site = self.use_user_site
        install_req.target_dir = self.target_dir
        install_req.pycompile = self.pycompile
        if not name:
            # url or path requirement w/o an egg fragment
            self.unnamed_requirements.append(install_req)
            return [install_req]
        else:
            try:
                existing_req = self.get_requirement(name)
            except KeyError:
                existing_req = None
            if (parent_req_name is None and existing_req and not
                    existing_req.constraint and
                    existing_req.extras == install_req.extras):
                raise InstallationError(
                    'Double requirement given: %s (already in %s, name=%r)'
                    % (install_req, existing_req, name))
            if not existing_req:
                # Add requirement
                self.requirements[name] = install_req
                # FIXME: what about other normalizations?  E.g., _ vs. -?
                if name.lower() != name:
                    self.requirement_aliases[name.lower()] = name
                result = [install_req]
            else:
                # Assume there's no need to scan, and that we've already
                # encountered this for scanning.
                result = []
                if not install_req.constraint and existing_req.constraint:
                    if (install_req.link and not (existing_req.link and
                       install_req.link.path == existing_req.link.path)):
                        self.reqs_to_cleanup.append(install_req)
                        raise InstallationError(
                            "Could not satisfy constraints for '%s': "
                            "installation from path or url cannot be "
                            "constrained to a version" % name)
                    # If we're now installing a constraint, mark the existing
                    # object for real installation.
                    existing_req.constraint = False
                    existing_req.extras = tuple(
                        sorted(set(existing_req.extras).union(
                               set(install_req.extras))))
                    logger.debug("Setting %s extras to: %s" % (
                        existing_req, existing_req.extras))
                    # And now we need to scan this.
                    result = [existing_req]
                # Canonicalise to the already-added object for the backref
                # check below.
                install_req = existing_req
            if parent_req_name:
                parent_req = self.get_requirement(parent_req_name)
                self._dependencies[parent_req].append(install_req)
            return result

    def has_requirement(self, project_name):
        name = project_name.lower()
        if (name in self.requirements and
           not self.requirements[name].constraint or
           name in self.requirement_aliases and
           not self.requirements[self.requirement_aliases[name]].constraint):
            return True
        return False

    @property
    def has_requirements(self):
        return list(req for req in self.requirements.values() if not
                    req.constraint) or self.unnamed_requirements

    @property
    def is_download(self):
        if self.download_dir:
            self.download_dir = expanduser(self.download_dir)
            if os.path.exists(self.download_dir):
                return True
            else:
                logger.critical('Could not find download directory')
                raise InstallationError(
                    "Could not find or access download directory '%s'"
                    % display_path(self.download_dir))
        return False

    def get_requirement(self, project_name):
        for name in project_name, project_name.lower():
            if name in self.requirements:
                return self.requirements[name]
            if name in self.requirement_aliases:
                return self.requirements[self.requirement_aliases[name]]
        raise KeyError("No project with the name %r" % project_name)

    def uninstall(self, auto_confirm=False):
        for req in self.requirements.values():
            if req.constraint:
                continue
            req.uninstall(auto_confirm=auto_confirm)
            req.commit_uninstall()

    def prepare_files(self, finder):
        """
        Prepare process. Create temp directories, download and/or unpack files.
        """
        # make the wheelhouse
        if self.wheel_download_dir:
            ensure_dir(self.wheel_download_dir)

        # If any top-level requirement has a hash specified, enter
        # hash-checking mode, which requires hashes from all.
        root_reqs = self.unnamed_requirements + self.requirements.values()
        require_hashes = (self.require_hashes or
                          any(req.has_hash_options for req in root_reqs))
        if require_hashes and self.as_egg:
            raise InstallationError(
                '--egg is not allowed with --require-hashes mode, since it '
                'delegates dependency resolution to setuptools and could thus '
                'result in installation of unhashed packages.')

        # Actually prepare the files, and collect any exceptions. Most hash
        # exceptions cannot be checked ahead of time, because
        # req.populate_link() needs to be called before we can make decisions
        # based on link type.
        discovered_reqs = []
        hash_errors = HashErrors()
        #ipdb.set_trace() # <~>
        for req in chain(root_reqs, discovered_reqs):
            try:
                discovered_reqs.extend(self._prepare_file(
                    finder,
                    req,
                    require_hashes=require_hashes,
                    ignore_dependencies=self.ignore_dependencies))
            except HashError as exc:
                exc.req = req
                hash_errors.append(exc)

        if hash_errors:
            raise hash_errors

        # <~> Conflict detection - no type 1 or type 2 conflicts detected.
        if self.find_dep_conflicts in [1, 2]:
          print("    <~> Success! - found no dependency conflicts.")
          self._s_report_conflict(False, "")
        elif self.find_dep_conflicts == 3:
          #import ipdb
          #ipdb.set_trace()
          #print("Currently writing conflict model 3 detection code.")

          # Here, we process the requirements.
          # self.requirements.keys() yields project names
          # self.requirements.values() yields InstalRequirement values
          # From there, we have two options:
          #      #1 - using project and version, look things up in my deps db
          #   or #2 - figure out how to pluck deps out of the InstallRequirements (would be easy with a dist, but don't have those here in the code).
          # WRT #1, In the worst case, I can use self.requirements.values()[n].link to get the link of the nth requirement.
          #
          # I'll start by trying #1
          # Yeah, version info not being available afterwards for a given requirement is a nuisance.
          # Let's just change that by adding it to the InstallRequirement class once and for all. /:

          # Done.... Let's now see if it's available.

          # Populate a list of the set of install candidates finally chosen by pip to install together in order to
          #   satisfy the initial install requirement passed to pip.
          candidates_chosen_by_pip = []
          versions_chosen_by_pip = dict() # will also populate this for now. redundant, but convenient at the moment.
          for req in self.requirements.values():
            # Get the key used to indicate that sdist in our dependencies db.
            req_key = _s_distkey_format(req.name, req.version)
            candidates_chosen_by_pip.append(req_key)
            versions_chosen_by_pip[req.name.lower()] = req.version
          
          # Walk through that list and check the dependencies of each item in our dependencies db.
          # If pip has avoided a dependency conflict, all of these dependencies should be satisfied by
          #   something in the candidates_chosen_by_pip list.
          # For every pip-selected install requirement:
          for req_key in candidates_chosen_by_pip:
            # For every registered dependency of this sdist in the dependencies db:
            for dep in dependencies_by_dist[req_key]:
              # Check to see if that dependency is met by something in the set of install requirements pip chose.
              package_name = dep[0].lower()
              list_of_spec_tuples = dep[1]
              specstring = ""
              # dep is a 2-tuple, first entry package name, second entry list of tuples (each constituting a specifier)
              #  e.g.  ('motor', [ [ '>', '0.4.0' ], [ '<', '0.6.6'] ])
              #    indicating: depends on package motor, version > 0.4.0, version < 0.6.6
              # Start by characterizing the dependency as a package name and SpecifierSet.
              for specification in list_of_spec_tuples: # for each specification (example specification: [ '>', '0.4.0' ]) in the list of specs:
                # append the operator and operand (version string) back together, with distinct specifiers separated by commas.
                specstring += specification[0] + specification[1] + ","

              # Trim trailing comma after loop.
              if specstring.endswith(','):
                specstring = specstring[:-1]

              specset = pip._vendor.packaging.specifiers.SpecifierSet(specstring)

              # Now we have a SpecifierSet for this dependency.
              # One of the capabilities of pip's SpecifierSet is to filter a list of version strings,
              #   returning only those that satisfy. We will be applying this filter to the list of
              #   (exactly 1) versions of the given package that pip is intending to install (the
              #   candidates_chosen_by_pip list). If the result is empty, pip has failed to satisfy
              #   the dependency. If it is not empty (that is, if it has the one version provided
              #   still in there), then pip has satisfied the dependency.
              filtered_output = None
              try:
                filtered_output = specset.filter([versions_chosen_by_pip[package_name]])
              except KeyError:
                # todo: handle key error in case of pip weirdness resulting in no version selected at all for a depended on package
                import ipdb
                ipdb.set_trace()
                
                #print("    " + req_key + " depends on " + str(dep) + " but pip has not selected ANY version of " + package_name)
                #exception_string = '   TENTATIVE Model ' + str(self.find_dep_conflicts) + ' conflict detected:\n    '
                #exception_string += req_key + " depends on " + str(dep)
                #exception_string += " but pip has not selected ANY version of " + package_name
                #exception_string += "\n   pip's install candidates: " str(candidates_chosen_by_pip)
                #self._s_report_conflict(True, exception_string)
                #raise DependencyConflictError(exception_string)
                raise

              filtered = [x for x in filtered_output] # filtered_output from specset.filter is a generator. I just want a list to get len().
              if filtered: # if list is not empty
                assert( len(filtered) == 1 ) # should never have more than 1 - pip chooses one version of each package only. filtering the choices for each package should produce 1 or 0 results.
                print ("    Satisfied: " + req_key + "'s dependency on " + str(dep) + " has been met by pip's choice of version " + filtered[0])
              else:
                exception_string = '   Model ' + str(self.find_dep_conflicts) + ' conflict detected:\n    '
                exception_string += req_key + " depends on " + str(dep)
                exception_string += " and pip has selected inconsistent version " + versions_chosen_by_pip[package_name]
                self._s_report_conflict(True, exception_string)
                raise DependencyConflictError(exception_string)

            # end of for each dep in dependencies_by_dist
          # end of for each req_key in candidates_chosen_by_pip
          
          # We have not found a model 3 conflict.
          #ipdb.set_trace()
          self._s_report_conflict(False, "")
          
        # <~> end end-of-prep conflict reporting/detection section

    def _check_skip_installed(self, req_to_install, finder):
        """Check if req_to_install should be skipped.

        This will check if the req is installed, and whether we should upgrade
        or reinstall it, taking into account all the relevant user options.

        After calling this req_to_install will only have satisfied_by set to
        None if the req_to_install is to be upgraded/reinstalled etc. Any
        other value will be a dist recording the current thing installed that
        satisfies the requirement.

        Note that for vcs urls and the like we can't assess skipping in this
        routine - we simply identify that we need to pull the thing down,
        then later on it is pulled down and introspected to assess upgrade/
        reinstalls etc.

        :return: A text reason for why it was skipped, or None.
        """
        # Check whether to upgrade/reinstall this req or not.
        req_to_install.check_if_exists()
        if req_to_install.satisfied_by:
            skip_reason = 'satisfied (use --upgrade to upgrade)'
            if self.upgrade:
                best_installed = False
                # For link based requirements we have to pull the
                # tree down and inspect to assess the version #, so
                # its handled way down.
                if not (self.force_reinstall or req_to_install.link):
                    try:
                        finder.find_requirement(req_to_install, self.upgrade)
                    except BestVersionAlreadyInstalled:
                        skip_reason = 'up-to-date'
                        best_installed = True
                    except DistributionNotFound:
                        # No distribution found, so we squash the
                        # error - it will be raised later when we
                        # re-try later to do the install.
                        # Why don't we just raise here?
                        pass

                if not best_installed:
                    # don't uninstall conflict if user install and
                    # conflict is not user install
                    if not (self.use_user_site and not
                            dist_in_usersite(req_to_install.satisfied_by)):
                        req_to_install.conflicts_with = \
                            req_to_install.satisfied_by
                    req_to_install.satisfied_by = None
            return skip_reason
        else:
            return None

    def _prepare_file(self,
                      finder,
                      req_to_install,
                      require_hashes=False,
                      ignore_dependencies=False):
        """Prepare a single requirements file.

        :return: A list of additional InstallRequirements to also install.
        """
        # Tell user what we are doing for this requirement:
        # obtain (editable), skipping, processing (local url), collecting
        # (remote url or package name)
        if req_to_install.constraint or req_to_install.prepared:
            return []

        req_to_install.prepared = True

        # ###################### #
        # # print log messages # #
        # ###################### #
        if req_to_install.editable:
            logger.info('Obtaining %s', req_to_install)
        else:
            # satisfied_by is only evaluated by calling _check_skip_installed,
            # so it must be None here.
            assert req_to_install.satisfied_by is None
            if not self.ignore_installed:
                skip_reason = self._check_skip_installed(
                    req_to_install, finder) # determine whether or not to skip this requirement based on several options and install state

            if req_to_install.satisfied_by:
                assert skip_reason is not None, (
                    '_check_skip_installed returned None but '
                    'req_to_install.satisfied_by is set to %r'
                    % (req_to_install.satisfied_by,))
                logger.info(
                    'Requirement already %s: %s', skip_reason,
                    req_to_install)
            else:
                if (req_to_install.link and
                        req_to_install.link.scheme == 'file'):
                    path = url_to_path(req_to_install.link.url)
                    logger.info('Processing %s', display_path(path))
                else:
                    logger.info('Collecting %s', req_to_install)

        with indent_log():
            # ################################ #
            # # vcs update or unpack archive # #
            # ################################ #
            if req_to_install.editable:
                if require_hashes:
                    raise InstallationError(
                        'The editable requirement %s cannot be installed when '
                        'requiring hashes, because there is no single file to '
                        'hash.' % req_to_install)
                req_to_install.ensure_has_source_dir(self.src_dir)
                req_to_install.update_editable(not self.is_download)
                abstract_dist = make_abstract_dist(req_to_install)
                abstract_dist.prep_for_dist()
                if self.is_download:
                    req_to_install.archive(self.download_dir)
            elif req_to_install.satisfied_by:
                if require_hashes:
                    logger.debug(
                        'Since it is already installed, we are trusting this '
                        'package without checking its hash. To ensure a '
                        'completely repeatable environment, install into an '
                        'empty virtualenv.')
                abstract_dist = Installed(req_to_install)
            else:
                # @@ if filesystem packages are not marked
                # editable in a req, a non deterministic error
                # occurs when the script attempts to unpack the
                # build directory
                req_to_install.ensure_has_source_dir(self.build_dir)
                # If a checkout exists, it's unwise to keep going.  version
                # inconsistencies are logged later, but do not fail the
                # installation.
                # FIXME: this won't upgrade when there's an existing
                # package unpacked in `req_to_install.source_dir`
                if os.path.exists(
                        os.path.join(req_to_install.source_dir, 'setup.py')):
                    raise PreviousBuildDirError(
                        "pip can't proceed with requirements '%s' due to a"
                        " pre-existing build directory (%s). This is "
                        "likely due to a previous installation that failed"
                        ". pip is being responsible and not assuming it "
                        "can delete this. Please delete it and try again."
                        % (req_to_install, req_to_install.source_dir)
                    )
                req_to_install.populate_link(
                    finder, self.upgrade, require_hashes)
                # We can't hit this spot and have populate_link return None.
                # req_to_install.satisfied_by is None here (because we're
                # guarded) and upgrade has no impact except when satisfied_by
                # is not None.
                # Then inside find_requirement existing_applicable -> False
                # If no new versions are found, DistributionNotFound is raised,
                # otherwise a result is guaranteed.
                assert req_to_install.link
                link = req_to_install.link

                # Now that we have the real link, we can tell what kind of
                # requirements we have and raise some more informative errors
                # than otherwise. (For example, we can raise VcsHashUnsupported
                # for a VCS URL rather than HashMissing.)
                if require_hashes:
                    # We could check these first 2 conditions inside
                    # unpack_url and save repetition of conditions, but then
                    # we would report less-useful error messages for
                    # unhashable requirements, complaining that there's no
                    # hash provided.
                    if is_vcs_url(link):
                        raise VcsHashUnsupported()
                    elif is_file_url(link) and is_dir_url(link):
                        raise DirectoryUrlHashUnsupported()
                    if (not req_to_install.original_link and
                            not req_to_install.is_pinned):
                        # Unpinned packages are asking for trouble when a new
                        # version is uploaded. This isn't a security check, but
                        # it saves users a surprising hash mismatch in the
                        # future.
                        #
                        # file:/// URLs aren't pinnable, so don't complain
                        # about them not being pinned.
                        raise HashUnpinned()
                hashes = req_to_install.hashes(
                    trust_internet=not require_hashes)
                if require_hashes and not hashes:
                    # Known-good hashes are missing for this requirement, so
                    # shim it with a facade object that will provoke hash
                    # computation and then raise a HashMissing exception
                    # showing the user what the hash should be.
                    hashes = MissingHashes()

                try:
                    download_dir = self.download_dir
                    # We always delete unpacked sdists after pip ran.
                    autodelete_unpacked = True
                    if req_to_install.link.is_wheel \
                            and self.wheel_download_dir:
                        # when doing 'pip wheel` we download wheels to a
                        # dedicated dir.
                        download_dir = self.wheel_download_dir
                    if req_to_install.link.is_wheel:
                        if download_dir:
                            # When downloading, we only unpack wheels to get
                            # metadata.
                            autodelete_unpacked = True
                        else:
                            # When installing a wheel, we use the unpacked
                            # wheel.
                            autodelete_unpacked = False
                    unpack_url(
                        req_to_install.link, req_to_install.source_dir,
                        download_dir, autodelete_unpacked,
                        session=self.session, hashes=hashes)
                except requests.HTTPError as exc:
                    logger.critical(
                        'Could not install requirement %s because '
                        'of error %s',
                        req_to_install,
                        exc,
                    )
                    raise InstallationError(
                        'Could not install requirement %s because '
                        'of HTTP error %s for URL %s' %
                        (req_to_install, exc, req_to_install.link)
                    )
                abstract_dist = make_abstract_dist(req_to_install)
                abstract_dist.prep_for_dist()
                if self.is_download:
                    # Make a .zip of the source_dir we already created.
                    if req_to_install.link.scheme in vcs.all_schemes:
                        req_to_install.archive(self.download_dir)
                # req_to_install.req is only avail after unpack for URL
                # pkgs repeat check_if_exists to uninstall-on-upgrade
                # (#14)
                if not self.ignore_installed:
                    req_to_install.check_if_exists()
                if req_to_install.satisfied_by:
                    if self.upgrade or self.ignore_installed:
                        # don't uninstall conflict if user install and
                        # conflict is not user install
                        if not (self.use_user_site and not
                                dist_in_usersite(
                                    req_to_install.satisfied_by)):
                            req_to_install.conflicts_with = \
                                req_to_install.satisfied_by
                        req_to_install.satisfied_by = None
                    else:
                        logger.info(
                            'Requirement already satisfied (use '
                            '--upgrade to upgrade): %s',
                            req_to_install,
                        )

            # ###################### #
            # # parse dependencies # #
            # ###################### #
            dist = abstract_dist.dist(finder)
            more_reqs = []

            req_to_install.version = dist.version # <~> Add version info to this install requirement, to be used later in conflict model 3 checking.

            def add_req(subreq):
                #import ipdb # <~>
                #ipdb.set_trace() # <~>
                sub_install_req = InstallRequirement(
                    str(subreq),
                    req_to_install,
                    isolated=self.isolated,
                    wheel_cache=self._wheel_cache,
                    #version=dist.version, # <~> for addition of version info to InstallRequirement - see change to InstallRequirement class (req_install.py) # Nope, this would be wrong - would be adding depending install requirement's version to depended-on install requirement. Correct way added. Leaving this commented out here in case I need it later.
                )
                more_reqs.extend(self.add_requirement(
                    sub_install_req, req_to_install.name))

            # We add req_to_install before its dependencies, so that we
            # can refer to it when adding dependencies.
            if not self.has_requirement(req_to_install.name):
                # 'unnamed' requirements will get added here
                self.add_requirement(req_to_install, None)

            if not ignore_dependencies:
                if (req_to_install.extras):
                    logger.debug(
                        "Installing extra requirements: %r",
                        ','.join(req_to_install.extras),
                    )
                missing_requested = sorted(
                    set(req_to_install.extras) - set(dist.extras)
                )
                for missing in missing_requested:
                    logger.warning(
                        '%s does not provide the extra \'%s\'',
                        dist, missing
                    )

                available_requested = sorted(
                    set(dist.extras) & set(req_to_install.extras)
                )
                

                # <~> -------------------------------
                # <~> adding package dependency recording
                #     (This obviously needs to be tidied up! Bad big O, etc.)
                #     JSON can't use a tuple-keyed dictionary, so for the dependencies
                #       dict, I'm using a single string with parens. (See distkey below.)
                #     A JSON is remarkably inefficient for frequent rewriting, so this
                #       should probably be changed to pickle or sqlite or something.
                #     I did not want to make a mess of pip's normal return stack, so I
                #       didn't take that (most natural) route.
                # <~> -------------------------------
                #ipdb.set_trace()
                if self.find_dep_conflicts in [1, 2, 3]:
                  import time as stdlib_time
                  #print("  Code sanity check: File "+__file__+", modified date is: "+stdlib_time.ctime(os.path.getmtime(__file__)))
                  #ipdb.set_trace()
                  ## Todo: here, need to save information about the initial requirements,
                  ##   since it's not apparently possible to retrieve dist info for them
                  ##   later, when we need it to store conflict information.
                  if req_to_install.comes_from is None:
                    # If self._s_initial_install_requirement_key is already defined, assert False.
                    # My code assumes we are instructed to install only one package (using --find-dep-conflicts, etc.)
                    try:
                      self._s_initial_install_requirement_key
                    except AttributeError:
                      pass  # Good, it's not already defined.
                    else:
                      #ipdb.set_trace()
                      assert False, "<~> We should never encounter a second initial install requirement. This code is written to handle one initial install requirement. If this is reached, perhaps I've made a bad assumption about when comes_from is set?"
                    # Now save the initial requirement.
                    self._s_initial_install_requirement_key = _s_get_distkey(dist)

                  dist_reqs = dist.requires(available_requested)
                  global dependencies_by_dist # rushing for now
                  # Ensure that the dependency dictionary is defined, importing it from its file if not.
                  _s_ensure_dependencies_global_defined(self.dependencies_db_file)

                  distkey = _s_get_distkey(dist)
                
                  # <~> Adding a temp and switching up the control structure to get around an issue noted in daily notes,
                  #       near end of day Wed Jan 13 2016. See daily notes.
                  #     This is not excellent because of the equality check between the temp and the db.
                  #     It is not exactly what is needed, I don't think.... But rushing right now and must fix later.
                  #     It will err on the side of extra work, not the side of being wrong.
                  this_dist_deps_temp = []
                  for subreq in dist_reqs:
                    this_dist_deps_temp.append( [subreq.project_name.lower(), subreq.specs] ) # now using lowercase; now using list for equality test since the json load yields lists, too /:
                  # This is not excellent because of the equality check.
                  if distkey not in dependencies_by_dist or not _s_deps_are_equal(dependencies_by_dist[distkey], this_dist_deps_temp):
                    dependencies_by_dist[distkey] = this_dist_deps_temp
                    print("    " + str(dist), "depends on", str(dist_reqs))
                    # <~> Write the dependency data from the global back to file.
                    #     This is exceedingly often, but I would rather not lose any dependency data,
                    #       and I would also rather not have an enormous try/except that writes and
                    #       then re-raises.
                    _s_write_dependencies_global(self.dependencies_db_file)


                # <~> -------------------------------
                # <~> end - of package dependency recording section
                # <~> -------------------------------

                for subreq in dist.requires(available_requested): # dist.requires returns all the requirements parsed for this dist

                    # <~> -------------------------------
                    # <~> adding conflict detection
                    # <~> -------------------------------
                    # Does this subreq's package name exist in the existing requirements for this requirement set?
                    # if subreq.key in [v.req.key for v in self.requirements.values()]:
                    #   print("    <~> Potential conflict detected: pre-existing requirement.")
                    if self.find_dep_conflicts in [1, 2]:
                      for old_install_req in self.requirements.values():

                        if old_install_req.req.project_name == subreq.project_name:
                          # CONFLICT MODEL 1 CODE FOLLOWS:
                          if self.find_dep_conflicts == 1 and old_install_req.req.specs == subreq.specs: # Conflict Type 1 and A-OK.
                            #print("    <~> Debug Info: Multiple packages to be installed have the same dependency, but the requirement specification is the same. All is well.")
                            pass
                          elif self.find_dep_conflicts == 1: # Conflict Type 1 and NOT OK.
                            exception_string = '   Model ' + str(self.find_dep_conflicts) + ' conflict detected:\n    '
                            if old_install_req.comes_from is None:
                              exception_string += 'original instruction included requirement '
                            else:
                              exception_string += 'First, found that ' + old_install_req.comes_from.name + ' had requirement '
                            exception_string += str(old_install_req.req)
                            exception_string += '\n    Then, found that ' + str(dist) +' has requirement '+ str(subreq) + '\n'
                            self._s_report_conflict(True, exception_string)
                            raise DependencyConflictError(exception_string)
                          # END OF CONFLICT MODEL 1 CODE
                          # Else we're using conflict model 2
                          # CONFLICT MODEL 2 CODE FOLLOWS
                          else:
                            # Here is where we need to test to see if pip.index.PackageFinder.find_requirement returns
                            #   the same link for the new subreq and for the old_install_req it matches.
                            # If so, we continue along happily.
                            # If not, we have encountered a conflict of type 2.
                            assert(self.find_dep_conflicts == 2) # Shouldn't be able to get to this spot in the code unless find_dep_conflicts is 2.
                            new_link = finder.find_requirement(InstallRequirement(subreq, None), False) # <~> Later comment: I have a vague suspicion this line may have unintended consequences. The instantiation of a temporary, throw-away InstallRequirement may impact other things. No clear evidence of impact yet. Investigate later.
                            old_link = finder.find_requirement(old_install_req, False)
                            if new_link == old_link:
                              # Conflict Type 2 and A-OK.
                              #print("    <~> Debug Info: Multiple packages to be installed have the same dependency, but the first-choice package selected by pip for both packages resolves to the same one. old_link="+str(old_link),"and new_link="+str(new_link))
                              pass
                            else: # Conflict Type 2 and NOT OK.
                              #ipdb.set_trace()
                              exception_string = '   Model ' + str(self.find_dep_conflicts) + ' conflict detected:\n    '
                              if old_install_req.comes_from is None:
                                exception_string += 'original instruction included requirement '
                              else:
                                exception_string += 'First, found that ' + old_install_req.comes_from.name + ' had requirement '
                              exception_string += str(old_install_req.req)
                              exception_string += '\n    Then, found that ' + str(dist) +' has requirement '+ str(subreq) + '\n'
                              exception_string += 'Link Resolution:\n      Old req link: '+str(old_link)+'\n      New req link: '+str(new_link)+'\n'
                              self._s_report_conflict(True, exception_string)
                              raise DependencyConflictError(exception_string)
                          # END OF CONFLICT MODEL 2 CODE
                        # end of if there is a package name collision in dependencies  
                      # end of loop over each pre-existing install requirement
                    # <~> -------------------------------
                    # <~> end - of conflict detection section
                    # <~> -------------------------------
                    add_req(subreq) # and here, we add them to the requirement set via helper function above

            # cleanup tmp src
            self.reqs_to_cleanup.append(req_to_install)

            if not req_to_install.editable and not req_to_install.satisfied_by:
                # XXX: --no-install leads this to report 'Successfully
                # downloaded' for only non-editable reqs, even though we took
                # action on them.
                self.successfully_downloaded.append(req_to_install)

        return more_reqs

    def cleanup_files(self):
        """Clean up files, remove builds."""
        logger.debug('Cleaning up...')
        with indent_log():
            for req in self.reqs_to_cleanup:
                req.remove_temporary_source()

    def _to_install(self):
        """Create the installation order.

        The installation order is topological - requirements are installed
        before the requiring thing. We break cycles at an arbitrary point,
        and make no other guarantees.
        """
        # The current implementation, which we may change at any point
        # installs the user specified things in the order given, except when
        # dependencies must come earlier to achieve topological order.
        order = []
        ordered_reqs = set()

        def schedule(req):
            if req.satisfied_by or req in ordered_reqs:
                return
            if req.constraint:
                return
            ordered_reqs.add(req)
            for dep in self._dependencies[req]:
                schedule(dep)
            order.append(req)
        for install_req in self.requirements.values():
            schedule(install_req)
        return order

    def install(self, install_options, global_options=(), *args, **kwargs):
        """
        Install everything in this set (after having downloaded and unpacked
        the packages)
        """
        to_install = self._to_install()

        if to_install:
            logger.info(
                'Installing collected packages: %s',
                ', '.join([req.name for req in to_install]),
            )

        with indent_log():
            for requirement in to_install:
                if requirement.conflicts_with:
                    logger.info(
                        'Found existing installation: %s',
                        requirement.conflicts_with,
                    )
                    with indent_log():
                        requirement.uninstall(auto_confirm=True)
                try:
                    requirement.install(
                        install_options,
                        global_options,
                        *args,
                        **kwargs
                    )
                except:
                    # if install did not succeed, rollback previous uninstall
                    if (requirement.conflicts_with and not
                            requirement.install_succeeded):
                        requirement.rollback_uninstall()
                    raise
                else:
                    if (requirement.conflicts_with and
                            requirement.install_succeeded):
                        requirement.commit_uninstall()
                requirement.remove_temporary_source()

        self.successfully_installed = to_install


    # <~> Class method to report that a given initial requirement has or has not resulted in a dependency conflict.
    def _s_report_conflict(self, conflict_exists, exception_string):
      assert(conflict_exists in [True, False]) # Expecting a boolean.
      assert(type(exception_string) is str) # Expecting a string.

      if conflict_exists:
        with open(_S_DEPENDENCIES_CONFLICT_LOG_FILENAME,"a") as fobj_conflicts_log:
          fobj_conflicts_log.write(exception_string)

      # <~> Fetch initial install requirement, stored earlier.
      try:
        self._s_initial_install_requirement_key
      except AttributeError as exc:
        assert False, "<~> Coding error."+str(exc)

      global conflicts_by_dist
      _s_ensure_dep_conflicts_global_defined(self.find_dep_conflicts, self.conflicts_db_file)

      ### Turns out we can't use get_dist(). Temp file is deleted? Not treated as a valid dist? Dist has ambiguous semantics, perhaps?
      ##initial_req_distkey = _s_get_distkey(initial_req.get_dist())
      conflicts_by_dist[self._s_initial_install_requirement_key] = conflict_exists
      print("  Adding",self._s_initial_install_requirement_key,"to Model " + str(self.find_dep_conflicts) + " conflicts db. (Conflict: " + str(conflict_exists) + ")")
      _s_write_dep_conflicts_global(self.find_dep_conflicts, self.conflicts_db_file)
      
  
      
# <~> end of class RequirementSet



# <~> Helper functions to determine the key for a given distribution to be used in the
#       dependency conflict db and the dependencies db.
#     Updating to make lowercase.
#     Splitting into two calls to allow for use on either a dist object or just name and version strings.
def _s_get_distkey(dist):
  #return dist.project_name.lower() + "(" + dist.version + ")"
  return _s_distkey_format(dist.project_name, dist.version)
def _s_distkey_format(name, version):
  return name.lower() + "(" + version + ")"


# <~> Helper function to write the dependencies global to its file.
def _s_write_dependencies_global(dependencies_db_filename):
  global dependencies_by_dist
  with open(dependencies_db_filename,"w") as fobj:
    json.dump(dependencies_by_dist, fobj)

# <~> Helper function to ensure that the global dependencies dictionary is defined,
#       importing it now if not.
def _s_ensure_dependencies_global_defined(dependencies_db_filename):
  global dependencies_by_dist
  try: # If the global is not defined yet, load the contents of the json file.
    dependencies_by_dist
  except NameError:
    dependencies_by_dist = None
    # Fill with JSON data from file.
    # If the dependencies db file doesn't exist, create it (open in append mode and close).
    if not os.path.exists(dependencies_db_filename):
      open(dependencies_db_filename, 'a').close()
    # Open the dependencies db file and then try parsing it as a json.
    # If the parse fails, just make an empty dict instead, and we'll overwrite the file later.
    with open(dependencies_db_filename,"r") as fobj:
      try:
        dependencies_by_dist = json.load(fobj)
      except ValueError:
        dependencies_by_dist = dict() # If it was invalid or empty, replace with empty.

# <~> Helper function to ensure that the global dependency conflicts dictionary is defined,
#       importing it now if not.
def _s_ensure_dep_conflicts_global_defined(conflict_model, conflicts_db_filename):
  # Ensure we're only using one conflict model. These are bools.
  #assert( use_model_1 + use_model_2 + use_model_3 == 1 )
  assert(conflict_model in [1,2,3])

  global conflicts_by_dist
  try: # If the global is not defined yet, load the contents of the json file.
    conflicts_by_dist
  except NameError:
    conflicts_by_dist = None
    # <~> Fill with JSON data from file.
    # If the conflicts db file doesn't exist, create it (open in append mode and close).
    if not os.path.exists(conflicts_db_filename):
      open(conflicts_db_filename, 'a').close()
    # Open the conflicts db file and then try parsing it as a json.
    # If the parse fails, just make an empty dict instead, and we'll overwrite the file later.
    with open(conflicts_db_filename,"r") as fobj:
      try:
        conflicts_by_dist = json.load(fobj)
      except ValueError:
        conflicts_by_dist = dict() # If it was invalid or empty, replace with empty.

# <~> Helper function to write the dependencies conflicts global to its file.
def _s_write_dep_conflicts_global(conflict_model, conflicts_db_filename):
  ## Ensure we're only using one conflict model. These are bools.
  #assert( use_model_1 + use_model_2 + use_model_3 == 1 )
  assert(conflict_model in [1,2,3])

  global conflicts_by_dist

  with open(conflicts_db_filename,"w") as fobj:
    json.dump(conflicts_by_dist, fobj)

# <~> Returns true if given lists of dependencies that are equivalent (regardless of order).
#     Expects e.g.:
#        a =  [ [ 'foo', [ '==', '1.0' ] ],
#               [ 'bar', [] ],
#               [ 'bat', ['>=', '1.57'], ['<=', '1.57.99'] ] 
#
#        b =  [ [ 'bat', ['>=', '1.57'], ['<=', '1.57.99'] ], 
#               [ 'foo', [ '==', '1.0' ] ],
#               [ 'bar', [] ] ]
#
#     Specifically, it returns true if every element in the first list is in the second list
#       and vice versa. Also returns true if both are empty lists.
#     This is not fast, but it's a hell of a lot faster than writing a large json to disk.
#
#     set(deps_a) == set(deps_b)         would be nice, but lists aren't hashable
#     sorted(deps_a) == sorted(deps_b)   may be faster - O( NlogN ) rather than O( N^2 )
#
#      Yeah, let's go with sorted instead of original solution. Faster and tidier.
#
def _s_deps_are_equal(deps_a, deps_b):
  #if not deps_a and not deps_b:
  #  return True
  #else:
  #  all_a_in_b = False in [dep in deps_b for dep in deps_a]
  #  all_b_in_a = False in [dep in deps_a for dep in deps_b]
  #  equality = all_a_in_b and all_b_in_a
  #  #if not equality:
  #  #  print("  Stored deps and freshly harvested deps not equal: \n    " + str(deps_a) + "\n    " + str(deps_b))
  #  return equality #all_a_in_b and all_b_in_a
  equality = sorted(deps_a) == sorted(deps_b)
  if not equality:
    print("  Debug: Stored deps and freshly harvested deps ARE NOT EQUAL: \n    " + str(deps_a) + "\n    " + str(deps_b))
  #else:
  #  print("  Stored deps and freshly harvested deps are equal: \n    " + str(deps_a) + "\n    " + str(deps_b))
  return equality
