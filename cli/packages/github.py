import os
import shutil

import requests

from abc import ABC, abstractmethod
from logging import Logger
from pathlib import Path

from github import Github
from github.Repository import Repository
from github.GithubException import UnknownObjectException
from rich.console import Console
from packaging.version import parse as parse_version, Version

from .base import Package


class GithubReleasePackage(Package, ABC):
    """
    Abstract class for packages hosted on GitHub releases.

    Attributes:
        repo_name: The name of the GitHub repository.
        asset_name: The name of the asset to download.
        version_file: Path to the file storing the current version.
        prerelease: Whether or not to consider pre-releases when searching for the latest version.
    """

    def __init__(
        self,
        name: str,
        location: Path,
        repo_name: str,
        asset_name: str,
        logger: Logger,
        console: Console,
        prerelease: bool = False,
    ) -> None:
        """
        Initialize a new GithubReleasePackage instance.

        Args:
            name: The name of the package.
            location: The installation location of the package.
            repo_name: The name of the GitHub repository.
            asset_name: The name of the asset to download.
            prerelease: Whether or not to consider pre-releases when searching for the latest version.
        """
        super().__init__(name=name, location=location, logger=logger, console=console)
        self.repo_name = repo_name
        self.asset_name = asset_name
        self.versions = []
        self._repo = None
        self.version_file = location.parent / f"{self.name}.version"
        self.prerelease = prerelease

    @abstractmethod
    def version_to_tag(self, version: Version) -> str:
        """
        Format a version for use in GitHub API calls.

        Args:
            version: The version to format.

        Returns:
            The formatted version string.
        """
        pass

    @property
    def repo(self) -> Repository:
        """
        Get the GitHub repository object.

        Returns:
            The GitHub repository.
        """
        if self._repo is None:
            self._repo = Github(os.environ.get("GITHUB_TOKEN", None)).get_repo(
                self.repo_name
            )
        return self._repo

    @property
    def is_installed(self) -> bool:
        """
        Check if the package is installed.

        Returns:
            True if the package is installed, False otherwise.
        """
        return self.location.exists()

    @property
    def current_version(self) -> Version | None:
        """
        Get the currently installed version of the package.

        Returns:
            The installed version, or None if not installed.
        """
        if not self.version_file.exists():
            return None
        with self.version_file.open("r") as file:
            return parse_version(file.read())

    @current_version.setter
    def current_version(self, value: Version) -> None:
        """
        Set the current version of the package.

        Args:
            value: The version to set.
        """
        with self.version_file.open("w") as file:
            file.write(str(value))

    @property
    def latest_version(self) -> Version:
        """
        Get the latest available version of the package.

        Returns:
            The latest available version.
        """
        if self.prerelease:
            return parse_version(self.repo.get_releases().get_page(page=0)[0].tag_name)
        return parse_version(self.repo.get_latest_release().tag_name)

    def version_exists(self, version: Version) -> bool:
        """
        Check if a specific version of the package exists.

        Args:
            version: The version to check.

        Returns:
            True if the version exists, False otherwise.
        """
        try:
            self.repo.get_release(self.version_to_tag(version))
            return True
        except UnknownObjectException:
            return False

    def post_install(self) -> None:
        """
        Actions to perform after installation.
        """
        pass

    def install(self, pkg_version: Version) -> None:
        """
        Install a specific version of the package.

        Args:
            pkg_version: The version to install.

        Raises:
            ValueError: If the version does not exist.
            RuntimeError: If the download fails.
        """
        if not self.version_exists(version=pkg_version):
            raise ValueError(
                f"Package {self.name} doesn't have any version {pkg_version}."
            )
        release = self.repo.get_release(self.version_to_tag(pkg_version))
        assets = release.get_assets()
        asset = next((a for a in assets if a.name == self.asset_name), None)
        if not asset:
            raise RuntimeError(
                f"Repository {self.repo.name} has no assets with name {self.asset_name}."
            )
        response = requests.get(asset.browser_download_url, stream=True)
        if response.status_code == 200:
            with self.location.open("wb") as file:
                for chunk in response.iter_content(chunk_size=8192):
                    file.write(chunk)
            self.current_version = parse_version(release.tag_name)
        else:
            raise RuntimeError(
                f"Failed to download {asset.name} (status code: {response.status_code})."
            )

        self.post_install()

    def uninstall(self) -> None:
        """
        Uninstall the package.
        """
        if self.location.is_file():
            self.location.unlink()
        else:
            shutil.rmtree(self.location)


class TLA2Tools(GithubReleasePackage):
    """
    Concrete class for the TLA2Tools package.
    """

    def __init__(self, location: Path, logger: Logger, console: Console) -> None:
        asset_name = "tla2tools.jar"
        super().__init__(
            name="TLA2Tools",
            location=(location / asset_name),
            repo_name="tlaplus/tlaplus",
            asset_name=asset_name,
            logger=logger,
            console=console,
            prerelease=True,
        )

    def version_to_tag(self, version: Version) -> str:
        """
        Format a version for use in GitHub API calls.

        Args:
            version: The version to format.

        Returns:
            The formatted version string.
        """
        return "v" + str(version)


class CommunityModules(GithubReleasePackage):
    """
    Concrete class for the CommunityModules package.
    """

    def __init__(self, location: Path, logger: Logger, console: Console) -> None:
        asset_name = "CommunityModules-deps.jar"
        super().__init__(
            name="CommunityModules",
            location=(location / asset_name),
            repo_name="tlaplus/CommunityModules",
            asset_name=asset_name,
            logger=logger,
            console=console,
        )

    def version_to_tag(self, version: Version) -> str:
        """
        Format a version for use in GitHub API calls.

        Args:
            version: The version to format.

        Returns:
            The formatted version string.
        """
        return str(version)


class TLAPS(GithubReleasePackage):
    """
    Binaries of the TLA+ Proof System.
    """

    def __init__(self, location: Path, logger: Logger, console: Console) -> None:
        asset_name = "tlapm-1.6.0-pre-x86_64-linux-gnu.tar.gz"
        super().__init__(
            name="TLAPS",
            location=(location / asset_name),
            repo_name="tlaplus/tlapm",
            asset_name=asset_name,
            logger=logger,
            console=console,
            prerelease=True,
        )

    def version_to_tag(self, version: Version) -> str:
        """
        Format a version for use in GitHub API calls.

        Args:
            version: The version to format.

        Returns:
            The formatted version string.
        """
        return str(version).removesuffix("rc0") + "-pre"

    def post_install(self) -> None:
        """Unpack the TLAPS tarball after installation."""
        import tarfile

        with tarfile.open(self.location, "r:gz") as tar:
            tar.extractall(path=self.location.parent)
        # Remove the tarball after extraction
        self.location.unlink()
