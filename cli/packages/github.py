import os
import shutil

import requests

from abc import ABC, abstractmethod
from pathlib import Path

from github import Github
from github.Repository import Repository
from github.GithubException import UnknownObjectException
from packaging.version import parse as parse_version, Version

from .base import Package
from ..tools import Tool


class GithubReleasePackage(Package, ABC):
    def __init__(
        self,
        name: str,
        location: Path,
        repo_name: str,
        asset_name: str,
        tools: list[str],
    ) -> None:
        super().__init__(name, location, tools)
        self.repo_name = repo_name
        self.asset_name = asset_name
        self.versions = []
        self._repo = None
        self.version_file = location.parent / f"{self.name}.version"

    @abstractmethod
    def formatted_version(self, version: Version) -> str:
        pass

    @property
    def repo(self) -> Repository:
        if self._repo is None:
            self._repo = Github(os.environ.get("GITHUB_TOKEN", None)).get_repo(
                self.repo_name
            )
        return self._repo

    @property
    def is_installed(self) -> bool:
        return self.location.exists()

    @property
    def current_version(self) -> Version | None:
        if not self.version_file.exists():
            return None
        with self.version_file.open("r") as file:
            return parse_version(file.read())

    @current_version.setter
    def current_version(self, value: Version) -> None:
        with self.version_file.open("w") as file:
            file.write(str(value))

    @property
    def latest_version(self) -> Version:
        return parse_version(self.repo.get_latest_release().tag_name)

    def version_exists(self, version: Version) -> bool:
        try:
            self.repo.get_release(self.formatted_version(version))
            return True
        except UnknownObjectException:
            return False

    def install(self, pkg_version: Version) -> None:
        if not self.version_exists(version=pkg_version):
            raise ValueError(
                f"Package {self.name} doesn't have any version {pkg_version}."
            )

        release = self.repo.get_release(self.formatted_version(pkg_version))

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

    def uninstall(self) -> None:
        if self.location.is_file():
            self.location.unlink()
        else:
            shutil.rmtree(self.location)


class TLA2Tools(GithubReleasePackage):
    def __init__(self, location: Path) -> None:
        asset_name = "tla2tools.jar"
        super().__init__(
            name="TLA2Tools",
            location=(location / asset_name),
            repo_name="tlaplus/tlaplus",
            asset_name=asset_name,
            tools=["TLC", "REPL", "TLATeX", "PCal"],
        )

    def get_tool(self, name: str) -> Tool:
        raise NotImplementedError()

    def formatted_version(self, version: Version) -> str:
        return "v" + str(version)


class CommunityModules(GithubReleasePackage):
    def __init__(self, location: Path) -> None:
        asset_name = "CommunityModules-deps.jar"
        super().__init__(
            name="CommunityModules",
            location=(location / asset_name),
            repo_name="tlaplus/CommunityModules",
            asset_name=asset_name,
            tools=[],
        )

    def formatted_version(self, version: Version) -> str:
        return str(version)

    def get_tool(self, name: str) -> Tool:
        raise ValueError(f"Package {self.name} doesn't have a tool name {name}.")
