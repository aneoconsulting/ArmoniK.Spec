from abc import ABC, abstractmethod
from pathlib import Path

from packaging.version import Version

from ..tools import Tool


class Package(ABC):
    def __init__(self, name: str, location: Path, tools: list[str]) -> None:
        self.name = name
        self.location = location
        self.tools = tools

    @abstractmethod
    def get_tool(self, name: str) -> Tool:
        pass

    @property
    @abstractmethod
    def is_installed(self) -> bool:
        pass

    @property
    @abstractmethod
    def current_version(self) -> Version | None:
        pass

    @property
    def is_up_to_date(self) -> bool:
        if not self.is_installed:
            return False
        if self.current_version == self.latest_version:
            return True
        return False

    @property
    @abstractmethod
    def latest_version(self) -> Version:
        pass

    @abstractmethod
    def version_exists(self, version: Version) -> bool:
        pass

    @abstractmethod
    def install(self, pkg_version: Version) -> None:
        pass

    def upgrade(self) -> None:
        self.install(self.latest_version)

    @abstractmethod
    def uninstall(self) -> None:
        pass
