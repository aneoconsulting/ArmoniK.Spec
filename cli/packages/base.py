from abc import ABC, abstractmethod
from pathlib import Path

from packaging.version import Version

from ..tools import Tool


class Package(ABC):
    """
    Abstract base class representing a software package for TLA+ tools.

    Attributes:
        name: The name of the package.
        location: The installation location of the package.
        tools: The list of tools provided by the package.
    """

    def __init__(self, name: str, location: Path, tools: list[str]) -> None:
        """
        Initialize a new Package instance.

        Args:
            name: The name of the package.
            location: The installation location of the package.
            tools: List of tool names provided by the package.
        """
        self.name = name
        self.location = location
        self.tools = tools

    @abstractmethod
    def get_tool(self, name: str) -> Tool:
        """
        Retrieve a tool by its name.

        Args:
            name: The name of the tool to retrieve.

        Returns:
            An instance of the requested tool.

        Raises:
            ValueError: If the name doesn't correspond to any tool.
        """
        pass

    @property
    @abstractmethod
    def is_installed(self) -> bool:
        """
        Check if the package is installed.

        Returns:
            True if the package is installed, False otherwise.
        """
        pass

    @property
    @abstractmethod
    def current_version(self) -> Version | None:
        """
        Get the currently installed version of the package.

        Returns:
            The installed version, or None if not installed.
        """
        pass

    @property
    def is_up_to_date(self) -> bool:
        """
        Check if the package is up to date.

        Returns:
            True if the package is up to date, False otherwise.
        """
        if not self.is_installed:
            return False
        if self.current_version == self.latest_version:
            return True
        return False

    @property
    @abstractmethod
    def latest_version(self) -> Version:
        """
        Get the latest available version of the package.

        Returns:
            The latest available version.
        """
        pass

    @abstractmethod
    def version_exists(self, version: Version) -> bool:
        """
        Check if a specific version of the package exists.

        Args:
            version: The version to check.

        Returns:
            True if the version exists, False otherwise.
        """
        pass

    @abstractmethod
    def install(self, pkg_version: Version) -> None:
        """
        Install a specific version of the package.

        Args:
            pkg_version: The version to install.
        """
        pass

    def upgrade(self) -> None:
        """
        Upgrade the package to the latest version.
        """
        self.install(self.latest_version)

    @abstractmethod
    def uninstall(self) -> None:
        """
        Uninstall the package.
        """
        pass
