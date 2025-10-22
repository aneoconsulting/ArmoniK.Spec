from abc import ABC
from logging import Logger

from rich.console import Console

from ..packages import Package


class Tool(ABC):
    def __init__(
        self, name: str, pkg: Package, logger: Logger, console: Console
    ) -> None:
        self.name = name
        self.pkg = pkg
        self.logger = logger
        self.console = console

    def is_available(self) -> bool:
        return self.pkg.is_installed
