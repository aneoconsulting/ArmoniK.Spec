from rich.panel import Panel
from rich_click import ClickException

from .constants import CONSOLE


class BaseCliError(ClickException):
    """Base exception for CLI errors."""

    def __init__(self, message: str) -> None:
        super().__init__(message)

    def show(self, file=None):
        """Override to display errors in a cleaner format."""
        CONSOLE.print(Panel(self.format_message(), title="Error", style="red"))


class InternalCliError(BaseCliError):
    """Error raised when an unknown internal error occured."""

    exit_code = 3


class ToolRuntimeError(BaseCliError):
    """Error raised when a TLA+ tool returns an error at runtime."""

    exit_code = 4
