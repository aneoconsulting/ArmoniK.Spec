import rich_click as click

from functools import partial, wraps
from typing import Any, Callable, Optional

from .constants import CONSOLE
from .exceptions import ToolRuntimeError, BaseCliError


def error_handler(func: Optional[Callable[..., Any]] = None) -> Callable[..., Any]:
    """
    Decorator to handle errors for Click commands and ensure proper error display.

    Args:
        func: The command function to be decorated. If None, a partial function is returned,
            allowing the decorator to be used with parentheses.

    Returns:
        The wrapped function with error handling.
    """
    if func is None:
        return partial(error_handler)

    @wraps(func)
    def wrapper(*args, **kwargs):
        try:
            return func(*args, **kwargs)
        except ToolRuntimeError:
            raise
        except Exception as e:
            CONSOLE.print_exception()
            raise BaseCliError(f"CLI errored with exception:\n{e}") from e

    return wrapper


class AliasedGroup(click.RichGroup):
    """A Click Group subclass that supports command aliases.

    This class extends `click.Group` to allow commands to be invoked using
    alternative names (aliases). For example, the alias "mc" can be used
    to invoke the "model-check" command.
    """

    def get_command(self, ctx: click.Context, cmd_name: str) -> click.Command | None:
        """Resolve a command by name, supporting command aliases.

        Args:
            ctx: The current Click context.
            cmd_name: The name of the command to resolve.

        Returns:
            The resolved Click command, or None if not found.
        """
        rv = super().get_command(ctx, cmd_name)
        if rv is not None:
            return rv
        if cmd_name == "mc":
            return click.Group.get_command(self, ctx, "model-check")
        elif cmd_name == "pc":
            return click.Group.get_command(self, ctx, "proof-check")
        return None

    def resolve_command(
        self, ctx: click.Context, args: list[str]
    ) -> tuple[str | None, click.Command | None, list[str]]:
        """Resolve the command and arguments, ensuring the full command name is returned.

        Args:
            ctx: The current Click context.
            args: The list of command-line arguments.

        Returns:
            A tuple of (command name, command object, remaining arguments).
        """
        _, cmd, args = super().resolve_command(ctx, args)
        return cmd.name if cmd is not None else None, cmd, args
