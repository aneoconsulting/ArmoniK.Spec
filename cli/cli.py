import rich_click as click

from pathlib import Path

from rich.live import Live
from rich.spinner import Spinner
from rich.text import Text

from .constants import CONSOLE, LOGGER, TOOLS_DIR, WORKDIR
from .packages import TLA2Tools, CommunityModules
from .tools import TLC, REPL
from .utils import AliasedGroup, error_handler


@click.group(
    name="tla",
    cls=AliasedGroup,
    context_settings={
        "help_option_names": ["-h", "--help"],
        "auto_envvar_prefix": "TLA_",
    },
    invoke_without_command=True,
)
@click.version_option(version="0.1.0", prog_name="tla")
@click.pass_context
@error_handler
def cli(ctx) -> None:
    """
    Command-line tool to simplify working with TLA+.
    """
    WORKDIR.mkdir(exist_ok=True)
    TOOLS_DIR.mkdir(exist_ok=True)
    if ctx.invoked_subcommand is None:
        REPL.run()


@cli.command(name="install")
@error_handler
def tla_install() -> None:
    """Install or update TLA+ tools (TLA2Tools, Community Modules, Apalache, TLAPS) and their dependencies."""
    tools = [TLA2Tools(), CommunityModules()]
    for tool in tools:
        with Live(
            Spinner("dots", text=f"Installing latest version of {tool.name}"),
            console=CONSOLE,
            refresh_per_second=10,
        ) as live:
            try:
                tool.install_or_upgrade()
                live.update(
                    Text(f"✔ Sucessfully upgraded {tool.name}.", style="bold green")
                )
            except RuntimeError as error:
                LOGGER.exception(error)
                live.update(
                    Text(f"❌ Failed to upgrade {tool.name}.", style="bold red")
                )


@cli.command(name="model-check")
@click.argument(
    "module_path",
    type=click.Path(exists=True, dir_okay=False, resolve_path=True, path_type=Path),
    help="File containing the specification.",
)
@error_handler
def tla_model_check(module_path: Path) -> None:
    """Run TLC against a specification."""
    tlc = TLC()
    model_path = module_path.with_suffix(".cfg")
    tlc.run(module_path, model_path)


if __name__ == "__main__":
    cli()
