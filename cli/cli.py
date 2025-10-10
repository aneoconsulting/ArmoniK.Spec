import re

import rich_click as click

from pathlib import Path

from packaging.version import parse as parse_version
from rich.live import Live
from rich.table import Table
from rich.spinner import Spinner

from .constants import (
    CONSOLE,
    ALL_PKGS,
    VALID,
    CROSS,
    WORKDIR,
    TOOLS_DIR,
    UNCHANGED,
)
from .tools import TLC, REPL
from .utils import AliasedGroup, error_handler


# Create a mapping for faster lookup
pkg_map = {p.name: p for p in ALL_PKGS}


@click.group(
    name="tla",
    cls=AliasedGroup,
    context_settings={
        "help_option_names": ["-h", "--help"],
        "auto_envvar_prefix": "TLA_",
    },
    invoke_without_command=True,
)
@click.version_option(version="0.1.0", prog_name="tla-cli")
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


@cli.group(name="package")
def tla_package() -> None:
    """Commands for managing TLA+ tool packages."""
    pass


@tla_package.command(name="list")
def tla_package_list() -> None:
    """
    Display the installation status of TLA+ tool packages.
    """
    table = Table(title="Package Installation Summary")
    table.add_column("Name", no_wrap=True, justify="center")
    table.add_column("Installed", justify="center")
    table.add_column("Version", justify="center")
    table.add_column("Up-to-date", justify="center")

    for pkg in ALL_PKGS:
        if pkg.is_installed:
            table.add_row(
                pkg.name,
                VALID,
                str(pkg.current_version),
                VALID if pkg.is_up_to_date else CROSS,
            )
        else:
            table.add_row(pkg.name, CROSS, "-", "-")

    CONSOLE.print(table)


@tla_package.command(name="install")
@click.argument(
    "pkg_specs",
    metavar="PACKAGE_SPEC",
    nargs=-1,
    type=str,
    default=[p.name for p in ALL_PKGS],
)
@error_handler
def tla_package_install(pkg_specs: list[str]) -> None:
    """
    Install one or more TLA+ tool packages and their dependencies.

    PACKAGE_SPEC format: name or name==version (e.g. tla2tools==1.5.7)
    """
    spec_pattern = r"^([a-zA-Z0-9_-]+)(?:==([vV]?\d+\.\d+\.\d+))?$"
    pkgs_to_install = []

    for spec in pkg_specs:
        match = re.match(spec_pattern, spec)
        if not match:
            raise click.BadArgumentUsage(f"Invalid package specifier format: '{spec}'.")

        pkg_name, version_str = match.groups()
        pkg = pkg_map.get(pkg_name)

        if pkg is None:
            raise click.BadArgumentUsage(f"Unknown package: '{pkg_name}'")

        # Determine version to install
        version = parse_version(version_str) if version_str else pkg.latest_version
        if not pkg.version_exists(version):
            raise click.BadArgumentUsage(
                f"Invalid version for package '{pkg_name}': '{version}'."
            )

        pkgs_to_install.append((pkg, version))

    for pkg, version in pkgs_to_install:
        with Live(
            Spinner("dots", text=f"Installing {pkg.name} (version {version})..."),
            console=CONSOLE,
            refresh_per_second=10,
        ) as live:
            if pkg.is_installed:
                live.update(f"{UNCHANGED} {pkg.name} is already installed.")
                continue
            try:
                pkg.install(version)
                live.update(f"{VALID} Installed {pkg.name} (version {version}).")
            except RuntimeError:
                live.update(f"{CROSS} Failed to install {pkg.name}.")
                raise


@tla_package.command(name="upgrade")
@click.argument(
    "pkg_names",
    metavar="PACKAGE_NAME",
    nargs=-1,
    type=str,
    default=[p.name for p in ALL_PKGS],
)
@error_handler
def tla_package_upgrade(pkg_names: list[str]) -> None:
    """
    Upgrade specified TLA+ tool packages to their latest versions.
    """
    pkgs_to_upgrade = []

    for pkg_name in pkg_names:
        pkg = pkg_map.get(pkg_name)
        if pkg is None:
            raise click.BadArgumentUsage(f"Unknown package: '{pkg_name}'")
        pkgs_to_upgrade.append(pkg)

    for pkg in pkgs_to_upgrade:
        with Live(
            Spinner(
                "dots", text=f"Upgrading {pkg.name} to version {pkg.latest_version}..."
            ),
            console=CONSOLE,
            refresh_per_second=10,
        ) as live:
            if pkg.is_up_to_date:
                live.update(f"{UNCHANGED} {pkg.name} is already up to date.")
                continue
            try:
                pkg.upgrade()
                live.update(
                    f"{VALID} Upgraded {pkg.name} to version {pkg.latest_version}."
                )
            except RuntimeError:
                live.update(f"{CROSS} Failed to upgrade {pkg.name}.")
                raise


@tla_package.command(name="uninstall")
@click.argument(
    "pkg_names",
    metavar="PACKAGE_NAME",
    nargs=-1,
    type=str,
    default=[p.name for p in ALL_PKGS],
)
@error_handler
def tla_package_uninstall(pkg_names: list[str]) -> None:
    """
    Uninstall one or more installed TLA+ tool packages.
    """
    pkgs_to_uninstall = []

    for pkg_name in pkg_names:
        pkg = pkg_map.get(pkg_name)
        if pkg is None:
            raise click.BadArgumentUsage(f"Unknown package: '{pkg_name}'")
        pkgs_to_uninstall.append(pkg)

    for pkg in pkgs_to_uninstall:
        with Live(
            Spinner("dots", text=f"Uninstalling {pkg.name}..."),
            console=CONSOLE,
            refresh_per_second=10,
        ) as live:
            if not pkg.is_installed:
                live.update(f"{UNCHANGED} {pkg.name} is not currently installed.")
                continue
            try:
                pkg.uninstall()
                live.update(f"{VALID} Uninstalled {pkg.name}.")
            except RuntimeError:
                live.update(f"{CROSS} Failed to uninstall {pkg.name}.")
                raise


@cli.command(name="model-check")
@click.argument(
    "module_path",
    type=click.Path(exists=True, dir_okay=False, resolve_path=True, path_type=Path),
    help="Path to the TLA+ module file (.tla) to check.",
)
@error_handler
def tla_model_check(module_path: Path) -> None:
    """
    Run the TLC model checker on a given TLA+ module file.
    """
    tlc = TLC()
    model_path = module_path.with_suffix(".cfg")
    tlc.run(module_path, model_path)


if __name__ == "__main__":
    cli()
