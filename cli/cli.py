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
    "Manage packages."
    pass


@tla_package.command(name="list")
def tla_package_list() -> None:
    """List package installation."""
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
    """Install TLA+ tools (TLA2Tools, Community Modules, Apalache, TLAPS) and their dependencies."""
    pkg_to_install = []
    spec_pattern = r"^([a-zA-Z0-9_-]+)(?:==(v?\d+\.\d+\.\d+))?$"
    for pkg_spec in pkg_specs:
        # Parse the package specifier
        match = re.match(spec_pattern, pkg_spec)
        if not match:
            raise click.BadArgumentUsage(
                f"Invalid package specifier format: {pkg_spec}."
            )

        pkg_name = match.group(1)
        pkg_version = match.group(3) if match.group(2) else None

        pkg = next((p for p in ALL_PKGS if p.name == pkg_name), None)
        if pkg is None:
            raise click.BadArgumentUsage(f"Package {pkg_name} doesn't exist.")
        if pkg_version is not None and pkg.version_exists(parse_version(pkg_version)):
            raise click.BadArgumentUsage(
                f"Invalid version package for {pkg_name}: {pkg_version}."
            )
        if pkg_version is None:
            pkg_version = pkg.latest_version
        pkg_to_install.append((pkg, pkg_version))

    for pkg, pkg_version in pkg_to_install:
        with Live(
            Spinner("dots", text=f"Installing version {pkg_version} of {pkg.name}"),
            console=CONSOLE,
            refresh_per_second=10,
        ) as live:
            if pkg.is_installed:
                live.update(f"{UNCHANGED} Package {pkg.name} is already installed.")
                continue
            try:
                pkg.install(pkg_version)
                live.update(
                    f"{VALID} Sucessfully installed {pkg.name} version {pkg_version}."
                )
            except RuntimeError:
                live.update(
                    f"{CROSS} Failed to install {pkg.name} version {pkg_version}."
                )
                raise


@tla_package.command(name="upgrade")
@click.argument(
    "pkg_names",
    metavar="PACKAGE NAME",
    nargs=-1,
    type=str,
    default=[p.name for p in ALL_PKGS],
)
@error_handler
def tla_package_upgrade(pkg_names: list[str]) -> None:
    """Uninstall packages."""
    pkg_to_upgrade = []
    for pkg_name in pkg_names:
        pkg = next((p for p in ALL_PKGS if p.name == pkg_name), None)
        if pkg is None:
            raise click.BadArgumentUsage(f"Invalid package name: {name}.")
        pkg_to_upgrade.append(pkg)

    for pkg in pkg_to_upgrade:
        with Live(
            Spinner(
                "dots",
                text=f"Upgrading package {pkg.name} to version {pkg.latest_version}.",
            ),
            console=CONSOLE,
            refresh_per_second=10,
        ) as live:
            if pkg.is_up_to_date:
                live.update(f"{UNCHANGED} Package {pkg.name} is already up to date.")
                continue
            try:
                pkg.upgrade()
                live.update(
                    f"{VALID} Sucessfully upgraded {pkg.name} to version {pkg.latest_version}."
                )
            except RuntimeError:
                live.update(
                    f"{CROSS} Failed to upgrade {pkg.name} to version {pkg.latest_version}."
                )
                raise


@tla_package.command(name="uninstall")
@click.argument(
    "pkg_names",
    metavar="PACKAGE NAME",
    nargs=-1,
    type=str,
    default=[p.name for p in ALL_PKGS],
)
@error_handler
def tla_package_uninstall(pkg_names: list[str]) -> None:
    """Uninstall packages."""
    pkg_to_uninstall = []
    for pkg_name in pkg_names:
        pkg = next((p for p in ALL_PKGS if p.name == pkg_name), None)
        if pkg is None:
            raise click.BadArgumentUsage(f"Invalid package name: {name}.")
        pkg_to_uninstall.append(pkg)

    for pkg in pkg_to_uninstall:
        with Live(
            Spinner("dots", text=f"Uninstalling package {pkg.name}."),
            console=CONSOLE,
            refresh_per_second=10,
        ) as live:
            if not pkg.is_installed:
                live.update(f"{UNCHANGED} Package {pkg.name} is not installed.")
                continue
            try:
                pkg.uninstall()
                live.update(f"{VALID} Sucessfully uninstalled package {pkg.name}.")
            except RuntimeError:
                live.update(f"{CROSS} Failed to uninstall package {pkg.name}.")
                raise


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
