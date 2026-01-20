import re

import rich_click as click

from pathlib import Path
from typing import Optional

from packaging.version import parse as parse_version
from rich.live import Live
from rich.table import Table
from rich.spinner import Spinner

from .constants import (
    CONSOLE,
    VALID,
    CROSS,
    WORKDIR,
    TOOLS_DIR,
    UNCHANGED,
    tla2tools,
    community_modules,
    tlc,
    repl,
    sany,
)
from .utils import AliasedGroup, error_handler


# Create a mapping for faster lookup
pkg_map = {p.name: p for p in [tla2tools, community_modules]}


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
@click.option(
    "--manifest",
    "-m",
    type=click.Path(exists=True, dir_okay=False, resolve_path=True, path_type=Path),
    help="Path to a manifest file defining TLA+ modules processing.",
)
@click.pass_context
@error_handler
def cli(ctx: click.Context, manifest: Path) -> None:
    """
    Command-line tool to simplify working with TLA+.
    """
    WORKDIR.mkdir(exist_ok=True)
    TOOLS_DIR.mkdir(exist_ok=True)

    if ctx.invoked_subcommand is None:
        if manifest is None and repl.is_available():
            repl.start()
        else:
            from .models import Manifest

            manifest_obj = Manifest.load_manifest(manifest)
            results = manifest_obj.process()

            table = Table(title="TLA+ Modules Processing Summary")
            table.add_column("Module", no_wrap=True, justify="center")
            table.add_column("Success", justify="center")

            for module_path, success in results.items():
                table.add_row(
                    module_path.name,
                    VALID if success else CROSS,
                )

            CONSOLE.print(table)


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

    for pkg in pkg_map.values():
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
    default=[p.name for p in pkg_map.values()],
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
    default=[p.name for p in pkg_map.values()],
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
    default=[p.name for p in pkg_map.values()],
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
@click.option(
    "--workers",
    "-w",
    metavar="NUM_WORKERS",
    type=int,
    default=1,
    show_default=True,
    help="Number of worker threads for TLC.",
)
@click.option(
    "--max-heap-size",
    metavar="SIZE",
    type=str,
    default="4G",
    show_default=True,
    help="Maximum heap size for the JVM (e.g., 4G, 512M).",
)
@click.option(
    "--community-modules/--no-community-modules",
    default=True,
    show_default=True,
    help="Whether to include CommunityModules in the classpath.",
)
@click.option(
    "--external-module",
    metavar="MODULE_PATH",
    type=click.Path(
        exists=True, dir_okay=True, file_okay=True, resolve_path=True, path_type=Path
    ),
    multiple=True,
    help="Additional external TLA+ modules or JAR files to include in the classpath.",
)
@click.option(
    "--model-path",
    metavar="MODEL_PATH",
    type=click.Path(exists=True, dir_okay=False, resolve_path=True, path_type=Path),
    help="Path to the TLC configuration file (.cfg). If not provided, it is assumed to be alongside the module file with a .cfg extension.",
)
@click.option(
    "--save-states", "-s", is_flag=True, help="Wheither to save the state graph."
)
@error_handler
def tla_model_check(
    module_path: Path,
    model_path: Optional[Path],
    workers: int,
    max_heap_size: str,
    community_modules: bool,
    external_module: list[Path],
    save_states: bool,
) -> None:
    """
    Run the TLC model checker on a given TLA+ module file.
    """
    for ext_module in external_module:
        if ext_module.is_file() and ext_module.suffix != ".jar":
            raise click.BadArgumentUsage(
                f"External module '{ext_module}' must be a .jar file."
            )

    model_path = model_path if model_path else module_path.with_suffix(".cfg")
    tlc.start(
        module_path,
        model_path,
        workers=workers,
        max_heap_size=max_heap_size,
        community_modules=community_modules,
        external_modules=external_module,
        save_states=save_states,
    )

@cli.command(name="parse")
@click.argument(
    "module_paths",
    type=click.Path(exists=True, dir_okay=False, resolve_path=True, path_type=Path),
    nargs=-1,
    help="Path(s) to the TLA+ module file(s) (.tla) to parse.",
)
@click.option(
    "--external-module",
    metavar="MODULE_PATH",
    type=click.Path(
        exists=True, dir_okay=True, file_okay=True, resolve_path=True, path_type=Path
    ),
    multiple=True,
    help="Additional external TLA+ modules or JAR files to include in the classpath.",
)
@error_handler
def tla_parse(module_paths: list[Path], external_module: list[Path]) -> None:
    """
    Run the SANY parser on TLA+ module files.
    """
    for module_path in module_paths:
        sany.start(module_path, list(external_module))

if __name__ == "__main__":
    cli()
