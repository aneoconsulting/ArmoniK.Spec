import logging

from pathlib import Path

from rich.console import Console
from rich.logging import RichHandler

from .packages import Package, TLA2Tools, CommunityModules


PROJECT_DIR = Path(__file__).parent.parent
WORKDIR = PROJECT_DIR / ".tla"
TOOLS_DIR = WORKDIR / "tools"

CONSOLE = Console()

logging.basicConfig(
    level="WARNING",
    format="%(message)s",
    datefmt="[%X]",
    handlers=[RichHandler(console=CONSOLE)],
)
LOGGER = logging.getLogger("rich")

ALL_PKGS: list[Package] = [
    TLA2Tools(location=TOOLS_DIR),
    CommunityModules(location=TOOLS_DIR),
]

VALID = "[green]✓[/green]"
CROSS = "[red]✗[/red]"
UNCHANGED = "[yellow]~[/yellow]"
