import logging

from pathlib import Path

from rich.console import Console
from rich.logging import RichHandler

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
