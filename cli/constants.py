import logging

from pathlib import Path

from rich.console import Console
from rich.logging import RichHandler

from .packages import TLA2Tools, CommunityModules
from .tools import TLC, REPL


VALID = "[green]✓[/green]"
CROSS = "[red]✗[/red]"
UNCHANGED = "[yellow]~[/yellow]"

PROJECT_DIR = Path(__file__).parent.parent
WORKDIR = PROJECT_DIR / ".tla"
TOOLS_DIR = WORKDIR / "tools"
RUN_DATA_DIR = WORKDIR / "data"

CONSOLE = Console()

logging.basicConfig(
    level="WARNING",
    format="%(message)s",
    datefmt="[%X]",
    handlers=[RichHandler(console=CONSOLE)],
)
LOGGER = logging.getLogger("rich")


tla2tools = TLA2Tools(location=TOOLS_DIR, logger=LOGGER, console=CONSOLE)
community_modules = CommunityModules(location=TOOLS_DIR, logger=LOGGER, console=CONSOLE)

repl = REPL(main_class="tlc2.REPL", pkg=tla2tools, logger=LOGGER, console=CONSOLE)

tlc = TLC(
    main_class="tlc2.TLC",
    data_path=RUN_DATA_DIR,
    community_modules=community_modules,
    pkg=tla2tools,
    logger=LOGGER,
    console=CONSOLE,
)
