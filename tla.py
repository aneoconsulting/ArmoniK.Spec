import logging

import requests
import rich_click as click

from pathlib import Path
from typing import TYPE_CHECKING

from github import Github
from github.GitRelease import GitRelease
from rich.console import Console
from rich.live import Live
from rich.logging import RichHandler
from rich.spinner import Spinner
from rich.text import Text
from rich.panel import Panel


WORKDIR = Path(__file__).parent / ".tla"
TOOLS_DIR = WORKDIR / "tools"
CONSOLE = Console()

logging.basicConfig(
    level="WARNING",
    format="%(message)s",
    datefmt="[%X]",
    handlers=[RichHandler(console=CONSOLE)]
)
LOGGER = logging.getLogger("rich")


class ReleaseHandler:
    def __init__(self, repo_name: str, tool_asset_name: str) -> None:
        self.repo = Github().get_repo(repo_name)
        self.tool_asset_name = tool_asset_name

    @property
    def latest_release(self) -> GitRelease:
        releases = self.repo.get_releases()

        if releases.totalCount == 0:
            raise RuntimeError(f"Repository {self.repo.name} has no release.")
        
        return releases[0]

    def download_latest_release(self) -> None:
        assets = self.latest_release.get_assets()
        if assets.totalCount == 0:
            raise RuntimeError("No assets found in the latest release of repository {self.repo.name}.")

        asset = [asset for asset in assets if asset.name == self.tool_asset_name]
        if len(asset) == 0:
            raise RuntimeError(f"Repository {self.repo.name} has no assets with name {self.tool_asset_name}.")
        elif len(asset) > 1:
            raise RuntimeError(f"Repository {self.repo.name} has multiple assets with name {self.tool_asset_name}.")

        asset = asset[0]
        LOGGER.info(f"Downloading: {asset.name} from {asset.browser_download_url}.")        
        response = requests.get(asset.browser_download_url, stream=True)
        if response.status_code == 200:
            with (TOOLS_DIR / asset.name).open("wb") as file:
                for chunk in response.iter_content(chunk_size=8192):
                    file.write(chunk)
            LOGGER.info(f"Successfully donwloaded {self.tool_asset_name}")
        else:
            raise RuntimeError(f"Failed to download {asset.name} (status code: {response.status_code}).")


class TLA2Tools:
    def __init__(self) -> None:
        self.release_handler = ReleaseHandler(
            repo_name="tlaplus/tlaplus",
            tool_asset_name="tla2tools.jar"
        )
        self.name = "TLA2 Tools"

    def install_or_upgrade(self) -> None:
        self.release_handler.download_latest_release()

class CommunityModules:
    def __init__(self) -> None:
        self.release_handler = ReleaseHandler(
            repo_name="tlaplus/CommunityModules",
            tool_asset_name="CommunityModules.jar"
        )
        self.name = "Community Modules"

    def install_or_upgrade(self) -> None:
        self.release_handler.download_latest_release()

@click.group(
    name="tla",
    context_settings={"help_option_names": ["-h", "--help"],"auto_envvar_prefix": "TLA_"}
)
@click.version_option(version="0.1.0", prog_name="tla")
def cli() -> None:
    """
    Command-line tool to simplify working with TLA+.
    """
    WORKDIR.mkdir(exist_ok=True)
    TOOLS_DIR.mkdir(exist_ok=True)



@cli.command(name="install")
def tla_install() -> None:
    """Install or update TLA+ tools (TLA2Tools, Community Modules, Apalache, TLAPS) and their dependencies."""
    tools = [TLA2Tools(), CommunityModules()]
    for tool in tools:
        with Live(Spinner("dots", text=f"Installing latest version of {tool.name}"), console=CONSOLE, refresh_per_second=10) as live:
            try:
                tool.install_or_upgrade()
                live.update(Text(f"✔ Sucessfully upgraded {tool.name}.", style="bold green"))
            except RuntimeError as error:
                LOGGER.exception(error)
                live.update(Text(f"❌ Failed to upgrade {tool.name}.", style="bold red"))


if __name__ == "__main__":
    cli()
