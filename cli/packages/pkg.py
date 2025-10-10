import requests

from github import Github
from github.GitRelease import GitRelease

from ..constants import LOGGER, TOOLS_DIR


class ReleaseHandler:
    def __init__(self, repo_name: str, tool_asset_name: str) -> None:
        self.repo = Github().get_repo(repo_name)
        self.tool_asset_name = tool_asset_name

    @property
    def latest_release(self) -> "GitRelease":
        releases = self.repo.get_releases()

        if releases.totalCount == 0:
            raise RuntimeError(f"Repository {self.repo.name} has no release.")

        return releases[0]

    def download_latest_release(self) -> None:
        assets = self.latest_release.get_assets()
        if assets.totalCount == 0:
            raise RuntimeError(
                "No assets found in the latest release of repository {self.repo.name}."
            )

        asset = [asset for asset in assets if asset.name == self.tool_asset_name]
        if len(asset) == 0:
            raise RuntimeError(
                f"Repository {self.repo.name} has no assets with name {self.tool_asset_name}."
            )
        elif len(asset) > 1:
            raise RuntimeError(
                f"Repository {self.repo.name} has multiple assets with name {self.tool_asset_name}."
            )

        asset = asset[0]
        LOGGER.info(f"Downloading: {asset.name} from {asset.browser_download_url}.")
        response = requests.get(asset.browser_download_url, stream=True)
        if response.status_code == 200:
            with (TOOLS_DIR / asset.name).open("wb") as file:
                for chunk in response.iter_content(chunk_size=8192):
                    file.write(chunk)
            LOGGER.info(f"Successfully donwloaded {self.tool_asset_name}")
        else:
            raise RuntimeError(
                f"Failed to download {asset.name} (status code: {response.status_code})."
            )


class TLA2Tools:
    def __init__(self) -> None:
        self.release_handler = ReleaseHandler(
            repo_name="tlaplus/tlaplus", tool_asset_name="tla2tools.jar"
        )
        self.name = "TLA2 Tools"

    def install_or_upgrade(self) -> None:
        self.release_handler.download_latest_release()


class CommunityModules:
    def __init__(self) -> None:
        self.release_handler = ReleaseHandler(
            repo_name="tlaplus/CommunityModules", tool_asset_name="CommunityModules.jar"
        )
        self.name = "Community Modules"

    def install_or_upgrade(self) -> None:
        self.release_handler.download_latest_release()