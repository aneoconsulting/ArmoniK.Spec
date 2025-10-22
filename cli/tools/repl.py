import subprocess
import sys

from logging import Logger
from typing import cast

from rich.console import Console
from packaging.version import Version

from ..packages import GithubReleasePackage
from .java import JavaClassTool


class REPL(JavaClassTool):
    """TLA+ REPL tool for interactive constant expressions evaluation."""

    def __init__(
        self,
        main_class: str,
        pkg: GithubReleasePackage,
        logger: Logger,
        console: Console,
    ) -> None:
        super().__init__(
            name="REPL",
            classpath=pkg.location,
            main_class=main_class,
            pkg=pkg,
            logger=logger,
            console=console,
        )

    def is_available(self) -> bool:
        if not super().is_available():
            return False
        elif cast(Version, self.pkg.current_version) >= Version("v1.8.0"):
            return True
        return False

    def start(self) -> None:
        """Starts the REPL if the version of TLA2Tools supports it."""
        try:
            process = subprocess.Popen(
                self.get_java_command(),
                stdin=sys.stdin,
                stdout=sys.stdout,
                stderr=subprocess.PIPE,
                text=True,
                bufsize=1,
            )
            process.wait()
            if process.returncode != 0:
                raise RuntimeError(
                    process.stderr.read() if process.stderr else "REPL failed."
                )
        except KeyboardInterrupt:
            pass
