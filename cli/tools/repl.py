import subprocess
import sys

from pathlib import Path

from packaging.version import Version

from .java import JavaClassTool


class REPL(JavaClassTool):
    """TLA+ REPL tool for interactive constant expressions evaluation."""

    def __init__(
        self, classpath: Path, main_class: str, tla2tools_version: Version
    ) -> None:
        super().__init__(name="REPL", classpath=classpath, main_class=main_class)
        self.tla2tools_version = tla2tools_version

    def start(self) -> None:
        """Starts the REPL if the version of TLA2Tools supports it."""
        if self.tla2tools_version < Version("v1.8.0"):
            return
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
