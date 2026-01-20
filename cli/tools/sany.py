import subprocess

import click

from logging import Logger
from pathlib import Path

from rich.console import Console

from ..packages import GithubReleasePackage
from .java import JavaClassTool


class SANY(JavaClassTool):
    def __init__(
        self,
        main_class: str,
        pkg: GithubReleasePackage,
        logger: Logger,
        console: Console,
    ) -> None:
        super().__init__(
            name="SANY",
            classpath=pkg.location,
            main_class=main_class,
            pkg=pkg,
            logger=logger,
            console=console,
        )

    def start(self, path: Path, external_modules: list[Path] = []) -> None:
        self.classpath.extend([path.parent] + external_modules)
        cmd = self.get_java_command([str(path)])
        output = subprocess.run(cmd, stdout=subprocess.PIPE, stderr=subprocess.PIPE)
        if output.returncode != 0:
            raise click.ClickException(f"Failed to parse {path}.\n\n{output.stdout.decode('utf-8')}\n{output.stderr.decode('utf-8')}")
        self.console.print(f"Successfully parsed module {path.name.removesuffix('.tla')}.")
