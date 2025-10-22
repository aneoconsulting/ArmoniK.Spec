from logging import Logger
from pathlib import Path
from typing import Optional

from rich.console import Console

from ..packages import Package
from .base import Tool


class JavaClassTool(Tool):
    """Base class for tools that wrap Java command-line applications.

    Attributes:
        name: Name of the tool.
        classpath: list of paths to include in the Java classpath.
        main_class: Fully qualified name of the main class to run.
        max_heap_size: Maximum heap size for the JVM (e.g., "4G").
        parallel_gc: Whether to enable parallel garbage collection.
    """

    def __init__(
        self,
        name: str,
        classpath: Path,
        main_class: str,
        pkg: Package,
        logger: Logger,
        console: Console,
    ) -> None:
        super().__init__(name, pkg, logger, console)
        self.classpath = [classpath]
        self.main_class = main_class
        self.max_heap_size = "4G"
        self.parallel_gc = False

    def get_java_command(self, program_args: Optional[list[str]] = None) -> list[str]:
        """Constructs the Java command to run the tool.

        Args:
            program_args: Arguments to pass to the main class.

        Returns:
            list of command-line arguments for `subprocess.Popen`.
        """
        cmd = [
            "java",
            "-cp",
            ":".join(str(p) for p in self.classpath),
            f"-Xmx{self.max_heap_size}",
        ]
        if self.parallel_gc:
            cmd.append("-XX:+UseParallelGC")
        cmd.append(self.main_class)
        if program_args:
            cmd.extend(program_args)
        return cmd
