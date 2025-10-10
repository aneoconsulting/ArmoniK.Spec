import subprocess
import sys

from pathlib import Path


import subprocess

from abc import ABC
from pathlib import Path

from .base import Tool

class JavaClassTool(Tool, ABC):
    
    def __init__(self, name: str, class_path: Path, class_name: str) -> None:
        super().__init__(name=name)
        self.class_path = class_path
        self.class_name = class_name

    def get_java_command(self):
         return ["java", "-cp", str(self.class_path), self.class_name]

    def run(self, stdin, stdout, stderr):
        process = subprocess.Popen(
             self.get_java_command(),
             stdin=stdin,
             stdout=stdout,
             stderr=stderr,
        )
        process.wait()


class REPL(JavaClassTool):

    def __init__(self, name: str, class_path: Path, class_name: str) -> None:
        super().__init__(
            name=name,
            class_path=class_path,
            class_name=class_name
        )

    def start(self):
        super().run(stdin=sys.stdin, stdout=sys.stdout, stderr=sys.stderr)
