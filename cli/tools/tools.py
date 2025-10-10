import subprocess

from pathlib import Path

from ..constants import TOOLS_DIR, WORKDIR
from ..exceptions import ToolRuntimeError


class TLC:
    default_jvm_params = ["-XX:+UseParallelGC", "-cp", f"{TOOLS_DIR}/*"]
    tlc_exit_codes = {
        0: "Success",
        10: "Assumption failure",
        11: "Deadlock failure",
        12: "Safety failure",
        13: "Liveness failure",
    }

    @classmethod
    def resolve_exit_code(cls, code: int) -> str:
        return cls.tlc_exit_codes[code] if code in cls.tlc_exit_codes else f"Unknown error (code {code})."

    @classmethod
    def run(cls, module_path: Path, model_path: Path) -> None:
        import sys

        tlc_params = [
            str(module_path),
            "-config",
            str(model_path),
        ]
        result = subprocess.run(
            ["java"] + cls.default_jvm_params + ["tlc2.TLC"] + tlc_params,
            stdout=sys.stdout,
            stderr=subprocess.PIPE,
            text=True,
            cwd=WORKDIR,
        )

        if result.returncode != 0:
            raise ToolRuntimeError(cls.resolve_exit_code(result.returncode))


class REPL:
    default_jvm_params = ["-cp", str(TOOLS_DIR / "tla2tools.jar")]

    @classmethod
    def run(cls) -> None:
        import sys

        result = subprocess.run(
            ["java"] + cls.default_jvm_params + ["tlc2.REPL"],
            stdin=sys.stdin,
            stdout=sys.stdout,
            stderr=subprocess.PIPE,
            text=True,
        )

        if result.stderr:
            raise RuntimeError(result.stderr)
