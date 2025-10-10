import re
import subprocess

from typing import cast, IO

from ..constants import PROJECT_DIR


class TLC:
    # default_jvm_params = ["-XX:+UseParallelGC", "-cp", f"{TOOLS_DIR}/*"]
    tlc_exit_codes = {
        0: "Success",
        10: "Assumption failure",
        11: "Deadlock failure",
        12: "Safety failure",
        13: "Liveness failure",
    }
    state_count_regex = re.compile(r'(?P<total_states>[\d,]+) states generated, (?P<distinct_states>[\d,]+) distinct states found, 0 states left on queue.')
    state_depth_regex = re.compile(r'The depth of the complete state graph search is (?P<state_depth>[\d,]+).')

    def handle_success(self, tlc_output) -> None:
        state_count_findings = self.state_count_regex.search(tlc_output)
        state_depth_findings = self.state_depth_regex.search(tlc_output)
        if state_count_findings is None or state_depth_findings is None:
            return ValueError("d")
        distinct_states = int(state_count_findings.group('distinct_states'))
        total_states = int(state_count_findings.group('total_states'))
        state_depth = int(state_depth_findings.group('state_depth'))

    def handle_error(self, code: int, stdout: str, stderr: str) -> None:
        self.tlc_exit_codes[code] if code in cls.tlc_exit_codes else f"Unknown error (code {code})."

    def run(self) -> None:
        process = subprocess.Popen(
            self.get_java_command(),
            stdout=subprocess.PIPE,
            stderr=subprocess.PIPE,
            text=True,
            bufsize=1,
            cwd=PROJECT_DIR,
        )

        step = "parsing"
        stream_out = cast(IO[str], process.stdout)
        with stream_out:
            with Live(
                Spinner("dots", text=f"Installing {pkg.name} (version {version})..."),
                console=CONSOLE,
                refresh_per_second=10,
            ) as live:
                for line in iter(stream_out.readline, ""):
                    if step == "error":
                        continue

                    new_step = ""
                    if line.startswith("Error"):
                        new_step = "error"
                    elif line.startswith("Parse"):
                        new_step = "parsing"
                    elif line.startswith("Semantic"):
                        new_step = "analyzing"
                    elif line.startswith("Linting"):
                        new_step = "linting"
                    elif line.startswith("Computing initial"):
                        new_step = "initializing"
                    elif line.startswith("Progress"):
                        new_step = "computing"
                    else:
                        new_step = "finalizing"
                    
                    if new_step != step:
                        live.update()
                        step = new_step

        process.wait()

        if process.returncode == 0:
            self.handle_success(stdout=process.stdout)
        else:
            self.handle_error(
                code=process.returncode,
                stdout=process.stdout,
                stderr=process.stderr,
            )
