import json
import re
import subprocess

from dataclasses import dataclass, asdict
from datetime import datetime, timedelta
from logging import Logger
from pathlib import Path
from typing import Optional, Any

from rich.console import Console

from ..packages import GithubReleasePackage
from .java import JavaClassTool


@dataclass
class TLCRun:
    """Data class to store the results of a TLC run."""

    started_at: datetime
    ended_at: Optional[datetime] = None
    duration: Optional[timedelta] = None
    tlc_version: Optional[str] = None
    tlc_rev: Optional[str] = None
    seed: Optional[int] = None
    num_workers: Optional[int] = None
    num_cores: Optional[int] = None
    heap_size: Optional[int] = None
    offheap_size: Optional[int] = None
    mode: Optional[str] = None
    modules: Optional[list[str]] = None
    loads: Optional[dict[str, str]] = None
    success: Optional[bool] = None
    total_states: Optional[int] = None
    total_distinct_states: Optional[int] = None
    num_states_queued: Optional[int] = None
    state_depth: Optional[int] = None
    error_type: Optional[str] = None
    error_msg: Optional[str] = None
    log_file: Optional[Path] = None
    states_file: Optional[Path] = None
    ttrace_spec: Optional[Path] = None

    def to_dict(self) -> dict[str, Any]:
        """Converts the TLCRun object to a dictionary for serialization."""
        return asdict(self)


class TLC(JavaClassTool):
    """Tool for running the TLC model checker.

    Static Attributes:
        tlc_exit_codes: Mapping of TLC exit codes to error types.
        regex: Regular expressions for parsing TLC output.

    Attributes:
        classpath: Classpath for TLA2Tools jar file.
        main_class: Main class for TLC.
        base_path: Base path for TLC runs.
        community_modules_classpath: Classpath for community modules.
    """

    tlc_exit_codes = {
        0: "Success",
        10: "Assumption failure",
        11: "Deadlock failure",
        12: "Safety failure",
        13: "Liveness failure",
    }

    regex = {
        "version": re.compile(r"TLC2 Version (?P<tlc_version>[\d.]+)"),
        "state_count": re.compile(
            r"(?P<total_states>[\d,]+) states generated, (?P<distinct_states>[\d,]+) distinct states found"
        ),
        "state_depth": re.compile(
            r"The depth of the complete state graph search is (?P<state_depth>[\d,]+)"
        ),
    }

    def __init__(
        self,
        main_class: str,
        data_path: Path,
        community_modules: GithubReleasePackage,
        pkg: GithubReleasePackage,
        logger: Logger,
        console: Console,
    ) -> None:
        super().__init__(
            name="TLC",
            classpath=pkg.location,
            main_class=main_class,
            pkg=pkg,
            logger=logger,
            console=console,
        )
        self.base_path = data_path
        self.community_modules = community_modules

    def create_run_dir(self) -> Path:
        """Creates a new directory for the TLC run."""
        run_dir = (
            self.base_path / f"tlc-run-{datetime.now().strftime('%Y-%m-%d-%H-%M-%S')}"
        )
        run_dir.mkdir(parents=True, exist_ok=True)
        return run_dir

    def start(
        self,
        module_path: Path,
        model_path: Path,
        *,
        workers: int,
        max_heap_size: str,
        community_modules: bool,
        external_modules: list[Path],
        save_states: bool = False,
        show_log: bool = True,
    ) -> TLCRun:
        """Runs TLC and returns the results.

        Args:
            module_path: Path to the TLA+ module.
            model_path: Path to the TLC model configuration file.
            workers: Number of worker threads.
            max_heap_size: Maximum heap size for the JVM.
            community_modules: Whether to include community modules.
            external_modules: list of paths to external modules.
            save_states: Weither to save the state space graph in a Graphviz .dot file.
            show_log: Whether to print TLC output to the console.

        Returns:
            The results of the TLC run.
        """
        run_dir = self.create_run_dir()
        tlc_run = TLCRun(started_at=datetime.now())

        # Set JVM parameters
        self.parallel_gc = True
        self.max_heap_size = max_heap_size
        if community_modules:
            self.classpath.append(self.community_modules.location)
        if external_modules:
            self.classpath.extend(external_modules)

        cmd = self.get_java_command(
            ["-workers", str(workers), "-config", str(model_path), str(module_path)]
        )

        if save_states:
            cmd.extend(["-dump", "dot", "states"])
            tlc_run.states_file = run_dir / "states.dot"
        process = subprocess.Popen(
            cmd,
            stdout=subprocess.PIPE,
            stderr=subprocess.STDOUT,
            cwd=run_dir,
            text=True,
        )

        if process.stdout is None:
            raise RuntimeError("Failed to launch TLC.")

        tlc_output = []
        for line in process.stdout:
            if show_log:
                print(line.replace("\n", ""))
            tlc_output.append(line)
        process.wait()

        tlc_run.ended_at = datetime.now()
        tlc_run.duration = tlc_run.ended_at - tlc_run.started_at
        tlc_output = "".join(tlc_output)

        if process.returncode == 0:
            self._parse_success(tlc_run, tlc_output)
        else:
            self._parse_failure(tlc_run, tlc_output, process.returncode)

        self._save_run_data(tlc_run, run_dir, tlc_output)
        return tlc_run

    def _parse_success(self, tlc_run: TLCRun, output: str) -> None:
        """Parses TLC output on successful run.

        Args:
            tlc_run: The TLCRun object to populate.
            output: The TLC output as a string.
        """
        tlc_run.success = True
        state_count = self.regex["state_count"].search(output)
        state_depth = self.regex["state_depth"].search(output)
        if not state_count or not state_depth:
            raise ValueError("Failed to parse TLC output.")
        tlc_run.total_states = int(state_count.group("total_states").replace(",", ""))
        tlc_run.total_distinct_states = int(
            state_count.group("distinct_states").replace(",", "")
        )
        tlc_run.state_depth = int(state_depth.group("state_depth").replace(",", ""))

    def _parse_failure(self, tlc_run: TLCRun, output: str, code: int) -> None:
        """Parses TLC output on failed run.

        Args:
            tlc_run: The TLCRun object to populate.
            output: The TLC output as a string.
            code: The exit code from TLC.
        """
        tlc_run.success = False
        tlc_run.error_type = self.tlc_exit_codes.get(code, "Unknown")
        tlc_run.error_msg = output.split("Error:")[-1].strip()

    def _save_run_data(self, tlc_run: TLCRun, run_dir: Path, output: str) -> None:
        """Saves TLC run data to files."""
        tlc_run.log_file = run_dir / "tlc.log"
        with tlc_run.log_file.open("w") as f:
            f.write(output)
        with (run_dir / "run-data.json").open("w") as f:
            json.dump(tlc_run.to_dict(), f, indent=4, default=str)
