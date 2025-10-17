import json

from datetime import timedelta
from pathlib import Path
from typing import List, Optional, Literal

from pydantic import BaseModel, FilePath, Field

from .constants import ALL_PKGS, CONSOLE


class Checks(BaseModel):
    """
    Expected results of model checking for a TLA+ module.

    Attributes:
        success: Whether the model checking is successful.
        total_states: Total number of states explored during model checking.
        distinct_states: Number of distinct states encountered.
        state_depth: Maximum depth of the state space explored.
        state_diameter: Diameter of the state space graph.
        error_type: Type of error encountered, if any.
    """

    success: bool
    total_states: Optional[int] = None
    distinct_states: Optional[int] = None
    state_depth: Optional[int] = None
    state_diameter: Optional[int] = None
    error_type: Optional[
        Literal[
            "Assumption failure",
            "Deadlock failure",
            "Safety failure",
            "Liveness failure",
        ]
    ] = None


class Configuration(BaseModel):
    """
    Configuration settings for model checking of a TLA+ module.

    Attributes:
        max_heap_size: Maximum heap size allocated for the JVM in Mio.
        cores: Number of CPU cores allocated for model checking.
    """

    max_heap_size: Optional[str] = None
    cores: int = 1


class Model(BaseModel):
    """
    TLA+ model with the configuration necessary for its verification and expected results.

    Attributes:
        name: Name of the model.
        path: FilePath to the model file.
        runtime: Maximal duration taken to verify the model.
        type: Type of model checking: "explicit" (TLC) or "symbolic" (Apalache).
        mode: Mode of model checking: "exhaustive" or "simulation".
        configuration: Configuration settings for the model verification.
        checks: Results of the model checking process.
    """

    name: str
    path: FilePath
    runtime: Optional[timedelta] = None
    type: Literal["explicit", "symbolic"]
    mode: Literal["exhaustive", "simulation"]
    configuration: Optional[Configuration] = None
    checks: Checks


class Dependencies(BaseModel):
    """
    External dependencies (outside the module directory) required by a module.

    Attributes:
        community_modules: Whether community modules are used.
        additional_modules: List of paths to additional TLA+ modules or JAR files.
    """

    community_modules: bool = False
    additional_modules: List[FilePath] = Field(default_factory=list)


class Module(BaseModel):
    """
    TLA+ module and its associated models and proofs.

    Attributes:
        path: FilePath to the TLA+ module file.
        dependencies: Additional external dependencies (outside the module
            directory) required by the module.
        models: List of models associated with the module.
    """

    path: FilePath
    dependencies: Dependencies
    models: List[Model] = []


class Manifest(BaseModel):
    """
    Processing manifest (parsing, model checking, proof checking, ...) of TLA+ modules.

    Attributes:
        tlc_version: Version of the TLA+ model checker (TLC) used.
        total_duration: Maximum total processing time.
        modules: List of TLA+ modules to be processed.
    """

    tlc_version: Optional[str] = None
    total_duration: Optional[timedelta] = None
    modules: List[Module]

    @classmethod
    def load_manifest(cls, path: FilePath) -> "Manifest":
        """Load a manifest from a JSON file.

        Args:
            path: Path to the JSON file containing the manifest.

        Returns:
            An instance of the Manifest class populated with data from the file.
        """
        with path.open("r") as f:
            data = replace_paths(json.loads(f.read()), path.parent)
            return cls(**data)

    def process(self) -> dict[Path, bool]:
        """Process all modules and their models as specified in the manifest.

        Returns:
            A dictionary mapping module paths to boolean values indicating
            whether the processing was successful.
        """
        processing_results = {}

        tlc = [p for p in ALL_PKGS if p.name == "TLA2Tools"][0].tools["TLC"]

        for module in self.modules:
            for model in module.models:
                if model.type == "explicit":
                    tlc_run = tlc.start(
                        module.path,
                        model.path,
                        community_modules=module.dependencies.community_modules,
                        external_modules=module.dependencies.additional_modules,
                        # timeout=model.runtime,
                        # mode=model.mode,
                        workers=model.configuration.cores,
                        max_heap_size=model.configuration.max_heap_size,
                        show_log=False,
                    )
                    if tlc_run.success == model.checks.success:
                        assertions = (
                            [
                                (
                                    tlc_run.total_states == model.checks.total_states,
                                    "Invalid total states",
                                ),
                                (
                                    tlc_run.total_distinct_states
                                    == model.checks.distinct_states,
                                    "Invalid distinct states",
                                ),
                                (
                                    tlc_run.state_depth == model.checks.state_depth,
                                    "Invalid state depth",
                                ),
                            ]
                            if model.checks.success
                            else [
                                (
                                    tlc_run.error_type == model.checks.error_type,
                                    "Invalid error type",
                                )
                            ]
                        )
                        failed = False
                        for assertion, msg in assertions:
                            try:
                                assert assertion
                            except AssertionError:
                                CONSOLE.print(
                                    f"[red]Model check failed for model '{model.name}' of module '{module.path.name}': {msg} [/red]"
                                )
                                failed = True
                        processing_results[module.path] = False if failed else True
                    else:
                        processing_results[module.path] = False
                else:
                    raise NotImplementedError(
                        "Symbolic model checking is not support yet."
                    )
        return processing_results


def replace_paths(data, base_path: Path):
    """Recursively replace 'path' fields in a nested data structure with absolute paths.

    Args:
        data: The nested data structure (dicts and lists).
        base_path: The base path to prepend to relative paths.

    Returns:
        The modified data structure with updated paths.
    """
    if isinstance(data, dict):
        return {
            k: replace_paths(base_path / v if k == "path" else v, base_path)
            for k, v in data.items()
        }
    elif isinstance(data, list):
        return [replace_paths(item, base_path) for item in data]
    else:
        return data
