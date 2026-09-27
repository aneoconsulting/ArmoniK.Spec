"""chunk_proofs: the tlapm runs that check a proof module, as line ranges.

A `<X>Theorems_proofs.tla` is checked by one tlapm run -- unless it is too large
for one. GraphProcessing2, and the GraphProcessing3/4 to come, exceed what a CI
job can carry with the upstream prover: the runner kills the process long before
the last obligation. tlapm's `--toolbox <begin> <end>` mode restricts proving to
the obligations of the proof steps located within those lines, so such a module
can be checked as several runs instead -- provided the ranges *tile* the file and
never cut a proof in two.

This module plans, for every proof module, the runs that check it. One rule:

  - a module of at most `--budget` leaf proof directives (BY / OBVIOUS / OMITTED,
    the cheapest proxy for the obligation count) fits one run, and its plan is a
    single range, the whole file;
  - a larger module is *split*: its top-level statements are grouped greedily
    into ranges of at most `--max-steps` leaf directives, and the module is also
    checked whole by the optimized tlapm build (scripts/install-tools.sh), the
    only prover fast enough to. The two checks are redundant on purpose: the
    optimized build is a fork, and the upstream ranges are the reference it is
    held against until it is trusted alone; in return, the whole-file run gives
    the module one status check whose name does not move with its ranges.

Range boundaries fall only on the first line of a top-level statement (THEOREM /
LEMMA / PROPOSITION / COROLLARY / AXIOM at column 0, outside comments), the first
range starts at line 1 and the last one ends at the last line, so every line --
hence every obligation -- belongs to exactly one range. A statement heavier than
the budget on its own becomes a range of its own rather than being cut.

`--strict` keeps its meaning inside a range: tlapm reports the failed, omitted
and missing proofs of the selected lines only, and is silent about the rest of
the file. The runs of a split module are therefore together exactly as strict as
one run over the whole of it, as long as the ranges tile the file -- which this
module asserts before printing any of them, rather than leaving CI to be green
over a gap. A range that is the whole file is a whole-file run: same
obligations, same exit code.

The two numbers are far apart because a leaf directive costs the upstream prover
about ten times more on the INSTANCE-heavy modules -- exactly the ones that need
splitting -- than on those that fit: the budget is what one run has been seen to
carry (GraphProcessing1, ~800 directives, passes; GraphProcessing2, ~1900, does
not), and at the measured 4.4 obligations per minute on GraphProcessing2, a range
of fifty directives is about 35 minutes of proving. Lower `--max-steps` when a
range runs out of time, raise it to spend fewer runners; lower `--budget` when a
whole-file run does.

Standard library only: CI builds its job matrices from `--json` in the discovery
job, before any venv exists.
"""

from __future__ import annotations

import argparse
import json
import re
import sys
from dataclasses import dataclass
from pathlib import Path

from .naming import SPECS_DIR, proof_modules

# A top-level statement of a proof module: no indentation, since a nested step is
# numbered (<3>1.) and never starts a line with one of these keywords.
STATEMENT = re.compile(r"^(THEOREM|LEMMA|PROPOSITION|COROLLARY|AXIOM)(?!\w)\s*(\w+)?")
# The leaf proof directives, whose count approximates the obligations of a range.
LEAF = re.compile(r"\b(BY|OBVIOUS|OMITTED)\b")

# Leaf directives one upstream tlapm run is trusted with, and per range of a
# module that exceeds it. See the module docstring for where the numbers come from.
DEFAULT_BUDGET = 1000
DEFAULT_MAX_STEPS = 50


@dataclass(frozen=True)
class Chunk:
    """A line range of `module` that tlapm checks in one `--toolbox begin end` run."""

    module: str
    index: int  # 1-based
    total: int  # ranges of the module; 1 means this range is the whole file
    begin: int
    end: int
    first: str  # name of the first statement of the range
    steps: int  # leaf directives, the estimate the range was sized by

    @property
    def name(self) -> str:
        """What to call the run: the module alone when the range is the whole file."""
        if self.total == 1:
            return self.module
        return f"{self.module} {self.index}/{self.total} {self.first}"

    def as_dict(self) -> dict[str, object]:
        return {
            "module": self.module,
            "begin": self.begin,
            "end": self.end,
            "steps": self.steps,
            "name": self.name,
        }


@dataclass(frozen=True)
class Plan:
    """The runs that check one proof module."""

    module: str
    steps: int
    # Over budget: the ranges are checked by the upstream tlapm, the whole module
    # by the optimized one besides.
    split: bool
    chunks: list[Chunk]


def strip_comments(text: str) -> str:
    """`text` with every comment blanked out, keeping the line and column of the rest.

    Blanking rather than deleting keeps line numbers intact, which is the whole
    point here: the ranges this module computes are read back by tlapm.
    """
    out = list(text)
    index, depth, in_string = 0, 0, False
    while index < len(text):
        rest = text[index : index + 2]
        if in_string:
            if text[index] == "\\" and index + 1 < len(text):
                index += 2
                continue
            in_string = text[index] != '"'
            index += 1
        elif depth:
            if rest == "(*":
                depth += 1
            elif rest == "*)":
                depth -= 1
            else:
                if text[index] != "\n":
                    out[index] = " "
                index += 1
                continue
            out[index] = out[index + 1] = " "
            index += 2
        elif rest == "(*":
            depth = 1
            out[index] = out[index + 1] = " "
            index += 2
        elif rest == "\\*":
            end = text.find("\n", index)
            end = len(text) if end < 0 else end
            out[index:end] = " " * (end - index)
            index = end
        else:
            in_string = text[index] == '"'
            index += 1
    return "".join(out)


def statements(lines: list[str]) -> list[tuple[int, str]]:
    """The (1-based line, name) of every top-level statement among comment-free `lines`."""
    found = []
    for number, line in enumerate(lines, start=1):
        match = STATEMENT.match(line)
        if match:
            found.append((number, match.group(2) or match.group(1)))
    return found


def plan(path: Path, budget: int = DEFAULT_BUDGET, max_steps: int = DEFAULT_MAX_STEPS) -> Plan:
    """The runs that check `path`: the whole file when it fits `budget`, else a tiling.

    A range never starts inside a statement, and the ranges cover every line of
    the file exactly once.
    """
    lines = strip_comments(path.read_text(encoding="utf-8")).splitlines()
    starts = statements(lines)
    # Leaf directives of [start, next start), so that a range's weight is the sum
    # over the statements it groups.
    bounds = [line for line, _ in starts] + [len(lines) + 1]
    weights = [
        sum(len(LEAF.findall(line)) for line in lines[bounds[i] - 1 : bounds[i + 1] - 1])
        for i in range(len(starts))
    ]
    steps = sum(weights)
    split = steps > budget

    # Greedy grouping: close the range as soon as it is full, so that a statement
    # heavier than the budget lands alone instead of being cut. A module within
    # budget is a single group, whatever its statements weigh.
    groups: list[list[int]] = [[]]
    weight = 0
    for index, statement_weight in enumerate(weights):
        if split and groups[-1] and weight + statement_weight > max_steps:
            groups.append([])
            weight = 0
        groups[-1].append(index)
        weight += statement_weight

    total = len(groups)
    chunks = [
        Chunk(
            module=path.stem,
            index=number,
            total=total,
            # The first range takes the module header with it, the last the footer.
            begin=1 if number == 1 else bounds[group[0]],
            end=len(lines) if number == total else bounds[group[-1] + 1] - 1,
            first=starts[group[0]][1] if group else path.stem,
            steps=sum(weights[index] for index in group),
        )
        for number, group in enumerate(groups, start=1)
    ]
    return Plan(path.stem, steps, split, chunks)


def tiles(chunks: list[Chunk], path: Path) -> str | None:
    """The reason `chunks` fails to tile `path`, None when it does.

    A gap between two ranges is obligations no job checks -- a green CI that
    verified nothing -- so it is checked rather than trusted.
    """
    lines = len(path.read_text(encoding="utf-8").splitlines())
    expected = 1
    for chunk in chunks:
        if chunk.begin != expected:
            return f"{path}: range {chunk.index} starts at line {chunk.begin}, expected {expected}"
        expected = chunk.end + 1
    if expected != lines + 1:
        return f"{path}: ranges stop at line {expected - 1} of {lines}"
    return None


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument(
        "proofs",
        type=Path,
        nargs="*",
        help="the *_proofs.tla modules to plan (default: every one under --specs)",
    )
    parser.add_argument(
        "--specs", type=Path, default=Path(SPECS_DIR), help="directory containing the .tla modules"
    )
    parser.add_argument(
        "--budget",
        type=int,
        default=DEFAULT_BUDGET,
        help=f"leaf proof directives a module may hold and still be one run (default {DEFAULT_BUDGET})",
    )
    parser.add_argument(
        "--max-steps",
        type=int,
        default=DEFAULT_MAX_STEPS,
        help=f"leaf proof directives per range of a split module (default {DEFAULT_MAX_STEPS})",
    )
    parser.add_argument(
        "--json",
        action="store_true",
        help='print the CI job matrices: {"chunks": [every range], "split": [the split modules]}',
    )
    args = parser.parse_args()
    if args.max_steps > args.budget:
        parser.error("--max-steps must not exceed --budget: a range is a run too")
    paths = args.proofs or [args.specs / f"{module}.tla" for module in proof_modules(args.specs)]

    plans: list[Plan] = []
    for path in paths:
        if not path.is_file():
            parser.error(f"{path}: no such file")
        module_plan = plan(path, args.budget, args.max_steps)
        gap = tiles(module_plan.chunks, path)
        if gap:
            print(gap, file=sys.stderr)
            return 1
        plans.append(module_plan)

    if args.json:
        matrices = {
            "chunks": [chunk.as_dict() for module_plan in plans for chunk in module_plan.chunks],
            "split": [module_plan.module for module_plan in plans if module_plan.split],
        }
        print(json.dumps(matrices, separators=(",", ":")))
        return 0
    for module_plan in plans:
        for chunk in module_plan.chunks:
            part = f"{chunk.index}/{chunk.total}" if module_plan.split else "whole"
            first = f"\t{chunk.first}" if module_plan.split else ""
            print(f"{chunk.module}\t{part}\t{chunk.begin}-{chunk.end}\t~{chunk.steps} steps{first}")
    return 0


if __name__ == "__main__":
    sys.exit(main())
