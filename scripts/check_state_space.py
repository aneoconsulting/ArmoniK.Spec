"""check-state-space: TLC's state-space statistics match the reference values.

A successful TLC run reports the number of generated states, distinct states,
and the depth of the state graph. Each model declares the expected values in a
comment line of its .cfg file:

    \\* state-space: states=1123 distinct=216 depth=6

The check fails when the actual values differ -- the state space changed, which
is either a bug or an intended spec change that must update the reference --
and when the reference line is absent. In both cases the line to paste into
the .cfg is printed, computed from the actual TLC output.
"""

import argparse
import re
import sys
from pathlib import Path

REFERENCE = re.compile(r"\\\* state-space: states=(\d+) distinct=(\d+) depth=(\d+)")
# Only the final summary line starts with the count; Progress(..) lines repeat
# the same text mid-line with thousands separators.
GENERATED = re.compile(r"^([\d,]+) states generated, ([\d,]+) distinct states found", re.MULTILINE)
DEPTH = re.compile(r"depth of the complete state graph search is (\d+)")


def actual_statistics(log: str) -> tuple[int, int, int]:
    """(states, distinct, depth) reported by a successful TLC run in `log`."""
    generated, depth = GENERATED.search(log), DEPTH.search(log)
    if generated is None or depth is None:
        raise ValueError("no state-space statistics found (did TLC succeed?)")
    states, distinct = (int(n.replace(",", "")) for n in generated.groups())
    return states, distinct, int(depth.group(1))


def check_state_space(cfg: Path, log: Path) -> list[str]:
    """Return every discrepancy between `cfg`'s reference and the run in `log`."""
    try:
        actual = actual_statistics(log.read_text())
    except ValueError as exc:
        return [str(exc)]
    line = "\\* state-space: states={} distinct={} depth={}".format(*actual)

    match = REFERENCE.search(cfg.read_text())
    if match is None:
        return [(f"no reference state-space line; if the current state space is\n"
                 f"    correct, add this line to {cfg.name}:\n    {line}")]
    reference = tuple(map(int, match.groups()))
    if reference != actual:
        return ["state space changed:\n"
                "    reference: states={} distinct={} depth={}\n".format(*reference)
                + "    actual:    states={} distinct={} depth={}\n".format(*actual)
                + f"    if this change is intended, update the reference to:\n    {line}"]
    return []


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("cfg", type=Path, help="TLC model configuration (.cfg)")
    parser.add_argument("log", type=Path, help="output of the TLC run on that model")
    args = parser.parse_args()

    try:
        errors = [f"{args.cfg}: {error}" for error in check_state_space(args.cfg, args.log)]
    except OSError as exc:  # unreadable .cfg or log file
        errors = [str(exc)]
    for error in errors:
        print(error, file=sys.stderr)
    if not errors:
        print(f"{args.cfg}: state space unchanged")
    return 1 if errors else 0


if __name__ == "__main__":
    sys.exit(main())
