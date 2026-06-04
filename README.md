# ArmoniK TLA+ Specification

**Formal specification of ArmoniK's scheduling algorithm using TLA+**

This repository contains the [TLA+](https://lamport.azurewebsites.net/tla/tla.html) specification for **ArmoniK**, a fault-tolerant, distributed scheduler designed to execute complex task graphs on elastic and unreliable infrastructures.

The goal of this specification is to:
- Capture the core logic of ArmoniK in a precise and verifiable way
- Validate key correctness and fault-tolerance properties
- Improve confidence in the system's reliability and robustness

## What is ArmoniK?

ArmoniK is a high-performance orchestration system for distributed DAG-based workloads. It efficiently schedules and executes tasks across dynamic and potentially crash-prone compute nodes.

## What is TLA+?

[TLA+](https://lamport.azurewebsites.net/tla/tla.html) (Temporal Logic of Actions) is a formal specification language developed by Leslie Lamport. It is used to design, model, document, and verify concurrent and distributed systems.

TLA+ is designed to:
- Model complex system behavior with simple mathematics;
- Check safety and liveness properties;
- Discover subtle bugs *before* implementation.

## Repository contents

## How to use this repository?

### Checking theorem/proof sync

Each `specs/XTheorems.tla` library module declares theorems without proofs; the
matching `specs/XTheorems_proofs.tla` module re-declares the same theorems with
proof bodies. `scripts/check_proofs_sync.py` verifies the two stay in sync: the
`_proofs` module is the source of truth, and the declaration module must match
it in theorem presence, order, statements, and doc-comments (proof bodies,
`EXTENDS`, the module name, and the module header comment are ignored). The
script is read-only — it reports discrepancies and never edits any file.

Run it locally (also suitable as a manual pre-commit check):

```sh
make check-sync
```

This creates a `.venv/` and installs the pinned dependencies from
`requirements.txt` (`tree-sitter`, `tree-sitter-tlaplus`), then checks every
pair under `specs/`. It exits non-zero if any module is out of sync. The same
check runs in CI. To run the script's own unit tests:

```sh
python -m unittest discover -s tests
```


## References

* [ArmoniK Project](https://github.com/aneoconsulting/ArmoniK)
* [TLA+ Home Page](https://lamport.azurewebsites.net/tla/tla.html)
