# ArmoniK TLA+ Specification

The formal specification of [ArmoniK](https://github.com/aneoconsulting/ArmoniK)'s scheduling
algorithm, written in [TLA+](https://lamport.azurewebsites.net/tla/tla.html) and verified with
the TLC model checker and the TLA+ Proof System (TLAPS).

ArmoniK is a fault-tolerant orchestrator that executes graphs of tasks on elastic,
crash-prone infrastructure. Tasks consume and produce data objects; the data dependencies form a
graph that grows as users submit work, as failed tasks are retried, and as users pause, resume or
cancel tasks. This repository states what the scheduler must guarantee, and proves it.

## Approach

The specification is built by **refinement**. An abstract layer describes a lifecycle with few
states; each refinement details it (outcomes of processing, retries, user interventions) and is
proved to implement the layer above, so that every property proved at an abstract layer holds
for the concrete ones.

Three stacks of layers:

| Layer | Describes | Refines |
|---|---|---|
| `Task1` | the lifecycle of a task: registered, staged, assigned, processed, finalized | |
| `Task2` | outcomes of processing (succeeded, failed, discarded) and retries of failed tasks | `Task1` |
| `Task3` | user interventions: pause, resume and cancel attempt chains | `Task2` |
| `Object1` | the lifecycle of a data object: registered, then finalized; the user targets objects | |
| `Object2` | finalization split into completion and abortion | `Object1` |
| `Graph1` | tasks and objects linked by an acyclic data-dependency graph | `Task1`, `Object1` |
| `Graph2` | outcomes and retries over the graph, discarding of tasks with aborted inputs | `Graph1`, `Task2`, `Object2` |
| `Graph3` | user interventions over the graph | `Graph2`, `Task3` |

A Graph layer composes its actions from the Task and Object layers of the same level. Each layer
states **safety** properties (invariants, permanence of final states) and **liveness**
properties (targets are eventually finalized, the system eventually quiesces), under explicit
fairness conditions and liveness assumptions.

## Repository contents

| Path | Content |
|---|---|
| `specs/<X>.tla` | the specification of layer `<X>`: state, actions, fairness, properties |
| `specs/<X>Theorems.tla` | its theorems: the statements only |
| `specs/<X>Theorems_proofs.tla` | their machine-checked proofs (TLAPS) |
| `specs/<X>_mc.tla`, `specs/<X>_mc.cfg`, `specs/<X>.cfg` | finite models checked with TLC |
| `lib/` | libraries: directed graphs and data-dependency graphs (`DiGraphs`, `DDGraphs`, with a Java override that speeds up TLC), denumerable sets, the lifecycle states shared by the layers, and generic temporal-logic theorems, each with its theorems, proofs and test models |
| `scripts/` | the checks run by CI, in Python, with their tests |
| `.github/workflows/` | CI: parsing, property coverage, theorem pairing, model checking and proof checking of every module |
| `Makefile` | the entry point for installing the tools and running every check |

## Getting started

Linux or WSL, with a JDK 17 or later, Python 3, `curl`, `tar` and `git`.

```sh
make install       # download the TLA+ tools, TLAPS and the Python checks into .tlatools/ and .venv/
make check         # verify the installation
make help          # list every target
```

The tools are installed in the repository (`.tlatools/`), not system-wide. `make install` also
generates the VS Code settings of the TLA+ extension from `.vscode/settings.json.template`.

## Checking

```sh
make sany MODULE=Task2                                     # parse a module
make tlc MODULE=Task2_mc                                   # model-check a model
make tlapm MODULE=Task2Theorems_proofs                     # check the proofs of a module
make tlapm MODULE=Task2Theorems_proofs BEGIN=100 END=200   # only a line range
make test                                                  # lint and test the Python checks
```

Proofs are checked with `tlapm --strict`: an omitted step or an unproved obligation fails the
check. CI runs every check on every module for each pull request, with the latest releases of the
tools; `make chunks` shows how it splits a large proof module into ranges.

## Contributing

Commits and pull requests follow [CONTRIBUTING.md](CONTRIBUTING.md): one kind of change and one
module per commit, a header that names the change, and pull requests that record the motivation
of each milestone and how its checks moved.

## License

[Apache License 2.0](LICENSE).

## References

- [ArmoniK](https://github.com/aneoconsulting/ArmoniK)
- [The TLA+ home page](https://lamport.azurewebsites.net/tla/tla.html)
- [The TLA+ Proof System (tlapm)](https://github.com/tlaplus/tlapm)
- Leslie Lamport, *Specifying Systems*, Addison-Wesley, 2002.
