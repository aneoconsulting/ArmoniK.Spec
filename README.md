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

## Environment set-up

Prerequisites:
* Ubuntu 24.04 or higher (because of glibc version).
* Visual Studio Code

To set-up the environment run the following command:

```bash
bash install.sh
```

It will install all the tools required to work with the specifications. It assumes Java is properl installed on your system.

The following tools are installed:
* TLA2Tools
* Apalache
* tlaps
* tlafmt

To finish the set-up, launch VSCode and install the required extensions.

## Repository contents

## How to use this repository?

## References

* [ArmoniK Project](https://github.com/aneoconsulting/ArmoniK)
* [TLA+ Home Page](https://lamport.azurewebsites.net/tla/tla.html)
