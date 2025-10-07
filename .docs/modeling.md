# ArmoniK Modeling Using TLA+

## Introduction

**ArmoniK** is a production-grade system with a complex codebase, components, and configurations. The purpose of this TLA+ specification is to formally describe the existing system, ensuring correctness and clarity. Since ArmoniK was developed without prior formal specification, many aspects require clarification and justification.

This document discusses and documents the assumptions and modeling choices made to formalize ArmoniK’s design and algorithms. It details the model design based on the actual implementation, specifying and justifying omissions and simplifications.

> **ℹ️ NOTE**
> The state-of-the-art modeling approach in TLA+ is iterative refinement. We start with an abstract description of ArmoniK’s operation and progressively refine it.

---

## Table of Contents

1. [An Abstract Decentralized Online Scheduling System](#an-abstract-decentralized-online-scheduling-system)
2. [Considering Task Inputs/Outputs](#considering-task-inputsoutputs)
3. [Adding Task Dependencies](#adding-task-dependencies)

---

## An Abstract Decentralized Online Scheduling System

At a high level, ArmoniK can be seen as a **decentralized online task scheduler**. It consists of a set of **Scheduling Agents** (whose number is unknown and may vary over time) responsible for executing tasks submitted to the system.

System constraints:
- **Task Submission**: New tasks can be submitted at any time. Each task must be unique and cannot be submitted more than once.
- **Task Acquisition**: An agent can acquire a set of available tasks (uncompleted and not being processed by any other agent) for execution.
- **Task Release**: An agent can release all or part of the tasks it is processing, making them available again.
- **Task Completion**: An agent can complete all or part of the tasks it is processing, notifying the system to avoid future re-executions.

System properties:
- **Exclusivity**: A task cannot be executed simultaneously by two distinct agents.
- **Completion**: Every submitted task must eventually be completed.
- **Persistence**: Once completed, a task remains completed forever.

> **ℹ️ REMARK**
> A *task* abstracts a request to perform a computation, i.e., executing a set of instructions.

**A status is associated with each task to track its position in the scheduling process.** Based on the previous informal description, it is possible to scheme the life-cycle of a task as shown in the following figure.

```mermaid
stateDiagram-v2
    direction LR
    [*] --> Submitted : Submit
    Submitted --> Started : Schedule
    Started --> Completed : Release
    Started --> Submitted : Complete
    classDef completed fill:#006400
    class Completed completed
```

**In this diagram, each state corresponds to a given status for a task, and the transitions describe the system as a transition system.** This transition system, associated with the desired properties, is specified in [SimpleTaskScheduling](../specs/SimpleTaskScheduling.tla).

> **ℹ️ NOTE**
> The set of tasks and agents is represented by unique identifiers from an implicit, potentially infinite set. For model checking, these sets are materialized and made finite. A dedicated specification, [MCSimpleTaskScheduling](../specs/MCSimpleTaskScheduling.tla), introduces a dummy terminating action to avoid deadlocks.

---

Here’s the corrected and expanded section for **Considering Task Inputs/Outputs**, restoring the two-step refinement and clarifying the role of task I/Os:

---

## Considering Task Inputs/Outputs

The previous description omits **task I/Os**, which are central to ArmoniK as they express dependencies between tasks. Tasks consume inputs and produce outputs, which are modeled as *objects*. The refinement of the specification to include I/Os is done in **two steps**:

1. **Abstract Object Processing**: A specification that describes how data (objects) are processed.
2. **Refined Task Scheduling with I/Os**: A specification that integrates task scheduling with their I/Os.

> **ℹ️ REMARK**
> Just as a *task* abstracts the notion of computation, we need an abstraction for data: this is called an *object*, which encapsulates all information relating to a particular piece of data.

### Abstract Object Processing

The high-level view of object processing by ArmoniK corresponds to the following constraints:
- **Object Creation**: An object can be created empty (a container for data that is not yet available) or completed (with its data provided at creation).
- **Object Completion**: An empty object can be completed by providing its data.
- **Object Locking**: A completed object can be locked to forbid overwriting, ensuring data consistency.

> **ℹ️ NOTE**
> The creation of a completed object is equivalent to the composition of the creation of the empty object with the completion of that object. This is why the action of creating a completed object does not appear in the specification.

> **ℹ️ NOTE**
> Early drafts considered objects as immutable, but this was abandoned to allow overwriting in case of task failures (e.g., if a task crashes after writing its first result, it must be able to overwrite it during future executions).

The processing of objects must guarantee the following properties:
- **Completion**: Every submitted object must eventually be completed.
- **Persistence**: Once completed, an object remains completed forever.

Like for tasks, a status is associated with each object to track its position in the processing. Based on the previous informal description, it is possible to scheme the life-cycle of an object as shown in the following figure.

```mermaid
stateDiagram-v2
    direction LR
    [*] --> Created : CreateEmpty
    [*] --> Completed : CreateCompleted
    Created --> Completed : Complete
    Completed --> Locked : Lock
    Locked --> Locked : Lock
    classDef locked fill:#006400
    class Locked locked
```

The processing of objects is specified in [SimpleObjectProcessing](../specs/SimpleObjectProcessing.tla). As with tasks, the specification uses an implicit set for object identifiers.

> **ℹ️ NOTE**
> To enable model checking, the [MCSimpleObjectProcessing](../specs/MCSimpleObjectProcessing.tla) specification extends [SimpleObjectProcessing](../specs/SimpleObjectProcessing.tla).

### Refined Task Scheduling with I/Os

The system now couples task scheduling with object processing, describing the scheduling of dynamic task graphs. This specification refines both [SimpleTaskScheduling](#) and [SimpleObjectProcessing](#).

### Additional Constraints

- The task and object dependencies form a **bipartite directed-acyclic graph** with objects as roots and leaves.
- Task dependencies cannot be modified after submission.
- A task can be scheduled only when all its input objects are completed.
- Objects are locked once consumed.
- A task cannot complete until all its output objects are completed.
- Task dependencies are resolved only after completion.

### System Properties

- The task graph is always consistent.
- The system refines the previous specifications.

> **ℹ️ THOUGHTS**
> - Tasks and data must be processed in the order defined by the task/data graph.
> - Consider using automata composition for state diagrams.

> **⚠️ IMPORTANT**
> In all specifications, tasks, objects, and agents are identified by labels. Swapping these labels does not change system behavior, encouraging the use of symmetry reduction.

---