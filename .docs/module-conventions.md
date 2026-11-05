# TLA+ Module Conventions

This document defines how the TLA+ modules of this repository are laid out, formatted and
commented. Each kind of module has its own template: specification, model-checking harness, theorem
interface, proof module and library.

The convention is a frame, not a law. It does not foresee every case: depart from it when a module
reads better otherwise, and say why in a one-line comment where the departure is not obvious. A
departure from a rule the linter checks is declared to it (see [Tooling](#tooling)).

## Table of Contents

* [Module kinds](#module-kinds)
* [General rules](#general-rules)
* [Comments](#comments)
* [Specification module](#specification-module)
* [Model-checking module](#model-checking-module)
* [Theorem interface module](#theorem-interface-module)
* [Proof module](#proof-module)
* [Library modules](#library-modules)
* [Checking a reformatting](#checking-a-reformatting)
* [Tooling](#tooling)

---

## Module kinds

The kind of a module follows from its name and directory (see `scripts/naming.py`).

| Kind | Files | Template |
|------|-------|----------|
| Specification | `specs/<X>.tla` | [Specification module](#specification-module) |
| Model-checking | `specs/<X>_mc.tla`, `specs/<X>_mc.cfg` | [Model-checking module](#model-checking-module) |
| Theorem interface | `specs/<X>Theorems.tla` | [Theorem interface module](#theorem-interface-module) |
| Proof | `specs/<X>Theorems_proofs.tla` | [Proof module](#proof-module) |
| Library | everything in `lib/` and `lib/temporal/` | [Library modules](#library-modules) |

## General rules

### Width and frame

* A line is at most **80** characters, comments included.
* The module header is centered on exactly 80 characters, the footer is 80 `=`:

  ```tla
  --------------------------------- MODULE Name ----------------------------------
  ...
  ================================================================================
  ```

* Sections are separated by a rule of 80 `-`, followed by a boxed banner of exactly 80 characters
  whose title is upper case and centered:

  ```tla
  --------------------------------------------------------------------------------
  (******************************************************************************)
  (*                                  HELPERS                                   *)
  (******************************************************************************)
  ```

* An empty section is omitted; the remaining ones keep their order.

### Indentation and layout

* Indentation is 4 spaces, never tabs.
* A definition that does not fit on one line puts its body on the next line, indented by 4:

  ```tla
  TypeOk ==
      /\ objectState \in [Object -> O1State]
      /\ objectTargets \in SUBSET Object
  ```

* A conjunction or disjunction of more than one term is written as an aligned bullet list. Bullets
  of the same list start in the same column: SANY and tlapm parse a misaligned bullet as a different
  formula.
* `LET` and `IN` sit on their own lines, the definitions and the body indented by 4 below them.

### Naming

| Entity | Form | Examples |
|--------|------|----------|
| Constant (`CONSTANTS`) | starts with an upper-case letter | `Object`, `MaxRetries`, `NULL` |
| Variable (`VARIABLES`) | starts with a lower-case letter | `objectState`, `nextAttemptOf`, `deps` |
| Operator, action, property | `UpperCamelCase` | `RegisterObjects`, `TargetValidity` |
| Predicate | `Is<Property>` | `IsOpenNode`, `IsDDGraph` |
| Lifecycle state value | `UPPER_SNAKE_CASE` equal to its own name as a string | `TASK_STAGED == "TASK_STAGED"` |
| Set of nodes in a state | `<State><Kind>`, singular | `UnknownTask`, `CompletedObject` |
| Refinement mapping | `<variable>Bar` | `taskStateBar`, `objectStateBar` |
| Named refinement instance | short name of the abstract module | `T3`, `G2`, `O2` |
| Model-checking variant | `MC<Name>` | `MCSpec`, `MCDirectedGraphOf` |
| Lemma, theorem | see [Naming lemmas and theorems](#naming-lemmas-and-theorems) | `LemTypeOk`, `ThmTypeOk` |

The short name of a module abbreviates it by its CamelCase initials and trailing digits:
`Graph1` → `G1`, `Task2` → `T2`.

A temporal theorem of `lib/temporal/` is the one exception to the case of variables: it may declare
variables that start with an upper-case letter (`VARIABLES S, T`), since they stand for the
set-valued state functions a proof substitutes for them.

### Operators

* Binary union is written `\union`, never `\cup`; the union of a set of sets is written `UNION`.

### Ordering

Lists whose order carries no meaning are sorted, so that a reader finds an item at once and a diff
shows only real changes.

* **Alphabetical**, case-insensitive:
  * the modules of `EXTENDS`;
  * the `VARIABLES` declaration and the `vars` tuple, in the same order;
  * the conjuncts of `Init` and `TypeOk`, one per variable;
  * the variable updates of an action and the variables of its `UNCHANGED` tuple.
* **Guards before updates**: in an action, the enabling conditions come first, then the updates in
  alphabetical order, then `UNCHANGED`.
* **Exception for TLC**: TLC evaluates a conjunction from left to right and needs a primed variable
  to be assigned before it is read. When an update reads another primed variable, the order TLC
  requires wins over the alphabetical one.
* **`BY` and `DEF` clauses** follow the order of the [proof module](#proof-module).

## Comments

A comment helps someone who reads TLA+ to understand the purpose of the specification, of an
operator, of an action or of a property. It may justify a writing or modeling choice. It is concise.

* **No history.** A comment describes the module as it is, not how it came to be. Rationales,
  measurements and past attempts belong to commit bodies and pull requests.
* **No paraphrase** of the TLA+ code, except where the formula is hard to read, for instance under
  nested temporal operators (`[]`, `<>`, `~>`).
* **English**, full sentences, ending with a period.

Four comment forms are used, each with its own role:

| Form | Role |
|------|------|
| Boxed block, 80 characters wide | the module header, right below the `MODULE` line, and the section banners; nothing else |
| `(** ... *)` doc comment | directly above the definition, lemma or theorem it documents |
| `\*` end-of-line comment | one per declared constant, variable or state value, aligned in a column |
| `(* ... *)` short comment | inside a proof, rarely: see [Proof module](#proof-module) |

A doc comment opens with a **tag** in upper case on its own line when the template of the module
names one (`ACTION`, `INVARIANT`, `LIVENESS`, ...), then the text:

```tla
(**
 * ACTION
 * A set 'O' of currently targeted objects is unmarked.
 *)
```

Identifiers of the formula cited in a comment are quoted with single quotes (`'O'`).

In a theorem interface and its proof module, the text of a doc comment above a `----` line is shared
and must be identical in both files; the text below it is proof-only (see `check_proof_pairing`).

## Specification module

A specification defines the states, the initial condition, the actions, the specification formula
and the properties of one layer of the refinement stack.

```tla
--------------------------------- MODULE Name ----------------------------------
(******************************************************************************)
(* Header comment: short general description of the specification. A refined  *)
(* specification says what it adds to the specification it refines.           *)
(******************************************************************************)

EXTENDS Module1, Module2

--------------------------------------------------------------------------------
(******************************************************************************)
(*                    CONSTANTS, ASSUMPTIONS AND VARIABLES                    *)
(******************************************************************************)

CONSTANTS
    Cst  \* Description of the constant

ASSUMPTION Assumptions ==
    P(Cst)  \* Description of the assumption

VARIABLES
    var1,  \* Description of var1
    var2   \* Description of var2

vars == << var1, var2 >>

--------------------------------------------------------------------------------
(******************************************************************************)
(*                               INSTANTIATIONS                               *)
(******************************************************************************)

(**
 * Optional description of the imported module.
 *)
INSTANCE Module3

(**
 * Describe how the concrete state is mapped onto the abstract one.
 *)
var1Bar ==
    ...

(**
 * Optional description of the refined module and of its mapping.
 *)
Abs == INSTANCE AbstractTheorems WITH var1 <- var1Bar

--------------------------------------------------------------------------------
(******************************************************************************)
(*                                  HELPERS                                   *)
(******************************************************************************)

(**
 * Any helper operator used throughout the module.
 *)
Helper(...) ==
    ...

--------------------------------------------------------------------------------
(******************************************************************************)
(*                    SYSTEM INITIAL STATE AND TRANSITIONS                    *)
(******************************************************************************)

(**
 * INITIAL STATE
 * Short description of the initial state.
 *)
Init ==
    /\ var1 = ...
    /\ var2 = ...

(**
 * ACTION
 * Short description of what the action models.
 *)
Action1(...) ==
    /\ <guards>
    /\ var1' = ...
    /\ UNCHANGED var2

--------------------------------------------------------------------------------
(******************************************************************************)
(*                               ACTION HELPERS                               *)
(******************************************************************************)

(**
 * Any helper operator built on the actions, such as an action predicate that
 * is not a transition of the system.
 *)
ActionHelper ==
    ... Action1(...) ...

--------------------------------------------------------------------------------
(******************************************************************************)
(*                            SYSTEM SPECIFICATION                            *)
(******************************************************************************)

(**
 * NEXT-STATE RELATION
 * All the atomic transitions of the system.
 *)
Next ==
    \E ... :
        \/ Action1(...)
        \/ ...

(**
 * FAIRNESS CONDITIONS
 * Actions that must eventually occur while they stay enabled.
 * - Weak fairness of Action1: short description of the fairness condition.
 *)
Fairness ==
    \A x \in Entity :
        WF_vars(... /\ Action1({x}))

(**
 * LIVENESS ASSUMPTION
 * Liveness assumption that cannot be written as a fairness condition.
 *)
AdditionalLiveness ==
    ...

(**
 * Full system specification.
 *)
Spec ==
    /\ Init
    /\ [][Next]_vars
    /\ Fairness
    /\ AdditionalLiveness  \* Optional

--------------------------------------------------------------------------------
(******************************************************************************)
(*                       SAFETY AND LIVENESS PROPERTIES                       *)
(******************************************************************************)

(**
 * INVARIANT
 * The state variables belong to their expected domains.
 *)
TypeOk ==
    /\ var1 \in Cst
    /\ var2 \in ...

(**
 * INVARIANT
 * Any other invariant.
 *)
SafeInv ==
    ...

(**
 * SAFETY
 * Non-invariant safety property.
 *)
SafeProp ==
    ...

(**
 * SAFETY
 * A safety property of each object.
 *)
SafeObjectProp ==
    \A o \in Object :
        [](P(o) => []P(o))

(**
 * LIVENESS
 * Any liveness property.
 *)
LiveProp ==
    ...

(**
 * LIVENESS
 * A liveness property of each object.
 *)
LiveObjectProp ==
    \A o \in Object :
        At(o) :: ...

(**
 * REFINEMENT
 * Any refinement property with an instantiated module.
 *)
RefineAbstract ==
    Abs!Spec

================================================================================
```

### Rules

* **Instantiations.** The section holds, in this order, the imported libraries (unnamed `INSTANCE`),
  the refinement mappings `<variable>Bar`, then the named instances of the refined layers. A named
  instance targets the theorem interface of the abstract layer (`INSTANCE Graph2Theorems`), not the
  specification itself, so that the proofs can lift its lemmas instead of re-proving them.
* **Helpers.** A helper sits in the `HELPERS` section before the transitions. A helper built on
  actions, which TLA+ requires to be defined first, sits in the `ACTION HELPERS` section, right
  after the transitions: an action predicate that is not a transition of the system.
* **Actions.** One action per lifecycle transition, parameterized by the set of entities it acts on
  (`RegisterObjects(O)`). Every action lists all variables, either updated or in `UNCHANGED`.
* **Fairness.** One conjunct per fairness condition, without label: proofs name a condition
  through its restatement without `ENABLED` (see the theorem interface). The doc comment describes
  each condition in one line, `- Weak fairness of Action1: ...` or `- Strong fairness of Action1:
  ...`. A condition is indexed by the entity it is about, even when the action acts on a related
  entity (the next attempt of a task `t`); the doc comment then says so. A condition about a pair
  of entities, such as a task in the open ancestry of a target object, is indexed by the pair,
  `\A t \in Task, o \in Object : WF_vars(...)`. When several conditions constrain the same action,
  each one fairly drives an action helper of the `ACTION HELPERS` section that names its case
  (`DiscardOnAbortedInput(t, o)`), and the condition is named after that helper.
* **Liveness assumption.** A liveness assumption quantified over entities labels its body
  `At(x) ::`, like a liveness property, and is written in its simplest equivalent form:
  `\A o \in Object : At(o) :: <>[](o \in objectTargets) => <>[][A(o)]_f(o)` rather than
  `[]([](o \in objectTargets) => ...)`.
* **Properties.** Every parameterless operator defined after the `SAFETY AND LIVENESS PROPERTIES`
  banner is a property: the interface restates it as a theorem (CI `check_property_coverage`).
  A parameterized operator placed there only serves the properties that follow it.
* **Inherited properties.** A refinement restates, in its own vocabulary, each property of the
  refined layer whose meaning changes through the refinement mapping, including the properties the
  refined layer itself inherits from the layers below, and proves it by lifting:
  `Spec => Abs!Spec`, the theorem of the refined layer, then the mapping unfolded. A property the
  mapping leaves unchanged stays inherited as `Abs!P` and is not restated.
* **Declared, not hidden.** Every property a proof relies on (`TypeOk`, each invariant) is defined
  in the specification, so that it is known without reading the proofs. The global inductive
  invariant `Inv` is the only exception: it lives in the interface. An invariant that is not
  inductive is replaced in the specification by its inductive strengthening, rather than proved
  through a helper invariant of the interface. An invariant that only holds for infinite
  constants is declared all the same and left out of the model's `.cfg`, which its doc comment
  says.
* **Names of properties.** A property is named after what it states. Only an invariant may end in
  `Invariant`, and its tag matches its form: `INVARIANT` for a state predicate, `SAFETY` for any
  other safety property.
* **Action properties.** A safety property `[](P => [][A]_f)` whose premise `P` is stable once it
  holds is written as the action property `[][P => A]_f`, which TLC checks and whose lemma is a
  step lemma.
* **Diamonds.** When a layer refines a layer both directly and through an intermediate one, it
  keeps its direct instance to state the refinement theorem, and proves it by lifting the
  refinement of the intermediate layer, without re-proving it.
* **Tags.** The doc comment of a definition after the transitions banner opens with one of
  `INITIAL STATE`, `ACTION`, `NEXT-STATE RELATION`, `FAIRNESS CONDITIONS`, `LIVENESS ASSUMPTION`,
  `INVARIANT`, `SAFETY`, `LIVENESS` or `REFINEMENT`. `Spec` and the helpers carry no tag.
* **Order of the properties.** The properties come in a logical order, at least the order in
  which they are proved: a property comes after those its proof relies on.
* **Liveness per element.** A liveness property quantified over entities labels its body
  `At(x) ::`, so that its lemma can be stated for one entity:
  `\A o \in Object : At(o) :: <>[](o \in objectTargets) => ...`.
* **Bound names.** A bound variable over a set of entities is named after it, the same way in every
  module: `o` for objects, `t` for tasks. tlapm matches the conclusion of a temporal lemma only at
  the bound name it is stated with.

## Model-checking module

A model-checking module adapts a specification to TLC: finite constants, operators TLC cannot
evaluate, deadlock and state-space control. It adds no behavior that matters for the properties.

```tla
-------------------------------- MODULE Name_mc --------------------------------
(******************************************************************************)
(* Short description of what this module changes to make the specification    *)
(* model-checkable.                                                           *)
(******************************************************************************)

EXTENDS Name, ...

--------------------------------------------------------------------------------
(******************************************************************************)
(*                                 OVERRIDES                                  *)
(******************************************************************************)

(**
 * Redefine an operator, action or property for the model checker. It is
 * substituted by the configuration file.
 *)
MCOp ==
    ...

(**
 * Redefined specification to make the formula compliant with TLC.
 *)
MCSpec ==
    ...

--------------------------------------------------------------------------------
(******************************************************************************)
(*                        MODEL-CHECKING CONFIGURATION                        *)
(******************************************************************************)

(**
 * Why TLC needs this constraint, and why it hides no relevant behavior.
 *)
StateConstraint ==
    ...

(**
 * Why TLC needs this constraint, and why it hides no relevant behavior.
 *)
ActionConstraint ==
    ...

\* Other model-checking configuration.

================================================================================
```

### Rules

* **Overrides** hold every `MC<Name>` redefinition: enumerators substituted in the `.cfg`
  (`MCDirectedGraphOf`), the terminal stuttering step and the `MCNext` that adds it, `MCSpec`, and
  the checkable forms of refinement properties (`MCRefineGraph2`). Each doc comment says why TLC
  needs it and why it does not weaken what is checked.
* **Model-checking configuration** holds the constraints (`StateConstraint`, `ActionConstraint`,
  `Symmetry`) and the assumptions on the finite constants (`ASSUME Cardinality(Task) > MaxRetries`).
* **The `.cfg` file** starts with the `\* state-space:` reference line (CI `check_state_space`),
  then the blocks `CONSTANTS`, `SPECIFICATION`, `INVARIANTS`, `PROPERTIES`, `SYMMETRY`,
  `CONSTRAINT`, `ACTION_CONSTRAINT`, in this order, each entry indented by 4. In `CONSTANTS`, the
  model values come first, then the substitutions `<-`, each group aligned on its operator.
  Invariants and properties are listed in the order of the specification.

## Theorem interface module

The interface states every lemma and theorem of the proof development of a specification, without
proofs. A refining layer instantiates it to lift these results. Its sections follow the order of the
proof: each result is stated after those it relies on.

```tla
----------------------------- MODULE NameTheorems ------------------------------
(******************************************************************************)
(* Proofs of all the properties of Name.                                      *)
(******************************************************************************)

EXTENDS Name

--------------------------------------------------------------------------------
(******************************************************************************)
(*                                  BRIDGES                                   *)
(******************************************************************************)

(**
 * Under the instance, the operators of Abs denote the operators of Name.
 *)
LEMMA LemAbsBridges ==
    /\ \A x : Abs!Op(x) = Op(x)
    /\ ...

(**
 * The assumptions of Name imply those of Abs.
 *)
LEMMA LemAbsAssumptions == Abs!Assumptions

--------------------------------------------------------------------------------
(******************************************************************************)
(*                               HELPER LEMMAS                                *)
(******************************************************************************)

(**
 * A result used by several proofs below.
 *)
LEMMA LemHelper ==
    ASSUME ...
    PROVE  ...

--------------------------------------------------------------------------------
(******************************************************************************)
(*                              TYPE CORRECTNESS                              *)
(******************************************************************************)

LEMMA LemTypeOk == Init /\ [][Next]_vars => []TypeOk

--------------------------------------------------------------------------------
(******************************************************************************)
(*                              STEP SIMULATION                               *)
(******************************************************************************)

LEMMA LemInitSimulateAbsInit == Init => Abs!Init

(**
 * Optional description of the correspondence.
 *)
LEMMA LemAction1SimulateAbsAction1 ==
    ASSUME NEW x ...
    PROVE  TypeOk /\ Action1(x) => Abs!Action1(x)

LEMMA LemNextSimulateAbsNext == TypeOk /\ [Next]_vars => [Abs!Next]_(Abs!vars)

--------------------------------------------------------------------------------
(******************************************************************************)
(*                                 INVARIANTS                                 *)
(******************************************************************************)

LEMMA LemSafeInv == Init /\ [][Next]_vars => []SafeInv

--------------------------------------------------------------------------------
(******************************************************************************)
(*                            INDUCTIVE INVARIANT                             *)
(******************************************************************************)

(**
 * The invariants used by the liveness proofs.
 *)
Inv ==
    /\ TypeOk
    /\ SafeInv

LEMMA LemInv == Init /\ [][Next]_vars => []Inv

--------------------------------------------------------------------------------
(******************************************************************************)
(*                          OTHER SAFETY PROPERTIES                           *)
(******************************************************************************)

LEMMA LemSafeProp == []Inv /\ [][Next]_vars => SafeProp

(**
 * P(o) holds at every step once it holds.
 *)
LEMMA LemSafeObjectProp ==
    ASSUME NEW o \in Object, [Next]_vars
    PROVE  P(o) => P(o)'

--------------------------------------------------------------------------------
(******************************************************************************)
(*                           ENABLED-FREE FAIRNESS                            *)
(******************************************************************************)

(**
 * The fairness conditions restated without ENABLED, which a substitution
 * does not distribute over.
 *)
EnabledAction1(x) == ...

FairAction1(x) == <>[]EnabledAction1(x) => []<><<... /\ Action1({x})>>_vars

LEMMA LemFairnessEnabledFree == Fairness <=> \A x \in Entity : FairAction1(x)

--------------------------------------------------------------------------------
(******************************************************************************)
(*                           FAIRNESS PRESERVATION                            *)
(******************************************************************************)

(**
 * The weak fairness of Abs!Action1 for one entity holds under Name.
 *)
LEMMA LemPreserveAbsWFAction1 ==
    ASSUME NEW x \in Entity
    PROVE  FairAction1(x) => Abs!FairAction1(x)

--------------------------------------------------------------------------------
(******************************************************************************)
(*                                  LIVENESS                                  *)
(******************************************************************************)

LEMMA LemLiveProp ==
    []Inv /\ [][Next]_vars /\ (\A x \in Entity : FairAction1(x)) => LiveProp

LEMMA LemLiveObjectProp ==
    ASSUME NEW o \in Object
    PROVE  []Inv /\ [][Next]_vars /\ FairAction1(o) => LiveObjectProp!At(o)

--------------------------------------------------------------------------------
(******************************************************************************)
(*                           SPECIFICATION THEOREMS                           *)
(******************************************************************************)

THEOREM ThmTypeOk == Spec => []TypeOk

THEOREM ThmSafeInv == Spec => []SafeInv

THEOREM ThmSafeProp == Spec => SafeProp

THEOREM ThmSafeObjectProp == Spec => SafeObjectProp

THEOREM ThmLiveProp == Spec => LiveProp

THEOREM ThmLiveObjectProp == Spec => LiveObjectProp

THEOREM ThmRefineAbstract == Spec => RefineAbstract

================================================================================
```

### Header

The header comment of a specification's theorem modules is generic: `Proofs of all the properties
of <X>.` A property that is not proved is named there as an exception.

### Section contents

1. **Bridges.** Under an `INSTANCE`, every operator of the instantiated module is a distinct symbol,
   even when the mapping is the identity. The bridges prove once that each instantiated operator
   denotes the local one, then that the local assumptions imply the instantiated ones, then the
   algebra of the refinement mapping (`LemBarUpdate`, `LemBarStutter`).
2. **Helper lemmas.** Results used by several proofs of the module, or by a refining layer. A
   result used once is a step of the proof that uses it, not a lemma.
3. **Type correctness.** `LemTypeOk`, proved inductive on its own, before the step simulation,
   which may need it.
4. **Step simulation.** For each refined layer, the simulation of its `Init`, of each action, and
   their assembly into `Next`. The converse lemmas that a refining layer needs, from a step of the
   refined layer back to an action, close the section.
5. **Invariants.** One lemma per invariant of the specification. The invariants lifted from a
   refined layer through step simulation come first. An invariant may be proved conjoined with
   `TypeOk` and with invariants proved before it.
6. **Inductive invariant.** The definition of `Inv`, the conjunction of `TypeOk` and of the
   invariants the liveness proofs use, and its lemma. `TypeOk` stays in `Inv` even when no liveness
   proof uses it, for the properties to come.
7. **Other safety properties.** One lemma per safety property that is not an invariant. It comes
   after `Inv`, which its proof may use. The lemma of a property per entity is its step for one
   entity (see [Statements](#statements)), from which the theorem derives the property by `PTL`.
   A step lemma wider than one property, such as the stability of every lifecycle state, stays a
   helper lemma with a descriptive name; the lemma of each property is then its corollary.
8. **ENABLED-free fairness.** Each fairness condition restated without `ENABLED` for one entity,
   `Enabled<Action>(x)` and `Fair<Action>(x)`, `<>[]Enabled<Action>(x) => []<><<...>>_vars` for
   weak fairness and `[]<>Enabled<Action>(x) => []<><<...>>_vars` for strong fairness, and the
   lemma `LemFairnessEnabledFree` that proves
   `Fairness` equivalent to their conjunction. The refining layers and the per-entity lemmas use
   these restatements.
9. **Fairness preservation.** For each refined layer, one lemma per condition of its fairness, in
   the order of that fairness, stated for one entity between restatements without `ENABLED`. The
   refinement theorem assembles them into `Fairness => Abs!Fairness` in one of its steps, since
   the liveness lemmas only need the conditions they use. A preservation that follows from a
   liveness property of the specification comes right after the lemma of that property.
10. **Liveness.** One lemma per liveness property. The properties lifted from a refined layer come
    first.
11. **Specification theorems.** The results expected of the specification: one theorem per
    property, stated over `Spec` and proved by citing its lemma. A property per entity is proved
    for one entity, `SUFFICES ASSUME NEW o \in Object PROVE Spec => ...`, from its per-entity lemma.

Step simulation and fairness preservation exist only in a refinement. They are stated as early as
the facts they need allow, even in the middle of the invariants or of the liveness lemmas, so that
the following results can lift the properties of the refined layer. The same holds for a step
lemma of a safety property, own or lifted, that an invariant or the step simulation cites.

### Statements

* **Minimal hypotheses.** A lemma assumes only what its proof uses: `[]Inv` when it uses an
  invariant, the fairness conditions it uses, never `Spec`. The theorem over `Spec` then follows
  from the lemma. One exception: a liveness lemma always assumes `[][Next]_vars`, which keeps the
  liveness lemmas uniform and which a refining layer supplies anyway.
* **No temporal `ASSUME`.** A temporal hypothesis is written as an implication, not as an `ASSUME`
  clause.
* **Per entity.** A refining layer reuses a lemma for one entity; removing a quantifier under a
  temporal operator costs a detour at every citation. A property quantified over entities is
  therefore stated for one entity, `ASSUME NEW o \in Object`:
  * a safety property is stated for one step, the counterpart of its body:
    `ASSUME NEW o \in Object, [Next]_vars PROVE P(o) => P(o)'` for a permanence
    `[](P(o) => []P(o))`, the action `[A(o)]_f` for an action property `[][A(o)]_f`, the
    strengthened step `P(o) /\ Q(o) => P(o)'` for `[](P(o) /\ Q(o) => []P(o))`. It assumes
    `TypeOk` or `Inv` when the step needs it;
  * a liveness property assumes the fairness conditions of that entity it uses, in their form
    without `ENABLED` and conjoined when there are several, and concludes the labelled body:
    `[]Inv /\ [][Next]_vars /\ FairAction1(o) => LiveObjectProp!At(o)`.

  A fairness condition about a pair of entities is restated for the pair, `FairAction1(t, o)`,
  and a lemma that uses it declares both, `ASSUME NEW t \in Task, NEW o \in Object`. A liveness
  assumption is assumed like a fairness condition, through its label: `AdditionalLiveness!At(o)`
  for one entity, or the assumption itself for all; its preservation by a refinement is stated for
  one entity, `ASSUME NEW o \in Object PROVE AdditionalLiveness!At(o) => Abs!AdditionalLiveness!At(o)`,
  in the fairness preservation section.

  Invariants, step simulation and properties without such a quantifier, such as termination,
  keep their global statement.
* **No `ENABLED` in a statement.** tlapm cannot instantiate `ENABLED` under a non-identity
  substitution. Enabledness facts are proof steps; a fairness condition that refinements must
  preserve is restated without `ENABLED` (`Enabled<Action>`, `Fair<Action>`), next to the lemma
  that proves the restatement equivalent. A lemma assumes these restatements, for one entity
  (`FairAction1(o)`) or for all (`\A x \in Entity : FairAction1(x)`), never `Fairness` nor one of
  its subexpressions, which tlapm unfolds under an instance. Only the theorems over `Spec` see
  `Fairness`, and recover the restatements through `LemFairnessEnabledFree`.
* **Temporal theorems** may declare `VARIABLES` over which they are stated; a proof substitutes them
  through `INSTANCE ... WITH`.

### Naming lemmas and theorems

* A lemma is named `Lem<X>`, a theorem `Thm<X>`.
* `<X>` is the name of the property when the statement is about a property: `LemTypeOk`,
  `ThmTargetValidity`, `ThmRefineGraph2`.
* `<X>` is `<Action>Simulate<Abs><AbsAction>` for the step simulation of an action by an action
  of the refined layer `<Abs>`: `LemInitSimulateO1Init`,
  `LemAbortObjectsSimulateO1FinalizeObjects`, `LemNextSimulateO1Next`. The statement is an
  implication, the parameters declared by `ASSUME NEW`:
  `ASSUME NEW O \in SUBSET Object PROVE AbortObjects(O) => O1!FinalizeObjects(O)`. An action that
  the refined layer sees as a stutter gives `<Action>Simulate<Abs>Stuttering`, concluding
  `UNCHANGED Abs!vars`; an action simulated by one of two actions gives
  `<Action>Simulate<Abs><AbsAction1>Or<AbsAction2>`, and by an action or a stutter
  `<Action>Simulate<Abs><AbsAction>OrStuttering`. A converse lemma is named
  `<Action>From<Abs>Step`.
* `<X>` is `Preserve<Abs><WF|SF><AbsAction>` for the preservation of a fairness condition of the
  refined layer: `LemPreserveO1WFFinalizeObjects`, and `Preserve<Abs><Assumption>` for a liveness
  assumption: `LemPreserveG1UpstreamStabilization`. Unlike an action, a fairness condition is not
  simulated by a single counterpart: the lemma may assume `[]Inv`, `[][Next]_vars` and any
  combination of the fairness conditions of the specification.
* A property lifted from a refined layer is named `Lem<Abs><P>`: `LemG2Inv`.
* Bridges are named `Lem<Abs>Bridges`, `Lem<Abs>Assumptions`, `Lem<Abs>BarStates`.
* Any other name says what the result states: `LemTargetsAreKnown`, `LemRootStable`. No history
  (`New`, `2`, `Fixed`), no proof technique.

## Proof module

The proof module copies the interface and adds the proofs.

* **Same layout.** Same header, same sections in the same order, same statements, same shared doc
  comments (CI `check_proof_pairing`). A proof-only note goes below the `----` line of the doc
  comment.
* **Preamble.** `EXTENDS` adds the proof libraries (`TLAPS`, `FiniteSetTheorems`, ...) to the
  modules of the interface, in alphabetical order. A `USE DEF` of the lifecycle state values follows
  it.
* **Step names** are numbers: `<n>1`, `<n>2`, ... A step nobody cites is written `<n>.`.
* **`BY` clauses** list, in this order: step references, by level then number; named facts; proof
  pragmas (`ExpandENABLED`, `PTL`, `Zenon`, `Isa`, ...); `DEF` and the definitions. Facts and
  definitions are alphabetical, case-insensitive, on the name after its last `!`, the local name
  first: `Ancestor, G1!Ancestor, Bijection`.
* **A theorem over `Spec`** is proved by citing its lemma: `BY LemLiveProp, LemInv DEF Spec`.
* **Proof-only definitions.** A definition that only proofs use, such as a primed predicate or an
  instance of a temporal theorem, stays in the proof module, right before the first proof that
  uses it, with a doc comment. It moves to the interface only when a statement uses it.
* **Citing a step lemma.** `PTL` does not instantiate the `ASSUME NEW` parameter of a step
  lemma: a one-line step states it for the entity at hand,
  `<1>3. [Next]_vars => (P(o) => P(o)') BY LemSafeObjectProp`, and `PTL` cites that step.
* **Comments in proofs.** A proof carries no comment by default: its step statements and the doc
  comments of the definitions it uses tell the argument. A short `(* ... *)` comment before a step
  is kept only where it makes the proof markedly easier to follow, or justifies a choice the reader
  would not guess (a tool constraint, a non-obvious decomposition).

The structure of the proofs themselves (step hierarchy, `DEFINE`s, backends) follows the
`tlaplus-proof-cleanup` skill.

## Library modules

A library is reusable and independent of any specification. There are five kinds.

* **Definition libraries** (`DiGraphs`, `DDGraphs`, `DenumerableSets`): a header comment states
  the objects defined and the representation chosen, then one doc comment per operator. A
  definition stays close to its mathematical formulation, so that proofs can use it. A variant
  optimized for TLC is named `MC<Name>`; when TLC needs Java speed, a `.java` override sits next to
  the module.
* **State libraries** (`TaskStates`, `ObjectStates`, `TaskRetries`, `TaskIntents`): they declare
  the constants and variables they are parameterized by, then the state values with an aligned
  `\*` comment each, then the sets of entities in each state. A specification imports them with an
  unnamed `INSTANCE`.
* **Theorem libraries** (`<X>Theorems`, `<X>Theorems_proofs`): the interface and proof pairing of
  the specifications applies. Libraries are extended together, so their theorems carry a prefix
  unique to the library: `DG_` for `DiGraphTheorems`, `DDG_` for `DDGraphTheorems`, `DS_` for
  `DenumerableSetTheorems`. A theorem bundles the facts about one subject.
* **Temporal theorems** (`lib/temporal/`): one theorem per module, named after the module, stated
  over module-level `VARIABLES` and over constant parameters `ASSUME NEW`. The header comment says
  under which bound names a proof must cite it.
* **Test modules** (`<X>Tests.tla`, `<X>Tests.cfg`): a list of `ASSUME AssertEq(...)` checked by
  TLC, grouped by operator under a short comment.

The general rules apply: header comment, sections with banners when the module has several parts,
doc comments, alphabetical `EXTENDS`.

## Checking a reformatting

A reformatting changes the layout, never the meaning. It is checked as follows.

1. **Syntax tree.** `scripts/check_reformat.py` compares the parse trees of the module before and
   after. It ignores comments, whitespace, the frame, redundant parentheses, the bullet or infix
   form of a conjunction or disjunction, and synonymous spellings (`\cup` and `\union`, `LEMMA`
   and `THEOREM`, ...). It compares the sorted lists of [Ordering](#ordering) and the operands of
   a conjunction as multisets, and lists each reordering. A renamed lemma or theorem is declared to
   it with `--rename OLD=NEW`.
2. **Parsers.** SANY parses the module with `-error-codes`.
3. **Model checking.** When the comparison lists a reordering in a definition (`vars`, `Init`, an
   action), TLC reproduces the `\* state-space:` line of each model that uses the module.
4. **Proofs.** When the comparison lists a reordering in a definition or a statement, or when a
   lemma or theorem was renamed, the proofs that depend on it still check (`tlaplus-proof-check`
   skill), and CI `check_proof_pairing` and `check_property_coverage` pass. A rename also reaches
   the modules that cite the renamed result.

## Tooling

| Command | Checks |
|---------|--------|
| `make style [MODULE=<mod>]` | the mechanical rules of this convention, on one module or on all |
| `.venv/bin/python -m scripts.check_reformat <path> [--rev <rev>] [--rename OLD=NEW]` | that a reformatting keeps the meaning of the module, against a git revision (default `HEAD`) |
| `.venv/bin/python -m scripts.check_property_coverage <spec>` | that each property `P` of a specification has its theorem `ThmP` |

The linter `scripts/check_module_style.py` reports each violation under the name of its rule (its
docstring lists them): line width, frame, banners and sections, the sorted lists, case of
constants and variables, binary union, names of lemmas and theorems, order of `BY` clauses. It
leaves to review what a reader must judge: what a comment says, doc-comment tags, whether a name
says what a result states.

A departure from a checked rule is declared by a line comment inside the top-level unit it concerns,
or on the lines just above it. It silences the rules it names for that unit only:

```tla
\* style-exception(action-order): TLC reads taskState' in the update of deps
RegisterGraph(G) ==
    ...
```
