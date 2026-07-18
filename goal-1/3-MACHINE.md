# 3-MACHINE

## Current Facts

- Stages 1 and 2 are complete. The public transition API provides deterministic
  option-valued steps, terminality, halting, reflexive and positive
  reachability, backward uniqueness, and same-type `PEquiv` execution.
- The project convention is read, write, then move on a doubly infinite tape
  with a distinguished blank cell.
- The paper's printed sign-reversed quintuple is not an inverse configuration
  step under that convention when the head moves: inverse execution must move
  back before checking and restoring the overwritten cell.
- A finite machine description can be represented by a finite list of rules;
  determinism of the description and reversibility of its induced partial step
  are logically separate properties.
- `Nat.Partrec.Code.evaln` is an executable bounded evaluator and mathlib proves
  its completeness for `Code.eval`. It is therefore a checked source for a
  budget-search transition.
- Mathlib's established undecidable halting predicate uses
  `Nat.Partrec.Code`, while its partial-recursive-to-Turing-machine development
  uses a different `Turing.ToPartrec.Code`. No explicit computable compiler
  between these finite descriptions has been found in the pinned source.

## Updated Assumptions and Design Choices

- The tape alphabet has an explicit `default` blank. Each half-tape is stored
  as either all-blank or a nearest-first prefix ending structurally in a
  subtype-certified nonblank cell, so trailing blanks cannot have multiple
  representations. Taking the alphabet to be `Option Γ` recovers `none` as a
  canonical blank when the payload type has no chosen blank.
- The tape stores the current cell and two canonical half-tapes, nearest cell
  first. Left and right moves are exact inverses; stationary movement is the
  identity.
- A rule records source state, read symbol, target state, written symbol, and
  movement. Its forward semantics checks source/read, writes, then moves.
- A rule's semantic inverse checks target, moves in the opposite direction,
  checks the written symbol, restores the read symbol, and returns to the
  source state. This phased operation, not the printed tuple alone, is the
  local inverse theorem.
- Machine execution selects the first applicable rule. A syntactic table
  predicate rules out conflicting rules with the same source/read key.
  Reverse determinism is stated separately as uniqueness of successful
  predecessors (equivalently, compatibility of inverse rule applications).
- The source bridge for this stage is an explicit `evaln` budget-search partial
  transition with a halting iff theorem and computability proof. Compiling that
  source into the finite tape-machine syntax is deferred unless a checked
  compiler can be completed in this stage; otherwise the exact obstruction and
  the replacement source model are recorded, as allowed by the stage plan.

## Big Picture Objective

Define a finite deterministic Turing-machine model with executable
read-write-move semantics, prove the exact phased inverse law for individual
rules and the global condition for reversible execution, and expose a checked
effective halting source for the history simulation.

## Detailed Implementation Plan

- Add `Lecerf.Machine.Tape` with canonical half-tapes, read/write operations,
  left/stay/right movement, inverse-move laws, and executable examples.
- Add `Lecerf.Machine.Core` with configurations, finite rules and machines,
  applicability, first-match execution, halting, and table determinism.
- Add `Lecerf.Machine.Reversible` with the repaired move-back/restore inverse,
  exact local forward/reverse iff, reverse-machine execution, global forward
  and reverse compatibility predicates, and a `PEquiv` for machines satisfying
  both predicates.
- Add `Lecerf.Machine.SourceBridge` with the `Nat.Partrec.Code.evaln` search
  process, a joint computability theorem, and a halting iff theorem.
- Add non-public `Lecerf.Machine.Audit` with concrete step tests and a checked
  moving-rule counterexample to the paper's printed inverse order.
- Add a thin `Lecerf.Machine.API`, update the public root, and fold only stable
  declarations into the public surface.

## Build Structure

- `formal/Lecerf/Machine/Tape.lean`: canonical runtime tape representation and
  elementary laws.
- `formal/Lecerf/Machine/Core.lean`: low-dependency finite rule/machine syntax
  and executable forward semantics.
- `formal/Lecerf/Machine/Reversible.lean`: local and global inverse proofs.
- `formal/Lecerf/Machine/SourceBridge.lean`: computability-source construction
  and semantic theorem; isolated because it imports partial-recursive code.
- `formal/Lecerf/Machine/Audit.lean`: diagnostics and counterexamples; never
  imported by the public API.
- `formal/Lecerf/Machine/API.lean`: stable re-exports.
- Focused builds target each new leaf; adjacent builds target the API and root.
  A full build is required after changing the public umbrella import.

## No-Cheating and Boundary Checks

- Canonicality must be enforced by the tape type or constructors, not asserted
  as an unproved well-formedness invariant.
- Rule execution must visibly implement read-write-move. The inverse theorem
  must visibly implement inverse-move/check-written/restore-read.
- The printed tuple inverse may be named only as audit syntax; it cannot be the
  semantic inverse of a moving rule without an independently proved phase
  theorem.
- First-match functionality alone is not called machine-table determinism.
  Syntactic forward determinism and semantic backward uniqueness receive
  distinct definitions.
- A collection of locally invertible rules is not called a reversible machine
  unless their domains and ranges are globally compatible.
- The source theorem must use a concrete computable transition and an exact
  halting iff. An existential machine code or a non-effective semantic
  simulation is not accepted as a compiler.
- No history-recording simulator, coupling gadget, undecidability conclusion,
  word-code encoding, or iterate theorem belongs in this stage.
- No `sorry`, `admit`, proof-bypassing `unsafe`, or project axiom is permitted.

## Completion Requirements

- Canonical tape operations and the configuration-step equation are executable
  and covered by focused examples.
- The exact local rule inverse law compiles with movement order explicit.
- Machine-table determinism and backward uniqueness are separate, with a
  theorem constructing a reversible partial step from the stated conditions.
- The `evaln` source transition is computable and halts exactly when the source
  code is defined at the chosen input, or any failure is reduced to a checked
  obstruction with a precise replacement theorem.
- Focused, adjacent, and full builds pass. Proof-hole/shortcut scans,
  representative `#print axioms` checks, trailing-whitespace checks, and
  `git diff --check` pass.
- Results are folded into `0-plan.md`, `DEPENDENCIES.md`, `THEOREM-OUTLINE.md`,
  `AUDIT.md`, and `PAPER-MAP.md`. Stage 4 is not started.

## Stage Results

In progress.
