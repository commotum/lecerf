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
- Stage 3 accepts this atomic semantic phase decomposition as the cleaner
  equivalent theorem allowed by the project objective. Generating an ordinary
  finite rule table with explicit micro-control states is recorded separately
  and is not part of the current public claim.
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

- Added `Lecerf.Machine.Tape`. `Side Γ` is either all blank or a finite
  nearest-first prefix ending in a subtype-certified nonblank symbol, so
  structural equality is canonical modulo trailing blanks. `Tape Γ` stores
  head/left/right, supports write-then-move execution, and proves exact
  left/right and reverse-direction laws plus `Tape.undo_act`.
- Added constructive `Primcodable` instances for nonblank symbols, movements,
  tapes, configurations, rules, and finite machines. `Option Γ` may be used as
  an alphabet when `none` should be the distinguished blank.
- Added `Lecerf.Machine.Core` with `Config`, five-field `Rule`,
  `FiniteMachine`, deterministic first-match lookup, first-success execution,
  `HaltsAt`, `TableDeterministic`, and `WellFormed`. The executable step is
  proved equal to lookup followed by the stated read-write-move update.
- Added `Lecerf.Machine.Reversible`. `Tape.checkedWrite` and
  `Tape.moveEquiv` expose the two reversible phases, and `Rule.tapeAction` is
  their `PEquiv.trans`. `Rule.undo` executes move-back/check-written/
  restore-read; `Rule.apply_eq_some_iff_undo_eq_some` proves the exact local
  inverse law and `Rule.toPEquiv` bundles it.
- Whole-table execution keeps three notions separate:
  `TableDeterministic`, `ForwardCompatible`, and `BackwardCompatible`.
  Table determinism implies forward compatibility. Pairwise common-direction/
  distinct-write incoming rules imply backward compatibility. First-match
  `step` and `reverseStep` satisfy an exact iff under both compatibility
  predicates. For a deterministic table,
  `backwardCompatible_iff_backwardUnique` is an exact semantic
  characterization, and `FiniteMachine.toPEquiv` packages a machine satisfying
  `Reversible := TableDeterministic ∧ BackwardUnique step`.
- The implemented phase compilation is semantic: `Rule.tapeAction` is a
  composition of tape `PEquiv`s, and `reverseStep` performs move-back/check/
  restore as one executable macro-step. It is not yet a generated
  `FiniteMachine` with explicit `normal`/`move` micro-control states. This is
  the cleaner equivalent theorem permitted by the project objective; a
  finite-alphabet syntactic phase compiler remains a later connection to
  Lecerf's presentation and must not be inferred from the current API.
  A compiling diagnostic prototype confirmed the expected `normal`/`move`
  rule families and table-determinism proof, but `Fintype Γ` enumeration via
  `Finset.univ.toList` is explicitly noncomputable and the two-step theorem was
  not completed. An effective version should accept a complete symbol list or
  use a concrete `Fin n` alphabet.
  `lake env lean /tmp/PhasePrototype.lean` passed with only unused-section-
  variable linter warnings; the prototype is not imported project code.
- `ReverseTableCompatible` is proved sufficient for backward compatibility.
  The exact theorem currently available is semantic
  `backwardCompatible_iff_backwardUnique`; the converse characterization by a
  finite pairwise rule predicate, and hence an executable reversibility
  validity test, remains a Stage-6 obligation.
- Added non-public `Lecerf.Machine.Audit`. Executable examples check blank
  normalization, a moving rule's forward and repaired inverse steps, and the
  concrete failure of the paper's printed inverse tuple. A two-rule merge
  table is proved forward-table-deterministic but not globally reversible,
  although each rule has its own `PEquiv`.
- Added `Lecerf.Machine.SourceBridge`. The fixed transition
  `universalEvalSearchStep` carries a `Nat.Partrec.Code` and input in its state;
  `universalEvalSearchStep_halts_iff_eval_dom` proves exact halting equivalence.
  The transition and joint program/input source-to-start map have checked
  `Primrec` theorems.
- The finite compiler requested as the preferred bridge is not claimed.
  Checked pinned-source obstruction: `Turing.ToPartrec.Code.exists_code`
  returns only an existential code; `PartrecToTM2.tr_supports` proves finite
  support but does not extract a project rule table; and TM2-to-TM1 and
  TM1-to-TM0 `trSupp` definitions are explicitly `noncomputable`. The fixed
  primitive-recursive search transition is the stage's permitted replacement
  source. Closing the compiler/reduction arrow remains a Stage-6 obligation.
- Added thin `Lecerf.Machine.API` and updated `Lecerf.lean`; the audit leaf is
  not publicly imported.
- Focused builds passed for Tape (794 jobs), Core (819), Reversible (822),
  SourceBridge (821), and Audit (823). The API/root adjacent build passed, and
  full `lake build` passed with 830 jobs.
- A temporary root-import probe checked the principal public signatures and
  was deleted. Representative `#print axioms` results were:
  - `Tape.undo_act` and the local rule inverse iff: `propext`;
  - global step/reverse-step iff: `propext`;
  - backward-compatibility characterization: `propext`, `Quot.sound`;
  - universal search halting iff and its `Primrec` theorem: `propext`,
    `Classical.choice`, `Quot.sound` inherited from mathlib encodings and
    `Part`/transition semantics.
  No project-specific axiom was introduced.
- Lean scans found no `sorry`, `admit`, `axiom`, `unsafe`, `noncomputable`, or
  explicit `Classical.choice` in project machine sources. Import and boundary
  scans found no history simulator, reduction conclusion, word-code layer, or
  iterate API. Trailing-whitespace checks and `git diff --check` passed.
- Stage 3 is complete. Stage 4 was not started.
