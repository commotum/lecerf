# 6-MACHINE-UNDEC

## Current Facts

- Stages 1--5 are complete. The public transition layer distinguishes
  reflexive reachability, strict reachability, halting, and positive return,
  and represents a reversible step by an exact `PEquiv`.
- `History.reversible Source.universalEvalSearchStep` is a fixed reversible
  partial transition. Its primitive-recursive start map sends a
  `Nat.Partrec.Code` and input to a fresh history checkpoint, and
  `History.universalHistory_halts_iff_eval_dom` proves halting preservation and
  reflection.
- The fixed open and closed couplings have primitive-recursive step and
  endpoint maps. `Coupling.History.universalTarget_strictlyReachable_iff_eval_dom`
  and `universalPositiveReturn_iff_eval_dom` give exact semantic iff theorems.
- Mathlib proves `ComputablePred.halting_problem 0` for
  `Nat.Partrec.Code`. `ManyOneReducible` requires a computable witness and an
  iff for every source input; `ComputablePred.computable_of_manyOneReducible`
  transfers a hypothetical target decision procedure back to the source.
- `FiniteMachine` is a finite ordered table of conventional read-write-move
  rules over canonical finite-support tapes. `FiniteMachine.Reversible`
  separates table determinism from semantic predecessor uniqueness.
  `ReverseTableCompatible` is an executable-looking pairwise sufficient
  condition for backward compatibility, but no packaged decidable raw
  validity predicate is yet public.
- Four finite-construction gaps remain. There is no checked compiler from
  `Nat.Partrec.Code` to a finite source rule table (`A-018`), no ordinary
  phase-rule compiler for semantic macro rules (`A-023`), no finalized
  decidable finite validity interface (`A-024`), and no compiler from the
  abstract unbounded history list to a conventional finite tape machine
  (`A-025`).
- Primitive-recursive abstract interpreters are not finite-machine output
  compilers. Stage 6 cannot be completed merely by renaming the Stage-4/5
  semantic iff theorems as Turing-machine reductions.

## Updated Assumptions

- First package the already checked universal history/coupling constructions
  as genuine many-one reductions to three fixed reversible *effective
  transition-system* predicates. This validates the reduction layer and is a
  reusable intermediate theorem, but it is not the finite Turing-machine
  result and cannot complete the stage.
- Raw finite-machine decision inputs should use one fixed `Primcodable`
  description type. Malformed descriptions are false, while every reduction
  output must carry or prove the chosen finite syntactic validity condition.
- A decidable sufficient subclass of reversible finite tables is acceptable
  if it is explicitly named, proves `FiniteMachine.Reversible`, and all
  reduction outputs belong to it. It must not be presented as an iff
  characterization of every semantically reversible table unless the converse
  is proved.
- The finite source/history/coupling bridge may use a fixed universal machine
  whose start tape encodes the source program, or a computable per-program
  compiler. Either route must yield an actual finite local rule table and an
  executable configuration encoding with both halting directions.
- A cleaner finite reversible compiler may replace Lecerf's incomplete marker
  scheme. Any use of classical choice to select a fixed universal program must
  be isolated, axiom-audited, and must not hide a noncomputable varying output
  map.

## Big Picture Objective

Define finite, validity-checked decision problems for reversible-machine
halting, positive return, and strict reachability of a distinct target.
Construct explicit computable reductions from mathlib's established halting
problem, prove preservation and reflection for all three targets, and derive
their noncomputability without assuming a project-specific undecidability
axiom.

## Detailed Implementation Plan

1. Add a low-dependency effective-transition reduction leaf. Define the three
   fixed universal predicates, computable source maps, exact many-one
   reductions, and noncomputability corollaries from
   `ComputablePred.halting_problem 0`.
2. Add a finite validity leaf. Package a decidable rule-table condition,
   connect it to `FiniteMachine.Reversible`, validate configuration bounds if
   the raw format uses numeric labels, and prove all checks computable.
3. Resolve the finite source bridge. Either construct a fixed universal local
   Turing machine with a computable program/input tape encoding, or define and
   verify a computable compiler from `Nat.Partrec.Code` to source rule tables.
4. Compile history recording and the open/closed couplings into finite local
   rules. Prove encode/decode and generated-configuration invariants, finite
   macro-run preservation and reflection, reversibility/validity of every
   output, and computability of the compiler and endpoints.
5. Define raw halting, return, and reachability input structures and
   predicates. Assemble the three finite-machine `ManyOneReducible` theorems
   and derive noncomputability with exact quantifiers.
6. Add executable positive/negative audits and `#print axioms` checks. Expose
   only stable theorem leaves through a thin API after focused and full builds
   pass.

## Build Structure

- `formal/Lecerf/Undecidability/EffectiveTransition.lean`: fixed abstract
  reversible-transition predicates, many-one reductions, and noncomputability;
  this imports the history/coupling computability leaves and mathlib reduction
  API, but no finite compiler.
- `formal/Lecerf/Machine/Validity.lean`: finite syntactic validity and
  decidability/computability facts; it depends only on concrete machine
  semantics/effectivity.
- `formal/Lecerf/Machine/Compiler/`: finite source and reversible-history
  compiler modules, split into runtime, correctness, and computability leaves
  once the checked design fixes their dependency boundary.
- `formal/Lecerf/Undecidability/ReversibleMachine.lean`: final raw input
  predicates, finite reduction witnesses, and noncomputability theorems.
- `formal/Lecerf/Undecidability/Audit.lean`: executable examples and axiom
  audit; never publicly imported.
- `formal/Lecerf/Undecidability/API.lean`: thin stable exports after the finite
  reductions compile.
- Initial focused build:
  `cd formal && lake build Lecerf.Undecidability.EffectiveTransition`.
  Each compiler leaf gets its own narrow build; API changes require adjacent
  root builds and a final full `lake build`.

## No-Cheating Checks

- Do not treat primitive-recursive interpretation of an abstract history list
  as generation of a finite local Turing-machine table.
- Do not define a target predicate that omits validity or accepts malformed
  descriptions in a way used by the reduction.
- Do not claim finite-machine reversibility from individually invertible rules
  or table determinism alone. Every compiled table must satisfy the checked
  global/syntactic condition implying `BackwardUnique`.
- Halting, return, and reachability require separate target predicates and
  reduction iff theorems. The total closed return gadget is not a halting
  machine.
- Positive return uses `PositiveReturn`; specified-target reachability uses
  `StrictlyReachable` and includes a proved start/target inequality.
- Every reduction witness must be `Computable`; theorem-level existence of a
  simulator or compiler is insufficient.
- A fixed universal machine is permitted only when the varying program/input
  encoding and start map are computable and the fixed finite table is exposed
  rather than replaced by an oracle transition.
- No `sorry`, `admit`, proof-bypassing `unsafe`, unexplained project axiom,
  fabricated compiler theorem, or hidden `noncomputable` varying reduction
  map is permitted.

## Boundary Checks

- Effective-transition reductions are explicitly named as abstract and are
  kept separate from conventional finite-machine predicates.
- Finite compiler runtime definitions cannot inspect halting witnesses,
  future traces, `StateTransition.eval`, or the truth of the source predicate.
- Proof-side simulation relations and invariants live above executable rule
  generation; diagnostic code remains outside public APIs.
- Scan final Stage-6 Lean sources for proof holes, project axioms, `unsafe`,
  unclassified `noncomputable`, zero-step return, missing validity conjuncts,
  and accidental imports of audit leaves.
- Inspect every final theorem signature to ensure the source predicate is
  `(Nat.Partrec.Code.eval code 0).Dom` and the target quantifiers match the
  raw finite-machine decision problem.

## Completion Requirements

- Three fixed effective-transition many-one reductions and their
  noncomputability corollaries compile as an intermediate checkpoint.
- A raw finite-machine description/input type has constructive
  `Primcodable` support and a decidable/computable validity predicate implying
  whole-machine reversibility.
- The source-to-finite-machine and finite reversible history/coupling
  construction is executable and computable on every source code.
- Configuration encoding/decoding, generated-run invariants, local macro-step
  simulation, preservation, reflection, halting equivalence, positive return
  equivalence, and distinct-target reachability equivalence all compile.
- Three explicit finite-machine `ManyOneReducible` theorems compile, followed
  by noncomputability theorems derived from the pinned mathlib halting theorem.
- Reduction outputs are valid reversible machines; malformed target inputs do
  not create a preservation/reflection loophole.
- Focused compiler/reduction builds, adjacent public builds, a full build,
  proof-hole and boundary scans, representative axiom audits, whitespace
  checks, and `git diff --check` pass.
- Results are folded into `0-plan.md`, `DEPENDENCIES.md`,
  `THEOREM-OUTLINE.md`, `AUDIT.md`, and `PAPER-MAP.md`. Stage 7 is not started.

## Stage Results

- In progress.
