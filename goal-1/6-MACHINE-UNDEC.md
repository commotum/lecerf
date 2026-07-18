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
- `Compiler.UniversalSource` isolates one classically selected closed
  universal `ToPartrec.Code`. `Compiler.FiniteSource` lowers it through
  mathlib's checked TM2-to-TM1-to-TM0 simulations, restricts the result to its
  proved finite support, and compiles an actual fixed one-tape
  `FiniteMachine`. `FiniteSource.halts_iff_eval_dom` preserves and reflects
  source halting, while `FiniteSourceComputable.initial_primrec` proves that
  the varying program/input tape map is primitive recursive.
- `Machine.Validity` and `Machine.TwoTape.Validity` package decidable,
  primitive-recursive pairwise certificates implying semantic
  whole-machine reversibility. They are sufficient subclasses; no false
  converse to semantic reversibility is asserted.
- `Machine.TwoTape.Core`, `Reversible`, and `Effectivity` define a conventional
  finite two-tape table model, exact inverse execution, whole-machine
  reversibility, primitive-recursive table execution, and primitive-recursive
  validity checking.
- `Machine.TwoTape.HistoryCompiler` now has finite runtime syntax, membership
  facts, normalized concrete rule traces, effectivity of varying endpoint
  maps, executable microstep equations, and checked global reversibility for
  the forward-history, open-turnaround, and closed-return tables. The reverse
  macro is `scan-left; inspect-and-move-work-back; restore-and-erase-staying`;
  only the final bottom rule moves the history head right.
- The original sketch saying that token restoration moves the history head
  right was corrected: doing so revisits the erased cell on the next scan and
  prematurely stops multi-step retracing. `restoreRule.move₂ = .stay` is the
  checked construction.
- `Undecidability.ReversibleTwoTape.Problems` defines validity-guarded raw
  halting, positive-return, and distinct-target strict-reachability predicates
  over fixed finite target types. The generic table enumeration uses
  `Finset.toList` through fixed `Fintype` data and is deliberately not claimed
  as a varying primitive-recursive compiler; the intended reduction uses one
  fixed closed target table and primitive-recursive start/target maps.
- `HistoryCompiler.Correctness` proves the generated-run invariant and the
  three concrete semantic equivalences:
  `historyMachine_haltsFrom_iff_source`,
  `turnaround_bottom_strictlyReachable_iff_source_halts`, and
  `return_positiveReturn_iff_source_halts`.
- `Compiler.ReversibleUniversal` instantiates the compiler at the fixed finite
  source. Its three closed target tables are syntactically certified and
  semantically reversible; its varying source/checkpoint/target maps are
  primitive recursive; and its three `eval.Dom` iff theorems connect the
  concrete machines directly to mathlib's source predicate.
- `Undecidability.ReversibleTwoTape.Reduction` defines three explicit
  primitive-recursive compilation maps, proves that every output is certified
  reversible (and that reachability endpoints differ), packages three
  `ManyOneReducible` witnesses, and derives three noncomputability theorems from
  `ComputablePred.halting_problem 0`.
- Primitive-recursive abstract interpreters are not finite-machine output
  compilers. The Stage-6 result instead uses the separate checked finite
  two-tape compiler and does not rename the Stage-4/5 semantic theorems.

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
- The selected route is a fixed universal finite one-tape source whose start
  tape encodes the source program, followed by fixed finite two-tape history
  and coupling tables. The machine component of every reduction output is a
  closed constant; only configurations vary, and those maps must be proved
  primitive recursive with both semantic directions.
- A cleaner finite reversible compiler replaces Lecerf's incomplete marker
  scheme at this stage. It is explicitly a two-tape theorem, not a claim about
  the existing one-tape `FiniteMachine`; a later two-to-one lowering remains a
  separate design choice. Classical choice selects only a fixed universal
  program and fixed finite encodings and must remain isolated in the audit.

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
- `formal/Lecerf/Machine/Compiler/{UniversalSource,Table,TapeBridge,
  FiniteSource,FiniteSourceComputable}.lean`: isolate the fixed universal
  program, lower it through checked mathlib TM simulations, restrict to finite
  support, and prove the varying input/start map primitive recursive.
- `formal/Lecerf/Machine/TwoTape/{Core,Reversible,Effectivity,Validity}.lean`:
  conventional finite two-tape execution, exact inverse semantics, uniform
  primitive-recursive execution, and the checked sufficient reversibility
  certificate.
- `formal/Lecerf/Machine/TwoTape/HistoryCompiler/{Core,Basic,Trace,Runtime,
  Reversible,Correctness,Effectivity}.lean`: finite compiler syntax and table
  membership, normalized traces, executable microsteps, table reversibility,
  preservation/reflection, and primitive-recursive endpoint maps.
- `formal/Lecerf/Machine/Compiler/ReversibleUniversal.lean`: the three fixed
  certified target tables and the exact universal semantic iff theorems.
- `formal/Lecerf/Undecidability/ReversibleTwoTape/{Problems,Reduction,API}.lean`:
  guarded raw predicates, explicit finite reductions/noncomputability results,
  and stable exports.
- `formal/Lecerf/Undecidability/ReversibleTwoTape/Audit.lean`: executable valid
  and invalid certificate examples plus headline `#print axioms`; this leaf is
  not publicly imported.
- `formal/Lecerf/Undecidability/API.lean` and `formal/Lecerf.lean`: thin public
  exports of the checked results.

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
  `Primcodable` support at the varying boundary and a decidable/computable
  validity predicate implying whole-machine reversibility. The fixed finite
  alphabet encodings selected once for the universal tables are explicitly
  noncomputable constants; no varying reduction map depends on an unproved
  computable selection.
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

- Complete. The project now has a genuine finite two-tape local-rule result,
  not only an abstract effective-transition checkpoint.
- The fixed source compiler preserves and reflects
  `(Nat.Partrec.Code.eval code 0).Dom`; the finite history compiler separately
  preserves and reflects halting, realizes distinct-target strict reachability
  after turnaround, and realizes positive return after bottom closure.
- `partrecHalts0_manyOne_haltingYes`,
  `partrecHalts0_manyOne_returnYes`, and
  `partrecHalts0_manyOne_reachabilityYes` are explicit computable reductions.
  `haltingYes_not_computable`, `returnYes_not_computable`, and
  `reachabilityYes_not_computable` derive solely from mathlib's pinned halting
  theorem.
- Every generated table satisfies `SyntacticallyReversible`, hence semantic
  `Reversible`; the reachability reduction proves its endpoints unequal. Raw
  predicates include the validity guard, so malformed descriptions cannot
  create a reduction loophole.
- A construction error in the provisional reverse macro was corrected:
  restoration erases the newest history token while staying on that cell;
  only the bottom transition moves right. This prevents premature termination
  during multi-token retracing.
- Focused reduction build: 876 jobs completed. Public API/root plus audit build:
  894 jobs completed. Final full `lake build`: 893 jobs completed. Proof-hole,
  project-axiom, `unsafe`, boundary, and whitespace scans passed, as did
  `git diff --check`.
- Representative correctness, reduction, and noncomputability declarations
  report exactly `[propext, Classical.choice, Quot.sound]`. `Classical.choice`
  is accounted for by the one-time selected universal program, finite support,
  encodings, and enumeration order; there is no project-specific axiom.
- Scope boundary: these final undecidability theorems concern the checked finite
  **two-tape** target model. A two-to-one-tape lowering and a literal connection
  to Lecerf's incomplete historical marker encoding remain follow-up work.
- Results were folded into the authoritative planning, dependency, theorem,
  audit, and paper-map documents. Stage 7 was not started.
