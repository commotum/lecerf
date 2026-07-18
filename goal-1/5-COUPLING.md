# 5-COUPLING

## Current Facts

- Stages 1--4 are complete. `Transition` distinguishes reflexive reachability,
  positive reachability, terminality, halting, and positive return.
- `History.reversible next` is an exact `PEquiv` whose forward direction pushes
  a complete predecessor and whose reverse direction checks and pops it.
- `History.reachable_iff_valid`, `Valid.backward_reachable_initial`, and
  `haltsFrom_forward_iff` give exact generated-history reflection, reverse
  retracing, and source/history halting equivalence.
- Every successful history-forward step increases the log length. A cyclic
  source may revisit a source state, but the history-forward simulator cannot
  positively return to the same complete history configuration.
- The paper's §2 coupling runs forward until a halting state-symbol pair,
  switches to starred control, and traverses image configurations backward.
  §4a(6) identifies the starred initial configuration as reachable exactly on
  source halting. §4a(7) says return or an extra framed target can be arranged,
  but does not supply the complete gadget or both directions.
- Stage 4 proves a primitive-recursive abstract history interpreter jointly in
  an existing finite source description. It does not generate an ordinary
  finite tape machine; Stage 5 must preserve that boundary.

## Updated Assumptions

- A generic forward/reverse coupling can be defined for any
  `ReversibleStep σ` by tagging configurations as forward or reverse.
- The open turnaround coupling executes forward steps, switches from
  `forward state` to `reverse state` exactly when the forward direction is
  terminal, executes inverse steps, and remains terminal at a state with no
  inverse predecessor. This is itself a partial equivalence.
- The reverse-tagged initial history checkpoint is the clean analogue of the
  paper's starred initial configuration. It is structurally distinct from the
  forward-tagged start and is reached only after the terminal switch and
  inverse retracing.
- A return gadget closes each reverse-terminal boundary back to its matching
  forward-tagged state. Closing all such boundary components, rather than
  testing equality with one privileged start at runtime, gives a uniform total
  reversible transition. On the generated history orbit, the only relevant
  reverse-terminal checkpoint is the empty-history initial checkpoint.
- Positive return reflection cannot hold for an arbitrary reversible source:
  its forward direction may already contain cycles. For the history lift,
  checked log growth rules out a forward-only cycle, while the implemented
  headline reflection uses the stronger exact-predecessor fact at the closed
  return boundary.
- No-spurious reflection will classify every positive run from a forward-tagged
  initial history: until a forward-terminal switch occurs it corresponds to a
  positive history-forward path; once a switch occurs, history/source halting
  is already witnessed. This avoids assuming that a phase transition occurred.
- Effectivity will be stated for jointly primitive-recursive forward and
  inverse interpreters, then specialized to history simulators, existing
  finite source-machine descriptions, and the universal evaluator-search
  source. This remains interpreter effectivity, not a finite output compiler.

## Big Picture Objective

Formalize a reusable reversible forward/terminal-switch/reverse coupling and a
reversible return closure. Prove that the reverse-tagged initial checkpoint is
strictly reachable exactly when the source halts and that the closed coupling
has a positive return exactly when the source halts. Make target distinctness,
phase-boundary reversibility, no-spurious reflection, and effectivity explicit.
Do not begin any many-one reduction or undecidability conclusion.

## Detailed Implementation Plan

- Add a low-dependency coupling core with a two-valued direction, tagged
  configurations, constructive encodings, an open turnaround step and its
  exact inverse, and a closed return gadget and its exact inverse.
- Prove executable equations for internal forward/reverse moves, the
  forward-terminal turnaround, reverse-terminal stopping in the open
  coupling, and reverse-terminal return in the closed gadget.
- Add generic path-lifting lemmas: forward paths stay forward-tagged, inverse
  paths stay reverse-tagged, forward halting reaches the reverse-tagged start,
  and a reverse-terminal start completes a positive closed return.
- Specialize to `History.reversible next`. Prove strict history-length growth
  over every positive forward path and hence absence of a positive
  history-forward return.
- Prove a generated-state invariant for both open and closed coupling
  behavior. Derive exact iff theorems for source halting versus distinct
  reverse-initial reachability and positive return; use the closed boundary's
  unique predecessor to reflect a return to the forward start.
- Prove forward and reverse initial configurations are unequal by constructor
  discrimination; never rely on a user-supplied inequality assumption.
- Add uniform primitive-recursive coupling interpreters and specialize them to
  history simulators over arbitrary primitive-recursive descriptions,
  `FiniteMachine` descriptions, and the fixed universal search source.
- Add a non-public audit leaf with initially halting, one-step halting, and
  nonhalting source examples. Check turnaround order, target distinctness,
  positive return, and absence of false positive return/reachability.
- Add a thin coupling API and expose it from `Machine.API` only after focused
  correctness and effectivity builds pass.

## Build Structure

- `formal/Lecerf/Machine/Coupling/Core.lean`: direction/configuration runtime,
  open turnaround `PEquiv`, closed return `PEquiv`, and boundary equations.
- `formal/Lecerf/Machine/Coupling/Correctness.lean`: generic path lifting and
  history-specialized halting/reachability/return equivalences.
- `formal/Lecerf/Machine/Coupling/Computable.lean`: uniform primitive-recursive
  interpreters and finite/universal source specializations.
- `formal/Lecerf/Machine/Coupling/Audit.lean`: executable examples and negative
  tests; never publicly imported.
- `formal/Lecerf/Machine/Coupling/API.lean`: stable Stage 5 exports.
- `formal/Lecerf/Machine/API.lean` and `formal/Lecerf.lean`: public descriptions
  updated only after all new leaves validate.
- Focused builds target each new module. Adjacent builds target the coupling
  API, machine API, and root. A full build is required after public imports.

## No-Cheating Checks

- The terminal switch must inspect the executable forward step result. It may
  not inspect a halting witness, future trace, `StateTransition.eval`, or a
  precomputed terminal endpoint at runtime.
- Reverse execution must use the `PEquiv` inverse/history checked pop. It may
  not replay a stored future trace or blindly discard history.
- Phase-boundary edges must participate in the exact ambient inverse law. A
  forward/reverse operational story without a compiled `PEquiv` is
  insufficient.
- Specified-target reachability uses `StrictlyReachable` and a proved unequal
  reverse-tagged target. Positive return uses `PositiveReturn`; reflexive
  `Reachable.refl` cannot prove either result.
- Reflection must rule out a forward-only positive cycle from checked facts,
  not an assumed acyclicity axiom. `history_length_lt_of_strictlyReachable`
  and `not_positiveReturn_forward` certify this directly; the headline return
  iff additionally uses the stronger exact-predecessor theorem at the closed
  boundary.
- The halting, target-reachability, and return statements are semantic iff
  theorems. They are not yet called many-one reductions or undecidability
  results.
- Effectivity claims must name primitive-recursive interpreter hypotheses and
  must not call an abstract-state interpreter a conventional finite-machine
  compiler.
- No finite decision predicate, `ManyOneReducible`, undecidability conclusion,
  free-monoid/code layer, or iterate equation belongs in this stage.
- No `sorry`, `admit`, proof-bypassing `unsafe`, unexplained project axiom,
  `noncomputable`, or explicit `Classical.choice` is permitted in Stage 5 Lean
  sources.

## Boundary Checks

- Generic direction/configuration and `PEquiv` runtime live in `Coupling.Core`
  and do not import history, source code, or finite-machine syntax.
- History-specific proof obligations live in `Coupling.Correctness`; the core
  coupling is not falsely claimed to reflect halting for arbitrary cyclic
  reversible steps.
- Computability proofs and source specializations live in
  `Coupling.Computable`; runtime core declarations cannot depend on proof-side
  evaluation semantics.
- Diagnostics remain in `Coupling.Audit` and are absent from every API import.
- The reverse-tagged initial state is the implemented specified target. The
  paper's optional additional framed `u_st` construction remains a later
  historical refinement unless a distinct need arises.
- Scan Stage 5 Lean sources for `sorry`, `admit`, project `axiom`, `unsafe`,
  `noncomputable`, explicit `Classical.choice`, `ManyOne`, `Undecidable`,
  `FreeMonoid`, and iterate/code declarations. Classify the intentional
  universal-source `Nat.Partrec.Code.eval` semantic corollaries separately
  from runtime definitions, which do not inspect evaluation or halting
  witnesses.

## Completion Requirements

- Tagged configuration encode/decode and constructive `Primcodable` instances
  compile; forward and reverse tags are provably unequal.
- Open turnaround and closed return transitions each satisfy an exact ambient
  inverse iff and produce a `ReversibleStep`.
- Internal forward/reverse lifting, terminal switching, inverse retracing, and
  phase-boundary stopping/return are checked.
- Strict history-path growth and no positive history-forward return compile.
- Source halting iff strict reachability of the unequal reverse-initial target
  compiles in both directions.
- Source halting iff positive return of the closed coupling compiles in both
  directions.
- Uniform, finite-description, and universal-source primitive-recursive
  interpreter/start-map theorems compile, with the finite-output compiler gap
  documented rather than hidden.
- Focused and adjacent builds, a full build after API changes, proof-hole and
  boundary scans, representative `#print axioms`, trailing-whitespace checks,
  and `git diff --check` pass.
- Results are folded into `0-plan.md`, `DEPENDENCIES.md`,
  `THEOREM-OUTLINE.md`, `AUDIT.md`, and `PAPER-MAP.md`. Stage 6 is not started.

## Stage Results

- Complete on 2026-07-17. Added
  `Lecerf.Machine.Coupling.{Core,Correctness,Computable,Audit,API}` and exposed
  the stable API through `Lecerf.Machine.API` and `Lecerf`; the audit leaf is
  not publicly imported.
- `Direction` and `Config` provide constructive phase tags and encodings.
  `turnaroundNext`/`turnaroundPrev` implement the open coupling, and
  `returnNext`/`returnPrev` implement the uniformly closed return gadget. The
  exact ambient inverse laws
  `turnaroundNext_eq_some_iff_turnaroundPrev_eq_some` and
  `returnNext_eq_some_iff_returnPrev_eq_some` construct `turnaround` and
  `returnGadget` as `ReversibleStep`s. Eight executable boundary equations
  cover internal forward/reverse moves, turnaround, open stopping, and closed
  return.
- Generic path lifting proves that source halting reaches the reverse-tagged
  start in both gadgets. The history specialization defines `History.start`
  and the structurally distinct `History.target`, propagates `History.Generated`
  over reachable coupled states, and proves
  `History.target_strictlyReachable_iff_halts`, `History.terminal_target`, and
  `History.positiveReturn_iff_halts`. Return reflection follows from
  `History.return_prev_start` and `History.predecessor_of_start`; independent
  log-growth theorems exclude a positive forward-history cycle.
- Generic, history-specific, existing-`FiniteMachine`, and fixed universal
  coupling interpreters and endpoint maps are primitive recursive. In
  particular, `universalTarget_strictlyReachable_iff_eval_dom` and
  `universalPositiveReturn_iff_eval_dom` specialize the semantic equivalences
  to the checked evaluator-search source.
- These are abstract interpreter/effectivity results. They do not generate a
  conventional finite tape machine, define a finite validity predicate, state
  a `ManyOneReducible` result, or derive undecidability. The finite source
  compiler, history-list tape compiler, and exact decidable finite
  reversibility criterion remain Stage-6 dependencies under `A-018`, `A-023`,
  `A-024`, and `A-025`.
- Focused builds through `Coupling.Audit`, adjacent public API builds, and full
  `lake build` passed. The final full build completed 839 jobs. Source scans,
  import-boundary checks, whitespace checks, and `git diff --check` passed.
  Representative axiom output contains only `propext`, `Quot.sound`, and,
  where inherited transition/evaluation infrastructure requires it,
  `Classical.choice`; no project axiom or proof hole was introduced.
- Stage 6 has not been started.
