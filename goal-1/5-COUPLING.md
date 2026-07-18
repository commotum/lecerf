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
  its forward direction may already contain cycles. It will be proved for the
  history lift using strict growth of the stored log.
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
- Prove the positive-run classification described above for both open and
  closed coupling forward behavior. Derive exact iff theorems for source
  halting versus distinct reverse-initial reachability and positive return.
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
- Reflection must rule out a forward-only positive cycle. For the history lift
  this must follow from checked log growth, not an assumed acyclicity axiom.
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
- Scan Stage 5 Lean sources for `eval`, `sorry`, `admit`, `axiom`, `unsafe`,
  `noncomputable`, `Classical.choice`, `ManyOne`, `Undecidable`, `FreeMonoid`,
  and iterate/code declarations. Classify proof-only imported `HaltsFrom`
  semantics separately from runtime dependencies.

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

- In progress.
