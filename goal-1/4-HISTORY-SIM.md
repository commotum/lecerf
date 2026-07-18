# 4-HISTORY-SIM

## Current Facts

- Stages 1--3 are complete. The stable transition API supplies deterministic
  option-valued steps, terminality, halting, reflexive and positive
  reachability, backward uniqueness, and same-type `PEquiv` execution.
- The finite machine layer separates first-match execution, table
  determinism, local rule inversion, and semantic whole-machine
  reversibility. It does not yet provide an effective compiler from
  `Nat.Partrec.Code` to a finite tape-machine table.
- `Lecerf.Machine.SourceBridge` supplies the fixed primitive-recursive
  transition `Source.universalEvalSearchStep`, a primitive-recursive start
  map, and an exact halting equivalence with `Nat.Partrec.Code.eval`.
- The paper sketches a history tape but omits a complete construction and has
  inconsistent displayed initial-history contents. The project permits a
  cleaner equivalent history simulation before connecting it to Lecerf's
  marker-level presentation.
- Recording each complete predecessor configuration is sufficient to make an
  arbitrary deterministic partial step reversibly executable. It is less
  space-efficient than recording only erased local data, but it isolates the
  correctness theorem from a later tape encoding.

## Updated Assumptions

- The abstract simulator state will contain the current source state and a
  newest-first list of prior source states. Its forward step pushes the
  current state exactly when the source takes a successful step.
- The inverse step pops a prior state only after re-executing the source step
  and checking that it produces the recorded current state. This validation
  is essential: an unconditional pop would accept malformed histories and
  would not be the partial inverse on the ambient simulator state space.
- The history invariant will be inductive from the chosen initial source
  state. It will be proved equivalent to simulator reachability, rather than
  assumed as a precondition of the main theorems.
- A simulator checkpoint is every history configuration in this abstract
  construction; one source step is one positive simulator step. Later
  microstate or tape encodings may refine a source step to several simulator
  steps without changing this semantic theorem.
- Effectivity will be stated uniformly for a computable source interpreter
  and instantiated for the checked universal search source. Whether the
  existing `FiniteMachine.step` interpreter can be proved uniformly
  computable within this stage is a checked implementation question. No
  finite-description compiler will be claimed without an explicit Lean
  construction and computability proof.
- "Checkpoint uniqueness" means injective encode/decode and exact
  characterization of reachable well-formed checkpoints. It does not mean a
  source state has a unique history: cycles can revisit a state with different
  valid histories.

## Big Picture Objective

Construct and verify a reusable reversible history simulator for arbitrary
deterministic partial transitions. Prove exact initialization, preservation,
forward simulation, reflection, history growth, and halting equivalence, and
show that the construction preserves effective execution for the checked
universal source. Do not begin coupling or any undecidability reduction.

## Detailed Implementation Plan

- Add a low-dependency history core with simulator configurations,
  encode/decode equivalence, initial configurations, executable forward and
  checked inverse steps, the exact one-step inverse law, and a bundled
  `ReversibleStep`.
- Define an inductive valid-history predicate generated from the initial
  source state. Prove initialization and preservation directly from the
  executable forward step.
- Add a correctness leaf proving that reachable simulator states are exactly
  the valid histories, that projecting a valid history reflects source
  reachability, and that every source run lifts to a simulator run.
- Prove a one-source-step/one-positive-simulator-step theorem, history-length
  growth, terminality correspondence, and source/simulator halting
  equivalence in both directions.
- Add an effectivity leaf with uniform computability theorems for forward and
  inverse execution under a computable source interpreter. Instantiate it for
  `Source.universalEvalSearchStep` and its computable start map.
- Add a non-public audit leaf with finite executable examples, including a
  malformed history rejected by the inverse and a cyclic source exhibiting
  multiple valid histories for the same current state.
- Add a thin history API and expose it from `Lecerf.Machine.API` only after
  focused builds and proof scans pass.

## Build Structure

- `formal/Lecerf/Machine/History/Core.lean`: runtime representation,
  encode/decode, forward/inverse execution, local inverse law, reversible
  bundle, and invariant definition.
- `formal/Lecerf/Machine/History/Correctness.lean`: reachability,
  simulation/reflection, growth, terminality, and halting proofs.
- `formal/Lecerf/Machine/History/Computable.lean`: computability-preservation
  results and the universal-source specialization.
- `formal/Lecerf/Machine/History/Audit.lean`: executable diagnostics and
  negative examples; excluded from public imports.
- `formal/Lecerf/Machine/History/API.lean`: stable Stage 4 exports.
- `formal/Lecerf/Machine/API.lean` and `formal/Lecerf.lean`: high-fanout
  surfaces changed only after the history leaves validate.
- Focused builds will target each new module. Adjacent builds will target the
  history API, machine API, and root. A full build is required after the
  public umbrella changes.

## No-Cheating Checks

- The inverse must recompute and validate the popped predecessor's forward
  image. A bare list pop is forbidden on malformed ambient states.
- The simulator must use only current source execution and stored history; it
  may not inspect a future trace, a halting witness, or `StateTransition.eval`
  as runtime data.
- The main correctness theorem must derive the invariant from reachability and
  construct reachability from the invariant. Merely restricting the theorem
  to an assumed invariant is insufficient.
- Halting equivalence must prove both preservation and reflection through
  terminal reachable states. It may not follow from an unproved simulation
  relation.
- Reversibility is an exact `PEquiv` law on all simulator configurations, not
  just locally invertible pushes on valid histories.
- A successful one-step simulation is positive reachability; zero-step
  reachability is not used to discharge it.
- Effectivity claims must name their computability hypotheses and checked
  instances. No existential compiler or `noncomputable` definition is called
  an effective construction.
- No coupling phase, return gadget, undecidability theorem, word encoding, or
  iterate equation belongs in this stage.
- No `sorry`, `admit`, proof-bypassing `unsafe`, unexplained project axiom, or
  explicit `Classical.choice` is permitted in project Stage 4 Lean sources.

## Boundary Checks

- Runtime declarations are confined to `History.Core`; semantic proof layers
  cannot become hidden runtime dependencies.
- Computability assumptions and source specializations are isolated in
  `History.Computable` so the generic simulator remains independent of
  partial-recursive code.
- Diagnostics remain in `History.Audit` and are not imported by either API.
- The abstract full-configuration log is explicitly not presented as the
  paper's tape-marker construction or as an ordinary finite Turing-machine
  compilation.
- Scan new Lean sources for `eval`, `Classical.choice`, `noncomputable`,
  `sorry`, `admit`, `axiom`, and `unsafe`; classify any semantic use of
  `StateTransition.eval` in proof-only imported APIs.
- Inspect public import edges to ensure `History.Audit` and future coupling or
  undecidability modules are absent.

## Completion Requirements

- Encode/decode round trips and injectivity compile.
- Forward and checked inverse execution satisfy an exact iff and produce a
  `ReversibleStep`, establishing deterministic execution and semantic
  backward uniqueness on the whole ambient state space.
- The valid-history predicate is initialized and preserved; it is equivalent
  to reachability from the encoded initial state.
- Forward single-step simulation, source reachability lifting, source
  reachability reflection, exact reachable-checkpoint characterization,
  one-step history growth, terminality correspondence, and halting equivalence
  compile.
- Uniform computability preservation compiles under explicit hypotheses, and
  the checked universal source has an effective history simulator and start
  map. Any remaining finite-machine-description gap is documented precisely
  and is not silently treated as closed.
- Focused and adjacent builds, a full build after API changes, proof-hole and
  boundary scans, representative `#print axioms`, trailing-whitespace checks,
  and `git diff --check` pass.
- Results are folded into `0-plan.md`, `DEPENDENCIES.md`,
  `THEOREM-OUTLINE.md`, `AUDIT.md`, and `PAPER-MAP.md`. Stage 5 is not started.

## Stage Results

- In progress.
