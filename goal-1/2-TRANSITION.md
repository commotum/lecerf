# 2-TRANSITION

## Current Facts

- Stage 1 fixed `StateTransition` for reachability/halting and same-type
  `PEquiv` for a generic reversible step.
- `StateTransition.Reaches` is reflexive-transitive closure;
  `StateTransition.Reaches₁` requires a nonempty run.
- `StateTransition.mem_eval` characterizes terminating evaluation by
  reachability of a terminal state.
- `PEquiv.eq_some_iff` gives the exact one-step inverse law, while
  `PEquiv.inj` gives uniqueness of successful preimages.
- Relation closure supplies `ReflTransGen.swap` and `TransGen.swap`, which can
  reverse paths without introducing a custom reachability relation.
- The current Lean project contains only `formal/Lecerf.lean`, a broad import
  smoke test. There are no project transition declarations or tests.
- The pinned baseline `lake build Lecerf` passed with 831 jobs at the end of
  Stage 1.

## Updated Assumptions

- `PEquiv σ σ` is sufficient for semantic reversible execution; a wrapper
  structure duplicating its inverse law would add no value at this layer.
- Project definitions should be thin named predicates over mathlib rather than
  aliases for every closure theorem.
- Option-valued execution is forward deterministic automatically, but
  predecessor uniqueness needs the `PEquiv` inverse law. Both facts should be
  exposed separately.
- Audit examples should demonstrate that reflexive reachability is not
  positive return and that an arbitrary deterministic `Step` need not admit a
  reversible inverse.
- Exact-length execution can remain a later addition unless a Stage-2 proof
  genuinely requires it; `Reaches`/`Reaches₁` cover this stage's consumers.

## Big Picture Objective

Build the low-dependency reusable API for deterministic partial execution,
terminality, halting, reachability, positive return, and semantic reversible
steps. Prove one-step and finite-path reversal from `PEquiv` and demonstrate
the critical distinctions with checked finite examples.

## Detailed Implementation Plan

- Add `Lecerf.Transition.Core` with `Step`, `Terminal`, `HaltsFrom`,
  `Reachable`, `StrictlyReachable`, and `PositiveReturn`, plus basic closure,
  forward-successor uniqueness, and halting characterization lemmas.
- Add `Lecerf.Transition.Reversible` with `ReversibleStep`, named `next` and
  `prev` projections, the exact inverse-step iff, predecessor uniqueness, and
  reversal iff theorems for both `Reachable` and `StrictlyReachable`.
- Add `Lecerf.Transition.Audit` with finite examples showing zero-step versus
  positive reachability, a nontrivial reversible path, and a deterministic
  merging step that cannot have a partial inverse.
- Add thin `Lecerf.Transition.API` re-exports and update the public root to
  import that API rather than retaining unrelated dependency-smoke imports.
- Update goal documentation only where actual compiled declaration names or
  findings change the plan.

## Build Structure

- `formal/Lecerf/Transition/Core.lean`: low-dependency runtime predicates and
  cheap generic theorems; imports only `Mathlib.Computability.StateTransition`.
- `formal/Lecerf/Transition/Reversible.lean`: reversible public proof surface;
  imports Core and `Mathlib.Data.PEquiv`.
- `formal/Lecerf/Transition/Audit.lean`: finite diagnostics and negative
  examples; never imported by the public API.
- `formal/Lecerf/Transition/API.lean`: thin stable re-export of Core and
  Reversible.
- `formal/Lecerf.lean`: public umbrella root; changed only to import the new
  API.
- Focused builds: `lake build Lecerf.Transition.Core`,
  `lake build Lecerf.Transition.Reversible`, and
  `lake build Lecerf.Transition.Audit`.
- Adjacent/public build: `lake build Lecerf.Transition.API Lecerf`.
- Full build required because the public umbrella import changes.

## No-Cheating Checks

- `PositiveReturn` must reduce to `Reaches₁`, never reflexive `Reaches`.
- Reversal theorems must use `r.symm` and the `PEquiv` inverse law, not assume
  the forward step is self-inverse.
- Forward successor uniqueness must be proved for every `Option` step;
  predecessor uniqueness must be proved separately from `PEquiv`.
- The negative audit example must rule out an inverse law for a merging step,
  not merely fail to construct one.
- No machine syntax, history simulator, computability reduction, word code, or
  partial-iterate API is introduced in this stage.
- No `sorry`, `admit`, proof-bypassing `unsafe`, or project axiom is permitted.

## Boundary Checks

- Runtime/public definitions: only generic transition predicates and
  reversible-step projections.
- Public proof declarations: basic closure/halting facts, one-step inverse,
  uniqueness, path reversal, and positive-return reversal.
- Diagnostics: finite examples and the deterministic-not-reversible
  obstruction stay in `Transition/Audit.lean`.
- Fallback/temporary declarations: none in project modules; local proof probes
  may be used outside the workspace and deleted.
- Shortcut scans inspect Lean source for proof holes/axioms and inspect the
  `PositiveReturn` definition and reversal theorem signatures directly.

## Completion Requirements

- All four transition modules and the public root compile.
- `Step` forward execution has a checked successor-uniqueness theorem.
- A reversible step has a checked exact next/previous iff and successful
  predecessor uniqueness.
- Both reflexive and positive finite reachability reverse iff under `symm`.
- Positive return reverses iff and is demonstrably not zero-step reachability.
- Halting is characterized by existence of a reachable terminal state.
- The audit leaf contains a proved deterministic merging transition with no
  possible `PEquiv` sharing that forward map.
- Focused, adjacent, and full builds pass; proof-hole/shortcut scans,
  `#print axioms` checks for representative public theorems, whitespace, and
  `git diff --check` pass.
- The stage results and affected plan/audit/dependency/theorem documents record
  exact evidence. Stage 3 is not started.

## Stage Results

- Added `formal/Lecerf/Transition/Core.lean` with `Step`, `StepRel`,
  `BackwardUnique`, `Terminal`, `HaltsFrom`, `Reachable`,
  `StrictlyReachable`, and `PositiveReturn`.
- Core theorems include `Step.stepRel_rightUnique`,
  `Step.successor_unique`, `terminal_iff_forall_not_step`, closure helpers,
  `reachable_iff_strictlyReachable_of_ne`,
  `haltsFrom_iff_exists_reachable_terminal`,
  `reachable_terminal_unique`, and terminal-state no-positive-run facts.
- Added `formal/Lecerf/Transition/Reversible.lean` with
  `ReversibleStep := PEquiv σ σ`, `next`, `prev`, exact one-step inverse laws,
  `backwardUnique`, `stepRel_biUnique`, reflexive and positive path reversal,
  positive-return reversal, reverse-reachability halting characterization, and
  endpoint evaluation reversal with both terminal hypotheses explicit.
- Added non-public `formal/Lecerf/Transition/Audit.lean`. Checked examples show:
  a terminal state is reflexively reachable but has no positive return; a
  Boolean toggle has a positive return; the empty `PEquiv` is not globally
  function-injective; a merge step is deterministic but not backward-unique;
  and its two branches are individually reversible partial edges.
- Added thin `formal/Lecerf/Transition/API.lean`; `formal/Lecerf.lean` now
  imports only that API. The audit leaf is not publicly re-exported.
- Initial focused probes exposed and corrected two implementation mistakes:
  unqualified `.trans` inside project namespaces recursively selected the
  theorem being defined, and using explicit `.toFun` projections obstructed
  convenient reduction of finite audit examples. The final code qualifies
  relation closure and defines `next`/`prev` through `PEquiv` coercions.
- `lake build Lecerf.Transition.Core`: passed, 655 jobs.
- `lake build Lecerf.Transition.Reversible`: passed, 657 jobs.
- `lake build Lecerf.Transition.Audit`: passed, 658 jobs.
- `lake build Lecerf.Transition.API Lecerf`: passed, 660 jobs.
- Full `lake build`: passed, 660 jobs.
- A temporary root-import API probe checked every principal public declaration
  and theorem signature; it exited successfully and was deleted.
- Temporary `#print axioms` audit results:
  - `Step.successor_unique`: no axioms;
  - `haltsFrom_iff_exists_reachable_terminal`:
    `propext`, `Classical.choice`, `Quot.sound`;
  - one-step inverse, reflexive reversal, and positive reversal:
    `propext`, `Quot.sound`;
  - endpoint evaluation reversal:
    `propext`, `Classical.choice`, `Quot.sound`;
  - diagnostic positive-cycle and merge-obstruction theorems use only the same
    standard Lean/mathlib axioms. No project-specific axiom was introduced.
- Lean scan for `sorry`, `admit`, `axiom`, and `unsafe`: no hits.
- Transition-source scan for `noncomputable` and `Classical.choice`: no hits;
  axiom-audit choice usage is inherited through mathlib proof semantics.
- Out-of-scope transition scan for Turing machines, word codes, reductions,
  iteration, and history declarations: no hits.
- Signature scan confirms `PositiveReturn` unfolds through `Reaches₁`, while
  the only `Function.Injective` transition occurrence is the proved negative
  audit example.
- Documentation scan hits for proof-hole terms are guardrail/evidence prose
  only. Import inspection confirms Core and Reversible use only the planned
  narrow dependencies.
- Trailing-whitespace scan and `git diff --check`: passed.
- Stage 2 is complete. Stage 3 was not started.
