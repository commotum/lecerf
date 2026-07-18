# 9-ITERATE-UNDEC

## Current Facts

- Stages 1--8 are complete and the worktree is clean at stage start. The pinned
  project uses Lean `v4.31.0` and mathlib commit
  `fabf563a7c95a166b8d7b6efca11c8b4dc9d911f`.
- Stage 6 exposes finite raw reversible two-tape descriptors, positive-return
  and distinct-target strict-reachability predicates, explicit primitive-
  recursive reduction maps, and their exact preservation/reflection theorems.
- Stage 8 exposes a proof-free finite `StepCode.Descriptor`, a primitive-
  recursive validity predicate, a uniformly primitive-recursive checked word
  interpreter, and a proof-side semantic `CodeIso` whose partial iteration on
  encoded configurations agrees exactly with machine execution.
- `Lecerf.Transition.exactIterate` and `ExactSteps` propagate failure through
  `Option.bind`. `Lecerf.PEquiv.PositiveIterate` executes `k + 1` partial
  applications, so exponent zero cannot witness it.
- The semantic successful-edge `CodeIso` can be generally infinite and its
  constructor is noncomputable. The finite runtime presentation for this stage
  must therefore be the raw machine descriptor plus words, not a stored
  `CodeIso`, function, or proof object.
- The paper's equation orientation is written `w₁ = θⁿ(w₂)`. Runtime orbit
  inputs will store the start word `w₂` before the target word `w₁`; this
  orientation must be documented rather than inferred from tuple positions.

## Updated Assumptions

- Use inherited product encodings for runtime inputs. This avoids bespoke
  serialization and preserves the existing `Primcodable` representations:
  `(descriptor, word)` for fixed orbit and `(descriptor, start, target)` for
  distinct-word orbit reachability.
- Define the two existential target predicates with a witness `k : Nat` and
  exact exponent `k + 1`. Do not expose a zero-inclusive wrapper whose fixed
  point branch is tautological.
- Keep descriptor validity as an explicit conjunct even though the checked
  interpreter rejects invalid tables. Validity is what certifies that a raw
  descriptor presents the proof-side code isomorphism.
- Define supplied-exponent recognition separately and prove it primitive
  recursive/computable. Existential witness search may be partial and the
  existential predicates may be recursively enumerable; no total existence
  decider or total witness finder may be inferred.
- First prove generic reductions from Stage-6 reversible positive return and
  distinct-target reachability. Compose those with the existing fixed halting
  reductions only after the generic preservation/reflection theorems compile.
- Empty-word fixed orbits can exist for arbitrary valid descriptors because a
  monoid isomorphism preserves the identity. Do not add an unproved
  `word ≠ 1` restriction: the reduction uses nonempty canonical configuration
  frames, and the positive-exponent target remains nontrivial as a uniform
  finite-presentation problem.

## Big Picture Objective

Give exact finite-presentation formulations of the paper's two iterate-
equation problems and reduce reversible-machine positive return and specified
distinct-target reachability to them. Prove computability of the maps,
preservation and reflection including all intermediate partial definedness,
undecidability of existential orbit membership, and computability of checking
a supplied positive exponent.

## Detailed Implementation Plan

1. Add low-dependency problem definitions for the finite descriptor, fixed-
   orbit input, distinct-orbit input, supplied-exponent input, and their guarded
   predicates.
2. Add a narrow generic effectivity leaf for exact iteration of a uniformly
   primitive-recursive option-valued transition, then instantiate it for the
   checked step-code interpreter. Prove supplied-exponent predicates primitive
   recursive/computable and, if the pinned API supports a clean proof, prove
   the existential problems recursively enumerable by partial witness search.
3. Prove checked iteration agrees with semantic partial `CodeIso` iteration
   for every exponent. Specialize to canonical configuration frames and derive
   exact positive-orbit iff strict machine reachability.
4. Define primitive-recursive maps from Stage-6 return/reachability inputs to
   code-orbit inputs. Prove generic iff theorems, including descriptor validity,
   endpoint injectivity, distinct output words, and malformed-input reflection.
5. Package generic and direct halting `ManyOneReducible` theorems and derive
   noncomputability of both existential target predicates.
6. Add a thin public API and audit leaf, run focused/adjacent/full builds,
   forbidden-shortcut scans, and `#print axioms`; then fold exact declarations
   and evidence into all affected goal documents.

## Build Structure

- `formal/Lecerf/Transition/ExactEffectivity.lean`: reusable uniform
  primitive-recursive exact iteration without totalizing `Option` failure.
- `formal/Lecerf/Undecidability/CodeIterates/Problems.lean`: finite raw input
  aliases and exact guarded predicates only.
- `formal/Lecerf/Undecidability/CodeIterates/Correspondence.lean`: checked
  interpreter/code-isomorphism agreement and canonical configuration orbit
  correspondence; it does not import the universal compiler.
- `formal/Lecerf/Undecidability/CodeIterates/Effectivity.lean`: supplied-
  exponent effectivity and partial witness-search/RE facts.
- `formal/Lecerf/Undecidability/CodeIterates/Reduction.lean`: generic reduction
  maps, exact iff theorems, many-one composition, and noncomputability.
- `formal/Lecerf/Undecidability/CodeIterates/API.lean`: thin stable re-export.
- `formal/Lecerf/Undecidability/CodeIterates/Audit.lean`: examples, negative
  boundaries, and axiom diagnostics; not imported by the public API.
- Avoid changing high-fanout word, transition-core, machine, and step-code
  modules unless checked obligations show that a genuinely reusable lower
  lemma is missing.
- Initial focused builds: `lake build Lecerf.Transition.ExactEffectivity` and
  then each new `Lecerf.Undecidability.CodeIterates.*` leaf. Adjacent builds
  include the new API and the root only after leaf builds pass.

## No-Cheating Checks

- Inspect target predicate definitions to confirm every existential exponent is
  definitionally `k + 1`; no `n = 0` witness can discharge fixed orbit.
- Inspect exact iteration and semantic correspondence to confirm failed
  intermediate applications remain `none`; no identity/sink/default-word
  totalization is introduced.
- Runtime input types must not contain `PEquiv`, `CodeIso`, functions,
  validity proofs, choice-based decoders, or halting/reachability witnesses.
- The distinct-orbit reduction must prove encoded start and target words are
  unequal from the Stage-6 configuration inequality and codec injectivity.
- Both reduction iff theorems must handle invalid descriptors in both
  directions, rather than proving only the certified forward case.
- Undecidability must flow through explicit computable maps and
  `ManyOneReducible`; do not introduce a project axiom or relabel an existing
  machine theorem as a code theorem.
- Keep supplied-exponent computability, partial witness search, recursive
  enumerability, and total decidability of existence as distinct statements.

## Boundary Checks

- Runtime: raw finite descriptor, `Word Bool` endpoints, checked partial word
  interpreter, exact supplied iteration.
- Public API: guarded existential predicates, supplied-exponent recognition,
  correspondence, reductions, and noncomputability results.
- Proof-side: validity-to-reversibility certificate and semantic successful-
  edge `CodeIso`; these certify meaning but are not encoded as runtime data.
- Diagnostic: empty-word and malformed/invalid cases plus axiom prints live
  only in `Audit.lean`.
- Historical boundary: this stage proves undecidability for the finite-machine-
  presented successful-edge code-isomorphism subclass. It does not claim a
  finite presentation of every code isomorphism or reconstruct Lecerf's finite
  local `alpha`/`omega`/`beta` relation list.

## Completion Requirements

- Both existential predicates use strictly positive exponents and partial
  exact iteration; the distinct predicate contains explicit word inequality.
- Supplied-exponent checking is proved uniformly primitive recursive or at
  least computable from the actual raw descriptor and words.
- Generic return/fixed-orbit and reachability/distinct-orbit maps are proved
  primitive recursive/computable and satisfy exact iff theorems.
- Direct fixed-halting many-one reductions and noncomputability corollaries
  compile for both targets.
- Correspondence theorems connect executable checked iteration to the
  proof-side code isomorphism and prove preservation/reflection for canonical
  configuration words.
- Focused leaf, adjacent API/root, and full builds pass. Scans classify every
  `sorry`, `admit`, `axiom`, and `unsafe` hit; shortcut/signature checks and
  `git diff --check` pass.
- `#print axioms` for both headline reductions/noncomputability theorems is
  recorded, and `0-plan.md`, `PAPER-MAP.md`, `AUDIT.md`, `DEPENDENCIES.md`, and
  `THEOREM-OUTLINE.md` agree on exact names, quantifiers, scope, and remaining
  historical gaps.

## Stage Results

- Added `Lecerf.Transition.ExactEffectivity.exactIterate_uniform_primrec`.
  Its recursive accumulator remains `Option X`, so failed intermediate steps
  are propagated rather than totalized.
- Added `CodeIterates.Problems` with `CodeDescriptor`, `FixedOrbitInput`,
  `DistinctOrbitInput`, `SuppliedExponentInput`, `PositiveFixedOrbitYes`,
  `DistinctOrbitYes`, and `PositiveIterateAtYes`. Runtime products contain no
  function, proof, `PEquiv`, semantic `CodeIso`, or orbit witness. Both
  existential predicates use exponent `k + 1`; supplied recognition requires
  `n ≠ 0`.
- Added `CodeIterates.Effectivity`. `checkedExactIterate_uniform_primrec` and
  `positiveIterateAtYes_primrec` prove uniform exact evaluation and recognition
  primitive recursive. `FixedOrbitWitnessYes` and
  `DistinctOrbitWitnessYes` have primitive-recursive/computable predicates;
  `positiveFixedOrbitYes_re` and `distinctOrbitYes_re` use partial recursive
  `Nat.rfind` search. These RE results do not claim a total finder or decider.
- Added `CodeIterates.Correspondence`. The checked exact and positive iterates
  agree with the partial action of `stepCodeIso` under the explicit validity
  guard. `encodedCheckedExactSteps_iff_exactSteps` and
  `encodedCheckedPositiveExactSteps_iff_strictlyReachable` prove exact
  canonical configuration preservation/reflection. The final canonical iff
  theorems cover positive return/fixed orbit and guarded distinct-target
  reachability/distinct word orbit for arbitrary raw descriptors.
- Added `CodeIterates.Reduction`. `encodeReturnInput` and
  `encodeReachabilityInput` preserve the descriptor verbatim and are primitive
  recursive/computable. `returnYes_iff_positiveFixedOrbitYes` and
  `reachabilityYes_iff_distinctOrbitYes` prove both directions even for invalid
  inputs; codec injectivity proves distinct output words. Generic many-one
  reductions are composed with Stage 6 to obtain
  `partrecHalts0_manyOne_positiveFixedOrbitYes` and
  `partrecHalts0_manyOne_distinctOrbitYes`, followed by
  `positiveFixedOrbitYes_not_computable` and
  `distinctOrbitYes_not_computable`.
- Added a thin `CodeIterates.API`, exported it through `Undecidability.API` and
  `Lecerf`, and kept `CodeIterates.Audit` non-public. The audit proves supplied
  exponent zero is rejected, exact-iteration failure persists under every
  extension, and canonical return-reduction words are nonempty.
- Focused builds passed: `Lecerf.Transition.ExactEffectivity` (812 jobs),
  `CodeIterates.Problems` (892), `CodeIterates.Effectivity` (894),
  `CodeIterates.Correspondence` (894), `CodeIterates.Reduction` (907), and
  `CodeIterates.Audit` (908). The new API, undecidability API, and public root
  built together with 927 jobs; an audit/root replay passed with 928 jobs;
  full `lake build` passed with 927 jobs.
- A temporary `import Lecerf` signature probe checked all public Stage-9 input,
  predicate, effectivity, correspondence, many-one, and noncomputability names
  and was deleted. Lean scans found no `sorry`, `admit`, project `axiom`, or
  proof-bypassing `unsafe`. The two `noncomputable section` declarations merely
  inherit Stage 6's documented fixed target encodings; all varying maps carry
  primitive-recursive/computable proofs. Shortcut scans confirmed literal
  `k + 1`, `n ≠ 0`, `ExactSteps`, and absence of a fallback totalizer.
- All nine `#print axioms` diagnostics report exactly `[propext,
  Classical.choice, Quot.sound]`. These are the already classified Lean/mathlib
  dependencies; no project-specific axiom was introduced. Documentation fence
  checks and stale Stage-9 text scans passed, and `git diff --check` passed.
- The theorem is scoped to the finite-machine-presented successful-edge
  code-isomorphism subclass. The generally infinite semantic edge family, a
  finite presentation of arbitrary `CodeIso`s, Lecerf's literal finite local
  `alpha`/`omega`/`beta` relations, and the two-to-one-tape lowering remain
  explicit Stage-10 audit/follow-up boundaries.
