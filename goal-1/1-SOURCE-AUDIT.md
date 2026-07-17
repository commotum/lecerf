# 1-SOURCE-AUDIT

## Current Facts

- The complete four-page paper was checked in French and English Markdown and
  against every scan page; the French scan is authoritative.
- English §1b omits French `au plus un`, and English §1e inserts “complete”
  where French says only `est bien un code`. Both are material translation
  errors.
- Under conventional read-write-then-move semantics, §2's printed inverse
  quintuple is not a one-step inverse for moving rules.
- The paper leaves `N` undefined, maps distinct generated submonoids with
  `θ`, and gives an inconsistent initial-history formula. Positive partial
  iteration and a clean empty history base case are required repairs.
- The pinned mathlib surface includes reusable transition, partial-equivalence,
  free-monoid, uniquely-decodable-code, computability, and reduction APIs.
- The checked halting theorem and universal TM construction use distinct code
  types and do not expose an end-to-end computable finite compiler.
- No substantive Lean declaration or proof was introduced in this stage.

## Updated Assumptions

- Generic reversible steps will use same-type `PEquiv`; reachability and
  halting will reuse `StateTransition`.
- Concrete paper-facing rules use conventional read-write-move semantics and
  are compiled through reversible write/move phases. The paper's inverse tuple
  remains audit syntax only.
- Tape semantics are doubly infinite, blank outside finite support. Stage 3
  selects `Turing.Tape` only if it can supply the required canonical executable
  encoding; otherwise it builds a canonical finite-support representation and
  a semantic bridge.
- Undecidability starts from `ComputablePred.halting_problem 0`, with
  `Nat.Partrec.Code.evaln` providing the preferred explicit search transition.
  A computable compiler into finite machine syntax remains a Stage-3
  obligation.
- Words use `FreeMonoid`. Indexed codehood is injectivity of
  `FreeMonoid.lift`; mathlib's set-based `UniquelyDecodable` is related only
  together with generator injectivity.
- Code isomorphisms are equivalences between generated submonoids with a
  law-carrying ambient partial view. Iteration uses partial composition and a
  positive exponent.
- Lecerf's “epimorphism of codes” gets a project-specific selector structure;
  duplicate targets and lack of surjectivity are permitted unless a separate
  theorem supplies stronger properties.

## Big Picture Objective

Turn the bilingual source and pinned mathlib surface into an explicit,
auditable formal specification. Fix conventions where evidence is decisive,
record corrections where the paper is false or incomplete under the chosen
semantics, and isolate later implementation obligations without proving them.

## Detailed Implementation Plan

- Compare every mathematical source statement and assign stable claim IDs.
- Fix machine action order, tape/blank model, halting, configuration equality,
  starred-state meaning, and the distinction between rule and machine
  reversibility.
- Resolve code, prefix/suffix, paper-epimorphism, positive return,
  distinct-target reachability, partial iteration, and exponent-search
  semantics.
- Inspect exact pinned mathlib declarations, imports, finite-encoding support,
  and the partial-recursive/TM bridge.
- Draft Lean-shaped definitions, theorem specifications, raw decision
  predicates, and every computable reduction arrow in documentation only.
- Fold decisions and evidence into `0-plan.md`, `PAPER-MAP.md`, `AUDIT.md`,
  `DEPENDENCIES.md`, and `THEOREM-OUTLINE.md`.

## Build Structure

- Lean modules touched: none.
- Documentation touched: this stage file and the five authoritative goal
  documents above.
- Public/high-fanout modules intentionally untouched: `formal/Lecerf.lean` and
  all future implementation modules.
- Focused build: `cd formal && lake build Lecerf`.
- Adjacent consumer builds: none, because no Lean source, dependency, or Lake
  configuration changed.

## No-Cheating Checks

- Source assertions, mathematical inferences, corrections, and proposed Lean
  declarations are labeled separately.
- Fixed orbit quantifies over `k + 1`; positive return uses `Reaches₁`.
- Ambient code-isomorphism iteration returns `none` when an intermediate word
  is outside the next domain.
- The printed tuple inverse is not accepted as an execution theorem.
- Forward simulation does not stand in for checkpoint reflection or a
  computable reduction.
- Decision inputs are finite raw descriptions; semantic function structures
  and unexplained proof-bearing subtypes are not treated as `Primcodable`.

## Boundary Checks

- Runtime declarations introduced: none.
- Public API declarations introduced: none.
- Proof-side declarations introduced: none.
- Diagnostics/evidence: bilingual source comparison, scan inspection, pinned
  mathlib source inspection, and one deleted temporary `#check` probe.
- Exact future tests are isolated for tape encoding, the finite halting
  compiler, historical marker correspondence, coupling gadgets, and the
  set/indexed uniquely-decodable bridge.

## Completion Requirements

- Every paper section and headline theorem has a stable claim identifier and a
  source-supported disposition.
- Machine, reachability, code, map, and exponent conventions are fixed or have
  an explicit later test that selects the representation.
- Zero-exponent, partial-iteration, inverse-transition, English code, history
  base-case, and “epimorphism” defects have concrete resolutions.
- Exact pinned imports and declaration names are checked, including bridge and
  `Primcodable` limitations.
- Proposed theorem and decision predicates expose quantifiers and keep
  evaluation, simulation, encoding, and reductions separate.
- The focused build, shortcut scans, whitespace checks, and `git diff --check`
  pass.
- No substantive Lean implementation or theorem is claimed complete.

## Stage Results

- Source audit: complete; all claims and material corrections are recorded in
  `PAPER-MAP.md` and `AUDIT.md`.
- Dependency audit: complete; exact checked imports, declarations, and bridge
  risks are recorded in `DEPENDENCIES.md`.
- Formal target audit: complete; proposed predicates and reduction iff
  obligations are recorded in `THEOREM-OUTLINE.md`.
- `cd formal && lake build Lecerf`: passed, `Build completed successfully (831
  jobs).`
- Lean-source scan for `sorry`, `admit`, `axiom`, and `unsafe`: no hits.
- Lean-source shortcut scan for reflexive-return, zero-iterate,
  `Classical.choice`, and `noncomputable` patterns: no hits.
- Documentation trailing-whitespace scan: no hits.
- `git diff --check`: passed.
- Changed Lean/configuration path check: no hits; this stage changed only goal
  documentation.
- Stage boundary: complete. `2-TRANSITION` was not started.
