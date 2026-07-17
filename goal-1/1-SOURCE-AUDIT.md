# 1-SOURCE-AUDIT

## Current Facts

- The worktree contains the complete four-page paper as French and English
  Markdown transcriptions, PDFs, and page images.
- The pinned Lean project builds before this stage; its only project module is
  an import smoke test.
- The first source comparison already confirms that English §1b drops the
  French phrase `au plus un`, materially changing unique decipherability into
  an existence claim.
- The paper sketches rather than fully specifies its machine convention,
  inverse execution, history simulator, and code encoding.
- Modern Lean `Nat` contains zero, so a direct transcription of
  `∃ n : Nat, w = θ^[n] w` would be trivially true.
- No previous numbered stage exists.

## Updated Assumptions

- `PEquiv σ σ` remains a strong candidate for the generic reversible-step
  carrier, but Stage 1 must verify that its inverse law and option semantics
  match the intended API.
- A custom finite machine syntax remains likely because mathlib's TM0 splits
  moves and writes, while Lecerf uses quintuples; the effective bridge from the
  established halting theorem remains a later proof obligation.
- `FreeMonoid` should be reused for words, with project-local definitions for
  uniquely decodable indexed codes and partial code isomorphism iteration.
- The fixed-orbit target will require positive iteration; whether this is best
  documented as a correction or a disambiguation depends on source evidence.
- Claims about the printed inverse quintuple must remain conditional until the
  action order and head-marker semantics have been reconstructed.

## Big Picture Objective

Turn the bilingual source and pinned mathlib surface into an explicit,
auditable formal specification. End the stage with fixed conventions where the
evidence is decisive and isolated proof obligations or candidate branches
where it is not. Do not implement the mathematical library in this stage.

## Detailed Implementation Plan

- Compare all French and English mathematical statements, assigning stable
  claim identifiers and recording material translation/OCR differences.
- Fix or explicitly branch the machine action order, tape/blank model, halting
  convention, configuration equality, image-state semantics, and global
  reversibility conditions.
- Resolve the formal target meanings of code, prefix/suffix code, complete
  code, paper code epimorphism, positive return, specified-target reachability,
  partial iteration, and existential exponent search.
- Inspect the pinned mathlib source for exact reusable declarations, theorem
  names, import boundaries, and semantic mismatches.
- Replace pseudocode-level theorem ideas with proposed Lean-shaped signatures
  and exact source/target decision predicates in documentation only.
- Fold all decisions into `0-plan.md`, `PAPER-MAP.md`, `AUDIT.md`,
  `DEPENDENCIES.md`, and `THEOREM-OUTLINE.md`.

## Build Structure

- Lean modules touched: none expected.
- Documentation touched: this stage file plus the five authoritative planning
  and audit documents listed above.
- High-fanout modules intentionally avoided: the root `Lecerf.lean` smoke
  module and all future implementation modules.
- Focused build command: `cd formal && lake build Lecerf` confirms the pinned
  dependency surface remains valid.
- Adjacent consumer builds: none, because no Lean source or configuration is
  planned to change.

## No-Cheating Checks

- Do not promote a plausible historical interpretation to source fact without
  textual evidence.
- Do not state `n = 0` fixed-orbit existence as the paper's undecidability
  predicate.
- Do not treat ambient-word iteration as total when a code isomorphism has
  distinct source and target submonoids.
- Do not accept syntactic sign reversal as inverse execution until a
  configuration-step equation validates it.
- Do not treat right-unique forward execution as backward-unique or reversible.
- Do not claim a computability reduction from the existence of a mathematical
  simulation; retain computability and preservation/reflection as separate
  obligations.

## Boundary Checks

- Runtime declarations introduced: none.
- Public API declarations introduced: none.
- Proof-side declarations introduced: none.
- Diagnostics/evidence: source comparisons, pinned-mathlib source locations,
  proposed signatures, and explicit unresolved tests only.
- Forbidden shortcuts will be checked by inspecting all final target
  predicates for zero-step/zero-exponent and partial-domain loopholes, and by
  scanning Lean sources for any new declaration or proof hole.

## Completion Requirements

- Every paper section and headline theorem has a stable claim identifier and a
  disposition supported by source evidence.
- Machine, reachability, code, map, and exponent conventions are fixed or have
  explicit candidate branches plus the exact later proof/source test that will
  select one.
- The `n = 0`, partial-iteration, inverse-transition, English code-definition,
  and “epimorphism” issues have concrete formal resolutions or isolated proof
  obligations.
- Exact pinned-mathlib module paths, definitions, theorem names, and intended
  reuse/bridge decisions are recorded.
- Proposed theorem and decision-problem signatures have explicit quantifiers
  and separate evaluation, simulation, and reduction layers.
- `lake build Lecerf`, the documentation/Lean shortcut scans, whitespace
  checks, and `git diff --check` pass.
- No substantive Lean implementation or theorem is claimed complete.

## Stage Results

- In progress.
