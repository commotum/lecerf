# 10-PAPER-AUDIT

## Current Facts

- Stages 1--9 are implemented. Stage 9's focused modules, public root, audit,
  and full project build passed before this stage began; its nine representative
  axiom prints report only `propext`, `Classical.choice`, and `Quot.sound`.
- The pinned project remains Lean `v4.31.0` with mathlib commit
  `fabf563a7c95a166b8d7b6efca11c8b4dc9d911f` in both `lakefile.toml` and
  `lake-manifest.json`.
- The worktree contains one carried Stage-9 documentation modification in
  `goal-1/AUDIT.md`. It belongs to the requested fold-back and must be
  preserved and validated, not discarded.
- `formal/Lecerf.lean` exports thin transition, machine, undecidability, word,
  and machine-step-code APIs. Feature-specific audit leaves are not imported by
  the public root.
- There is no consolidated `Lecerf.Audit` target. Existing audit leaves already
  exercise the principal boundaries and print representative axioms; Stage 10
  must decide from coverage, not aesthetics, whether a non-public aggregator is
  useful.
- `0-plan.md` contains a checked documentation contradiction: Stage-8 results
  are misplaced under `4-HISTORY-SIM`, and its dependency-shape prose still
  calls now-realized later module names provisional. These must be repaired.
- The remaining one-tape lowering and literal finite local
  `alpha`/`omega`/`beta` reconstruction are explicitly documented historical
  follow-ups. The user permits a cleaner equivalent theorem first, so these
  gaps do not by themselves refute completion, but no declaration may be
  described as the historical construction.

## Updated Assumptions

- Treat the ten success metrics in `0-plan.md`, the objective attachment, and
  every stage completion requirement as the completion checklist. For each,
  cite direct declarations, signatures, build output, scans, or source-map
  entries; absence of an obvious error is not evidence.
- Stage 10 is primarily an integration and trust audit. Add Lean only for a
  demonstrated public-boundary or verification gap, and keep any consolidated
  audit target diagnostic and non-public.
- A clean Lake-state build is explicitly required. After focused consumer
  checks, run `lake clean` followed by `lake build`, then rebuild any diagnostic
  target excluded from the default root.
- Classify classical dependencies by boundary: fixed universal program and
  encodings, semantic arbitrary-code decoding/membership, and standard mathlib
  quotient/`Part` semantics are permitted when documented; varying reduction
  maps must still carry `Primrec`/`Computable` proofs.
- Historical fidelity is a disposition, not a boolean. Every paper claim must
  be labeled source-confirmed, corrected, cleaner-equivalent, weaker/stronger,
  or explicitly unresolved with no misleading public theorem name.

## Big Picture Objective

Prove that the completed library satisfies the original objective as scoped by
its expressly permitted cleaner constructions. Reconcile the public API,
paper-claim map, correction and trust log, dependency graph, theorem outline,
and actual Lean declarations; repair concrete gaps; then perform a clean full
build and consolidated no-cheating/axiom audit.

## Detailed Implementation Plan

1. Build a requirement-to-evidence matrix for all ten success metrics and the
   attachment's explicit constraints. Inspect actual theorem signatures and
   import ownership rather than relying on stage summaries.
2. Audit every public API and diagnostic leaf. Add a thin non-public aggregate
   audit or missing re-export only if it materially strengthens verification or
   exposes a stable declaration that is otherwise absent from the documented
   public surface.
3. Reconcile every `PAPER-MAP.md` claim disposition and every material
   correction/open issue in `AUDIT.md` with exact declaration names. Repair the
   misplaced/stale plan prose and update dependency/theorem notes.
4. Run a public-root signature probe covering the principal transition,
   machine, simulation, coupling, code, encoding, reduction, and iterate
   declarations. Run `#print axioms` for every headline theorem class not
   already directly covered by a checked audit leaf.
5. Run focused public/audit consumer builds, then `lake clean` and full
   `lake build`. Rebuild the non-default diagnostic surface afterward. Run
   complete proof-hole, project-axiom, unsafe, noncomputable-boundary, shortcut,
   import-boundary, stale-doc, whitespace, and diff checks.
6. Fold exact results into this file and all authoritative goal documents. Mark
   the original goal complete only if every requirement has direct evidence;
   otherwise leave precise unresolved work and the goal active.

## Build Structure

- Existing thin public roots are the first candidates for focused verification:
  `Lecerf.Transition.API`, `Lecerf.Machine.API`, `Lecerf.Word.API`,
  `Lecerf.Encoding.StepCode.API`, `Lecerf.Undecidability.API`, and `Lecerf`.
- Existing audit leaves remain diagnostic and non-public. A possible
  `formal/Lecerf/Audit.lean` may aggregate them and own final headline axiom
  commands; it must not be imported by `Lecerf.lean`.
- Goal documents expected to change are `0-plan.md`, `PAPER-MAP.md`,
  `AUDIT.md`, `DEPENDENCIES.md`, `THEOREM-OUTLINE.md`, and this stage file.
- Avoid edits to mathematical core/proof modules unless a signature probe or
  requirement audit demonstrates a real missing theorem or false claim.
- Focused builds will target any touched API/audit leaf and adjacent root.
  Stage completion additionally requires a clean-state full build.

## No-Cheating Checks

- Scan every project Lean source, not only Stage-10 changes, for `sorry`,
  `admit`, project `axiom`, and proof-bypassing `unsafe` declarations.
- Inspect all `noncomputable` and explicit classical-choice occurrences and
  classify whether they are fixed-data, semantic code decoding, diagnostics,
  or an impermissible varying reduction dependency.
- Inspect every undecidability theorem chain for a named computable map,
  preservation/reflection iff, `ManyOneReducible`, and established source
  noncomputability theorem.
- Check signatures distinguish `Reaches`/`Reaches₁`, positive/exponent-zero,
  exact partial iteration/total iteration, local rule inverse/global machine
  reversibility, and `PaperCodeEpi`/`CodeIso`/injective morphism.
- Verify no audit module is imported from a public API or runtime/proof core.
- Search documentation for stale `planned`, `unstarted`, old theorem names,
  false one-tape claims, claims of a finite local historical encoding, and
  statements that arbitrary semantic `CodeIso` decoding is executable.
- Axiom output must contain no project-specific axiom; standard dependencies
  must be tied to their actual boundary rather than merely listed.

## Boundary Checks

- Runtime: executable tapes, finite rule tables, history compiler, codecs,
  descriptor checks, and reduction maps.
- Public proof API: generic reversible transition results, simulation and
  coupling correctness, word/code structures, semantic code isomorphism,
  step/orbit correspondence, and undecidability theorems.
- Fixed classical data: selected universal program, finite encodings, and
  closed compiled tables; every varying endpoint/map remains proved effective.
- Semantic noncomputable data: arbitrary generated-submonoid decoding and
  ambient arbitrary-code action; never used as runtime reduction input.
- Diagnostic: counterexamples, native/kernel checks, obstruction statements,
  and axiom commands; never publicly re-exported.
- Historical follow-up: literal one-tape marker/sweeping implementation,
  finite `tau_min`, and comparison with the cleaner two-tape whole-
  configuration edge schema. These remain documented without being presented
  as missing proof obligations for the permitted cleaner main theorem.

## Completion Requirements

- Each of the ten `0-plan.md` success metrics has a direct evidence row, and
  every source claim has an exact Lean declaration or explicit disposition.
- Public-root signature probes cover every headline theorem family and confirm
  documented names/types are actually exported.
- Every main axiom audit is checked and classified; no project-specific axiom,
  proof hole, or unsafe proof bypass remains.
- Every computability conclusion has an explicit effective reduction and exact
  preservation/reflection evidence; supplied-exponent recognition remains
  distinct from existential undecidability.
- API/audit import boundaries and historical scope claims pass direct scans.
- Focused API/audit builds, clean-state `lake build`, post-clean diagnostic
  builds, source/document scans, Markdown fence checks, and
  `git diff --check` pass.
- All authoritative documents agree on exact status, theorem names, scope,
  trust assumptions, and explicit maintenance/historical follow-ups.

## Stage Results

- In progress. This contract records the initial contradictions and direct
  evidence requirements before any Stage-10 integration edits.

