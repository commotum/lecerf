# 10-PAPER-AUDIT

## Current Facts

- Stages 1--9 are implemented. Stage 9's focused modules, public root, audit,
  and full project build passed before this stage began; its nine representative
  axiom prints report only `propext`, `Classical.choice`, and `Quot.sound`.
- The pinned project remains Lean `v4.31.0` with mathlib commit
  `fabf563a7c95a166b8d7b6efca11c8b4dc9d911f` in both `lakefile.toml` and
  `lake-manifest.json`.
- At stage start the worktree contained one carried Stage-9 documentation
  modification in `goal-1/AUDIT.md`; it has been preserved through the
  Stage-10 reconciliation.
- `formal/Lecerf.lean` exports thin transition, machine, undecidability, word,
  and machine-step-code APIs. Feature-specific audit leaves are not imported by
  the public root.
- `Lecerf.PublicAudit` now probes the root-exported headline signatures and
  their axioms; non-public `Lecerf.Audit` aggregates it with every feature
  audit without entering the public import graph.
- Stage-8 results were initially misplaced under `4-HISTORY-SIM`, and the
  dependency sketch used obsolete provisional names. Both authoritative
  records have been repaired.
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

## Realized Build Structure

- Thin public roots used for focused verification are
  `Lecerf.Transition.API`, `Lecerf.Machine.API`, `Lecerf.Word.API`,
  `Lecerf.Encoding.StepCode.API`, `Lecerf.Undecidability.API`, and `Lecerf`.
- `Transition.ExactCore` now owns Word-free exact execution;
  `Transition.Exact` owns only the `PEquiv` bridge. `Transition.API` exports
  the core and effectivity layer without importing Word.
- `Machine.TwoTape.API` intentionally exports the conventional two-tape model,
  validity, history-compiler correctness, and endpoint effectivity through
  `Machine.API`.
- `PublicAudit` imports only `Lecerf`; `Lecerf.Audit` aggregates it and every
  feature audit. Neither diagnostic module is imported by a public or internal
  proof/runtime module.
- Mathematical core edits were limited to narrowing two umbrella imports;
  the only proof-body repairs replace generated-axiom `native_decide` uses in
  diagnostic leaves with kernel `decide`.

## No-Cheating Checks

- Scan every project Lean source, not only Stage-10 changes, for `sorry`,
  `admit`, project `axiom`, proof-bypassing `unsafe`, and `native_decide`.
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
- Diagnostic: counterexamples, kernel-checked executable checks, obstruction
  statements, and axiom commands; never publicly re-exported.
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

## Requirement-to-Evidence Matrix

| Success metric | Disposition | Direct evidence and scope |
|---:|---|---|
| 1 | Met | `Transition.{Core,Reversible,ExactCore,ExactEffectivity}` exports deterministic option execution, successful-predecessor uniqueness, exact/positive reachability, halting, return, reversible path inversion, partial exact iteration, and uniform primitive-recursive iteration. |
| 2 | Met semantically | `Machine.{Tape,Core,Reversible}` fixes canonical blank-tape and read-write-move semantics. `Rule.apply_eq_some_iff_undo_eq_some`, `step_eq_some_iff_reverseStep_eq_some`, and `backwardCompatible_iff_backwardUnique` prove repaired local and whole-table inverse behavior. `SyntacticallyReversible` remains correctly documented as a decidable sufficient certificate, not an iff characterization. |
| 3 | Met by the permitted cleaner construction | The abstract `History` simulator is an exact `PEquiv`; `reachable_iff_valid`, projection/reflection, growth, and `haltsFrom_forward_iff` prove correctness, while `finiteForward_uniform_primrec`/`finiteBackward_uniform_primrec` give a uniform effective interpreter. For every finite deterministic one-tape source, `HistoryCompiler.historyMachine` is a conventional finite reversible two-tape realization with `historyMachine_haltsFrom_iff_source`. Its generic table generator has no claimed `Primrec` theorem because of finite-enumeration choice; the fixed tables used in reductions avoid that boundary. |
| 4 | Met for certified finite two-tape machines | `compileHalting`, `compileReturn`, and `compileReachability` each have `Primrec`/`Computable`, exact iff, `ManyOneReducible`, and transferred noncomputability theorems. The one-tape historical lowering remains follow-up. |
| 5 | Met | `Word.{Code,Prefix,CodeMorphism}` supplies the exact indexed/set-code bridge, prefix/suffix marker lemmas, generated submonoids, and distinct `MonoidHom`, `InjectiveMorphism`, `PaperCodeEpi`, `CodeIso`, and partial ambient `CodeIso.toPEquiv` boundaries. |
| 6 | Met by a cleaner finite-descriptor presentation | `ConfigCode` gives exact primitive-recursive Boolean framing. `StepCode` gives successful-edge codes, exact backward-uniqueness/codehood, `PaperCodeEpi`/`CodeIso`, strong step/iterate reflection, and a finite validity-guarded primitive-recursive interpreter. The semantic edge family is generally infinite and is not named as Lecerf's finite local relation list. |
| 7 | Met for that corrected presentation | `PositiveFixedOrbitYes` and `DistinctOrbitYes` use exponent `k + 1`; supplied nonzero exponent recognition is computable, existence is RE, and the two explicit many-one reductions establish noncomputability. `ExactSteps` preserves partial failure and the distinct problem carries endpoint inequality. |
| 8 | Met | All 32 material source claim IDs in `PAPER-MAP.md` have a checked declaration or an explicit non-formal disposition: source-confirmed, corrected target, cited background, conjecture, out-of-scope follow-up, or `spec-gap`/historical obligation. |
| 9 | Met after trust repair | `AUDIT.md` records corrections `A-001`--`A-036`, noncomputable boundaries, validation history, and headline axioms. `PublicAudit` imports only `Lecerf`; aggregate `Lecerf.Audit` adds every diagnostic leaf. Stage 10 removed 21 `native_decide` uses whose generated axioms evaded source-token scans. |
| 10 | Pending final clean verification | Focused public/audit builds have passed. Completion still requires the final clean-state root build, post-clean aggregate audit build, complete scans, Markdown checks, and `git diff --check`. |

## Stage Results

- In progress. This contract records the initial contradictions and direct
  evidence requirements before any Stage-10 integration edits.
