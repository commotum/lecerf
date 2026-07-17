# Audit, Corrections, and Trust Log

This is a living ledger. An entry is not a proved correction merely because it
looks mathematically necessary; source evidence and eventual Lean evidence are
recorded separately.

## Current Correction and Uncertainty Log

| ID | Issue | Evidence | Planned disposition | Status |
|---|---|---|---|---|
| `A-001` | The English §1b code definition says an arbitrary word has a factorization, omitting uniqueness. | French transcription says “il existe au plus un ensemble d'indices” (“there exists at most one sequence of indices”). | Treat a code as uniquely decipherable; correct the English transcription separately only if later authorized. | source-confirmed |
| `A-002` | If `n = 0`, `w = θⁿ(w)` is true for every `w`, so the stated decision problem is trivial. | Paper writes `n ∈ N` and also calls the identity solution trivial, but does not state `n > 0`. | Audit historical `N`; formal theorem will use positive iteration unless evidence supports a different nontrivial quantifier. | critical-unresolved |
| `A-003` | `θ` maps one generated submonoid to another, so `θⁿ` need not be total or even composable. | §1b defines domain `φ(A†)` and codomain `ψ(A†)` without asserting equality. | Model `θ` as a partial map on ambient words or require/prove closure at every iterate. | critical-unresolved |
| `A-004` | Negating displacement in a standard write-then-move quintuple does not obviously produce a legal inverse step, because the inverse head initially scans a neighboring cell. | §2 lists `(p₂*, q₂, p₁*, q₁, -d)` without spelling out operation order; §3 tracks both next-read and previously-written positions. | Fix the exact convention and prove a one-step inverse theorem before accepting the syntax. | critical-unresolved |
| `A-005` | “Inverse-image rules constitute a Turing machine” does not itself spell out forward determinism, backward uniqueness, or conflicts in the union used by coupling. | §2 uses an informal machine well-formedness test. | Define all three properties separately and prove coupling phase tags avoid rule conflicts. | unresolved |
| `A-006` | The history construction is incomplete. | §4 gives one representative relation and refers to unspecified control and working instructions. | Prove a complete cleaner history-log simulator first; later map it to Lecerf's marker construction if worthwhile. | source-confirmed |
| `A-007` | The history word records only nonidentity `τ` relations, while the index is written as one record per source time. | §4a(4) says each `r_k` represents a nonidentity relation but writes `r_{k_p}` for every step. | Specify whether identity relations count as machine steps, are compressed, or receive an explicit history token. | unresolved |
| `A-008` | “Return to the initial configuration” is trivial under reflexive reachability. | Theorem 1 intends a dynamic return. | Formalize with a nonempty run (`Reaches₁`) and prove any constructed return has positive length. | correction-required |
| `A-009` | “Epimorphism of codes” is not standard categorical epimorphism or plainly a surjective monoid homomorphism. | §1e gives only a source code and constrains target words to words of a code. | Use a deliberately paper-specific name and fields after source audit; never inherit categorical meaning from the term. | unresolved |
| `A-010` | The English bibliographic header says meeting of October 28, while its footnote and French source may indicate October 21. | Repository transcription contains both dates. | Verify against the scan; bibliographic only, no theorem impact. | minor-unresolved |
| `A-011` | §3 says “if `τ_min` is an isomorphism, MT is reversible,” but necessity and sufficiency depend on which configurations/rules are retained. | Reachability restriction is informal. | Formalize only the proved direction first; strengthen to iff only after a complete language argument. | unresolved |
| `A-012` | Deciding a supplied equation at a supplied finite `n` is generally computable for finite data, unlike deciding existence of some `n`. | The phrase “recursively unsolvable in `n`” is historically ambiguous in English. | State separately: evaluation/recognition for a supplied exponent, semidecidability of existence when applicable, and undecidability of existential orbit problems. | critical-unresolved |

## No-Cheating Audit Categories

Every completed stage must classify findings under these headings:

- **Proof holes:** `sorry`, `admit`, placeholder theorems, or hidden generated
  assumptions.
- **Axioms:** project-specific `axiom`, accidental classical/noncomputable use
  in an executable reduction, and axioms reported by `#print axioms`.
- **Semantic shortcuts:** zero-step return, `n = 0`, totalized partial maps,
  malformed-input escape hatches, or only one direction of a claimed iff.
- **Layer violations:** using a theorem statement as a simulation, using
  reversibility assumptions to obtain determinism silently, or importing audit
  code into public/runtime cores.
- **Source drift:** changing a paper claim without recording whether it is a
  correction, strengthening, weakening, or equivalent reformulation.

## Axiom Audit Table

There are no substantive project declarations yet.

| Lean declaration | Role | `#print axioms` result | Disposition |
|---|---|---|---|
| _none_ | Scaffold only | Not applicable | Await completed theorem modules |

For each headline theorem, record the exact command, Lean output, mathlib or
logical axioms present, and whether those axioms affect executability or trust.

## Scaffold Audit

- Numbered implementation stages created: none.
- Substantive definitions/proofs created: none.
- Minimal Lean root is an import smoke test only.
- Toolchain and mathlib pins are recorded in `DEPENDENCIES.md`.
- `lake update` generated the pinned manifest successfully on 2026-07-17.
- `lake build Lecerf`: passed, 831 jobs.
- `lake build`: passed, 831 jobs.
- Scan of project Lean sources for `sorry`, `admit`, `axiom`, and `unsafe`:
  no hits.
- Scaffold path/count checks and whitespace checks passed.
