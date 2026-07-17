# Audit, Corrections, and Trust Log

This ledger distinguishes source evidence, mathematical inference, and the
formal disposition. A correction is never presented as text printed by the
paper, and a planned theorem is never presented as a checked Lean result.

Status vocabulary:

- `source-confirmed`: directly settled by the scans;
- `correction-required`: the printed/translated statement is unusable as a
  formal target and the repair is fixed;
- `resolved-design`: the source is incomplete or nonstandard and Stage 1 fixes
  a formal interpretation;
- `isolated-obligation`: a later stage has a precise test or proof obligation;
  and
- `minor-source-note`: recorded without mathematical impact.

## Current Correction and Uncertainty Log

| ID | Issue | Evidence | Formal disposition | Status |
|---|---|---|---|---|
| `A-001` | English §1b omits “at most one,” turning unique decipherability into an existence/generation assertion | French §1b and the page-1 scan read `il existe au plus un ensemble d'indices` | Define codehood by at-most-one ordered factorization, equivalently injectivity of the induced free-monoid morphism | correction-required |
| `A-002` | If `n = 0`, `w = θⁿ(w)` is true for every `w` | The paper says `n ∈ N` but never defines `N`; its empty-word observation concerns all iterates and does not settle whether zero is included | State fixed orbit as `∃ k, iterate θ (k + 1) w = some w`; label this a necessary disambiguation/repair | correction-required |
| `A-003` | `θⁿ` is not automatically composable because `θ` maps one generated submonoid to another | §1b gives domain `φ(A†)` and codomain `ψ(A†)` without equating them | Use an intrinsic submonoid equivalence plus an ambient `PEquiv`; iterate by partial composition and require a `some` result | resolved-design |
| `A-004` | The printed sign-reversed quintuple is not a semantic inverse of a standard moving rule | §2 changes only the state tag. After write-then-move, the new head scans a neighbor rather than the written symbol. §3's displayed `+1` relation confirms the marker moves past the written symbol | Preserve the tuple only as syntax. Use conventional read-write-move semantics and compile a moving rule into reversible write/move phases, then prove the actual inverse-step iff | correction-required |
| `A-005` | “Inverse-image rules constitute a Turing machine” does not define determinism, backward uniqueness, or coupling conflicts | §2 leaves the machine well-formedness convention implicit | Define rule-table determinism, global successful-output injectivity/partial inverse, and phase disjointness separately | resolved-design |
| `A-006` | The history construction is incomplete | §4 says it gives only the principle and spells out one representative relation, omitting the other rules and invariants | Prove a complete clean history-log simulator first; any theorem connecting it to the historical marker scheme is later work | source-confirmed |
| `A-007` | The source says every history token represents a nonidentity relation while indexing one token per source time step | §4a(4) does not specify whether identity relations are compressed or count as steps | Record one explicit token for every actual source transition; identities used only to copy untouched word symbols are not source-machine transitions | resolved-design |
| `A-008` | “Return to the initial configuration” is trivial under reflexive reachability | Theorem 1 describes a dynamic return | Define return with `StateTransition.Reaches₁` and prove the constructed run has positive length | correction-required |
| `A-009` | “Epimorphism of codes” is neither a standard categorical epi nor necessarily a surjective monoid map | §1e requires the source indexed family to equal a code but only requires each target word to belong to some code; §3 intentionally repeats target relation words | Define a paper-specific source code, target code, and selector that may repeat and need not be onto. State injectivity/surjectivity/bijectivity only as separate proved properties | resolved-design |
| `A-010` | The header and note footnote use different October dates | Both scans show header session 28 October and footnote presentation 21 October | Retain both metadata facts; use 21 October when naming the note's presentation date | minor-source-note |
| `A-011` | `τ_min` code-isomorphism and machine reversibility are not shown equivalent | French §3 prints only the implication from code isomorphism to reversibility after conditional pruning | Formalize only the printed direction; an iff requires a separate reachable-language theorem | resolved-design |
| `A-012` | “Recursively unsolvable in `n`” can be misread as inability to check a supplied finite exponent | Theorem 2 follows existential machine reachability and takes arbitrary given finite `w, θ`; a fixed instance has a constant truth value | Use a uniform existential positive-orbit predicate. Separately prove supplied-exponent evaluation decidable/computable and, where effective enumeration is available, yes-instance semidecidability | resolved-design |
| `A-013` | English §1e inserts the technical phrase “complete code” | French and the page-2 scan read `est bien un code`, “is indeed a code,” not `code complet` | Do not introduce maximal/complete-code theory or a completeness hypothesis | correction-required |
| `A-014` | The French code definition calls ordered factorization data an `ensemble d'indices` | Multiplication order `mᵢ₁ … mᵢₚ` makes the indices a finite sequence, not an unordered set | Formalize factors as `FreeMonoid I`/lists | correction-required |
| `A-015` | The printed history invariant has an inconsistent base case | §4a(3) gives `u₀,₀ = λv₀μν`, hence empty `w₀`; §4a(4), stated for every `i`, gives `w₀ = b²b = b³` | Use an explicit empty initial history and state the later history format only after actual steps; document this departure | correction-required |
| `A-016` | §4a(7) does not itself prove both directions of the return/extra-target reductions | The direct clause gives extra-target passage only after the starred initial; the following prose says the behavior can be conditioned on halting but supplies no gadget proof | Construct explicit reversible gadgets and prove halt iff positive return / distinct reachability | isolated-obligation |
| `A-017` | A semantic simulation theorem is insufficient for a computability reduction | The paper never provides finite encodings or proves its construction effective | Every reduction arrow must include a computable instance map, validity proof, and preservation/reflection iff | isolated-obligation |
| `A-018` | Mathlib's established halting predicate and its partial-recursive-to-TM construction use different code types | `ComputablePred.halting_problem` is over `Nat.Partrec.Code`; `Turing.PartrecToTM2.tr_eval` is over `Turing.ToPartrec.Code` | Do not claim an existing end-to-end bridge. Stage 3 must implement a computable syntax compiler/semantic iff, prove an undecidability source for `ToPartrec.Code`, or select another explicit interpreter route | isolated-obligation |
| `A-019` | Mathlib's set-based uniquely-decodable predicate forgets repeated indices in an indexed family | `InformationTheory.UniquelyDecodable` is defined for a `Set (List α)`; Lecerf's code data are indexed | Relate it to project `IsIndexedCode` only together with injectivity of the generator family | resolved-design |
| `A-020` | Tape semantics and computable finite encodings pull in different directions | `Turing.Tape` has useful blank-normalized semantics, but Stage-1 inspection did not find a ready `Primcodable` instance for it | Fix doubly infinite finite-support semantics now. In Stage 3, reuse `Turing.Tape` only if an executable canonical encoding is supplied; otherwise define a canonical finite-support tape and bridge it | isolated-obligation |

## Source Corrections Versus Design Choices

Material changes to the paper are:

- positive rather than possibly-zero iteration (`A-002`);
- a partial rather than silently total ambient iterate (`A-003`);
- repaired phased inverse execution rather than the printed moving inverse
  tuple (`A-004`);
- positive return (`A-008`);
- removal of the English-only completeness claim (`A-013`); and
- a consistent empty history base case (`A-015`).

Independent representation choices, not claims about the historical text,
are `PEquiv` for generic reversible steps, `FreeMonoid` for words, a custom
indexed-code predicate, phase-tagged coupling, and a finite-support tape model.

## No-Cheating Audit Categories

Every completed stage must classify findings under these headings:

- **Proof holes:** `sorry`, `admit`, placeholder theorems, or hidden generated
  assumptions.
- **Axioms:** project-specific `axiom`, accidental classical/noncomputable use
  in an executable reduction, and axioms reported by `#print axioms`.
- **Semantic shortcuts:** zero-step return, `n = 0`, totalized partial maps,
  malformed-input escape hatches, or only one direction of a claimed iff.
- **Layer violations:** using a theorem statement as a simulation, silently
  obtaining reversibility from determinism, or importing audit code into
  public/runtime cores.
- **Source drift:** changing a paper claim without recording whether it is a
  correction, strengthening, weakening, or equivalent reformulation.

## Axiom Audit Table

There are no substantive project declarations yet.

| Lean declaration | Role | `#print axioms` result | Disposition |
|---|---|---|---|
| _none_ | Scaffold/source audit only | Not applicable | Await completed theorem modules |

For every later headline theorem, record the exact command, Lean output,
mathlib or logical axioms present, and whether those axioms affect
executability or trust.

## Validation History

### Scaffold

- Lean `4.31.0` and mathlib commit
  `fabf563a7c95a166b8d7b6efca11c8b4dc9d911f` are pinned.
- `lake update` generated the pinned manifest on 2026-07-17.
- `lake build Lecerf` and `lake build` passed with 831 jobs.
- The initial project Lean-source scan found no `sorry`, `admit`, `axiom`, or
  `unsafe`.

### Stage 1 source audit

- Bilingual Markdown and all four French/English scan pages were compared.
- A temporary import/`#check` probe validated the exact pinned declaration
  names listed in `DEPENDENCIES.md`; it compiled successfully and was deleted.
- Final build, shortcut, whitespace, and diff checks are recorded in
  `1-SOURCE-AUDIT.md` once the stage closes.
