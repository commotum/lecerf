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
| `A-004` | The printed sign-reversed quintuple is not a semantic inverse of a standard moving rule | §2 changes only the state tag. After write-then-move, the new head scans a neighbor rather than the written symbol. Checked `Machine.Audit.printedInverse_fails_on_moving_rule` gives a concrete counterexample | The tuple exists only in the non-public audit. Public `Rule.tapeAction` composes checked-write and move phases; `Rule.apply_eq_some_iff_undo_eq_some` proves the actual inverse step moves back before restoring | correction-required |
| `A-005` | “Inverse-image rules constitute a Turing machine” does not define determinism, backward uniqueness, or coupling conflicts | §2 leaves the machine well-formedness convention implicit. The checked merge audit has a deterministic input-key table and individually reversible rules but two predecessors for one output | `TableDeterministic`, `ForwardCompatible`, `BackwardCompatible`, `BackwardUnique step`, and `FiniteMachine.Reversible` are separate. `backwardCompatible_iff_backwardUnique` characterizes the global condition for a deterministic table | resolved-design |
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
| `A-018` | Mathlib's established halting predicate and its partial-recursive-to-TM construction use different code types | `ComputablePred.halting_problem` is over `Nat.Partrec.Code`; `Turing.PartrecToTM2.tr_eval` is over `Turing.ToPartrec.Code`. `ToPartrec.Code.exists_code` is existential, while the TM2→TM1 and TM1→TM0 support maps are explicitly `noncomputable` | Stage 3 supplies fixed primitive-recursive `universalEvalSearchStep`, a primitive-recursive start map, and exact halting iff as the replacement source. Do not claim an end-to-end finite compiler; Stage 6 must construct one or establish another explicit finite source | isolated-obligation |
| `A-019` | Mathlib's set-based uniquely-decodable predicate forgets repeated indices in an indexed family | `InformationTheory.UniquelyDecodable` is defined for a `Set (List α)`; Lecerf's code data are indexed | Relate it to project `IsIndexedCode` only together with injectivity of the generator family | resolved-design |
| `A-020` | Tape semantics and computable finite encodings pull in different directions | `Turing.Tape` has useful quotient-normalized semantics but no ready `Primcodable` instance. Stage-3 probes verified a canonical structural representation and an equivalence to the reference halves | `Side` structurally stores a nonblank farthest cell, giving unique trailing-blank normalization. `Tape`, `Config`, `Rule`, and `FiniteMachine` now have constructive `Primcodable` instances; a quotient bridge remains optional in a narrow audit leaf | resolved-design |
| `A-021` | Treating a partial equivalence's option-valued function as globally injective is false | Checked theorem `Audit.emptyReversibleStep_next_not_injective`: the empty `PEquiv` sends distinct Boolean inputs to `none` | Use `BackwardUnique`, i.e. left uniqueness only for successful steps; `ReversibleStep.backwardUnique` proves it | resolved-design |
| `A-022` | A reversible step does not make forward and reverse terminality or same-start halting pointwise equal | Checked single-edge audit: the target is forward-terminal but not reverse-terminal | Reverse paths with exchanged endpoints; require both appropriate endpoint terminal hypotheses in `mem_eval_next_iff_mem_eval_prev` | resolved-design |
| `A-023` | Semantic phase composition is not yet an ordinary finite phase-control machine | `Rule.tapeAction` composes a checked write and move `PEquiv`; `FiniteMachine.reverseStep` performs move-back/check/restore as one macro-step. A checked prototype generated `normal`/`move` rules and proved table determinism, but its use of `Finset.univ.toList` is explicitly noncomputable and its two-step correspondence remains unproved | Treat the checked atomic `PEquiv` theorem as the permitted cleaner equivalent result. An effective syntactic compiler must take an explicit complete symbol list or a concrete `Fin n` alphabet and prove the two-step iff | isolated-obligation |
| `A-024` | The implemented finite reverse-key condition has only a sufficient-direction theorem | `reverseTableCompatible_backwardCompatible` compiles; exact `backwardCompatible_iff_backwardUnique` quantifies over configurations | Before finite decision predicates, prove the converse pairwise characterization (same target implies common move and distinct writes for distinct rules) and its decidability, or use another checked finite validity criterion | isolated-obligation |

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

Stages 2 and 3 introduce the checked transition and finite-machine surfaces.

| Lean declaration | Role | `#print axioms` result | Disposition |
|---|---|---|---|
| `Lecerf.Transition.Step.successor_unique` | Forward determinism | no axioms | Fully constructive |
| `Lecerf.Transition.haltsFrom_iff_exists_reachable_terminal` | Halting characterization | `propext`, `Classical.choice`, `Quot.sound` | Standard Lean/mathlib axioms inherited from `Part`/evaluation semantics; no project axiom |
| `Lecerf.Transition.ReversibleStep.next_eq_some_iff_prev_eq_some` | One-step inverse law | `propext`, `Quot.sound` | Standard Lean/mathlib axioms; no project axiom |
| `Lecerf.Transition.ReversibleStep.reachable_iff_reverse_reachable` | Reflexive path reversal | `propext`, `Quot.sound` | Standard Lean/mathlib axioms; no project axiom |
| `Lecerf.Transition.ReversibleStep.strictlyReachable_iff_reverse_strictlyReachable` | Positive path reversal | `propext`, `Quot.sound` | Standard Lean/mathlib axioms; no project axiom |
| `Lecerf.Transition.ReversibleStep.mem_eval_next_iff_mem_eval_prev` | Endpoint evaluation reversal | `propext`, `Classical.choice`, `Quot.sound` | Standard Lean/mathlib axioms; endpoint terminal hypotheses are explicit |
| `Lecerf.Machine.Tape.undo_act` | Write/move inverse order | `propext` | Constructive data/proof surface modulo proposition extensionality; no project axiom |
| `Lecerf.Machine.Rule.apply_eq_some_iff_undo_eq_some` | Exact individual-rule inverse | `propext` | No project axiom; movement order is explicit in executable definitions |
| `Lecerf.Machine.FiniteMachine.step_eq_some_iff_reverseStep_eq_some` | Exact global forward/reverse iff under compatibility | `propext` | No project axiom |
| `Lecerf.Machine.FiniteMachine.backwardCompatible_iff_backwardUnique` | Whole-table reversibility characterization | `propext`, `Quot.sound` | Standard Lean quotient axiom inherited through relational infrastructure; no project axiom |
| `Lecerf.Machine.Source.universalEvalSearchStep_halts_iff_eval_dom` | Effective source halting equivalence | `propext`, `Classical.choice`, `Quot.sound` | Standard mathlib `Part`/transition dependencies; no project axiom |
| `Lecerf.Machine.Source.universalEvalSearchStep_primrec` | Primitive-recursive fixed source step | `propext`, `Classical.choice`, `Quot.sound` | The proof uses mathlib's encoded computability infrastructure; the declaration is constructive runtime data plus a standard proof, with no project axiom |

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
- `lake build Lecerf` passed with 831 jobs.
- Lean proof-hole and shortcut scans, documentation whitespace checks, changed
  Lean/configuration path checks, and `git diff --check` passed.
- No substantive declaration exists to audit with `#print axioms`; the stage
  boundary is documentation only.

### Stage 2 transition API

- Added `Lecerf.Transition.Core`, `Reversible`, `Audit`, and `API`; the public
  root imports `API`, while `Audit` remains non-public.
- Focused Core, Reversible, and Audit builds passed; the public/API build and
  full `lake build` passed with 660 jobs.
- A root-import API probe checked the exact public declaration signatures and
  was deleted.
- The Lean proof-hole/axiom/unsafe scan, noncomputable/classical-source scan,
  out-of-scope import scan, whitespace check, and `git diff --check` passed.
- Documentation scan hits are guardrail prose only. The exact `#print axioms`
  results are in the table above; no project-specific axiom was introduced.

### Stage 3 finite-machine API

- Added canonical `Machine.Tape`, finite `Machine.Core`, repaired
  `Machine.Reversible`, effective `Machine.SourceBridge`, non-public
  `Machine.Audit`, and thin `Machine.API`; the public root imports the API but
  not the diagnostic leaf.
- Focused builds passed for Tape, Core, Reversible, SourceBridge, and Audit.
  The API/root adjacent build passed; full `lake build` passed with 830 jobs.
- Executable audit examples check normalization and the exact read-write-move
  equation. `printedInverse_fails_on_moving_rule` certifies the paper-tuple
  counterexample, and `mergeMachine_not_reversible` certifies that local rule
  invertibility plus table determinism is not whole-machine reversibility.
- A temporary public-import signature/axiom probe checked the headline
  declarations and was deleted. Exact representative results appear in the
  table above; no project-specific axiom was introduced.
- Lean scans over project machine sources found no `sorry`, `admit`, `axiom`,
  `unsafe`, `noncomputable`, or explicit `Classical.choice`. Boundary scans
  found no history simulator, code layer, iterate API, many-one reduction, or
  undecidability conclusion in Stage 3.
- Import inspection confirms the canonical tape core depends only on
  `Primrec.List`; partial-recursive code is isolated in `SourceBridge`; and
  `Audit` is not re-exported. Trailing-whitespace and `git diff --check`
  passed.
- The finite compiler from `Nat.Partrec.Code` to `FiniteMachine` remains
  explicitly open under `A-018`. The replacement source theorem does not
  discharge that future reduction arrow.
