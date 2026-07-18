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
| `A-005` | “Inverse-image rules constitute a Turing machine” does not define determinism, backward uniqueness, or coupling conflicts | §2 leaves the machine well-formedness convention implicit. The checked merge audit has a deterministic input-key table and individually reversible rules but two predecessors for one output | `TableDeterministic`, `ForwardCompatible`, `BackwardCompatible`, `BackwardUnique step`, and `FiniteMachine.Reversible` are separate. `backwardCompatible_iff_backwardUnique` characterizes the global condition for a deterministic table. Stage 5 uses disjoint phase tags and proves exact ambient inverse laws for both couplings rather than assuming their union is conflict-free | resolved-design |
| `A-006` | The history construction is incomplete | §4 says it gives only the principle and spells out one representative relation, omitting the other rules and invariants | Stage 4 supplies a complete abstract simulator: full predecessor push, checked pop, exact `PEquiv`, generated-history invariant, reflection, and halting iff. Connecting it to the historical marker/tape scheme remains later work | source-confirmed |
| `A-007` | The source says every history token represents a nonidentity relation while indexing one token per source time step | §4a(4) does not specify whether identity relations are compressed or count as steps | The clean simulator records the complete predecessor for every successful source transition. `history_length_of_forward` proves one new entry per actual step; word-copy identities are not source-machine transitions | resolved-design |
| `A-008` | “Return to the initial configuration” is trivial under reflexive reachability | Theorem 1 describes a dynamic return | Define return with `StateTransition.Reaches₁` and prove the constructed run has positive length | correction-required |
| `A-009` | “Epimorphism of codes” is neither a standard categorical epi nor necessarily a surjective monoid map | §1e requires the source indexed family to equal a code but only requires each target word to belong to some code; §3 intentionally repeats target relation words | Define a paper-specific source code, target code, and selector that may repeat and need not be onto. State injectivity/surjectivity/bijectivity only as separate proved properties | resolved-design |
| `A-010` | The header and note footnote use different October dates | Both scans show header session 28 October and footnote presentation 21 October | Retain both metadata facts; use 21 October when naming the note's presentation date | minor-source-note |
| `A-011` | `τ_min` code-isomorphism and machine reversibility are not shown equivalent | French §3 prints only the implication from code isomorphism to reversibility after conditional pruning | Formalize only the printed direction; an iff requires a separate reachable-language theorem | resolved-design |
| `A-012` | “Recursively unsolvable in `n`” can be misread as inability to check a supplied finite exponent | Theorem 2 follows existential machine reachability and takes arbitrary given finite `w, θ`; a fixed instance has a constant truth value | Use a uniform existential positive-orbit predicate. Separately prove supplied-exponent evaluation decidable/computable and, where effective enumeration is available, yes-instance semidecidability | resolved-design |
| `A-013` | English §1e inserts the technical phrase “complete code” | French and the page-2 scan read `est bien un code`, “is indeed a code,” not `code complet` | Do not introduce maximal/complete-code theory or a completeness hypothesis | correction-required |
| `A-014` | The French code definition calls ordered factorization data an `ensemble d'indices` | Multiplication order `mᵢ₁ … mᵢₚ` makes the indices a finite sequence, not an unordered set | Formalize factors as `FreeMonoid I`/lists | correction-required |
| `A-015` | The printed history invariant has an inconsistent base case | §4a(3) gives `u₀,₀ = λv₀μν`, hence empty `w₀`; §4a(4), stated for every `i`, gives `w₀ = b²b = b³` | `History.Config.initial` has an explicit empty list, and `Valid.history_eq_nil_iff` proves that a generated empty history is exactly the initial checkpoint. The departure is intentional | correction-required |
| `A-016` | §4a(7) does not itself prove both directions of the return/extra-target reductions | The direct clause gives extra-target passage only after the starred initial; the following prose says the behavior can be conditioned on halting but supplies no gadget proof | Stage 5 supplies complete abstract gadgets. `Coupling.History.target_strictlyReachable_iff_halts` and `positiveReturn_iff_halts` prove both directions, with structural target distinctness and positive rather than reflexive return. Compiling these gadgets to a finite tape machine remains separate under `A-017`/`A-025` | resolved-design |
| `A-017` | A semantic simulation theorem is insufficient for a computability reduction | The paper never provides finite encodings or proves its construction effective | Stages 4–5 prove semantic iff theorems and joint primitive-recursive interpreters/endpoints for abstract history and coupling, including an existing `FiniteMachine` description. A later finite-machine reduction must still construct a finite target description, prove validity, and establish the final iff | isolated-obligation |
| `A-018` | Mathlib's established halting predicate and its partial-recursive-to-TM construction use different code types | `ComputablePred.halting_problem` is over `Nat.Partrec.Code`; `Turing.PartrecToTM2.tr_eval` is over `Turing.ToPartrec.Code`. `ToPartrec.Code.exists_code` is existential, while the TM2→TM1 and TM1→TM0 support maps are explicitly `noncomputable` | Stages 3–5 supply the primitive-recursive universal search, exact source/history/coupling semantic iff theorems, and primitive-recursive existing-machine interpreters. They still do not compile `Nat.Partrec.Code` to a finite project machine; Stage 6 must construct that arrow or establish another explicit finite source | isolated-obligation |
| `A-019` | Mathlib's set-based uniquely-decodable predicate forgets repeated indices in an indexed family | `InformationTheory.UniquelyDecodable` is defined for a `Set (List α)`; Lecerf's code data are indexed | Relate it to project `IsIndexedCode` only together with injectivity of the generator family | resolved-design |
| `A-020` | Tape semantics and computable finite encodings pull in different directions | `Turing.Tape` has useful quotient-normalized semantics but no ready `Primcodable` instance. Stage-3 probes verified a canonical structural representation and an equivalence to the reference halves | `Side` structurally stores a nonblank farthest cell, giving unique trailing-blank normalization. `Tape`, `Config`, `Rule`, and `FiniteMachine` now have constructive `Primcodable` instances; a quotient bridge remains optional in a narrow audit leaf | resolved-design |
| `A-021` | Treating a partial equivalence's option-valued function as globally injective is false | Checked theorem `Audit.emptyReversibleStep_next_not_injective`: the empty `PEquiv` sends distinct Boolean inputs to `none` | Use `BackwardUnique`, i.e. left uniqueness only for successful steps; `ReversibleStep.backwardUnique` proves it | resolved-design |
| `A-022` | A reversible step does not make forward and reverse terminality or same-start halting pointwise equal | Checked single-edge audit: the target is forward-terminal but not reverse-terminal | Reverse paths with exchanged endpoints; require both appropriate endpoint terminal hypotheses in `mem_eval_next_iff_mem_eval_prev` | resolved-design |
| `A-023` | Semantic phase composition is not yet an ordinary finite phase-control machine | `Rule.tapeAction` composes a checked write and move `PEquiv`; `FiniteMachine.reverseStep` performs move-back/check/restore as one macro-step. A checked prototype generated `normal`/`move` rules and proved table determinism, but its use of `Finset.univ.toList` is explicitly noncomputable and its two-step correspondence remains unproved | `FiniteMachine.step_uniform_primrec` now proves source-table interpretation effective without enumeration, but it does not generate phase rules. Treat the atomic `PEquiv` as the cleaner theorem; a syntactic compiler still needs explicit alphabet data and a two-step iff | isolated-obligation |
| `A-024` | The implemented finite reverse-key condition has only a sufficient-direction theorem | `reverseTableCompatible_backwardCompatible` compiles; exact `backwardCompatible_iff_backwardUnique` quantifies over configurations | Before finite decision predicates, prove the converse pairwise characterization (same target implies common move and distinct writes for distinct rules) and its decidability, or use another checked finite validity criterion | isolated-obligation |
| `A-025` | An effective abstract history interpreter is not automatically a generated conventional finite Turing machine | `finiteForward_uniform_primrec` and `finiteBackward_uniform_primrec` interpret a finite source description, but `History.Config` contains an unbounded `List` of source configurations | Treat Stage 4 as the permitted cleaner equivalent reversible simulation. A finite tape/microstate compiler must separately encode the log and prove step/halting correspondence before finite-machine undecidability | isolated-obligation |
| `A-026` | “Checkpoint uniqueness” cannot mean that a source configuration has only one valid history | The checked Boolean-cycle audit revisits `false` with histories `[]` and `[true, false]` | State uniqueness at equal elapsed/history length (`Valid.eq_of_history_length_eq`) and uniqueness of the empty initial checkpoint; retain longer cycle histories | resolved-design |
| `A-027` | Blindly popping a stored predecessor is not an inverse on malformed ambient history states | `History.Audit.malformed_predecessor_rejected` checks a predecessor that does not step to the recorded current state | `History.backward` recomputes and validates the edge before popping; `forward_eq_some_iff_backward_eq_some` proves the exact inverse law without assuming `Valid` | resolved-design |
| `A-028` | Closing only one privileged reverse-initial state would make the return gadget depend on runtime equality with a reduction input and can break the ambient inverse law on other components | The paper sketches conditioning behavior at one initial configuration but gives no total rule family or global reversibility argument | `Coupling.returnGadget` uniformly closes every inverse-terminal state to its matching forward-tagged state. `returnNext_eq_some_iff_returnPrev_eq_some` proves the exact ambient law; `exists_returnNext`, `exists_returnPrev`, and `returnGadget_not_terminal` expose totality | resolved-design |
| `A-029` | The closed coupling is total, so it cannot itself serve as the halting machine in a halting reduction | Both branches of `returnNext` succeed, formalized by `exists_returnNext` and `returnGadget_not_terminal`; the open `turnaround` instead stops at the reverse-initial checkpoint | Use the Stage-4 partial history simulator for halting, the open coupling for distinct-target reachability, and the closed gadget only for positive return. Do not conflate these target predicates | resolved-design |

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
indexed-code predicate, complete predecessor lists for the first clean history
simulator, phase-tagged coupling, and a finite-support tape model.

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

Stages 2 through 5 introduce the checked transition, finite-machine, abstract
history-simulation, and forward/reverse coupling surfaces.

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
| `Lecerf.Machine.History.forward_eq_some_iff_backward_eq_some` | Exact checked-push/pop inverse law | `propext`, `Quot.sound` | Standard Lean/mathlib axioms only; no project axiom or invariant assumption |
| `Lecerf.Machine.History.reachable_iff_valid` | Exact reachable-history invariant | `propext`, `Quot.sound` | Initialization and preservation are proved from execution; no project axiom |
| `Lecerf.Machine.History.Valid.eq_of_history_length_eq` | Checkpoint uniqueness at equal elapsed length | `propext`, `Classical.choice`, `Quot.sound` | Standard mathlib/logical dependencies; the cycle-safe length qualifier is explicit |
| `Lecerf.Machine.History.haltsFrom_forward_iff` | History simulation halting preservation/reflection | `propext`, `Classical.choice`, `Quot.sound` | Standard transition/`Part` dependencies; both directions are proved |
| `Lecerf.Machine.FiniteMachine.step_uniform_primrec` | Joint finite-description interpreter | `propext`, `Classical.choice`, `Quot.sound` | Runtime definition is constructive and alphabet-enumeration-free; proof uses standard encoded-computability infrastructure |
| `Lecerf.Machine.History.finiteForward_uniform_primrec` | Joint effective finite-source history execution | `propext`, `Classical.choice`, `Quot.sound` | Effective abstract interpreter, not a generated conventional finite tape machine |
| `Lecerf.Machine.History.universalHistory_halts_iff_eval_dom` | Effective universal-source history halting iff | `propext`, `Classical.choice`, `Quot.sound` | Composes checked Stage-3 and Stage-4 equivalences; no project axiom |
| `Lecerf.Machine.Coupling.turnaround` | Open phase-tagged reversible coupling | `propext`, `Quot.sound` | Exact `PEquiv` assembled from executable forward, terminal-switch, and inverse branches; no project axiom |
| `Lecerf.Machine.Coupling.returnGadget` | Uniformly closed reversible return gadget | `propext`, `Quot.sound` | Exact `PEquiv`; every inverse-terminal component is closed uniformly |
| `Lecerf.Machine.Coupling.History.target_strictlyReachable_iff_halts` | Distinct-target reachability iff source halting | `propext`, `Classical.choice`, `Quot.sound` | Both directions proved through generated-state reflection; target inequality is structural |
| `Lecerf.Machine.Coupling.History.positiveReturn_iff_halts` | Positive return iff source halting | `propext`, `Classical.choice`, `Quot.sound` | Uses exact predecessor uniqueness at the return boundary; reflexive reachability is excluded |
| `Lecerf.Machine.Coupling.History.universalReturnNext_primrec` | Primitive-recursive fixed universal return step | `propext`, `Classical.choice`, `Quot.sound` | Interpreter effectivity only; no finite output compiler is inferred |
| `Lecerf.Machine.Coupling.History.universalTarget_strictlyReachable_iff_eval_dom` | Universal evaluation domain iff distinct-target reachability | `propext`, `Classical.choice`, `Quot.sound` | Semantic specialization of the checked universal source; not yet a finite-description reduction |
| `Lecerf.Machine.Coupling.History.universalPositiveReturn_iff_eval_dom` | Universal evaluation domain iff positive return | `propext`, `Classical.choice`, `Quot.sound` | Semantic specialization; no `ManyOneReducible` or undecidability conclusion is claimed |

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

### Stage 4 reversible history simulation

- Added `Machine.Effectivity` and
  `Machine.History.{Core,Correctness,Computable,Audit,API}`. The public machine
  API re-exports the history API but not either diagnostic leaf.
- The runtime stores the complete predecessor on each successful source step.
  Its checked inverse recomputes the stored edge, and
  `forward_eq_some_iff_backward_eq_some` constructs an exact `PEquiv` on the
  whole ambient state space, not only on well-formed histories.
- `reachable_iff_valid` proves the generated invariant exactly equivalent to
  reachability. Forward simulation, source projection/reflection, history
  growth, cycle-safe checkpoint uniqueness, reverse retracing, terminality,
  and halting iff all compile. Audit examples check merge disambiguation,
  malformed history rejection, and cyclic revisits with longer histories.
- `FiniteMachine.step_uniform_primrec` proves concrete first-match execution
  primitive recursive jointly in its finite description. Generic and finite
  forward/checked-backward history interpreters and their start encodings are
  primitive recursive. The universal evaluator-search specialization has an
  exact halting iff with `Nat.Partrec.Code.eval`.
- The abstract state contains an unbounded predecessor list. No conventional
  finite tape-rule compiler, coupling gadget, many-one reduction, or
  undecidability theorem is claimed; `A-018`, `A-023`, `A-024`, and `A-025`
  remain open boundaries.
- Focused builds passed for Effectivity (820 jobs), History Core (821),
  Correctness (822), Computable (830), and Audit (831). Public API/root builds
  and full `lake build` passed with 835 jobs.
- A temporary root-import axiom probe produced the exact Stage-4 rows above
  and was deleted. Lean scans found no project `sorry`, `admit`, `axiom`,
  `unsafe`, `noncomputable`, or explicit `Classical.choice`; boundary scans
  found no future coupling, reduction, code, or iterate layer. Whitespace and
  `git diff --check` passed.

### Stage 5 forward/reverse coupling

- Added `Machine.Coupling.{Core,Correctness,Computable,Audit,API}`. The public
  machine API re-exports `Coupling.API`; the executable/axiom audit leaf remains
  non-public.
- The open `turnaround` and closed `returnGadget` satisfy exact ambient
  forward/inverse iff laws. Audit examples cover halt-now, one-step halting,
  and a nonhalting loop, including negative reachability and return checks.
- `History.target_strictlyReachable_iff_halts` and
  `History.positiveReturn_iff_halts` prove both semantic reduction directions.
  The former uses a constructor-distinct target and positive reachability; the
  latter uses `PositiveReturn` and exact predecessor uniqueness. Checked log
  growth independently rules out a forward-history cycle.
- Generic four-way coupling interpreters, history specializations, existing
  finite-description specializations, and universal endpoints/steps are
  primitive recursive. The two universal semantic iff corollaries terminate
  at `Nat.Partrec.Code.eval` domain membership; no finite output machine,
  validity predicate, many-one reduction, or undecidability conclusion is
  present.
- Focused `lake build Lecerf.Machine.Coupling.Audit` passed with 834 jobs.
  Adjacent coupling/machine/root API builds passed, and full `lake build`
  passed with 839 jobs.
- Lean scans found no project proof hole, axiom declaration, proof-bypassing
  `unsafe`, `noncomputable`, or explicit `Classical.choice`. Out-of-stage token
  and public-import scans, trailing-whitespace checks, and `git diff --check`
  passed. The exact `#print axioms` results are recorded above and contain only
  standard Lean/mathlib axioms.
