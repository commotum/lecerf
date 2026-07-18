# Audit, Corrections, and Trust Log

This ledger distinguishes source evidence, mathematical inference, and the
formal disposition. A correction is never presented as text printed by the
paper, and a planned theorem is never presented as a checked Lean result.

Status vocabulary:

- `source-confirmed`: directly settled by the scans;
- `correction-required`: a printed/translated statement or a checked
  implementation/trust defect required repair, and the repair is recorded;
- `resolved-design`: the source is incomplete or nonstandard and Stage 1 fixes
  a formal interpretation;
- `isolated-obligation`: an explicit historical or generalization follow-up
  has a precise proof obligation;
  and
- `minor-source-note`: recorded without mathematical impact.

## Current Correction and Uncertainty Log

| ID | Issue | Evidence | Formal disposition | Status |
|---|---|---|---|---|
| `A-001` | English §1b omits “at most one,” turning unique decipherability into an existence/generation assertion | French §1b and the page-1 scan read `il existe au plus un ensemble d'indices` | Stage 7 defines `IsIndexedCode c` as injectivity of `FreeMonoid.lift c`, hence at-most-one ordered factorization. `isIndexedCode_iff_injective_and_uniquelyDecodable` checks the exact bridge to mathlib's set predicate | correction-required |
| `A-002` | If `n = 0`, `w = θⁿ(w)` is true for every `w` | The paper says `n ∈ N` but never defines `N`; its empty-word observation concerns all iterates and does not settle whether zero is included | `PositiveFixedOrbitYes` and `DistinctOrbitYes` quantify over an exact exponent `k + 1`; `PositiveIterateAtYes` explicitly requires its supplied exponent to be nonzero. The Stage-9 zero-exponent audit checks rejection directly | correction-required |
| `A-003` | `θⁿ` is not automatically composable because `θ` maps one generated submonoid to another | §1b gives domain `φ(A†)` and codomain `ψ(A†)` without equating them | Stage 7 implements `CodeIso` as an intrinsic generated-submonoid equivalence and defines `PEquiv.iterate` by literal partial composition. Stage 9's `checkedExactIterate_eq_stepCodeIso_iterate` proves that executable exact iteration is this partial semantic iterate; failure remains `none` through every extension | resolved-design |
| `A-004` | The printed sign-reversed quintuple is not a semantic inverse of a standard moving rule | §2 changes only the state tag. After write-then-move, the new head scans a neighbor rather than the written symbol. Checked `Machine.Audit.printedInverse_fails_on_moving_rule` gives a concrete counterexample | The tuple exists only in the non-public audit. Public `Rule.tapeAction` composes checked-write and move phases; `Rule.apply_eq_some_iff_undo_eq_some` proves the actual inverse step moves back before restoring | correction-required |
| `A-005` | “Inverse-image rules constitute a Turing machine” does not define determinism, backward uniqueness, or coupling conflicts | §2 leaves the machine well-formedness convention implicit. The checked merge audit has a deterministic input-key table and individually reversible rules but two predecessors for one output | `TableDeterministic`, pairwise input/output separation, `BackwardUnique step`, and whole-machine `Reversible` remain separate. Stage 6 proves `TwoTape.FiniteMachine.SyntacticallyReversible` for each generated table; its soundness theorem supplies semantic reversibility rather than inferring it from local rule inverses | resolved-design |
| `A-006` | The history construction is incomplete | §4 says it gives only the principle and spells out one representative relation, omitting the other rules and invariants | Stage 4 supplies a complete abstract simulator: full predecessor push, checked pop, exact `PEquiv`, generated-history invariant, reflection, and halting iff. Connecting it to the historical marker/tape scheme remains an explicit follow-up | source-confirmed |
| `A-007` | The source says every history token represents a nonidentity relation while indexing one token per source time step | §4a(4) does not specify whether identity relations are compressed or count as steps | The clean simulator records the complete predecessor for every successful source transition. `history_length_of_forward` proves one new entry per actual step; word-copy identities are not source-machine transitions | resolved-design |
| `A-008` | “Return to the initial configuration” is trivial under reflexive reachability | Theorem 1 describes a dynamic return | `PositiveReturn` and `ReturnYes` use `StateTransition.Reaches₁`. `return_positiveReturn_iff_source_halts` proves the constructed positive cycle exactly, and `partrecHalts0_manyOne_returnYes` packages the computable reduction | correction-required |
| `A-009` | “Epimorphism of codes” is neither a standard categorical epi nor necessarily a surjective monoid map | §1e requires the source indexed family to equal a code but only requires each target word to belong to some code; §3 intentionally repeats target relation words | Stage 7's `PaperCodeEpi` bundles source/target codes, an unrestricted selector, and its generated-submonoid morphism. `PaperCodeEpi.ofCodes` imposes neither selector injectivity nor surjectivity, and the audit checks a selector that both repeats and omits targets | resolved-design |
| `A-010` | The header and note footnote use different October dates | Both scans show header session 28 October and footnote presentation 21 October | Retain both metadata facts; use 21 October when naming the note's presentation date | minor-source-note |
| `A-011` | `τ_min` code-isomorphism and machine reversibility are not shown equivalent | French §3 prints only the implication from code isomorphism to reversibility after conditional pruning | The current library proves an exact backward-uniqueness characterization only for its cleaner whole-configuration edge schema. The printed `τ_min` construction and its one-way implication remain an explicit historical formalization obligation; no present declaration is named as that result | isolated-obligation |
| `A-012` | “Recursively unsolvable in `n`” can be misread as inability to check a supplied finite exponent | Theorem 2 follows existential machine reachability and takes arbitrary given `w, θ`; a fixed instance has a constant truth value | `positiveIterateAtYes_primrec`/`positiveIterateAtYes_computablePred` prove uniform recognition of a supplied nonzero exponent. `positiveFixedOrbitYes_re` and `distinctOrbitYes_re` prove existential yes-instances semidecidable, while the separate `_not_computable` theorems rule out total existence decision procedures | resolved-design |
| `A-013` | English §1e inserts the technical phrase “complete code” | French and the page-2 scan read `est bien un code`, “is indeed a code,” not `code complet` | Do not introduce maximal/complete-code theory or a completeness hypothesis | correction-required |
| `A-014` | The French code definition calls ordered factorization data an `ensemble d'indices` | Multiplication order `mᵢ₁ … mᵢₚ` makes the indices a finite sequence, not an unordered set | Formalize factors as `FreeMonoid I`/lists | correction-required |
| `A-015` | The printed history invariant has an inconsistent base case | §4a(3) gives `u₀,₀ = λv₀μν`, hence empty `w₀`; §4a(4), stated for every `i`, gives `w₀ = b²b = b³` | `History.Config.initial` has an explicit empty list, and `Valid.history_eq_nil_iff` proves that a generated empty history is exactly the initial checkpoint. The departure is intentional | correction-required |
| `A-016` | §4a(7) does not itself prove both directions of the return/extra-target reductions | The direct clause gives extra-target passage only after the starred initial; the following prose says the behavior can be conditioned on halting but supplies no gadget proof | Stage 5 supplies complete abstract gadgets. Stage 6 compiles cleaner finite two-tape versions and proves `turnaround_bottom_strictlyReachable_iff_source_halts` and `return_positiveReturn_iff_source_halts`, including structural target distinctness and positive rather than reflexive return. Correspondence with Lecerf's literal one-tape marker construction remains separate | resolved-design |
| `A-017` | A semantic simulation theorem is insufficient for a computability reduction | The paper never provides finite encodings or proves its construction effective | Stage 6 uses three fixed closed finite two-tape tables, proves their syntactic validity and semantic reversibility, proves the varying start/target maps primitive recursive, establishes all three semantic iff theorems, and packages explicit `ManyOneReducible` witnesses. No theorem-level simulator is substituted for an executable reduction | resolved-design |
| `A-018` | Mathlib's established halting predicate and its partial-recursive-to-TM construction use different code types | `ComputablePred.halting_problem` is over `Nat.Partrec.Code`; `Turing.PartrecToTM2.tr_eval` is over `Turing.ToPartrec.Code`. `ToPartrec.Code.exists_code` is existential, while the TM2→TM1 and TM1→TM0 support maps are explicitly `noncomputable` | `Compiler.UniversalSource` chooses one closed universal `ToPartrec.Code`, then `FiniteSource` checks its TM2→TM1→TM0 lowering and finite support. The varying `Nat.Partrec.Code` is data on the start tape: `encodedInput`, `initial_primrec`, and the three Stage-6 reduction maps are primitive recursive. Classical choice and finite encodings affect only fixed constants | resolved-design |
| `A-019` | Mathlib's set-based uniquely-decodable predicate forgets repeated indices in an indexed family | `InformationTheory.UniquelyDecodable` is defined for a `Set (List α)`; Lecerf's code data are indexed | Stage 7 proves `isIndexedCode_iff_injective_and_uniquelyDecodable`: the missing index information is recovered exactly by a separate `Function.Injective c` conjunct. The duplicate-index audit confirms that the conjunct cannot be discarded | resolved-design |
| `A-020` | Tape semantics and computable finite encodings pull in different directions | `Turing.Tape` has useful quotient-normalized semantics but no ready `Primcodable` instance. Stage-3 probes verified a canonical structural representation and an equivalence to the reference halves | `Side` gives canonical finite-support tapes and constructive encodings. `Compiler.TapeBridge` now proves the equivalence with mathlib tapes and commutation with head, write, and both moves; Stage 6 transfers the fixed source semantics through this bridge while keeping the varying canonical start map primitive recursive | resolved-design |
| `A-021` | Treating a partial equivalence's option-valued function as globally injective is false | Checked theorem `Audit.emptyReversibleStep_next_not_injective`: the empty `PEquiv` sends distinct Boolean inputs to `none` | Use `BackwardUnique`, i.e. left uniqueness only for successful steps; `ReversibleStep.backwardUnique` proves it | resolved-design |
| `A-022` | A reversible step does not make forward and reverse terminality or same-start halting pointwise equal | Checked single-edge audit: the target is forward-terminal but not reverse-terminal | Reverse paths with exchanged endpoints; require both appropriate endpoint terminal hypotheses in `mem_eval_next_iff_mem_eval_prev` | resolved-design |
| `A-023` | Semantic phase composition is not yet an ordinary finite phase-control machine | `Rule.tapeAction` composes a checked write and move `PEquiv`; `FiniteMachine.reverseStep` performs move-back/check/restore as one macro-step | Stage 6 avoids conflating the layers: it introduces an ordinary finite simultaneous two-tape rule model and a checked finite microstate history compiler. Lowering that model to the existing one-tape `FiniteMachine` is still an explicit later bridge, not part of the two-tape theorem | isolated-obligation |
| `A-024` | The implemented finite reverse-key condition originally had only a sufficient-direction theorem | `reverseTableCompatible_backwardCompatible` compiles; exact `backwardCompatible_iff_backwardUnique` quantifies over configurations | Stage 6 deliberately uses the permitted sufficient route. `TwoTape.FiniteMachine.SyntacticallyReversible` is decidable and primitive recursive, its pairwise input/output conditions imply semantic `Reversible`, and every generated table satisfies it. It is not advertised as characterizing all semantic reversible tables | resolved-design |
| `A-025` | An effective abstract history interpreter is not automatically a generated conventional finite Turing machine | `finiteForward_uniform_primrec` and `finiteBackward_uniform_primrec` interpret a finite source description, but `History.Config` contains an unbounded `List` of source configurations | `TwoTape.HistoryCompiler` now stores finite rule tokens on a canonical history tape and proves generated-run preservation/reflection, halting, open reachability, and closed return equivalences for actual finite tables. This resolves the finite-machine reduction in the stated two-tape model; a one-tape lowering and Lecerf-marker correspondence remain open | resolved-design |
| `A-026` | “Checkpoint uniqueness” cannot mean that a source configuration has only one valid history | The checked Boolean-cycle audit revisits `false` with histories `[]` and `[true, false]` | State uniqueness at equal elapsed/history length (`Valid.eq_of_history_length_eq`) and uniqueness of the empty initial checkpoint; retain longer cycle histories | resolved-design |
| `A-027` | Blindly popping a stored predecessor is not an inverse on malformed ambient history states | `History.Audit.malformed_predecessor_rejected` checks a predecessor that does not step to the recorded current state | `History.backward` recomputes and validates the edge before popping; `forward_eq_some_iff_backward_eq_some` proves the exact inverse law without assuming `Valid` | resolved-design |
| `A-028` | Closing only one privileged reverse-initial state would make the return gadget depend on runtime equality with a reduction input and can break the ambient inverse law on other components | The paper sketches conditioning behavior at one initial configuration but gives no total rule family or global reversibility argument | `Coupling.returnGadget` uniformly closes every inverse-terminal state to its matching forward-tagged state. `returnNext_eq_some_iff_returnPrev_eq_some` proves the exact ambient law; `exists_returnNext`, `exists_returnPrev`, and `returnGadget_not_terminal` expose totality | resolved-design |
| `A-029` | The closed coupling is total, so it cannot itself serve as the halting machine in a halting reduction | Both branches of `returnNext` succeed, formalized by `exists_returnNext` and `returnGadget_not_terminal`; the open `turnaround` instead stops at the reverse-initial checkpoint | Use the Stage-4 partial history simulator for halting, the open coupling for distinct-target reachability, and the closed gadget only for positive return. Do not conflate these target predicates | resolved-design |
| `A-030` | Moving the history head right while erasing a restored token breaks multi-token retracing | After `scanRule` moves left onto the newest token, a right-moving restore would revisit the freshly erased blank; the next scan would then encounter blank rather than the preceding token | The checked finite compiler uses `restoreRule.move₂ = .stay`. Each reverse macro is scan-left, inspect/move-work-back, then restore/erase in place; only `bottomRule` moves right when closing the return cycle | correction-required |
| `A-031` | Generic finite enumeration and selected encodings are noncomputable even though a reduction witness must be computable | `Finset.univ.toList`, the existential universal program, and fixed `Primcodable` choices occur in compiler constants; treating a varying compilation as computable would be unjustified | Stage 6 fixes the universal program, finite source table, and three target tables once. Only `sourceStart`, `startCheckpoint`, `bottomTarget`, and `compileHalting`/`compileReturn`/`compileReachability` vary, and each has a checked primitive-recursive theorem. The noncomputable boundary is therefore closed data, not a varying oracle | resolved-design |
| `A-032` | The paper requires the fresh marker to be absent from both the existing code `C` and the auxiliary prefix/suffix family `K` | In the marker construction every auxiliary word receives a new boundary marker, so occurrences of that marker inside an auxiliary word do not compromise boundary recognition | Stage 7 proves the sharper `isIndexedCode_prependMarkerExtension_of_freshFor_left` and `isIndexedCode_appendMarkerExtension_of_freshFor_left` using freshness only for `C`. The paper-shaped wrapper theorems retain the stated, redundant `FreshFor marker k` hypothesis for source fidelity | resolved-design |
| `A-033` | A semantic code equivalence does not by itself provide executable decoding or generated-submonoid membership | Inverting an arbitrary injective free-monoid lift and deciding membership in an arbitrary `Submonoid.closure` have no uniform decision procedure in the Stage-7 representation | `encodingEquiv`, `CodeIso.ofCodes`, `CodeIso.toPEquiv`, and `PaperCodeEpi.ofCodes` remain deliberately `noncomputable`. Stage 8 does not claim a general algorithm for them: it supplies a specialized primitive-recursive Boolean codec and a raw finite-table `Descriptor` whose checked executable interpreter agrees with the semantic edge-code action whenever the table is valid. Thus no semantic choice or proof object is stored in later runtime input | resolved-design |
| `A-034` | A complete-configuration edge schema is not Lecerf's finite local `α`/`ω`/`β` relation list | §3 prints finitely many local one-tape relation families per rule. The project's undecidability source is instead a conventional finite reversible two-tape table, and no two-tape-to-one-tape lowering for those target tables has been proved | Stage 8 uses self-delimiting words over the finite alphabet `Bool` and indexes source/target words by all successful configuration edges. This family is generally infinite but uniformly described and interpreted by the supplied finite table. It proves the required step and iterate semantics as a cleaner construction, but no declaration identifies it with `τ_max`, `τ_min`, the historical marker words, or a one-tape lowering | isolated-obligation |
| `A-035` | The empty word is a trivial positive fixed point of a monoid code isomorphism, and an arbitrary semantic `CodeIso` has no chosen finite input syntax | §1c explicitly notes the empty-word solution and treats `θ` as given by relations, but never specifies a finite or effective presentation class | Stage 9 uses raw finite reversible-machine tables as presentations of their successful-edge code isomorphisms and leaves the empty-word yes-instances in the uniform problem. The actual return reduction produces `ConfigCode.encodeConfig config ≠ 1`, checked in `CodeIterates.Audit`, so undecidability does not route through the trivial word. No theorem claims a presentation of every arbitrary semantic `CodeIso` or the historical finite relation list | resolved-design |
| `A-036` | Source scans for the token `axiom` do not detect axioms generated by `native_decide` | Stage-10 `#print axioms` probes exposed project-named native-decision axioms in four diagnostic modules despite clean source scans | All 21 audit uses were replaced by kernel-checked `decide`. The four focused audit builds pass; representative repaired diagnostics now use no axioms or only `propext`, and the final trust gate scans for both `axiom` and `native_decide` | correction-required |

Stage 7 closes `A-001`, `A-003`, `A-009`, and `A-019` at the semantic API
level. Stage 8 closes the specialized executable boundary in `A-033` for its
successful-configuration-edge schema while leaving arbitrary semantic code
inversion noncomputable. `A-034` records the still-open comparison with the
paper's genuinely finite local one-tape construction. Stage 9 closes the
effective distinctions in `A-002`, `A-003`, and `A-012`; `A-035` records the
precise finite-presentation and empty-word boundary of the resulting theorem.

## Source Corrections Versus Design Choices

Material changes to the paper are:

- positive rather than possibly-zero iteration (`A-002`);
- a partial rather than silently total ambient iterate (`A-003`);
- repaired phased inverse execution rather than the printed moving inverse
  tuple (`A-004`);
- positive return (`A-008`);
- removal of the English-only completeness claim (`A-013`); and
- a consistent empty history base case (`A-015`).

`A-030` is instead a correction to the reconstructed finite compiler, not a
claim about text omitted by the paper: token restoration must leave the
history head in place for the next leftward scan.

`A-032` is a checked mathematical sharpening rather than a source correction.
The paper-shaped declarations retain the paper's stronger freshness
hypothesis, while separately named sharp declarations expose its redundancy.

Independent representation choices, not claims about the historical text,
are `PEquiv` for generic reversible steps, `FreeMonoid` for words, a custom
indexed-code predicate, complete predecessor lists for the first clean history
simulator, phase-tagged coupling, a finite-support tape model, and the Stage-6
finite two-tape rule-token compiler. Stage 7 additionally chooses generated
submonoids for intrinsic code maps and a semantic ambient `PEquiv`; its
noncomputable membership/decoding boundary is recorded under `A-033` rather
than being mistaken for an executable finite representation. Stage 8 chooses
unary self-delimiting encodings of complete configurations over `Bool` and a
generally infinite successful-edge index. The raw runtime descriptor is only
the finite two-tape table; the edge family and semantic `CodeIso` remain
proof-side objects. This is a cleaner replacement theorem, not a transcription
of Lecerf's local `α`/`ω`/`β` syntax. Stage 9 additionally chooses inherited
product encodings for raw descriptor/word/exponent inputs and treats them as a
finite presentation class. The semantic `CodeIso` appears only in
correspondence theorems, never as runtime input.

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

Stages 2 through 9 introduce the checked transition, one- and two-tape
finite-machine surfaces, abstract and finite history simulations,
forward/reverse coupling, validity-guarded undecidability reductions, and the
semantic and executable machine/code bridge.

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
| `Lecerf.Machine.Coupling.History.universalTarget_strictlyReachable_iff_eval_dom` | Universal evaluation domain iff distinct-target reachability | `propext`, `Classical.choice`, `Quot.sound` | This declaration is a semantic specialization of the checked universal source; Stage 6 separately supplies the finite-description reduction |
| `Lecerf.Machine.Coupling.History.universalPositiveReturn_iff_eval_dom` | Universal evaluation domain iff positive return | `propext`, `Classical.choice`, `Quot.sound` | Semantic specialization; no `ManyOneReducible` or undecidability conclusion is claimed |
| `Lecerf.Machine.TwoTape.HistoryCompiler.return_positiveReturn_iff_source_halts` | Finite closed two-tape return iff source halting | `propext`, `Classical.choice`, `Quot.sound` | Both directions use the generated-run invariant and checked backward uniqueness; no project axiom |
| `Lecerf.Machine.Compiler.ReversibleUniversal.eval_dom_iff_history_halts` | Fixed finite two-tape history-table halting iff universal evaluation domain | `propext`, `Classical.choice`, `Quot.sound` | Classical dependencies belong to the fixed universal program/encodings and standard transition semantics; the varying start map is separately primitive recursive |
| `Lecerf.Undecidability.ReversibleTwoTape.partrecHalts0_manyOne_haltingYes` | Explicit computable many-one reduction to guarded finite halting | `propext`, `Classical.choice`, `Quot.sound` | The witness is `compileHalting`, proved primitive recursive; no project axiom or varying noncomputable oracle |
| `Lecerf.Undecidability.ReversibleTwoTape.haltingYes_not_computable` | Finite reversible two-tape halting noncomputability | `propext`, `Classical.choice`, `Quot.sound` | Derived from mathlib's `ComputablePred.halting_problem 0` through the explicit reduction |
| `Lecerf.Undecidability.ReversibleTwoTape.returnYes_not_computable` | Finite reversible two-tape positive-return noncomputability | `propext`, `Classical.choice`, `Quot.sound` | Derived from the same established source theorem; the target predicate uses positive return |
| `Lecerf.Undecidability.ReversibleTwoTape.reachabilityYes_not_computable` | Finite reversible two-tape distinct-target reachability noncomputability | `propext`, `Classical.choice`, `Quot.sound` | Derived from the same established source theorem; target inequality and strict reachability are explicit guards |
| `Lecerf.Word.isIndexedCode_iff_injective_and_uniquelyDecodable` | Exact indexed/set-code bridge | `propext`, `Quot.sound` | The explicit generator-injectivity conjunct repairs the information lost by `Set.range`; no project axiom |
| `Lecerf.Word.isIndexedCode_prependMarkerExtension` | Paper-shaped right-prefix fresh-marker criterion | `propext`, `Classical.choice`, `Quot.sound` | Standard free-monoid/list dependencies only; the sharper theorem shows the auxiliary-family freshness hypothesis is redundant |
| `Lecerf.Word.isIndexedCode_appendMarkerExtension` | Paper-shaped left/suffix fresh-marker criterion | `propext`, `Classical.choice`, `Quot.sound` | Dual checked code theorem; no project axiom |
| `Lecerf.Word.CodeIso.toPEquiv_generator` | Ambient partial action maps corresponding generators | `propext`, `Classical.choice`, `Quot.sound` | `Classical.choice` belongs to semantic decoding/membership for arbitrary codes; this declaration is not claimed executable |
| `Lecerf.PEquiv.iterate_symm` | Inversion commutes with partial iteration | `propext`, `Quot.sound` | Pure partial-equivalence algebra; no project axiom |
| `Lecerf.PEquiv.positiveIterate` | Positive-exponent wrapper `k + 1` | `propext`, `Quot.sound` | Pure definition over partial composition; excludes the zero-exponent loophole |
| `Lecerf.PEquiv.positiveIterate_symm` | Inversion commutes with positive iteration | `propext`, `Quot.sound` | Pure partial-equivalence algebra; undefined intermediate results remain undefined |
| `Lecerf.Encoding.ConfigCode.decodeConfigs_eq_some_iff` | Exact accepted-language characterization for concatenated Boolean frames | `propext`, `Quot.sound` | Malformed, unterminated, and noncanonical inputs are rejected; no arbitrary inverse is used |
| `Lecerf.Encoding.ConfigCode.decodeConfigs_primrec` | Primitive-recursive complete frame-sequence decoder | `propext`, `Classical.choice`, `Quot.sound` | Standard encoded-computability and free-monoid dependencies; the runtime decoder is explicit |
| `Lecerf.Encoding.StepCode.targetWord_isIndexedCode_iff_backwardUnique` | Target edge codehood iff successful-predecessor uniqueness | `propext`, `Classical.choice`, `Quot.sound` | The hypothesis is whole-step `BackwardUnique`, not individual-rule inversion or forward determinism |
| `Lecerf.Encoding.StepCode.stepCodeIso_apply_eq_some_iff_exists` | Strong one-step preservation/reflection with arbitrary ambient output | `propext`, `Classical.choice`, `Quot.sound` | Starting from a canonical frame, every successful output is exactly an encoded machine successor |
| `Lecerf.Encoding.StepCode.stepCodeIso_iterate_eq_some_iff` | Exact supplied-exponent machine/code iteration iff | `propext`, `Classical.choice`, `Quot.sound` | Iteration uses literal `Option.bind`; failed intermediate steps remain undefined |
| `Lecerf.Encoding.StepCode.stepCodeIso_positiveIterate_iff_strictlyReachable` | Positive code orbit iff strict machine reachability | `propext`, `Classical.choice`, `Quot.sound` | The witness is `k + 1`; no zero-exponent shortcut is available |
| `Lecerf.Encoding.StepCode.liftPEquiv_machine_eq_stepCodeIso_toPEquiv` | Executable interpreter equals the semantic edge-code action on every Boolean word | `propext`, `Classical.choice`, `Quot.sound` | Choice occurs only on the semantic comparison side; the decode/traverse/encode interpreter itself is explicit |
| `Lecerf.Encoding.StepCode.Descriptor.checkedApply_uniform_primrec` | Primitive-recursive validity-guarded interpreter for raw finite tables | `propext`, `Classical.choice`, `Quot.sound` | Runtime input stores a finite table and word, not `Edge`, `CodeIso`, `PEquiv`, a function, or a proof |
| `Lecerf.Encoding.StepCode.Descriptor.applyWord_eq_stepCodeIso_toPEquiv` | Valid raw descriptor agrees pointwise with semantic code isomorphism | `propext`, `Classical.choice`, `Quot.sound` | The primitive-recursive validity guard supplies semantic reversibility only in the proof; it is not stored as data |
| `Lecerf.Transition.pequiv_positiveIterate_iff_strictlyReachable` | Generic positive partial iteration iff `StateTransition.Reaches₁` | `propext`, `Quot.sound` | Pure exact-length/closure bridge, independent of the code construction |
| `Lecerf.Undecidability.CodeIterates.positiveFixedOrbitYes_iff_stepCodeIso_positiveIterate` | Executable fixed-orbit predicate iff the semantic successful-edge code-isomorphism equation | `propext`, `Classical.choice`, `Quot.sound` | Validity supplies the proof-side `CodeIso`; runtime input contains only a raw finite table and word |
| `Lecerf.Undecidability.CodeIterates.distinctOrbitYes_iff_stepCodeIso_positiveIterate` | Executable distinct-word predicate iff the semantic positive code orbit | `propext`, `Classical.choice`, `Quot.sound` | Word inequality and exponent positivity are explicit; all intermediate applications remain partial |
| `Lecerf.Undecidability.CodeIterates.positiveIterateAtYes_computablePred` | Total computable recognition of a supplied nonzero exponent | `propext`, `Classical.choice`, `Quot.sound` | The proof is uniform in the raw descriptor, exponent, and words and uses exact `Option` iteration |
| `Lecerf.Undecidability.CodeIterates.positiveFixedOrbitYes_re` | Semidecidability of positive fixed-orbit existence | `propext`, `Classical.choice`, `Quot.sound` | Partial recursive search ranges over `k`; no total witness finder or no-instance recognizer is inferred |
| `Lecerf.Undecidability.CodeIterates.distinctOrbitYes_re` | Semidecidability of distinct positive-orbit existence | `propext`, `Classical.choice`, `Quot.sound` | The searched witness relation includes descriptor validity and endpoint inequality |
| `Lecerf.Undecidability.CodeIterates.partrecHalts0_manyOne_positiveFixedOrbitYes` | Explicit halting-to-positive-fixed-orbit reduction | `propext`, `Classical.choice`, `Quot.sound` | Composition of the checked Stage-6 return reduction and primitive-recursive canonical configuration encoding |
| `Lecerf.Undecidability.CodeIterates.partrecHalts0_manyOne_distinctOrbitYes` | Explicit halting-to-distinct-word-orbit reduction | `propext`, `Classical.choice`, `Quot.sound` | Composition of the checked Stage-6 reachability reduction; canonical word inequality follows from codec injectivity |
| `Lecerf.Undecidability.CodeIterates.positiveFixedOrbitYes_not_computable` | Positive fixed-orbit existence is not computable | `propext`, `Classical.choice`, `Quot.sound` | Derived from mathlib halting through the explicit many-one reduction, not a project axiom |
| `Lecerf.Undecidability.CodeIterates.distinctOrbitYes_not_computable` | Distinct-word positive-orbit existence is not computable | `propext`, `Classical.choice`, `Quot.sound` | Both preservation and reflection flow through the generic guarded reachability iff theorem |

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
- At the close of Stage 3, the finite compiler from `Nat.Partrec.Code` to
  `FiniteMachine` was still open under `A-018`; Stage 6 later closes the fixed
  universal-source reduction boundary without claiming a varying compiler.

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
- At the close of Stage 4, the abstract state still contained an unbounded
  predecessor list and `A-018`, `A-023`, `A-024`, and `A-025` were open.
  Stages 5--6 later supply coupling, a conventional finite two-tape compiler,
  and the explicit reductions while retaining the one-tape historical gaps.
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

### Stage 6 finite reversible two-tape undecidability

- Added the fixed universal source bridge in
  `Machine.Compiler.{UniversalSource,Table,TapeBridge,FiniteSource,FiniteSourceComputable}`.
  One closed `ToPartrec.Code` is selected and lowered through mathlib's
  TM2→TM1→TM0 translations into an actual fixed one-tape `FiniteMachine`.
  `FiniteSource.halts_iff_eval_dom` proves preservation and reflection, while
  `FiniteSource.initial_primrec` proves the varying program/input start tape
  primitive recursive.
- Added `Machine.TwoTape.{Core,Reversible,Effectivity,Validity}` and the finite
  `TwoTape.HistoryCompiler` runtime, trace invariant, correctness,
  reversibility, and endpoint-effectivity leaves. The forward-only, open
  turnaround, and closed return tables have checked
  `SyntacticallyReversible` certificates implying semantic `Reversible`.
  The corrected reverse macro erases a token with `restoreRule.move₂ = .stay`;
  moving right there would stop a multi-token retrace early.
- `Machine.Compiler.ReversibleUniversal` fixes those three target tables and
  proves primitive-recursive start and bottom-target maps plus exact source
  evaluation-domain iff theorems for finite halting, distinct-target strict
  reachability, and positive return.
- `Undecidability.ReversibleTwoTape.Problems` guards every raw predicate by the
  primitive-recursive finite validity certificate. `Reduction` supplies the
  primitive-recursive maps `compileHalting`, `compileReturn`, and
  `compileReachability`, their three exact iff theorems, three explicit
  `ManyOneReducible` witnesses, and `haltingYes_not_computable`,
  `returnYes_not_computable`, and `reachabilityYes_not_computable` from
  mathlib's `ComputablePred.halting_problem 0`.
- Classical choice selects only the one fixed universal program. Other
  `noncomputable` declarations package fixed finite supports, encodings,
  enumeration orders, tables, or semantic reversible-step data. Every map
  varying with `Nat.Partrec.Code` and used as a reduction witness has a checked
  `Primrec` theorem; no varying compiler or oracle is hidden behind those
  constants.
- `lake build Lecerf.Undecidability.ReversibleTwoTape.Audit Lecerf` passed with
  894 jobs, replaying all six representative axiom checks. Full `lake build`
  passed with 893 jobs. Every reported Stage-6 headline dependency was exactly
  `[propext, Classical.choice, Quot.sound]`; no project-specific axiom appears.
- Focused scans found no `sorry`, `admit`, project `axiom`, or proof-bypassing
  `unsafe`. All `noncomputable`/`Classical.choose` occurrences were classified
  at the fixed-data boundary. At the Stage-6 boundary, the then-future
  code/iterate scan had no hits, and whitespace plus `git diff --check` passed.
- These are exact results for conventional finite reversible **two-tape**
  machines. No lowering to the project's one-tape `FiniteMachine` and no
  correspondence with Lecerf's literal one-tape marker/sweeping relations is
  claimed; that historical representation gap remains explicit.

### Stage 7 free monoids, codes, and code maps

- Added `Word.{Code,Prefix,CodeMorphism,API,Audit}` and re-exported only the
  thin public API from `Lecerf`. `Word.Audit` remains diagnostic and
  non-public.
- `IsIndexedCode` is injectivity of the indexed substitution morphism.
  `isIndexedCode_iff_injective_and_uniquelyDecodable` proves the exact bridge
  to mathlib's set-based predicate, including the necessary injectivity of the
  generator family. Audit examples reject duplicate indices and an empty
  generator.
- Prefix and suffix codehood imply indexed codehood. The two sharp
  fresh-marker theorems require marker freshness only for the already-coded
  family; `isIndexedCode_prependMarkerExtension` and
  `isIndexedCode_appendMarkerExtension` retain the paper's redundant
  auxiliary-family freshness hypothesis as source-shaped wrappers.
- `CodeIso` is an intrinsic generated-submonoid equivalence respecting every
  displayed generator. `CodeIso.ofCodes` constructs the canonical
  correspondence, and `CodeIso.toPEquiv` exposes its exactly partial ambient
  action. `PaperCodeEpi` remains separate: its selector may repeat or omit
  target generators, as checked by the audit example.
- `PEquiv.iterate` uses literal partial composition, its exact addition and
  inverse laws compile, and `positiveIterate` represents exponent `k + 1`.
  Undefinedness is propagated by `Option.bind`; zero is never silently used
  for a positive-orbit predicate.
- The generic decoding inverses and generated-submonoid membership tests are
  semantic and explicitly `noncomputable`. Stage 7 deliberately deferred
  effective finite syntax, machine-step encoding, executable iteration, and
  reductions; Stages 8--9 now supply those for the finite-machine-described
  successful-edge subclass, not for arbitrary semantic `CodeIso` values.
- Focused builds passed for `Lecerf.Word.Code` (522 jobs),
  `Lecerf.Word.Prefix` (526), and `Lecerf.Word.CodeMorphism` (693). The API and
  audit build passed with 696 jobs; `Lecerf.Word.Audit Lecerf` passed with 914
  jobs; full `lake build` passed with 913 jobs.
- The seven Stage-7 axiom prints are recorded above. The indexed/set bridge
  and pure iterate declarations report exactly `[propext, Quot.sound]`; the
  marker theorems and code-isomorphism generator theorem report exactly
  `[propext, Classical.choice, Quot.sound]`. No project axiom appears.
- Project Lean scans found no `sorry`, `admit`, project `axiom`, or
  proof-bypassing `unsafe`. Noncomputable declarations are confined to the
  documented semantic code-decoding/membership boundary. Whitespace and
  `git diff --check` passed.

### Stage 8 machine steps as code actions

- Added `Transition.Exact`, executable
  `Encoding.{ConfigCode,ConfigCodeEffectivity}`, and
  `Encoding.StepCode.{Core,Correctness,Interpreter,Effectivity,API,Audit}`.
  `API` is a thin semantic/effectivity boundary re-exported by `Lecerf`; the
  audit is a diagnostic leaf and is not a public or runtime dependency.
- `ConfigCode` frames the canonical `Primcodable` number of a complete
  two-tape configuration as `true^n false` over the finite alphabet `Bool`.
  Single and concatenated decoders have exact accepted-language theorems;
  their encoders and decoders have checked `Primrec` and `Computable`
  declarations.
- `Edge machine` records a successful whole-configuration transition.
  `sourceWord_isIndexedCode` follows from option-valued forward functionality;
  `targetWord_isIndexedCode_iff_backwardUnique` proves that target codehood is
  exactly whole-step successful-predecessor uniqueness. `stepCodeEpi` gives
  the paper-specific weaker map for every table, while `stepCodeIso` is a
  genuine `CodeIso` under `BackwardUnique`.
- `stepCodeIso_apply_eq_some_iff_exists` reflects an arbitrary successful
  ambient output to a canonical machine successor. The supplied-endpoint,
  terminal-undefinedness, exact-iterate, definedness, machine-`PEquiv`, and
  positive-reachability iff theorems prove both directions without admitting
  malformed intermediate words or exponent zero.
- `applyWord` explicitly decodes every complete frame sequence, traverses the
  machine step pointwise, and re-encodes.
  `liftPEquiv_machine_eq_stepCodeIso_toPEquiv` proves equality with the
  semantic ambient action on every Boolean word for a reversible table,
  including simultaneous rejection of malformed words.
- `Descriptor` is definitionally just a raw finite two-tape table.
  `Descriptor.Valid` is the existing primitive-recursive syntactic
  reversibility guard; `applyWord_uniform_primrec`, `valid_primrec`, and
  `checkedApply_uniform_primrec` establish the varying runtime boundary.
  Neither the infinite `Edge` type, a proof, a function, nor the noncomputable
  semantic `CodeIso` is stored in descriptor input.
- The non-public audit checks unterminated and trailing frames, a terminated
  but noncanonical natural code, canonical round trips, concrete `.left`,
  `.stay`, and `.right` one-rule two-tape machines, normalized blank extension,
  terminal undefinedness, and a forward-deterministic merge whose repeated
  target makes `targetWord` fail codehood. Small executable checks use kernel
  `decide`, not generated native-evaluation axioms.
- Available focused evidence includes `Transition.Exact` (729 jobs),
  `ConfigCodeEffectivity` (805), `StepCode.Interpreter` (844),
  `StepCode.Correctness` (845), and `StepCode.Effectivity` (852). A focused
  audit integration build passed with 855 jobs before the final import
  refactor. After that refactor, the public root and full builds passed with
  921 jobs, and the combined post-refactor audit/root build passed with 922.
  The audit replays the representative axiom results above; they contain only
  `propext`, `Classical.choice`, and `Quot.sound`, with the pure
  exact-transition bridge omitting choice. Focused and whole-project
  forbidden-construct, whitespace, and diff checks passed.
- This completed stage is a cleaner, generally infinite configuration-edge
  schema uniformly described by a finite two-tape table. It is **not**
  Lecerf's finite local `α`/`ω`/`β` list, a proof about `τ_min`, or
  a lowering of the reversible two-tape tables to a one-tape machine. Stage 9
  consumes the checked finite descriptor boundary without claiming those
  historical identifications.

### Stage 9 positive code-iterate undecidability

- Added reusable `Transition.ExactEffectivity` and
  `Undecidability.CodeIterates.{Problems,Effectivity,Correspondence,Reduction,
  API,Audit}`. The audit is not imported by any public API.
- Raw problem inputs are inherited finite products containing a table, Boolean
  words, and optionally a natural exponent. They contain no semantic
  `CodeIso`, `PEquiv`, function, proof, or orbit witness. Descriptor validity is
  an explicit conjunct in every yes-predicate.
- `PositiveFixedOrbitYes` and `DistinctOrbitYes` quantify exact exponent
  `k + 1`; `PositiveIterateAtYes` explicitly requires its supplied exponent to
  be nonzero. The partiality diagnostic proves a failed exact iterate remains
  failed after every extension, and the public correspondence uses literal
  semantic `PEquiv.iterate`.
- `positiveIterateAtYes_primrec` and
  `positiveIterateAtYes_computablePred` separate total supplied-exponent
  recognition from existential search. The witness relations are primitive
  recursive, and `positiveFixedOrbitYes_re` / `distinctOrbitYes_re` are proved
  by partial recursive `Nat.rfind`; no total finder or no-instance recognizer
  is inferred.
- `encodeReturnInput` and `encodeReachabilityInput` leave arbitrary raw tables
  unchanged and canonically encode only endpoints. Their primitive-recursive
  proofs, generic iff theorems, and generic `ManyOneReducible` witnesses are
  checked before composition with Stage 6. Invalid descriptors reflect to
  no-instances in both directions, and configuration-code injectivity supplies
  distinct target words. The audit also checks that fixed-orbit reduction words
  are nonempty, so the proof does not use the free-monoid identity solution.
- Focused builds passed for `ExactEffectivity` (812 jobs), `Problems` (892),
  `Effectivity` (894), `Correspondence` (894), `Reduction` (907), and `Audit`
  (908). Public API/root integration passed with 927 jobs; replaying the audit
  with the root passed with 928 jobs; full `lake build` passed with 927 jobs.
- A temporary root-import probe checked the exact public input, predicate,
  effectivity, correspondence, many-one, and noncomputability signatures and
  was deleted. Lean scans found no `sorry`, `admit`, project `axiom`, or
  proof-bypassing `unsafe`. Stage-9 `noncomputable section`s inherit only the
  documented one-time fixed target encodings; every varying map is proved
  primitive recursive/computable. Shortcut scans confirmed positive exponents,
  exact `Option` iteration, and no fallback totalization. Whitespace and
  `git diff --check` passed.
- The nine Stage-9 axiom commands recorded in the table all report exactly
  `[propext, Classical.choice, Quot.sound]`. No project-specific axiom appears.
  The completed theorem is for the finite-machine-presented successful-edge
  code-isomorphism subclass. The historical finite local relation encoding and
  two-to-one-tape lowering remain explicitly unresolved.
