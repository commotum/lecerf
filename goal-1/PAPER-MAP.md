# Paper Map

## Source Policy

- `lecerf-1963-fr/lecerf-1963-fr.pdf` and its page images are the primary
  historical source. The French Markdown is the searchable transcription.
- The English PDF is a translation, not independent evidence. Its Markdown
  faithfully transcribes that translation, including two material errors.
- A source assertion is not a Lean theorem. Every simulation or reduction
  claim below remains unformalized until its named stage supplies definitions,
  computability, and both directions of the required specification.

Status labels in this file are:

- `cited-background`: cited rather than proved in the note;
- `source-confirmed`: the source meaning is stable; the formal-disposition
  column records whether a checked Lean result now exists;
- `corrected-target`: the formal target deliberately repairs or disambiguates
  the printed claim;
- `spec-gap`: the source omits information needed for a proof;
- `conjecture`: explicitly conjectural in the note; and
- `out-of-scope-follow-up`: announced for another note.

## Claim Inventory

| ID | Location | Source claim | Formal disposition | Status |
|---|---|---|---|---|
| `L0-ANNOUNCE` | Introduction | The note will define code isomorphisms, reversible machines, and derive iterate-equation undecidability | Organization only; the mathematical claims are inventoried separately below | source-confirmed |
| `L0-FOLLOWUP` | Introduction | A second note will apply the results to a Schützenberger problem | Do not attribute the promised result to this paper or formalization | out-of-scope-follow-up |
| `L1a-POST` | §1a | Post's diagonal equation problem is recursively unsolvable for arbitrary morphisms | Possible background reduction only; verify the cited theorem before reuse | cited-background |
| `L1a-MONIC` | §1a | The problem remains unsolvable when one morphism is injective, attributed to Tag | Possible background reduction only; not proved in this note | cited-background |
| `L1a-BOTH` | §1a | Unsolvability when both morphisms are injective | The note explicitly presents this as a conjecture, not a theorem | conjecture |
| `L1b-EQ` | §1b | With injective `φ` and `ψ`, `φ(x) = ψ(x)` becomes `w = θ(w)` for `θ = ψ ∘ φ⁻¹` | Make injectivity hypotheses and exclusion of the empty-word solution explicit | source-confirmed |
| `L1b-ISO` | §1b | `θ` is a multiplicative bijection from `φ(A†)` to `ψ(A†)` | Stage 7's `CodeIso` bundles an equivalence of `generated source` and `generated target`, generator correspondence, and its exactly partial ambient `toPEquiv`. `toPEquiv_isSome_iff` identifies the source domain; no ambient automorphism is claimed | source-confirmed |
| `L1b-CODE` | §1b | The generator images are codes because a word has at most one indexed factorization | `IsIndexedCode c` is injectivity of `FreeMonoid.lift c`. `isIndexedCode_iff_injective_and_uniquelyDecodable` proves the exact bridge to mathlib's set predicate, retaining generator injectivity because a set forgets repeated indices | corrected-target |
| `L1c-EMPTY` | §1c | The empty word is fixed and is a trivial solution of every iterate equation | `CodeIso.toPEquiv_one` checks that the ambient partial action maps the empty word to itself. The independent `PEquiv.iterate`/`positiveIterate` API keeps this source fixed point distinct from the separate zero-exponent loophole | source-confirmed |
| `L1c-REL` | §1c | Two indexed code families in bijective correspondence determine a code isomorphism | `CodeIso.ofCodes` canonically constructs the generated-submonoid equivalence for two codes on the same index type, and `CodeIso.toPEquiv_generator` checks every displayed generator correspondence | source-confirmed |
| `L1d-RIGHT` | §1d | A fresh-marker union with a “right prefix-code” is a code | `isIndexedCode_prependMarkerExtension` proves the paper-shaped modern prefix-free theorem. The sharper `_of_freshFor_left` theorem proves freshness for the auxiliary family `K` redundant while retaining freshness for the existing code | source-confirmed |
| `L1d-LEFT` | §1d | The left-handed fresh-marker construction is dual | `isIndexedCode_appendMarkerExtension` proves the suffix-free dual, with `_of_freshFor_left` again exposing the sharper freshness hypothesis | source-confirmed |
| `L1e-EPI` | §1e | A source indexed family is a code and each assigned target word belongs to some target code | `PaperCodeEpi` and `PaperCodeEpi.ofCodes` implement the paper-specific generated-submonoid morphism with an unrestricted selector. The selector may repeat or omit target generators; no categorical epi, injectivity, or surjectivity is inferred. `CodeIso.toPaperCodeEpi` records the stronger special case | corrected-target |
| `L2-RULEINV` | §2 | `(p₁,q₁,p₂,q₂,d)` has printed inverse `(p₂*,q₂,p₁*,q₁,-d)` | Audit syntax `printedInverse` is non-public; `printedInverse_fails_on_moving_rule` checks the failure. Public `Rule.apply_eq_some_iff_undo_eq_some` proves the repaired semantic inverse | corrected-target |
| `L2-REV` | §2 | A machine is reversible when the printed inverse family constitutes a machine and starred runs reverse | `Rule.tapeAction` composes checked-write and movement phases. `FiniteMachine.Reversible`, `backwardCompatible_iff_backwardUnique`, and `toPEquiv` separate table determinism from global inverse execution | corrected-target |
| `L2-COUPLE` | §2 | Forward rules, inverse rules, and halt-to-star switches run forward and then backward | `Coupling.turnaround` and `returnGadget` use disjoint phase tags and exact ambient inverse laws. The open gadget switches only at forward terminality and retraces through the supplied inverse; the closed gadget uniformly closes inverse-terminal boundaries. Correspondence with the paper's omitted finite rule table remains open | spec-gap |
| `L3-RELATIONS` | §3 | Three source relations per move rule, plus symbol identities, define an “epimorphism of codes” `τ_max` | Stage 8 proves a cleaner analogue: `Edge`, `sourceWord`, `targetWord`, and `stepCodeEpi` give a `PaperCodeEpi` indexed by every successful whole-configuration edge. The schema is generally infinite, although uniformly described by the finite two-tape table. It is not the printed finite local relation family | spec-gap |
| `L3-CONFIG` | §3 | `α/ω/β` markers record the next-read and previous-written positions so `uᵢ₊₁ = τ_max(uᵢ)` | `ConfigCode.encodeConfig`/`decodeConfig` use self-delimiting complete-configuration words over finite `Bool`. `stepCodeIso_apply_eq_some_iff_exists`, `stepCodeIso_apply_eq_some_iff`, and the exact iterate theorems prove the functional step claim with strong reflection, but no theorem identifies these words with the historical marker language | corrected-target |
| `L3-MIN` | §3 | After conditional pruning to `τ_min`, code isomorphism implies machine reversibility | For the cleaner edge schema, `targetWord_isIndexedCode_iff_backwardUnique` exactly characterizes target codehood, and `stepCodeIso` constructs a genuine `CodeIso` under whole-step backward uniqueness. This is not a theorem about `τ_min`; the printed historical implication remains unformalized | spec-gap |
| `L4a-SIM1` | §4a(1) | Every source step is simulated by a finite reversible macro-run | `History.strictlyReachable_of_source_step` gives one positive abstract simulator step, and `History.reversible` supplies the exact inverse. A later tape encoding may refine it to several microsteps | source-confirmed |
| `L4a-SIM2` | §4a(2) | Source steps use an epimorphism `τ`; simulator steps use a code isomorphism `θ` | `stepCodeEpi` supplies the weaker paper map for any deterministic option-valued two-tape step; under `BackwardUnique`, `stepCodeIso` and its one-step/iterate iff theorems supply a genuine code isomorphism action. This is a clean whole-configuration realization, not Lecerf's local marker construction | corrected-target |
| `L4a-SIM3` | §4a(3) | A checkpoint `λ vᵢ μ wᵢ ν` recovers the source configuration and history | `History.Config.encode/decode/project` and `History.reachable_iff_valid` implement a cleaner full-predecessor checkpoint with exact recovery and no-spurious-checkpoint reflection; correspondence with the printed marker word remains open | spec-gap |
| `L4a-SIM4` | §4a(4) | `wᵢ = b² rₖ₁ … rₖᵢ b` records one distinguished nonidentity relation per source step | Stage 4 uses an explicit empty initial list and pushes the complete predecessor on every actual source step. `history_length_of_forward` proves one-entry growth. This is intentionally more redundant than the printed token scheme | corrected-target |
| `L4a-SIM5` | §4a(5) | Simulator halting checkpoints are exactly source-halting checkpoints | `terminal_forward_iff`, `haltsFrom_forward_iff`, and `universalHistory_halts_iff_eval_dom` prove preservation and reflection for the clean simulator | source-confirmed |
| `L4a-SIM6` | §4a(6) | The coupled machine reaches the starred initial configuration iff the source halts | `TwoTape.HistoryCompiler.turnaround_bottom_strictlyReachable_iff_source_halts` gives a finite conventional two-tape realization using a structurally distinct exposed reverse-bottom microstate. `ReversibleUniversal.eval_dom_iff_turnaround_bottom_strictlyReachable` specializes it to the fixed universal table, and the endpoint map is primitive recursive. The target is a cleaner microstate analogue, not literally Lecerf's starred marker word | source-confirmed |
| `L4a-SIM7` | §4a(7) | Return or passage through a framed target can be conditioned on source halting | `TwoTape.HistoryCompiler.return_positiveReturn_iff_source_halts` and the open-turnaround theorem prove both directions for finite two-tape tables. `partrecHalts0_iff_returnYes` and `partrecHalts0_iff_reachabilityYes` add validity guards and computable reduction maps. Correspondence with the omitted historical one-tape table remains open | spec-gap |
| `L4a-SKETCH` | §4a proof | One representative relation is simulated by sweeping, editing, appending history, shifting delimiters, and returning control | `TwoTape.HistoryCompiler` now gives complete finite rule families: forward steps append source-rule tokens, and reverse execution scans left, checks the token, moves the work head back, then restores and erases in place. The crucial checked correction is `restoreRule.move₂ = .stay`. This is a cleaner two-tape construction; no theorem identifies it with Lecerf's one-tape sweeping/marker encoding | spec-gap |
| `L4b-THM1H` | Theorem 1 | Halting is recursively unsolvable for arbitrary reversible Turing machines | For fixed finite two-tape control/alphabet types, `HaltingYes` guards an arbitrary supplied table by primitive-recursive `Certified`; `partrecHalts0_manyOne_haltingYes` is an explicit computable reduction and `haltingYes_not_computable` proves noncomputability. This establishes the finite two-tape version, not a one-tape lowering | source-confirmed |
| `L4b-THM1R` | Theorem 1 | Return to the initial configuration is recursively unsolvable | `ReturnYes` uses `PositiveReturn`, excluding the zero-step loophole. `partrecHalts0_manyOne_returnYes` and `returnYes_not_computable` establish the validity-guarded finite reversible two-tape result | corrected-target |
| `L4b-THM1T` | Theorem 1 | Passage through a specified configuration other than the initial one is recursively unsolvable | `ReachabilityYes` explicitly requires unequal endpoints and `StrictlyReachable`. `partrecHalts0_manyOne_reachabilityYes` and `reachabilityYes_not_computable` establish the validity-guarded finite reversible two-tape result with both reduction directions | source-confirmed |
| `L4c-THM2F` | Theorem 2 | `w = θⁿ(w)` is recursively unsolvable in `n` for arbitrary given `w, θ` | Stage 8 proves the semantic bridge `stepCodeIso_positiveIterate_iff_strictlyReachable`, which also covers positive return when the endpoints coincide. The uniform fixed-orbit predicate, explicit reduction, and undecidability proof remain Stage 9; supplied-exponent evaluation stays separate | corrected-target |
| `L4c-THM2O` | Theorem 2 | `w₁ = θⁿ(w₂)`, with `w₁ ≠ w₂`, is recursively unsolvable in `n` | The same Stage-8 theorem maps positive code orbit reachability exactly to strict machine reachability for supplied endpoints. Packaging unequal words, a computable reduction, and noncomputability remains Stage 9 | corrected-target |

## Fixed Stage-1 Conventions

### Machine semantics

- The concrete paper-facing machine uses a doubly infinite tape with a
  distinguished blank and finite nonblank support. Configuration equality is
  exact structural equality of state and an intrinsically canonical tape;
  trailing blanks have a unique representation.
- A source quintuple means read the current symbol, write the replacement,
  then move by `-1`, `0`, or `+1`. Absence of an applicable rule means halt.
- Under that convention the printed inverse quintuple fails for moving rules
  in general: after a forward move the head scans a neighboring cell, not
  the symbol just written. `Rule.tapeAction` splits checked write and movement
  as composed partial equivalences; `Rule.undo` executes those operations in
  reverse order and its exact inverse iff is checked.
- Individually invertible operations, syntactic inverse rules, deterministic
  rule lookup, global backward uniqueness, and a whole reversible machine are
  separate notions. Starred states are phase-tagged copies of control states;
  `star` alone does not move the head or alter the tape.

### Codes and partial iteration

- For an indexed family `c : I → FreeMonoid S`, project codehood is
  `Function.Injective (FreeMonoid.lift c)`. Stage 7 proves it equivalent to
  mathlib's set-based
  `InformationTheory.UniquelyDecodable (Set.range ...)` together with
  injectivity of `c`, exactly accounting for the indices forgotten by a set.
- “Complete code” is not a concept used by this note. English §1e mistranslates
  French `est bien un code` (“is indeed a code”).
- A code isomorphism is intrinsically a monoid equivalence between generated
  submonoids. Stage 7 implements its ambient action as a partial equivalence.
  Every iterate must remain in the next domain; undefinedness is represented
  by `none`, never by identity or a sink.
- The inverse of an arbitrary indexed-code encoding and membership in an
  arbitrary generated submonoid are semantic, so `encodingEquiv`, the
  canonical code-map constructors, and `CodeIso.toPEquiv` are explicitly
  noncomputable. Stage 8 does not change that general fact. For its specialized
  successful-edge schema it instead supplies an explicit primitive-recursive
  Boolean frame codec and a raw finite-table descriptor whose checked
  interpreter agrees with the semantic action. Runtime input never stores the
  infinite edge family, a semantic `CodeIso`, or a proof.
- The paper's fresh-marker hypothesis for the auxiliary family `K` is
  mathematically redundant. Sharp Stage-7 theorems omit it, while separate
  paper-shaped wrapper theorems retain it so the source statement remains
  directly recognizable.
- The paper never defines whether `ℕ` contains zero. Since zero makes the
  fixed-orbit existence predicate universally true, the formal theorem uses
  `k + 1`. This is a necessary semantic repair, not a claim about Lecerf's
  historical convention.
- “Recursively unsolvable in `n`” is read uniformly: finite descriptions of
  `(θ,w)` or `(θ,w₂,w₁)` are input and the question asks whether some positive
  admissible exponent exists. Checking a supplied finite exponent remains a
  separate computable/decidable theorem; existential yes-instances are
  expected to be semidecidable.

### Source limitations

- The note does not provide a complete history rule table, effectiveness proof,
  or code proof. Its §4 invariant also makes `w₀` both empty and `b³`. Stage 4
  now supplies a complete effective abstract simulator with an explicit empty
  base history and full predecessor records. Compilation to Lecerf's tape
  layout remains open and is not inferred from that result.
- §3 prints only `τ_min` code-isomorphism implies reversibility, not an iff.
- §4a(7) motivates return/reachability gadgets but does not prove their full
  reduction iff. Stage 5 supplies cleaner abstract gadgets and both semantic
  directions; a correspondence with the historical finite tape construction
  remains open.
- Stage 8 supplies a cleaner complete-configuration encoding and exact
  machine-step/iterate correspondence over `Bool`, together with a
  primitive-recursive finite-table interpreter. Its successful-edge index is
  generally infinite. The paper's finite local one-tape `α`/`ω`/`β`
  relations, the `τ_min` claim, and a lowering of the project's reversible
  two-tape target tables remain separate historical obligations.
- The header records the proceedings session of 28 October 1963; the footnote
  records presentation of the note on 21 October 1963. Both scan readings are
  retained and have no mathematical effect.

## Declaration Map

Names in completed rows are exact checked declarations. Later rows remain
proposed API targets.

| Claim family | Declaration family | Planned stage |
|---|---|---:|
| Generic reversible execution | `Step`, `BackwardUnique`, `ReversibleStep`, `ReversibleStep.next_eq_some_iff_prev_eq_some`, `ReversibleStep.reachable_iff_reverse_reachable`, `ReversibleStep.strictlyReachable_iff_reverse_strictlyReachable` | 2 (implemented) |
| Concrete machine semantics | `Tape`, `Config`, `Rule`, `FiniteMachine`, `FiniteMachine.step`, `FiniteMachine.TableDeterministic`, `FiniteMachine.Reversible` | 3 (implemented) |
| Repaired inverse semantics | `Tape.checkedWrite`, `Tape.moveEquiv`, `Rule.tapeAction`, `Rule.apply_eq_some_iff_undo_eq_some`, `FiniteMachine.step_eq_some_iff_reverseStep_eq_some`, `FiniteMachine.toPEquiv` | 3 (implemented atomically; finite microstate compiler open) |
| Effective source transition | `Source.universalEvalSearchStep`, `Source.universalEvalSearchStep_halts_iff_eval_dom`, `Source.universalEvalSearchStep_primrec`, `Source.evalSearchStart_joint_primrec` | 3 (implemented replacement source; finite compiler open) |
| History simulation | `History.forward`, `History.backward`, `History.reversible`, `History.reachable_iff_valid`, `History.source_reachable_iff_exists_reachable_checkpoint`, `History.haltsFrom_forward_iff` | 4 (implemented abstractly; historical tape compiler open) |
| Effective history interpretation | `FiniteMachine.step_uniform_primrec`, `History.forwardInterpreter_primrec`, `History.backwardInterpreter_primrec`, `History.finiteForward_uniform_primrec`, `History.finiteBackward_uniform_primrec`, `History.universalHistory_halts_iff_eval_dom` | 4 (implemented; generated conventional history machine open) |
| Coupling | `Coupling.turnaround`, `Coupling.returnGadget`, `Coupling.History.target_strictlyReachable_iff_halts`, `Coupling.History.positiveReturn_iff_halts`, `Coupling.History.universalTarget_strictlyReachable_iff_eval_dom`, `Coupling.History.universalPositiveReturn_iff_eval_dom` | 5 (implemented abstractly; finite compiler open) |
| Fixed conventional universal source | `Compiler.UniversalSource.universalCode`, `Compiler.FiniteSource.machine`, `Compiler.FiniteSource.halts_iff_eval_dom`, `Compiler.FiniteSource.initial_primrec` | 6 (implemented; fixed one-tape source) |
| Finite reversible two-tape compiler | `TwoTape.HistoryCompiler.historyMachine`, `turnaroundMachine`, `returnMachine`, `historyMachine_haltsFrom_iff_source`, `turnaround_bottom_strictlyReachable_iff_source_halts`, `return_positiveReturn_iff_source_halts` | 6 (implemented; one-tape lowering open) |
| Finite two-tape validity | `TwoTape.FiniteMachine.SyntacticallyReversible`, `TwoTape.FiniteMachine.syntacticallyReversible_primrec`, `HistoryCompiler.historyMachine_syntacticallyReversible`, `turnaroundMachine_syntacticallyReversible`, `returnMachine_syntacticallyReversible` | 6 (implemented sufficient guard) |
| Fixed universal reversible tables | `Compiler.ReversibleUniversal.historyTable`, `turnaroundTable`, `returnTable`, `startCheckpoint_primrec`, `bottomTarget_primrec`, `eval_dom_iff_history_halts`, `eval_dom_iff_turnaround_bottom_strictlyReachable`, `eval_dom_iff_return_positiveReturn` | 6 (implemented; finite two-tape) |
| Machine undecidability | `ReversibleTwoTape.HaltingYes`, `ReturnYes`, `ReachabilityYes`, `partrecHalts0_manyOne_haltingYes`, `partrecHalts0_manyOne_returnYes`, `partrecHalts0_manyOne_reachabilityYes`, `haltingYes_not_computable`, `returnYes_not_computable`, `reachabilityYes_not_computable` | 6 (implemented; finite two-tape) |
| Indexed codes and mathlib bridge | `Word`, `IsIndexedCode`, `codewordSet`, `IsIndexedCode.injective`, `IsIndexedCode.ne_one`, `isIndexedCode_iff_injective_and_uniquelyDecodable` | 7 (implemented semantically) |
| Prefix/suffix and marker criteria | `FreshFor`, `IsPrefixFree`, `IsSuffixFree`, `IsPrefixCode`, `IsSuffixCode`, `IsPrefixCode.isIndexedCode`, `IsSuffixCode.isIndexedCode`, `isIndexedCode_prependMarkerExtension_of_freshFor_left`, `isIndexedCode_appendMarkerExtension_of_freshFor_left`, `isIndexedCode_prependMarkerExtension`, `isIndexedCode_appendMarkerExtension` | 7 (implemented) |
| Intrinsic and ambient code isomorphism | `generated`, `generator`, `encodingEquiv`, `CodeIso`, `CodeIso.ofCodes`, `CodeIso.toInjectiveMorphism`, `CodeIso.toPEquiv`, `CodeIso.toPEquiv_generator` | 7 (implemented semantically; arbitrary decoding/membership noncomputable) |
| Paper-specific code epimorphism | `PaperCodeEpi`, `PaperCodeEpi.ofCodes`, `CodeIso.toPaperCodeEpi` | 7 (implemented; unrestricted selector) |
| Partial and positive iteration | `PEquiv.iterate`, `iterate_succ_apply`, `iterate_add`, `iterate_symm`, `positiveIterate`, `PositiveDefined`, `PositiveIterate`, `positiveIterate_iff_exists_ne_zero` | 7 (implemented semantically) |
| Executable Boolean configuration codec | `ConfigCode.unaryFrame`, `encodeConfig`, `decodeConfig`, `encodeConfigs`, `decodeConfigs`, `decodeConfig_eq_some_iff`, `decodeConfigs_eq_some_iff`, `encodeConfig_isIndexedCode`, `encodeConfigs_primrec`, `decodeConfigs_primrec` | 8 (implemented; finite alphabet and exact accepted language) |
| Successful-edge code maps | `StepCode.Edge`, `sourceWord`, `targetWord`, `sourceWord_isIndexedCode`, `targetWord_isIndexedCode_iff_backwardUnique`, `stepCodeEpi`, `stepCodeIso`, `stepCodeIso_edge` | 8 (implemented as a generally infinite schema uniformly described by a finite table) |
| Exact step and orbit correspondence | `exactIterate`, `ExactSteps`, `reachable_iff_exists_exactSteps`, `strictlyReachable_iff_exists_exactSteps_succ`, `stepCodeIso_apply_eq_some_iff_exists`, `stepCodeIso_apply_eq_some_iff`, `stepCodeIso_iterate_eq_some_iff_exists`, `stepCodeIso_iterate_eq_some_iff`, `stepCodeIso_positiveIterate_iff_strictlyReachable` | 8 (implemented with strong preservation/reflection) |
| Executable step-code interpretation | `StepCode.applyWord`, `liftPEquiv`, `liftPEquiv_machine_eq_stepCodeIso_toPEquiv`, `Descriptor`, `Descriptor.Valid`, `Descriptor.checkedApply`, `Descriptor.applyWord_uniform_primrec`, `Descriptor.valid_primrec`, `Descriptor.checkedApply_uniform_primrec`, `Descriptor.applyWord_eq_stepCodeIso_toPEquiv` | 8 (implemented; raw finite-table runtime boundary) |
| Iterate undecidability | `positiveFixedOrbit_not_computable`, `distinctOrbit_not_computable` | 9 (unstarted) |

Stage 3 supplies the concrete read-write-move semantics and repaired local and
global inverse laws for the machine portion of `L2-RULEINV`/`L2-REV`. Stages
4–5 supply the clean abstract history and coupling theorems. Stage 6 adds a
fixed conventional one-tape universal source, a complete finite reversible
two-tape history/coupling compiler, primitive-recursive validity and endpoint
maps, three exact many-one reductions, and three noncomputability theorems.
Stage 7 adds the independent semantic free-monoid layer: exact indexed
codehood, the set-code bridge, prefix/suffix marker theorems, intrinsic code
isomorphisms, the paper-specific epimorphism class, ambient partial action, and
positive iteration. Its arbitrary generated-submonoid decoding and membership
are deliberately noncomputable. Stage 8 adds a primitive-recursive
self-delimiting Boolean codec, the successful-edge `PaperCodeEpi`/`CodeIso`,
strong one-step and iterate reflection, an all-word executable interpreter,
and a primitive-recursive validity-guarded raw finite-table descriptor. This
is the completed cleaner edge-schema route. Identifying it with Lecerf's
literal finite marker/sweeping table or lowering the reversible target tables
to one tape remains open. Stage 9 has not started.

## Principal Reduction Map

```text
PartrecHalts0(code) := (Nat.Partrec.Code.eval code 0).Dom
  -- one fixed universal ToPartrec program; primitive-recursive encoded input;
     checked TM2 → TM1 → TM0 lowering and canonical tape bridge -->
HaltsFrom FiniteSource.machine.step
  (FiniteSource.initial (UniversalSource.encodedInput code 0).1)
  -- three fixed finite two-tape history/coupling tables;
     primitive-recursive endpoints; checked validity/reversibility;
     preservation and reflection -->
HaltingYes (compileHalting code)
ReturnYes (compileReturn code)
ReachabilityYes (compileReachability code)
  -- explicit ManyOneReducible witnesses + halting_problem 0 -->
¬ComputablePred HaltingYes
¬ComputablePred ReturnYes
¬ComputablePred ReachabilityYes

finite reversible two-tape steps/configurations
  -- primitive-recursive Bool framing and finite-table descriptor;
     generally infinite successful-edge CodeIso as proof-side semantics;
     checked one-step/iterate/positive-reachability iff -->
semantic positive fixed orbit / distinct orbit of the edge code isomorphism

  -- Stage 9 still owes finite target problem inputs, explicit computable
     reduction maps, endpoint guards, and both undecidability transfers -->
positiveFixedOrbit_not_computable / distinctOrbit_not_computable
```

Every Stage-6 arrow above is checked separately; the fixed tables do not hide a
varying compiler. Stage 8 checks the displayed machine-to-semantic-orbit arrow
and separately proves that its Boolean codec, raw finite descriptor, validity
guard, and forward interpreter are primitive recursive. The generally
infinite `Edge` family and noncomputable semantic `CodeIso` are not runtime
input. Stage 9 still must define the two uniform orbit decision problems and
give explicit computable reductions with both directions. A one-tape lowering
and correspondence with Lecerf's historical local encoding remain open and
are not prerequisites silently inferred from the cleaner theorem.
