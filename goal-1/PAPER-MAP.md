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
- `source-confirmed`: the source meaning is stable, but no Lean result exists;
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
| `L1b-ISO` | §1b | `θ` is a multiplicative bijection from `φ(A†)` to `ψ(A†)` | Model an equivalence of generated submonoids and its induced ambient partial equivalence, not an ambient automorphism | source-confirmed |
| `L1b-CODE` | §1b | The generator images are codes because a word has at most one indexed factorization | Use an ordered list of indices and injectivity of the induced `FreeMonoid.lift`; zero factorizations are allowed | corrected-target |
| `L1c-EMPTY` | §1c | The empty word is fixed and is a trivial solution of every iterate equation | Preserve as a source fact; it is distinct from the separate `n = 0` loophole | source-confirmed |
| `L1c-REL` | §1c | Two indexed code families in bijective correspondence determine a code isomorphism | Construct the equivalence of their generated submonoids and an ambient `PEquiv` | source-confirmed |
| `L1d-RIGHT` | §1d | A fresh-marker union with a “right prefix-code” is a code | Formalize the displayed no-proper-right-extension condition; this is modern prefix-freeness | source-confirmed |
| `L1d-LEFT` | §1d | The left-handed fresh-marker construction is dual | Formalize the displayed no-proper-left-extension condition; this is modern suffix-freeness | source-confirmed |
| `L1e-EPI` | §1e | A source indexed family is a code and each assigned target word belongs to some target code | Define `PaperCodeEpi` with a source code, a target code, and a possibly repeating/non-surjective selector; expose stronger map properties separately | corrected-target |
| `L2-RULEINV` | §2 | `(p₁,q₁,p₂,q₂,d)` has printed inverse `(p₂*,q₂,p₁*,q₁,-d)` | Audit syntax `printedInverse` is non-public; `printedInverse_fails_on_moving_rule` checks the failure. Public `Rule.apply_eq_some_iff_undo_eq_some` proves the repaired semantic inverse | corrected-target |
| `L2-REV` | §2 | A machine is reversible when the printed inverse family constitutes a machine and starred runs reverse | `Rule.tapeAction` composes checked-write and movement phases. `FiniteMachine.Reversible`, `backwardCompatible_iff_backwardUnique`, and `toPEquiv` separate table determinism from global inverse execution | corrected-target |
| `L2-COUPLE` | §2 | Forward rules, inverse rules, and halt-to-star switches run forward and then backward | Rebuild with disjoint phase tags and prove the switch and reverse run do not create conflicts | spec-gap |
| `L3-RELATIONS` | §3 | Three source relations per move rule, plus symbol identities, define an “epimorphism of codes” `τ_max` | Reconstruct every relation family and separately prove source codehood and the induced map's actual properties | spec-gap |
| `L3-CONFIG` | §3 | `α/ω/β` markers record the next-read and previous-written positions so `uᵢ₊₁ = τ_max(uᵢ)` | Require a well-formed configuration language, encode/decode, and a one-step iff theorem | spec-gap |
| `L3-MIN` | §3 | After conditional pruning to `τ_min`, code isomorphism implies machine reversibility | Formalize only this printed direction until reachable-language necessity is proved | source-confirmed |
| `L4a-SIM1` | §4a(1) | Every source step is simulated by a finite reversible macro-run | `History.strictlyReachable_of_source_step` gives one positive abstract simulator step, and `History.reversible` supplies the exact inverse. A later tape encoding may refine it to several microsteps | source-confirmed |
| `L4a-SIM2` | §4a(2) | Source steps use an epimorphism `τ`; simulator steps use a code isomorphism `θ` | Keep machine simulation correctness separate from the later word encoding | source-confirmed |
| `L4a-SIM3` | §4a(3) | A checkpoint `λ vᵢ μ wᵢ ν` recovers the source configuration and history | `History.Config.encode/decode/project` and `History.reachable_iff_valid` implement a cleaner full-predecessor checkpoint with exact recovery and no-spurious-checkpoint reflection; correspondence with the printed marker word remains open | spec-gap |
| `L4a-SIM4` | §4a(4) | `wᵢ = b² rₖ₁ … rₖᵢ b` records one distinguished nonidentity relation per source step | Stage 4 uses an explicit empty initial list and pushes the complete predecessor on every actual source step. `history_length_of_forward` proves one-entry growth. This is intentionally more redundant than the printed token scheme | corrected-target |
| `L4a-SIM5` | §4a(5) | Simulator halting checkpoints are exactly source-halting checkpoints | `terminal_forward_iff`, `haltsFrom_forward_iff`, and `universalHistory_halts_iff_eval_dom` prove preservation and reflection for the clean simulator | source-confirmed |
| `L4a-SIM6` | §4a(6) | The coupled machine reaches the starred initial configuration iff the source halts | Implement as a computable distinct-target reachability reduction | source-confirmed |
| `L4a-SIM7` | §4a(7) | Return or passage through a framed target can be conditioned on source halting | Build a complete gadget and prove an iff; the prose only sketches the construction and directly supports one implication for the extra target | spec-gap |
| `L4a-SKETCH` | §4a proof | One representative relation is simulated by sweeping, editing, appending history, shifting delimiters, and returning control | The clean abstract simulator is now complete. Its unbounded list has not been compiled into the paper's sweeping tape/marker rules, so a historical correspondence theorem remains a separate obligation | spec-gap |
| `L4b-THM1H` | Theorem 1 | Halting is recursively unsolvable for arbitrary reversible Turing machines | Uniform noncomputability of a validity-checked finite reversible-machine halting predicate | source-confirmed |
| `L4b-THM1R` | Theorem 1 | Return to the initial configuration is recursively unsolvable | Use `StateTransition.Reaches₁`; reflexive reachability would trivialize the claim | corrected-target |
| `L4b-THM1T` | Theorem 1 | Passage through a specified configuration other than the initial one is recursively unsolvable | Include target distinctness in the predicate/reduction output and prove both reduction directions | source-confirmed |
| `L4c-THM2F` | Theorem 2 | `w = θⁿ(w)` is recursively unsolvable in `n` for arbitrary given `w, θ` | Uniform existence of a positive, fully defined iterate; supplied-exponent evaluation is a separate decidable problem | corrected-target |
| `L4c-THM2O` | Theorem 2 | `w₁ = θⁿ(w₂)`, with `w₁ ≠ w₂`, is recursively unsolvable in `n` | Uniform existence of a positive, fully defined iterate from start `w₂` to target `w₁` | corrected-target |

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
  `Function.Injective (FreeMonoid.lift c)`. It will be related to mathlib's
  set-based `InformationTheory.UniquelyDecodable (Set.range ...)` together
  with injectivity of `c`, because a set forgets duplicate indices.
- “Complete code” is not a concept used by this note. English §1e mistranslates
  French `est bien un code` (“is indeed a code”).
- A code isomorphism is intrinsically a monoid equivalence between generated
  submonoids. Its ambient action is partial. Every iterate must remain in the
  next domain; undefinedness is represented by `none`, never by identity or a
  sink.
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
  reduction iff. The later formalization must supply it.
- The header records the proceedings session of 28 October 1963; the footnote
  records presentation of the note on 21 October 1963. Both scan readings are
  retained and have no mathematical effect.

## Declaration Map

Names in completed rows are exact checked declarations. Later rows remain
proposed API targets.

| Claim family | Proposed declaration family | Planned stage |
|---|---|---:|
| Generic reversible execution | `Step`, `BackwardUnique`, `ReversibleStep`, `ReversibleStep.next_eq_some_iff_prev_eq_some`, `ReversibleStep.reachable_iff_reverse_reachable`, `ReversibleStep.strictlyReachable_iff_reverse_strictlyReachable` | 2 (implemented) |
| Concrete machine semantics | `Tape`, `Config`, `Rule`, `FiniteMachine`, `FiniteMachine.step`, `FiniteMachine.TableDeterministic`, `FiniteMachine.Reversible` | 3 (implemented) |
| Repaired inverse semantics | `Tape.checkedWrite`, `Tape.moveEquiv`, `Rule.tapeAction`, `Rule.apply_eq_some_iff_undo_eq_some`, `FiniteMachine.step_eq_some_iff_reverseStep_eq_some`, `FiniteMachine.toPEquiv` | 3 (implemented atomically; finite microstate compiler open) |
| Effective source transition | `Source.universalEvalSearchStep`, `Source.universalEvalSearchStep_halts_iff_eval_dom`, `Source.universalEvalSearchStep_primrec`, `Source.evalSearchStart_joint_primrec` | 3 (implemented replacement source; finite compiler open) |
| History simulation | `History.forward`, `History.backward`, `History.reversible`, `History.reachable_iff_valid`, `History.source_reachable_iff_exists_reachable_checkpoint`, `History.haltsFrom_forward_iff` | 4 (implemented abstractly; historical tape compiler open) |
| Effective history interpretation | `FiniteMachine.step_uniform_primrec`, `History.forwardInterpreter_primrec`, `History.backwardInterpreter_primrec`, `History.finiteForward_uniform_primrec`, `History.finiteBackward_uniform_primrec`, `History.universalHistory_halts_iff_eval_dom` | 4 (implemented; generated conventional history machine open) |
| Coupling | `coupled_reaches_star_iff`, `coupled_returns₁_iff` | 5 |
| Machine undecidability | `reversibleHalting_not_computable`, `reversibleReturn_not_computable`, `reversibleReachability_not_computable` | 6 |
| Indexed codes | `IsIndexedCode`, `IsPrefixCode`, `IsSuffixCode` | 7 |
| Code maps | `CodeIso`, `PaperCodeEpi`, `iteratePEquiv` | 7 |
| Step encoding | `encodeConfig`, `stepCodeIso`, `iterate_encode_iff_reaches` | 8 |
| Iterate undecidability | `positiveFixedOrbit_not_computable`, `distinctOrbit_not_computable` | 9 |

Stage 3 supplies the concrete read-write-move semantics and repaired local and
global inverse laws for the machine portion of `L2-RULEINV`/`L2-REV`. Stage 4
supplies clean abstract analogues of the machine-simulation content in
`L4a-SIM1` through `L4a-SIM5`, including effectivity and halting reflection;
the printed marker words, finite macro-machine, and code-map layer remain open.
Starred coupling and the paper's halt-to-reverse construction remain in Stage
5, and a conventional finite tape compiler remains open, so no undecidability
claim follows from these declarations alone.

## Principal Reduction Map

```text
established encoded halting predicate
  -- computable finite-machine compiler + semantic iff -->
ordinary finite-machine halting
  -- effective abstract history interpreter + halting iff (Stage 4 checked) -->
abstract reversible-transition halting
  -- pending history-list-to-finite-tape compiler -->
finite reversible-machine halting
  -- phase-tagged coupling gadgets + iff -->
positive return / distinct-target reachability
  -- configuration code + step/iterate iff -->
positive fixed orbit / distinct orbit of a partial code isomorphism
```

Every arrow is a separate theorem obligation. A mathematical existence proof
of a simulator cannot discharge computability, well-formedness, preservation,
or reflection for any arrow.
