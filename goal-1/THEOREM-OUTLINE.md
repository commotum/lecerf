# Proposed Theorem and Reduction Outline

Stage 2 and Stage 3 declarations are identified as implemented below. All
later-layer names remain proposed Lean surfaces and may be refined when
implementation evidence requires it.

## 1. Partial Transition Systems (implemented)

Public modules:

```text
Lecerf.Transition.Core
Lecerf.Transition.Reversible
Lecerf.Transition.API
```

Checked core declarations:

```lean
abbrev Step (σ : Type u) := σ → Option σ

def StepRel (next : Step σ) (source target : σ) : Prop :=
  target ∈ next source

def BackwardUnique (next : Step σ) : Prop :=
  Relator.LeftUnique (StepRel next)

def Terminal (next : Step σ) (s : σ) : Prop :=
  next s = none

def HaltsFrom (next : Step σ) (s : σ) : Prop :=
  (StateTransition.eval next s).Dom

def Reachable (next : Step σ) (s t : σ) : Prop :=
  StateTransition.Reaches next s t

def StrictlyReachable (next : Step σ) (s t : σ) : Prop :=
  StateTransition.Reaches₁ next s t

def PositiveReturn (next : Step σ) (s : σ) : Prop :=
  StateTransition.Reaches₁ next s s

abbrev ReversibleStep (σ : Type u) := PEquiv σ σ
```

Checked theorem families include:

```lean
Step.stepRel_rightUnique
Step.successor_unique
terminal_iff_forall_not_step
reachable_iff_strictlyReachable_of_ne
haltsFrom_iff_exists_reachable_terminal
reachable_terminal_unique
Terminal.not_strictlyReachable

ReversibleStep.next_eq_some_iff_prev_eq_some
ReversibleStep.stepRel_iff_reverseStepRel
ReversibleStep.backwardUnique
ReversibleStep.stepRel_biUnique
ReversibleStep.reachable_iff_reverse_reachable
ReversibleStep.strictlyReachable_iff_reverse_strictlyReachable
ReversibleStep.positiveReturn_iff_reverse_positiveReturn
ReversibleStep.haltsFrom_iff_exists_terminal_reverseReachable
ReversibleStep.mem_eval_next_iff_mem_eval_prev
```

`ReversibleStep.next r` is `r`; `ReversibleStep.prev r` is `r.symm`. The exact
`PEquiv` inverse law, rather than function injectivity into `Option`, supplies
successful predecessor uniqueness. Multiple out-of-domain inputs may all map
to `none`.

`Reachable` is deliberately reflexive; dynamic return always uses
`StrictlyReachable`/`Reaches₁`. “Strictly” means positive length, not unequal
endpoints: a positive cycle returns to the same state. Forward and reverse
terminality are not pointwise equal, so the evaluation reversal theorem
requires both endpoint terminal hypotheses.

`Lecerf.Transition.Audit` is a non-public diagnostic leaf. It checks a partial
edge, a Boolean positive cycle, a noninjective bottom partial map, and a
deterministic merge whose individual branches are reversible but whose union
is not backward-unique.

## 2. Concrete Machine Syntax and Semantics (implemented)

Public modules:

```text
Lecerf.Machine.Tape
Lecerf.Machine.Core
Lecerf.Machine.Reversible
Lecerf.Machine.SourceBridge
Lecerf.Machine.API
```

`Lecerf.Machine.Audit` is a non-public diagnostic leaf.

The alphabet's `default` value is blank. `Side Γ` is intrinsically canonical:
it is empty or stores a nearest-first finite prefix ending in a certified
nonblank far cell. `Tape Γ` stores the scanned symbol plus two sides. Checked
runtime and encoding declarations include:

```lean
Side.cells             Side.head             Side.tail
Side.cons              Side.ofList_cells
Tape.write             Tape.move             Tape.act
Tape.move_reverse_move Tape.undo_act
Primcodable (Tape Γ)
```

`Tape.act written direction tape` is definitionally move-after-write.
`Tape.undo_act` states the required opposite order: move back, then restore the
old scanned symbol.

The exact finite syntax is:

```lean
structure Config (Q Γ) where
  state : Q
  tape  : Tape Γ

structure Rule (Q Γ) where
  source : Q
  read   : Γ
  target : Q
  write  : Γ
  move   : Tape.Move

structure FiniteMachine (Q Γ) where
  rules : List (Rule Q Γ)
```

`Config`, `Rule`, and `FiniteMachine` have constructive `Primcodable`
instances from their parameter instances. `FiniteMachine.lookup` and
`FiniteMachine.step` are executable first-match operations, and
`applyRules_eq_lookupRules_map` proves that first-success execution is exactly
lookup followed by read-write-move semantics. `HaltsAt` is absence of a
matching rule.

The checked separation between rule and whole-machine reversibility is:

```lean
Rule.tapeAction                    -- checked write, then total move
Rule.undo                          -- move back, check, restore
Rule.apply_eq_some_iff_undo_eq_some
Rule.toPEquiv

FiniteMachine.TableDeterministic
FiniteMachine.ForwardCompatible
FiniteMachine.BackwardCompatible
FiniteMachine.ReverseTableCompatible
FiniteMachine.reverseStep
FiniteMachine.Reversible :=
  TableDeterministic ∧ BackwardUnique step
```

`tableDeterministic_forwardCompatible` derives order-independent forward
semantics from key uniqueness. `reverseTableCompatible_backwardCompatible`
uses the finite local condition that distinct rules entering one target share
a movement and write distinct symbols. The headline exact results are:

```lean
step_eq_some_iff_reverseStep_eq_some
backwardCompatible_iff_backwardUnique
FiniteMachine.toPEquiv
```

Thus individually invertible rules are not conflated with a reversible rule
table. The audit's two-rule merge is table-deterministic and each entry has a
`PEquiv`, but the whole machine is not reversible. The same leaf defines the
paper's printed tuple inverse only as diagnostic syntax and proves it fails on
a concrete moving-rule successor.

The phase decomposition above is semantic, not yet a generated finite table
of ordinary rules with `normal`/`move` microstates. Likewise,
`ReverseTableCompatible` currently has a proved sufficient direction, while
the exact checked characterization uses semantic `BackwardCompatible`. The
finite syntactic compiler and decidable pairwise converse are explicit later
obligations, not consequences of `FiniteMachine.toPEquiv`.

The effective replacement halting source is one fixed transition:

```lean
abbrev EvalSearchConfig := (Nat.Partrec.Code × Nat) × Nat

universalEvalSearchStep : Step EvalSearchConfig
evalSearchStart : Nat.Partrec.Code → Nat → EvalSearchConfig

universalEvalSearchStep_halts_iff_eval_dom :
  HaltsFrom universalEvalSearchStep (evalSearchStart code input) ↔
    (code.eval input).Dom

universalEvalSearchStep_primrec : Primrec universalEvalSearchStep
evalSearchStart_primrec : Primrec fun code => evalSearchStart code input
evalSearchStart_joint_primrec :
  Primrec fun data => evalSearchStart data.1 data.2
```

This is a complete effective source-transition theorem, not yet the first
reduction arrow to `FiniteMachine`. The pinned mathlib TM route exposes an
existential `ToPartrec.Code` and noncomputable downstream support maps, so the
project records that obstruction instead of fabricating a compiler. A later
undecidability stage must still provide an explicit computable finite-machine
compiler and its own halting iff.

## 3. History-Recording Reversible Simulation

For a deterministic source `next : C → Option C`, a simulator checkpoint
contains the current source configuration and a history list. Each item records
the selected transition/rule and precisely the information erased by that
step. Microstep control uses a finite phase type.

The base checkpoint has an empty history. This deliberately repairs the
paper's inconsistent `w₀ = e` versus `w₀ = b³` formulas.

Required theorem chain:

```lean
encode_initial :
  decodeCheckpoint (initialCheckpoint c) = some (c, [])

checkpoint_step :
  sourceStep c = some c' →
  StateTransition.Reaches₁ simStep
    (checkpoint c h) (checkpoint c' (record c c' :: h))

checkpoint_reflect :
  StateTransition.Reaches simStep
    (checkpoint c []) (checkpoint c' h) →
  ∃ trace, sourceTrace sourceStep c trace c' ∧ historyMatches trace h

history_spec :
  decodeCheckpoint s = some (c, h) → historyInvariant sourceMachine c h

historySim_halts_iff :
  HaltsFrom simStep (checkpoint c []) ↔ HaltsFrom sourceStep c

historySim_reversible :
  Machine.Reversible historySimulator
```

The actual statement may use `StateTransition.Respects` for forward macro-step
simulation, but that theorem does not replace checkpoint reflection. The
construction on finite machine descriptions and its validity evidence must be
computable.

## 4. Forward–Reverse Coupling

Use disjoint phase tags:

```text
forward history simulation
  -> switch only at a terminal checkpoint
  -> inverse history simulation
  -> starred initial checkpoint
  -> optional reversible return/target gadget
```

Required exact specifications:

```lean
coupled_reaches_star_iff :
  HaltsFrom sourceStep sourceStart ↔
  Reachable coupledStep coupledStart starredInitial

coupled_returns₁_iff :
  HaltsFrom sourceStep sourceStart ↔
  PositiveReturn returnGadgetStep returnGadgetStart

coupled_reaches_target_iff :
  HaltsFrom sourceStep sourceStart ↔
  StrictlyReachable targetGadgetStep targetGadgetStart target

target_ne_start : target ≠ targetGadgetStart
```

The switch is permitted only after simulated halting. Phase disjointness must
show the union remains deterministic and backward-unique. The paper motivates
these gadgets but does not supply the second and third iff proofs.

## 5. Finite Decision Problems and Machine Reductions

Target predicates live on raw `Primcodable` descriptions. Malformed inputs are
false; reduction functions must always construct valid ones. Indicative
shapes:

```lean
def ReversibleHaltingYes (x : RevHaltInput) : Prop :=
  x.machine.Valid ∧ x.machine.Reversible ∧
    HaltsFrom x.machine.step x.start

def ReversibleReturnYes (x : RevReturnInput) : Prop :=
  x.machine.Valid ∧ x.machine.Reversible ∧
    PositiveReturn x.machine.step x.start

def ReversibleReachabilityYes (x : RevReachInput) : Prop :=
  x.machine.Valid ∧ x.machine.Reversible ∧ x.start ≠ x.target ∧
    StrictlyReachable x.machine.step x.start x.target
```

If `Reversible` already entails deterministic forward and backward execution,
that implication is proved in the machine API; validity still checks all
finite bounds and lookup constraints.

For source predicate

```lean
def PartrecHalts (c : Nat.Partrec.Code) : Prop := (c.eval 0).Dom
```

construct computable raw-description maps and iff theorems:

```lean
compileHalt   : Nat.Partrec.Code → RevHaltInput
compileReturn : Nat.Partrec.Code → RevReturnInput
compileReach  : Nat.Partrec.Code → RevReachInput

PartrecHalts c ↔ ReversibleHaltingYes      (compileHalt c)
PartrecHalts c ↔ ReversibleReturnYes       (compileReturn c)
PartrecHalts c ↔ ReversibleReachabilityYes (compileReach c)
```

Package each as `ManyOneReducible`. Transfer noncomputability from
`ComputablePred.halting_problem 0` with
`ComputablePred.computable_of_manyOneReducible`. No theorem may replace the
computable maps with existence of an equivalent machine.

## 6. Words, Codes, and Code Maps

Use:

```lean
abbrev Word (A : Type u) := FreeMonoid A

def IsIndexedCode (c : I → Word A) : Prop :=
  Function.Injective (FreeMonoid.lift c)
```

Prove the bridge to mathlib's set predicate, accounting for lost indices:

```lean
isIndexedCode_iff_injective_and_uniquelyDecodable :
  IsIndexedCode c ↔
    Function.Injective c ∧
      InformationTheory.UniquelyDecodable
        (Set.range fun i => (c i).toList)
```

The exact orientation/namespace can change after compiling the proof, but the
extra generator injectivity cannot be omitted.

Prefix/suffix predicates use the displayed equations in §1d:

```text
PrefixFree C: x,y ∈ C and x is a prefix of y imply x = y
SuffixFree C: x,y ∈ C and x is a suffix of y imply x = y
```

Exclude the empty word where needed; a naive pairwise predicate alone admits
the singleton empty code. Prove both fresh-marker extension lemmas with
freshness meaning that the marker occurs in no component word.

Map classes remain distinct:

- `MonoidHom`: a total multiplicative function;
- `IsIndexedCode`: injectivity of the generator-induced homomorphism;
- `CodeIso`: a `MulEquiv` between source/target generated submonoids, with a
  multiplicative ambient partial-equivalence view;
- `PaperCodeEpi`: a source code, target code, and generator selector whose
  values may repeat and need not cover the target code.

For a same-ambient-type partial equivalence:

```lean
def PEquiv.iterate (θ : α ≃. α) : Nat → α ≃. α
  | 0     => PEquiv.refl α
  | n + 1 => (iterate θ n).trans θ
```

Prove that its forward application is repeated `Option.bind`. No undefined
application is totalized as identity or an absorbing value.

## 7. Machine-Step Encoding by Codes

Construct a finite alphabet containing tape symbols, control/head markers,
boundaries, phase/history symbols, and fresh separators. Proposed public
surface:

```lean
encodeConfig : Config → Word Alphabet
decodeConfig : Word Alphabet → Option Config
stepCodeIso  : CodeIso Alphabet

decode_encode : decodeConfig (encodeConfig c) = some c

stepCodeIso_apply_iff :
  machine.step c = some c' ↔
    stepCodeIso.toPEquiv (encodeConfig c) = some (encodeConfig c')

iterate_encode_iff_reaches :
  (stepCodeIso.toPEquiv.iterate n) (encodeConfig c) =
      some (encodeConfig c') ↔
    exactSteps machine.step n c c'
```

The reverse implication is essential: no malformed ambient word may
masquerade as an encoded checkpoint. Every rule family, boundary case,
stationary move, and tape-extension case must be covered. A later comparison
theorem may relate this cleaner encoding to Lecerf's `α/ω/β` relations.

## 8. Iterate Decision Problems

Actual inputs are finite code-isomorphism descriptions with executable
validation and interpretation, not raw `PEquiv` functions. The semantic
predicates are:

```lean
def PositiveFixedOrbitYes (x : FixedOrbitInput) : Prop :=
  x.iso.Valid ∧
    ∃ k : Nat,
      (x.iso.toPEquiv.iterate (k + 1)) x.word = some x.word

def DistinctOrbitYes (x : DistinctOrbitInput) : Prop :=
  x.iso.Valid ∧ x.start ≠ x.target ∧
    ∃ k : Nat,
      (x.iso.toPEquiv.iterate (k + 1)) x.start = some x.target
```

This fixes the paper's orientation: in `w₁ = θⁿ(w₂)`, `w₂` is the start and
`w₁` is the target. Positive iteration is explicit in both predicates; it is
logically redundant in the distinct case but keeps the API uniform.

Separate effective results:

```text
iterateAtExponent_decidable   checking a supplied finite exponent
positiveFixedOrbit_re         existential yes-instances are semidecidable
distinctOrbit_re              existential yes-instances are semidecidable
positiveFixedOrbit_not_computable
distinctOrbit_not_computable
```

Semidecidability requires an executable finite description and decidable word
equality. It does not imply a total witness finder or a decision procedure for
no-instances.

## Principal Reduction Chain

```text
Nat.Partrec.Code halting
  ≤₀ computable search-transition halting
  ≤₀ ordinary finite-machine halting
  ≤₀ reversible-machine halting
  ≤₀ reversible positive return / distinct reachability
  ≤₀ positive fixed orbit / distinct orbit of a partial code isomorphism
```

The first generic search step may be folded into the finite-machine compiler,
but the semantic iff and computability proof remain explicit. Fixed orbit is
fed by positive return; distinct orbit is fed by start-to-distinct-target
reachability. Each arrow requires:

1. a computable function on finite encodings;
2. a proof that its output passes the target validity predicate;
3. preservation of yes-instances; and
4. reflection/no-spurious yes-instances.

Simulation, code encoding, and reduction theorems stay in separate layers even
when later proofs reuse the same construction.
