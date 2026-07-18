# Proposed Theorem and Reduction Outline

Stage 2 through Stage 6 declarations are identified as implemented below.
The word, code-encoding, and iterate-problem layers remain proposed Lean
surfaces and may be refined when implementation evidence requires it.

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

For this one-tape model, the phase decomposition above remains semantic rather
than a generated finite table of ordinary `normal`/`move` microstates.
Likewise, `ReverseTableCompatible` has a proved sufficient direction while the
exact checked characterization uses semantic `BackwardCompatible`. Stage 6
does not claim a converse here: it introduces a separate simultaneous
read-write-move two-tape model with its own decidable sufficient validity
certificate. A future two-to-one-tape lowering must still implement and prove
the missing phase-control bridge.

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

This remains a complete effective source-transition theorem. Stage 6 also
closes the finite source side by selecting one fixed universal
`Turing.ToPartrec.Code`, compiling its proved finite support to a fixed
one-tape machine, and putting the varying `Nat.Partrec.Code` on the input tape:

```lean
Compiler.UniversalSource.encodedInput_joint_primrec

Compiler.FiniteSource.machine : FiniteMachine State Symbol
Compiler.FiniteSource.machine_tableDeterministic
Compiler.FiniteSource.halts_iff_eval_dom

Compiler.FiniteSource.initial_joint_primrec
Compiler.FiniteSource.initial_primrec
```

`universalCode`, the finite support, the induced fixed encodings, and the
fixed machine table are isolated noncomputable constants. The changing input
configuration is primitive recursive; no varying source code is passed to a
classical machine selector.

## 3. History-Recording Reversible Simulation (implemented)

Public modules:

```text
Lecerf.Machine.Effectivity
Lecerf.Machine.History.Core
Lecerf.Machine.History.Correctness
Lecerf.Machine.History.Computable
Lecerf.Machine.History.API
```

`Lecerf.Machine.History.Audit` is a non-public diagnostic leaf.

For any deterministic partial source `next : Step σ`, the clean simulator
stores the current source state and the complete predecessor at every
successful step:

```lean
structure History.Config (σ) where
  current : σ
  history : List σ

History.forward next ⟨current, history⟩ =
  (next current).map fun target => ⟨target, current :: history⟩
```

`History.backward` accepts a popped predecessor only if recomputing its source
step produces the recorded current state. Thus a blind pop from malformed
ambient data is impossible. Checked representation and inverse declarations
include:

```lean
History.Config.encode
History.Config.decode
History.Config.project
History.Config.decode_encode
History.Config.encode_decode
History.Config.encode_injective

History.forward_eq_some_iff_backward_eq_some
History.reversible : ReversibleStep (History.Config σ)
```

This is a correctness-first equivalent construction, not Lecerf's compact
marker tape. One source step is one simulator step; the complete predecessor
contains more information than the minimal erased symbol/rule identifier.
The empty `Config.initial` repairs the paper's inconsistent empty versus `b³`
base history.

The invariant is generated from the initial state and actual source steps:

```lean
History.Valid next start : History.Config σ → Prop

History.reachable_iff_valid :
  Reachable (History.forward next) (History.Config.initial start) config ↔
    History.Valid next start config

History.strictlyReachable_of_source_step :
  next current = some target →
  StrictlyReachable (History.forward next)
    (History.Config.encode current history)
    (History.Config.encode target (current :: history))

History.source_reachable_iff_exists_reachable_checkpoint :
  Reachable next start target ↔
    ∃ history, Reachable (History.forward next)
      (History.Config.initial start)
      (History.Config.encode target history)

History.terminal_forward_iff :
  Terminal (History.forward next) config ↔ Terminal next config.current

History.haltsFrom_forward_iff :
  HaltsFrom (History.forward next) (History.Config.initial start) ↔
    HaltsFrom next start
```

`reachable_iff_valid` is the exact reflection/no-spurious-checkpoint theorem;
the invariant is not a theorem precondition that callers must assume.
`history_length_of_forward` proves one-entry growth. Checkpoint uniqueness is
correctly indexed by elapsed time:
`Valid.eq_of_history_length_eq` and
`reachable_checkpoint_unique_of_history_length_eq` show equality at equal
history lengths. A cycle may revisit the same source state with a longer valid
history, as the audit checks. `Valid.history_eq_nil_iff` makes the fresh
checkpoint unique, and `Valid.backward_reachable_initial` proves inverse
retracking to it.

Effectivity is checked at both abstraction levels:

```lean
FiniteMachine.step_uniform_primrec :
  Primrec fun data : FiniteMachine Q Γ × Machine.Config Q Γ =>
    data.1.step data.2

History.forwardInterpreter_primrec
History.backwardInterpreter_primrec

History.finiteForward_uniform_primrec
History.finiteBackward_uniform_primrec
History.finiteDescribedInitial_primrec

History.universalHistoryStart_joint_primrec
History.universalForward_primrec
History.universalBackward_primrec
History.universalHistory_halts_iff_eval_dom
```

The finite theorems in this abstract layer interpret an existing finite
machine description against an unbounded abstract history log. They do not
themselves generate a conventional one-tape `FiniteMachine`. Stage 6 supplies
a separate finite two-tape history-token compiler with a concrete history
tape and microstates. Thus the finite reversible-machine claim is now proved
for that two-tape target, while one-tape lowering remains distinct.

## 4. Forward–Reverse Coupling (implemented)

Public modules:

```text
Lecerf.Machine.Coupling.Core
Lecerf.Machine.Coupling.Correctness
Lecerf.Machine.Coupling.Computable
Lecerf.Machine.Coupling.API
```

The non-public `Coupling.Audit` leaf contains executable examples and axiom
checks. The runtime uses disjoint phase tags and provides two exact partial
equivalences:

```lean
inductive Coupling.Direction | forward | reverse
structure Coupling.Config (σ : Type u)

Coupling.turnaroundNext_eq_some_iff_turnaroundPrev_eq_some
Coupling.turnaround : ReversibleStep (Coupling.Config σ)

Coupling.returnNext_eq_some_iff_returnPrev_eq_some
Coupling.returnGadget : ReversibleStep (Coupling.Config σ)

Coupling.exists_returnNext
Coupling.exists_returnPrev
Coupling.returnGadget_not_terminal
```

`turnaround` executes the given reversible step forward, switches phase at a
forward-terminal state, retraces with its exact inverse, and stops at an
inverse-terminal state. `returnGadget` closes every inverse-terminal boundary
back to the corresponding forward-tagged state. The closure is uniform: it
does not compare against a privileged initial state or inspect a halting
witness.

For the reversible full-history simulator, the exact headline declarations
are:

```lean
Coupling.History.start_ne_target (initial : σ) :
  Coupling.History.start initial ≠ Coupling.History.target initial

Coupling.History.target_strictlyReachable_iff_halts
    [DecidableEq σ] (source : Step σ) (initial : σ) :
  StrictlyReachable (Coupling.History.turnaroundStep source).next
      (Coupling.History.start initial) (Coupling.History.target initial) ↔
    HaltsFrom source initial

Coupling.History.terminal_target
    [DecidableEq σ] (source : Step σ) (initial : σ) :
  Terminal (Coupling.History.turnaroundStep source).next
    (Coupling.History.target initial)

Coupling.History.positiveReturn_iff_halts
    [DecidableEq σ] (source : Step σ) (initial : σ) :
  PositiveReturn (Coupling.History.returnStep source).next
      (Coupling.History.start initial) ↔
    HaltsFrom source initial
```

Generic forward/reverse path lifts supply the constructive directions. The
history `Generated` invariant reflects any reachable reverse phase to source
halting. The positive-return reflection uses the exact unique predecessor of
the forward start (`return_prev_start` and `predecessor_of_start`). Separately,
`history_length_lt_of_strictlyReachable` and `not_positiveReturn_forward`
certify that the forward history phase has no positive cycle.

Effectivity is checked at three levels:

```lean
Coupling.turnaroundNextInterpreter_primrec
Coupling.turnaroundPrevInterpreter_primrec
Coupling.returnNextInterpreter_primrec
Coupling.returnPrevInterpreter_primrec

Coupling.History.turnaroundStep_next_primrec
Coupling.History.turnaroundStep_prev_primrec
Coupling.History.returnStep_next_primrec
Coupling.History.returnStep_prev_primrec

Coupling.History.finiteTurnaroundNext_uniform_primrec
Coupling.History.finiteTurnaroundPrev_uniform_primrec
Coupling.History.finiteReturnNext_uniform_primrec
Coupling.History.finiteReturnPrev_uniform_primrec
Coupling.History.finiteDescribedStartTarget_primrec

Coupling.History.universalStartTarget_joint_primrec
Coupling.History.universalTurnaroundNext_primrec
Coupling.History.universalTurnaroundPrev_primrec
Coupling.History.universalReturnNext_primrec
Coupling.History.universalReturnPrev_primrec

Coupling.History.universalTarget_strictlyReachable_iff_eval_dom
Coupling.History.universalPositiveReturn_iff_eval_dom
```

The finite theorems here interpret an existing `FiniteMachine` description on
an abstract phase-tagged full-history state. Stage 6 does not reinterpret them
as syntax: it proves an independent concrete two-tape compiler and connects
its finite microstep semantics to the same halting, return, and target ideas.

## 5. Finite Two-Tape Decision Problems and Machine Reductions (implemented)

Public modules:

```text
Lecerf.Machine.Compiler.UniversalSource
Lecerf.Machine.Compiler.Table
Lecerf.Machine.Compiler.TapeBridge
Lecerf.Machine.Compiler.FiniteSource
Lecerf.Machine.Compiler.FiniteSourceComputable
Lecerf.Machine.Compiler.ReversibleUniversal

Lecerf.Machine.TwoTape.Core
Lecerf.Machine.TwoTape.Reversible
Lecerf.Machine.TwoTape.Effectivity
Lecerf.Machine.TwoTape.Validity
Lecerf.Machine.TwoTape.HistoryCompiler.Core
Lecerf.Machine.TwoTape.HistoryCompiler.Basic
Lecerf.Machine.TwoTape.HistoryCompiler.Trace
Lecerf.Machine.TwoTape.HistoryCompiler.Reversible
Lecerf.Machine.TwoTape.HistoryCompiler.Runtime
Lecerf.Machine.TwoTape.HistoryCompiler.Correctness
Lecerf.Machine.TwoTape.HistoryCompiler.Effectivity

Lecerf.Undecidability.ReversibleTwoTape.Problems
Lecerf.Undecidability.ReversibleTwoTape.Reduction
Lecerf.Undecidability.ReversibleTwoTape.API
```

`ReversibleTwoTape.Audit` is a non-public executable and axiom-audit leaf.

### Finite target syntax, validity, and history compiler

`TwoTape.Config Q Γ₁ Γ₂` carries two canonical project tapes.
`TwoTape.Rule Q Γ₁ Γ₂` reads both heads and then writes and moves both tapes
simultaneously. `TwoTape.FiniteMachine` is a raw finite first-match rule list.
The exact inverse and semantic separation are checked by:

```lean
TwoTape.Rule.apply_eq_some_iff_undo_eq_some
TwoTape.Rule.toPEquiv

TwoTape.FiniteMachine.TableDeterministic
TwoTape.FiniteMachine.IncomingSeparatedPair
TwoTape.FiniteMachine.OutputSeparated
TwoTape.FiniteMachine.SyntacticallyReversible
TwoTape.FiniteMachine.SyntacticallyReversible.reversible
TwoTape.FiniteMachine.syntacticallyReversible_primrec
TwoTape.FiniteMachine.step_uniform_primrec
```

`SyntacticallyReversible` is a decidable, primitive-recursive sufficient
certificate: forward rule keys are pairwise separated and incoming rules are
separated on at least one written tape head. It implies
`TableDeterministic ∧ BackwardUnique step`. No converse claiming that every
semantically reversible table passes this certificate is asserted.

The finite history alphabet and compiler controls are:

```lean
inductive TwoTape.HistoryCompiler.Mark
  | blank | bottom | token (rule : Machine.Rule Q Γ)

inductive TwoTape.HistoryCompiler.Control
  | forward (state : Q)
  | reverse (state : Q)
  | inspect (state : Q)
  | restore (rule : Machine.Rule Q Γ)

TwoTape.HistoryCompiler.historyMachine
TwoTape.HistoryCompiler.turnaroundMachine
TwoTape.HistoryCompiler.returnMachine
TwoTape.HistoryCompiler.checkpoint
TwoTape.HistoryCompiler.bottomTarget
```

The first tape runs the source; the second records a complete source rule per
successful step. The open table switches at a source terminal state and
reverses to a distinct exposed-bottom target. The closed table adds one
bottom rule returning to the fresh forward checkpoint. The generated-table
and correctness declarations include:

```lean
TwoTape.HistoryCompiler.historyMachine_syntacticallyReversible
TwoTape.HistoryCompiler.turnaroundMachine_syntacticallyReversible
TwoTape.HistoryCompiler.returnMachine_syntacticallyReversible

TwoTape.HistoryCompiler.historyMachine_reversible
TwoTape.HistoryCompiler.turnaroundMachine_reversible
TwoTape.HistoryCompiler.returnMachine_reversible

TwoTape.HistoryCompiler.checkpoint_ne_bottomTarget
TwoTape.HistoryCompiler.historyMachine_haltsFrom_iff_source
TwoTape.HistoryCompiler.turnaround_bottom_strictlyReachable_iff_source_halts
TwoTape.HistoryCompiler.return_positiveReturn_iff_source_halts

TwoTape.HistoryCompiler.checkpoint_primrec
TwoTape.HistoryCompiler.reverseCheckpoint_primrec
TwoTape.HistoryCompiler.bottomTarget_primrec
```

The `CanonicalRun` invariant classifies every state reachable from a generated
checkpoint, including the forward, boundary, scan, inspect, restore, reverse,
and exposed-bottom microstates. It supplies reflection: neither a malformed
history nor a spurious microstate can produce the target or positive return in
the headline iff theorems.

### Fixed universal instantiation

`Compiler.ReversibleUniversal` instantiates the compiler at the fixed
one-tape universal source:

```lean
Compiler.ReversibleUniversal.historyTable
Compiler.ReversibleUniversal.turnaroundTable
Compiler.ReversibleUniversal.returnTable

Compiler.ReversibleUniversal.sourceStart
Compiler.ReversibleUniversal.startCheckpoint
Compiler.ReversibleUniversal.bottomTarget

Compiler.ReversibleUniversal.historyTable_syntacticallyReversible
Compiler.ReversibleUniversal.turnaroundTable_syntacticallyReversible
Compiler.ReversibleUniversal.returnTable_syntacticallyReversible

Compiler.ReversibleUniversal.startCheckpoint_primrec
Compiler.ReversibleUniversal.bottomTarget_primrec
Compiler.ReversibleUniversal.startCheckpoint_ne_bottomTarget

Compiler.ReversibleUniversal.eval_dom_iff_history_halts
Compiler.ReversibleUniversal.eval_dom_iff_turnaround_bottom_strictlyReachable
Compiler.ReversibleUniversal.eval_dom_iff_return_positiveReturn
```

All three machine tables are closed constants. Classical choice and
`Finset.toList` enumeration are confined to those fixed constants and their
fixed encodings. Only the start/target configurations vary with the source
code. The final maps are declared inside a `noncomputable section` because
they mention the constants, but the complete maps have checked `Primrec` and
`Computable` proofs; there is no varying noncomputable compiler or oracle.

### Raw problems and exact reductions

The raw target types have fixed finite state and alphabet types, while the
finite rule table remains part of each input:

```lean
abbrev HaltingInput := TargetMachine × TargetConfig
abbrev ReturnInput := TargetMachine × TargetConfig
abbrev ReachabilityInput := TargetMachine × TargetConfig × TargetConfig

def Certified (machine : TargetMachine) : Prop :=
  machine.SyntacticallyReversible

def HaltingYes (input : HaltingInput) : Prop :=
  Certified input.1 ∧ HaltsFrom input.1.step input.2

def ReturnYes (input : ReturnInput) : Prop :=
  Certified input.1 ∧ PositiveReturn input.1.step input.2

def ReachabilityYes (input : ReachabilityInput) : Prop :=
  Certified input.1 ∧ input.2.1 ≠ input.2.2 ∧
    StrictlyReachable input.1.step input.2.1 input.2.2
```

`certified_primrec` proves the raw guard primitive recursive.
`HaltingYes.reversible`, `ReturnYes.reversible`, and
`ReachabilityYes.reversible` derive semantic whole-machine reversibility from
the guard. Uncertified descriptions are false, and every generated instance
has an explicit certificate.

The source predicate, reduction maps, effectivity theorems, and exact iff
theorems are:

```lean
def PartrecHalts0 (code : Nat.Partrec.Code) : Prop :=
  (Nat.Partrec.Code.eval code 0).Dom

compileHalting      : Nat.Partrec.Code → HaltingInput
compileReturn       : Nat.Partrec.Code → ReturnInput
compileReachability : Nat.Partrec.Code → ReachabilityInput

compileHalting_primrec
compileHalting_computable
compileReturn_primrec
compileReturn_computable
compileReachability_primrec
compileReachability_computable

compileHalting_certified
compileReturn_certified
compileReachability_certified
compileReachability_start_ne_target

partrecHalts0_iff_haltingYes
partrecHalts0_iff_returnYes
partrecHalts0_iff_reachabilityYes
```

The three packaged reductions and transferred noncomputability theorems are:

```lean
partrecHalts0_manyOne_haltingYes : PartrecHalts0 ≤₀ HaltingYes
partrecHalts0_manyOne_returnYes : PartrecHalts0 ≤₀ ReturnYes
partrecHalts0_manyOne_reachabilityYes : PartrecHalts0 ≤₀ ReachabilityYes

haltingYes_not_computable : ¬ComputablePred HaltingYes
returnYes_not_computable : ¬ComputablePred ReturnYes
reachabilityYes_not_computable : ¬ComputablePred ReachabilityYes
```

Each last theorem transfers `ComputablePred.halting_problem 0` backward along
the displayed `ManyOneReducible`; none relies on a project-specific
undecidability axiom. These are finite reversible **two-tape** results. They do
not yet state the same decision problems for the earlier one-tape
`FiniteMachine`, and they do not yet identify the compiler with Lecerf's
historical compact marker encoding.

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
  |-- ≤₀ certified halting of a finite reversible two-tape table
  |-- ≤₀ certified positive return of a finite reversible two-tape table
  `-- ≤₀ certified distinct-target strict reachability of a finite
          reversible two-tape table

Planned next machine/code arrows:
  finite reversible two-tape positive return
    -> positive fixed orbit of a partial code isomorphism
  finite reversible two-tape distinct reachability
    -> distinct orbit of a partial code isomorphism
```

The three Stage-6 arrows are direct packaged reductions. Internally, their iff
proofs pass through a fixed universal one-tape source and fixed finite
two-tape history/turnaround/return tables; the only varying data are
primitive-recursive configurations. Fixed orbit will be fed by positive
return, and distinct orbit by start-to-distinct-target reachability. Each
future arrow still requires:

1. a computable function on finite encodings;
2. a proof that its output passes the target validity predicate;
3. preservation of yes-instances; and
4. reflection/no-spurious yes-instances.

Simulation, code encoding, and reduction theorems stay in separate layers even
when later proofs reuse the same construction. A two-to-one-tape lowering and
the correspondence with Lecerf's historical marker encoding also remain
separate from the implemented Stage-6 reduction branch.
