# Theorem and Reduction Outline

Stages 2 through 9 implement the declarations identified below, and Stage 10
audits their integrated public and trust surface. Historical one-tape and
finite local relation-list reconciliation remains explicitly outside the
cleaner theorem branch claimed by these declarations.

## 1. Partial Transition Systems (implemented)

Public modules:

```text
Lecerf.Transition.Core
Lecerf.Transition.Reversible
Lecerf.Transition.ExactCore
Lecerf.Transition.ExactEffectivity
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
Lecerf.Machine.TwoTape.API
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

## 6. Words, Codes, and Code Maps (implemented)

Public modules:

```text
Lecerf.Word.Code
Lecerf.Word.Prefix
Lecerf.Word.CodeMorphism
Lecerf.Word.API
```

`Lecerf.Word.Audit` is a non-public diagnostic leaf.

The checked indexed-code core is:

```lean
abbrev Lecerf.Word (A : Type u) := FreeMonoid A

def Lecerf.Word.IsIndexedCode (c : I → Word A) : Prop :=
  Function.Injective (FreeMonoid.lift c)

def Lecerf.Word.codewordSet (c : I → Word A) : Set (List A) :=
  Set.range fun i ↦ (c i).toList

isIndexedCode_iff_injective_and_uniquelyDecodable :
  IsIndexedCode c ↔
    Function.Injective c ∧
      InformationTheory.UniquelyDecodable
        (Set.range fun i ↦ (c i).toList)
```

The generator-injectivity conjunct is necessary: the set predicate forgets
duplicate indices. Checked supporting declarations include:

```text
IsIndexedCode.injective
IsIndexedCode.ne_one
IsIndexedCode.uniquelyDecodable
isIndexedCode_of_injective_of_uniquelyDecodable
isIndexedCode_singleton_iff
isIndexedCode_of
```

Thus duplicate indices and empty codewords are rejected by the indexed
predicate rather than being hidden by the set representation.

The prefix/suffix layer exposes:

```lean
def FreshFor (marker : A) (c : I → Word A) : Prop
def IsPrefixFree (c : I → Word A) : Prop
def IsSuffixFree (c : I → Word A) : Prop
def IsPrefixCode (c : I → Word A) : Prop
def IsSuffixCode (c : I → Word A) : Prop

IsPrefixCode.isIndexedCode
IsSuffixCode.isIndexedCode
IsIndexedCode.reverse
isIndexedCode_reverse_iff
```

`IsPrefixCode` and `IsSuffixCode` pair their pairwise condition with
`∀ i, c i ≠ 1`; a singleton empty family is therefore not promoted to a code.
The checked fresh-marker results are:

```lean
isIndexedCode_prependMarkerExtension_of_freshFor_left
isIndexedCode_appendMarkerExtension_of_freshFor_left
isIndexedCode_prependMarkerExtension
isIndexedCode_appendMarkerExtension
```

The sharp prepend theorem assumes `IsIndexedCode c`, `IsPrefixFree k`, and
`FreshFor marker c`; its append dual uses `IsSuffixFree k`. The final two
paper-shaped theorems additionally accept `FreshFor marker k`, documenting
that the paper's extra auxiliary-family freshness is sufficient but
mathematically redundant.

Generated submonoids and map classes are separate checked objects:

```lean
def generated (codewords : I → Word A) : Submonoid (Word A) :=
  Submonoid.closure (Set.range codewords)

def generator (codewords : I → Word A) (i : I) : generated codewords

noncomputable def encodingEquiv (codewords : I → Word A)
    (code : IsIndexedCode codewords) :
    Word I ≃* generated codewords

structure InjectiveMorphism (M N) [Monoid M] [Monoid N] where
  toMonoidHom : M →* N
  injective' : Function.Injective toMonoidHom

structure CodeIso (A : Type u) (I : Type v) where
  source : I → Word A
  target : I → Word A
  sourceCode : IsIndexedCode source
  targetCode : IsIndexedCode target
  toMulEquiv : generated source ≃* generated target
  map_generator : ∀ i,
    toMulEquiv (generator source i) = generator target i

structure PaperCodeEpi (A : Type u) (I : Type v) (J : Type w) where
  source : I → Word A
  target : J → Word A
  selector : I → J
  sourceCode : IsIndexedCode source
  targetCode : IsIndexedCode target
  toMonoidHom : generated source →* generated target
  map_generator : ∀ i,
    toMonoidHom (generator source i) = generator target (selector i)
```

`MonoidHom`, `InjectiveMorphism`, `CodeIso`, and `PaperCodeEpi` are not
aliases. In particular, `PaperCodeEpi.selector` need not be injective or
surjective; the audit constructs one that repeats a selected target and omits
another. `CodeIso.ofCodes` canonically constructs the intrinsic equivalence
from two equally indexed codes, while `CodeIso.toPaperCodeEpi` forgets to the
paper-specific class with identity selector.

The semantic ambient action is:

```lean
noncomputable def CodeIso.toPEquiv (iso : CodeIso A I) : Word A ≃. Word A

CodeIso.toPEquiv_isSome_iff :
  (iso.toPEquiv word).isSome ↔ word ∈ generated iso.source

CodeIso.toPEquiv_symm_isSome_iff :
  (iso.toPEquiv.symm word).isSome ↔ word ∈ generated iso.target

CodeIso.toPEquiv_generator :
  iso.toPEquiv (iso.source i) = some (iso.target i)
```

The file also proves the exact in-domain/out-of-domain equations, inverse
equations, identity equation, and multiplication law. `encodingEquiv`, both
`ofCodes` constructors, and `CodeIso.toPEquiv` are intentionally
noncomputable: a bare semantic code proof does not provide an executable
decoder or generated-submonoid membership test. Stage 8 preserves that general
boundary. For the particular successful-edge schema, it separately supplies
canonical whole-configuration decoding and an executable finite-table
interpreter, then proves that interpreter equal to the semantic ambient
action. The generally infinite edge index and semantic `CodeIso` never become
stored computability data.

Partial iteration is project-local under `Lecerf.PEquiv`:

```lean
def iterate (theta : X ≃. X) : Nat → X ≃. X
  | 0 => PEquiv.refl X
  | n + 1 => (iterate theta n).trans theta

iterate_succ_apply :
  iterate theta (n + 1) x = (iterate theta n x).bind theta

iterate_add :
  iterate theta (m + n) = (iterate theta m).trans (iterate theta n)

iterate_symm :
  (iterate theta n).symm = iterate theta.symm n

iterate_symm_eq_some_iff :
  iterate theta.symm n target = some source ↔
    iterate theta n source = some target

def positiveIterate (theta : X ≃. X) (k : Nat) : X ≃. X :=
  iterate theta (k + 1)

def PositiveIterate (theta : X ≃. X) (source target : X) : Prop :=
  ∃ k, positiveIterate theta k source = some target
```

`DefinedAt`, `PositiveDefinedAt`, and `PositiveDefined` keep supplied-exponent
and existential definedness separate. `iterate_add_eq_none_of_eq_none` proves
that undefinedness propagates; `positiveIterate_zero` means one application,
not exponent zero. No undefined application is totalized as identity or an
absorbing value.

The focused builds passed with 522 jobs for `Word.Code`, 526 for
`Word.Prefix`, 693 for `Word.CodeMorphism`, and 696 for `Word.API` plus the
audit. The adjacent audit/root build passed with 914 jobs and the full build
with 913. The audit reports `[propext, Quot.sound]` for the code bridge and
pure iteration declarations, and additionally `Classical.choice` for the two
paper-shaped marker theorems and semantic ambient generator equation. No
project-specific axiom is used.

## 7. Machine-Step Encoding by Codes (Stage 8, implemented)

Public modules:

```text
Lecerf.Encoding.ConfigCode
Lecerf.Encoding.ConfigCodeEffectivity
Lecerf.Transition.ExactCore
Lecerf.Transition.Exact
Lecerf.Encoding.StepCode.Core
Lecerf.Encoding.StepCode.Correctness
Lecerf.Encoding.StepCode.Interpreter
Lecerf.Encoding.StepCode.Effectivity
Lecerf.Encoding.StepCode.API
```

`Lecerf.Encoding.StepCode.Audit` is non-public. `StepCode.API` is a thin
re-export of the correctness and effectivity leaves.

### Executable whole-configuration frames

For any `[Primcodable C]`, the codec uses the finite alphabet `Bool` and the
canonical self-delimiting frame

```lean
def unaryFrame : Nat → List Bool
  | 0 => [false]
  | n + 1 => true :: unaryFrame n

def encodeConfigBits (config : C) : List Bool :=
  unaryFrame (Encodable.encode config)

def encodeConfig (config : C) : Word Bool :=
  FreeMonoid.ofList (encodeConfigBits config)
```

The exact decoders use `Encodable.decode₂`, not the weaker raw decoder, and
therefore reject natural codes outside the canonical range. The checked
single- and concatenated-frame surface includes:

```text
decodeUnaryFrame_eq_some_iff
decodeConfigBits_encodeConfigBits
decodeConfigBits_eq_some_iff
decodeConfig_encodeConfig
decodeConfig_eq_some_iff
decodeConfigListBits_encodeConfigListBits
decodeConfigListBits_eq_some_iff
decodeConfigs_encodeConfigs
decodeConfigs_eq_some_iff
encodeConfigs_eq_lift
encodeConfig_isPrefixFree
encodeConfig_isPrefixCode
encodeConfig_isIndexedCode
```

Thus decoder success reconstructs the complete accepted word; unterminated,
trailing, malformed, and noncanonical frames cannot masquerade as encoded
configurations. `ConfigCodeEffectivity` supplies a list-induced
`Primcodable (Word A)` representation and proves `Primrec` and `Computable`
versions of unary framing, single-configuration encoding/decoding, and
concatenated encoding/decoding. In particular:

```lean
encodeConfigs_primrec :
  Primrec (encodeConfigs : List C → Word Bool)

decodeConfigListBits_primrec :
  Primrec (decodeConfigListBits : List Bool → Option (List C))

decodeConfigs_primrec :
  Primrec (decodeConfigs : Word Bool → Option (List C))
```

### Exact transition and semantic code schema

`Lecerf.Transition.ExactCore` defines bind-preserving `exactIterate` and
`ExactSteps` and proves their addition, reflexive-reachability, and
strict-reachability laws. `Lecerf.Transition.Exact` adds the isolated bridge to
`Lecerf.PEquiv.iterate` without pulling the Word layer into `Transition.API`.
Failure at any intermediate step remains `none`.

For a finite two-tape table, the semantic relation index is the generally
infinite successful-edge type:

```lean
structure Edge (machine : FiniteMachine Q Γ₁ Γ₂) where
  source : Config Q Γ₁ Γ₂
  target : Config Q Γ₁ Γ₂
  step_eq : machine.step source = some target
```

`sourceWord` and `targetWord` encode the two endpoints. Forward functionality
makes the source projection injective. The target boundary is exact:

```lean
targetWord_isIndexedCode_iff_backwardUnique :
  IsIndexedCode (targetWord (machine := machine)) ↔
    BackwardUnique machine.step
```

Consequently `stepCodeEpi` gives the paper's weaker `PaperCodeEpi` for any
table, while `stepCodeIso machine backward` is a genuine `CodeIso Bool
(Edge machine)` under whole-step predecessor uniqueness. These are semantic,
noncomputable constructors over an infinite successful-edge schema; they are
not the runtime descriptor and are not claimed to be Lecerf's finite local
relation table.

One-step preservation and reflection are both implemented:

```lean
stepCodeIso_apply_eq_some_iff_exists :
  stepCodeIso.toPEquiv (encodeConfig source) = some word ↔
    ∃ target, machine.step source = some target ∧
      word = encodeConfig target

stepCodeIso_apply_eq_some_iff :
  stepCodeIso.toPEquiv (encodeConfig source) =
      some (encodeConfig target) ↔
    machine.step source = some target

stepCodeIso_apply_eq_none_iff :
  stepCodeIso.toPEquiv (encodeConfig source) = none ↔
    machine.step source = none
```

The strong existential form rules out malformed successful targets. The
generic theorem covers left, stay, right, blank extension, and every table
rule through the already checked `machine.step`, rather than enumerating only
representative directions.

Supplied iteration and positive reachability are exact as well:

```text
stepCodeIso_iterate_encodeConfig
stepCodeIso_iterate_eq_some_iff_exists
stepCodeIso_iterate_eq_some_iff
stepCodeIso_definedAt_iff
stepCodeIso_iterate_iff_machinePEquiv
stepCodeIso_positiveIterate_iff_strictlyReachable
```

In particular, a successful ambient iterate from a canonical source always
ends at a canonical configuration word, and `PositiveIterate` corresponds to
strict machine reachability with exponent `k + 1`, never exponent zero.

### Constructive all-word interpreter and finite descriptor

`StepCode.traverse`, `applyWord`, and `liftPEquiv` decode a whole canonical
frame sequence, apply a partial configuration map pointwise, and re-encode it.
For every semantically reversible finite table:

```lean
liftPEquiv_machine_eq_stepCodeIso_toPEquiv :
  liftPEquiv (machine.toPEquiv reversible) =
    (stepCodeIso machine reversible.2).toPEquiv
```

This is equality on all Boolean words, not merely the single-configuration
generators.

The runtime boundary is finite despite the infinite semantic edge index:

```lean
abbrev Descriptor Q Γ₁ Γ₂ := FiniteMachine Q Γ₁ Γ₂

def Descriptor.Valid (descriptor) : Prop :=
  descriptor.SyntacticallyReversible

def Descriptor.checkedApply (descriptor) (word : Word Bool) :=
  if descriptor.Valid then descriptor.applyWord word else none
```

`Descriptor.Valid` is decidable and primitive recursive. The uniform
effectivity and semantic-agreement declarations are:

```text
Descriptor.applyWord_uniform_primrec
Descriptor.applyWord_uniform_computable
Descriptor.valid_primrec
Descriptor.checkedApply_uniform_primrec
Descriptor.checkedApply_uniform_computable
Descriptor.applyWord_eq_stepCodeIso_toPEquiv
Descriptor.checkedApply_eq_stepCodeIso_toPEquiv
```

Invalid tables are rejected before word interpretation. Only the forward
interpreter is claimed primitive recursive; no executable inverse is inferred
from the semantic `PEquiv`.

This implemented theorem is deliberately cleaner than the historical note:
it frames whole canonical two-tape configurations and uses an infinite
successful-edge schema uniformly described by a finite raw machine. A literal
finite local `α/ω/β` construction, and the two-to-one-tape lowering needed
to connect the project's two-tape source to that syntax, remain unresolved.

## 8. Iterate Decision Problems (Stage 9, implemented)

Public module:

```text
Lecerf.Undecidability.CodeIterates.API
```

Implementation leaves:

```text
Lecerf.Transition.ExactEffectivity
Lecerf.Undecidability.CodeIterates.Problems
Lecerf.Undecidability.CodeIterates.Effectivity
Lecerf.Undecidability.CodeIterates.Correspondence
Lecerf.Undecidability.CodeIterates.Reduction
```

`Lecerf.Undecidability.CodeIterates.Audit` is a non-public diagnostic leaf.
The runtime input uses the Stage-8 finite raw descriptor and Boolean words; it
does not store the generally infinite `Edge` type, a semantic `CodeIso`, a
`PEquiv`, a function, a validity proof, or an orbit witness:

```lean
abbrev CodeDescriptor :=
  StepCode.Descriptor ReversibleTwoTape.MachineState
    ReversibleTwoTape.WorkSymbol ReversibleTwoTape.HistorySymbol

abbrev FixedOrbitInput := CodeDescriptor × Word Bool

abbrev DistinctOrbitInput :=
  CodeDescriptor × Word Bool × Word Bool

abbrev SuppliedExponentInput :=
  CodeDescriptor × Nat × Word Bool × Word Bool
```

The products associate to the right. For `DistinctOrbitInput`, the order is
descriptor, start, target. For `SuppliedExponentInput`, it is descriptor,
exponent, start, target. Hence the paper's `w₁ = θⁿ(w₂)` is represented with
`w₂` as the stored start and `w₁` as the stored target.

The checked predicates are exactly:

```lean
def PositiveFixedOrbitYes (input : FixedOrbitInput) : Prop :=
  input.1.Valid ∧
    ∃ k : Nat,
      ExactSteps input.1.checkedApply (k + 1) input.2 input.2

def DistinctOrbitYes (input : DistinctOrbitInput) : Prop :=
  input.1.Valid ∧ input.2.1 ≠ input.2.2 ∧
    ∃ k : Nat,
      ExactSteps input.1.checkedApply (k + 1)
        input.2.1 input.2.2

def PositiveIterateAtYes (input : SuppliedExponentInput) : Prop :=
  input.1.Valid ∧ input.2.1 ≠ 0 ∧
    ExactSteps input.1.checkedApply input.2.1
      input.2.2.1 input.2.2.2
```

The existential predicates quantify a predecessor `k`; their actual exponent
is definitionally `k + 1`. The supplied predicate instead stores the exponent
and rejects zero explicitly. All three use `ExactSteps`, whose
`Option.bind` semantics preserves undefined intermediate applications rather
than replacing them with an identity, sink, or default word.

The uniform effectivity declarations are:

```text
Transition.exactIterate_uniform_primrec
checkedExactIterate_uniform_primrec
positiveIterateAtYes_primrec
positiveIterateAtYes_computablePred
```

The two search relations and their effectivity facts are:

```text
FixedOrbitWitnessYes
fixedOrbitWitnessYes_primrec
fixedOrbitWitnessYes_computablePred
DistinctOrbitWitnessYes
distinctOrbitWitnessYes_primrec
distinctOrbitWitnessYes_computablePred
positiveFixedOrbitYes_iff_exists_witness
distinctOrbitYes_iff_exists_witness
positiveFixedOrbitYes_re
distinctOrbitYes_re
```

Thus checking a supplied positive exponent is primitive recursive, while
existence of some positive exponent is recursively enumerable. These are
deliberately different claims: neither `positiveFixedOrbitYes_re` nor
`distinctOrbitYes_re` supplies a total witness finder or a total decision
procedure for no-instances.

Checked iteration and semantic code-isomorphism iteration agree through the
following implemented correspondence chain:

```text
checkedExactIterate_eq_stepCodeIso_iterate
checkedExactSteps_iff_stepCodeIso_iterate_eq_some
checkedPositiveExactSteps_iff_stepCodeIso_positiveIterate
positiveFixedOrbitYes_iff_stepCodeIso_positiveIterate
distinctOrbitYes_iff_stepCodeIso_positiveIterate
positiveIterateAtYes_iff_stepCodeIso_iterate
encodedCheckedExactSteps_iff_exactSteps
encodedCheckedPositiveExactSteps_iff_strictlyReachable
positiveFixedOrbitYes_encodeConfig_iff_returnYes
distinctOrbitYes_encodeConfig_iff_reachabilityYes
```

The first six theorems connect a valid descriptor's executable
`checkedApply` to `(stepCodeIso descriptor valid.reversible.2).toPEquiv` at an
exact or positive exponent. The next two specialize canonical configuration
words to exact machine execution and strict reachability. The last two give
the exact positive-return/fixed-orbit and distinct-reachability/orbit
equivalences used by the reductions.

The generic endpoint encodings and reductions are:

```text
encodeReturnInput
encodeReturnInput_primrec
encodeReturnInput_computable
encodeReachabilityInput
encodeReachabilityInput_primrec
encodeReachabilityInput_computable
encodeReachabilityInput_start_ne_target
returnYes_iff_positiveFixedOrbitYes
reachabilityYes_iff_distinctOrbitYes
returnYes_manyOne_positiveFixedOrbitYes
reachabilityYes_manyOne_distinctOrbitYes
```

Both maps preserve the raw descriptor verbatim and only apply
`ConfigCode.encodeConfig` to endpoints. Consequently the iff theorems cover
invalid descriptors too: the source and target predicates share the same
validity conjunct, and the checked interpreter rejects invalid tables. The
maps do not repair malformed descriptors or prove only a certified forward
direction. Configuration-code injectivity supplies the unequal-word proof for
the distinct reduction.

Composing these generic arrows with the Stage-6 halting reductions yields:

```lean
partrecHalts0_manyOne_positiveFixedOrbitYes :
  ReversibleTwoTape.PartrecHalts0 ≤₀ PositiveFixedOrbitYes

partrecHalts0_manyOne_distinctOrbitYes :
  ReversibleTwoTape.PartrecHalts0 ≤₀ DistinctOrbitYes

positiveFixedOrbitYes_not_computable :
  ¬ComputablePred PositiveFixedOrbitYes

distinctOrbitYes_not_computable :
  ¬ComputablePred DistinctOrbitYes
```

The noncomputability proofs transfer `ComputablePred.halting_problem 0`
backward along the explicit composed many-one reductions; no new
undecidability axiom is introduced.

This makes precise one useful reading of the paper's “recursively unsolvable
in `n`”: the uniform problem asking whether a positive exponent exists is not
computable, even though a supplied exponent can be checked. It does not claim
that recognizing a correct supplied exponent is undecidable. The current
finite runtime descriptor uniformly presents a generally infinite
successful-edge code schema. A literal finite local `α`/`ω`/`β` relation
list, proof that it realizes the same iterates, a two-to-one-tape lowering,
and a theorem about every independently presented code isomorphism remain
historical/generalization obligations rather than consequences of Stage 9.

## Principal Reduction Chain

```text
Nat.Partrec.Code halting
  |-- ≤₀ certified halting of a finite reversible two-tape table
  |-- ≤₀ certified positive return of a finite reversible two-tape table
  `-- ≤₀ certified distinct-target strict reachability of a finite
          reversible two-tape table

Implemented Stage-8 semantic/effective bridge:
  finite reversible two-tape table plus configurations
    -> finite validity-guarded Descriptor plus canonical Boolean words
    -> exact semantic CodeIso iterate / positive-orbit correspondence

Implemented Stage-9 generic arrows:
  finite reversible two-tape positive return
    -> positive fixed orbit of a code isomorphism's partial ambient action
  finite reversible two-tape distinct reachability
    -> distinct orbit of a code isomorphism's partial ambient action

Implemented direct compositions:
  Nat.Partrec.Code halting
    -> positive fixed orbit of a code isomorphism's partial ambient action
  Nat.Partrec.Code halting
    -> distinct orbit of a code isomorphism's partial ambient action
```

The three Stage-6 arrows are direct packaged reductions. Internally, their iff
proofs pass through a fixed universal one-tape source and fixed finite
two-tape history/turnaround/return tables; the only varying data are
primitive-recursive configurations. Stage 8 supplies the finite descriptor,
primitive-recursive interpreter, validity guard, and no-spurious-iterate
theorems. Stage 9 feeds fixed orbit from positive return and distinct orbit
from start-to-distinct-target reachability through the computable maps
`encodeReturnInput` and `encodeReachabilityInput`. Preservation and reflection
are the exact iff theorems `returnYes_iff_positiveFixedOrbitYes` and
`reachabilityYes_iff_distinctOrbitYes`; the packaged generic arrows are
`returnYes_manyOne_positiveFixedOrbitYes` and
`reachabilityYes_manyOne_distinctOrbitYes`.

Simulation, code encoding, and reduction theorems stay in separate layers even
though the final compositions reuse all three. A finite local edge presentation,
the two-to-one-tape lowering, and correspondence with Lecerf's historical
marker encoding remain separate from the implemented Stage-6/8/9 branch.
They are not silently folded into the current code-isomorphism claim.
