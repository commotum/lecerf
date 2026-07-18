import Lecerf.Machine.Compiler.FiniteSource
import Lecerf.Machine.TwoTape.HistoryCompiler.Effectivity

/-!
# Raw decision problems for finite reversible two-tape machines

All descriptions below use one fixed finite control type and two fixed finite
alphabets large enough for the universal history compiler.  The machine table
itself remains part of the input.  A decidable syntactic certificate guards
each yes-predicate; malformed or uncertified descriptions are therefore not a
loophole in the later reductions.

These are explicitly two-tape problems.  No claim is made here that the
machines have already been lowered back to the project's one-tape model.
-/

namespace Lecerf.Undecidability.ReversibleTwoTape

open Lecerf.Transition
open Lecerf.Machine

namespace HC = Lecerf.Machine.TwoTape.HistoryCompiler
namespace FS = Lecerf.Machine.Compiler.FiniteSource

/-- Fixed work-machine state type selected by the universal source bridge. -/
abbrev SourceState := FS.State

/-- Fixed work-tape alphabet selected by the universal source bridge. -/
abbrev WorkSymbol := FS.Symbol

/-- Fixed control type of the compiled reversible two-tape machines. -/
abbrev MachineState := HC.Control SourceState WorkSymbol

/-- Fixed history-tape alphabet containing source-rule tokens. -/
abbrev HistorySymbol := HC.Mark SourceState WorkSymbol

/-- Raw target-machine descriptions all have these fixed finite types. -/
abbrev TargetMachine :=
  TwoTape.FiniteMachine MachineState WorkSymbol HistorySymbol

/-- Configurations of raw target-machine descriptions. -/
abbrev TargetConfig :=
  TwoTape.Config MachineState WorkSymbol HistorySymbol

/-- A machine description paired with a proposed start configuration. -/
abbrev HaltingInput := TargetMachine × TargetConfig

/-- A machine description paired with a proposed return configuration. -/
abbrev ReturnInput := TargetMachine × TargetConfig

/-- A machine description, start configuration, and specified target. -/
abbrev ReachabilityInput := TargetMachine × TargetConfig × TargetConfig

/-- Executable finite certificate used to guard every raw decision problem. -/
def Certified (machine : TargetMachine) : Prop :=
  machine.SyntacticallyReversible

instance (machine : TargetMachine) : Decidable (Certified machine) :=
  inferInstance

/-- The raw certificate predicate is primitive recursive in the finite table
description. -/
theorem certified_primrec : PrimrecPred Certified := by
  exact TwoTape.FiniteMachine.syntacticallyReversible_primrec

/-- Certified halting: the supplied finite reversible table terminates from
the supplied configuration. -/
def HaltingYes (input : HaltingInput) : Prop :=
  Certified input.1 ∧ HaltsFrom input.1.step input.2

/-- Certified positive return: at least one step returns to the supplied
configuration. -/
def ReturnYes (input : ReturnInput) : Prop :=
  Certified input.1 ∧ PositiveReturn input.1.step input.2

/-- Certified reachability of a supplied, structurally distinct target. -/
def ReachabilityYes (input : ReachabilityInput) : Prop :=
  Certified input.1 ∧ input.2.1 ≠ input.2.2 ∧
    StrictlyReachable input.1.step input.2.1 input.2.2

/-- The validity guard of a halting yes-instance implies semantic
whole-machine reversibility. -/
theorem HaltingYes.reversible {input : HaltingInput}
    (yes : HaltingYes input) : input.1.Reversible :=
  yes.1.reversible

/-- The validity guard of a return yes-instance implies semantic
whole-machine reversibility. -/
theorem ReturnYes.reversible {input : ReturnInput}
    (yes : ReturnYes input) : input.1.Reversible :=
  yes.1.reversible

/-- The validity guard of a reachability yes-instance implies semantic
whole-machine reversibility. -/
theorem ReachabilityYes.reversible {input : ReachabilityInput}
    (yes : ReachabilityYes input) : input.1.Reversible :=
  yes.1.reversible

end Lecerf.Undecidability.ReversibleTwoTape
