import Lecerf.Machine.Compiler.FiniteSourceComputable
import Lecerf.Machine.TwoTape.HistoryCompiler.Correctness
import Lecerf.Machine.TwoTape.HistoryCompiler.Effectivity

/-!
# A fixed universal reversible two-tape machine

This leaf instantiates the generic finite history compiler at the fixed
universal source table.  The source table, its finite encodings, and the three
compiled target tables are closed noncomputable constants: their definitions
include the one-time choices and `Finset.toList` order used by the finite
compiler.  No varying program is compiled.  Only the initial and target
configurations vary with a partial-recursive code, and those maps are proved
primitive recursive below.
-/

namespace Lecerf.Machine.Compiler.ReversibleUniversal

open Lecerf.Transition

noncomputable section

/-- Control states of the fixed conventional universal source table. -/
abbrev SourceState := Lecerf.Machine.Compiler.FiniteSource.State

/-- Tape symbols of the fixed conventional universal source table. -/
abbrev SourceSymbol := Lecerf.Machine.Compiler.FiniteSource.Symbol

/-- Configurations of the fixed conventional universal source table. -/
abbrev SourceConfig := Lecerf.Machine.Config SourceState SourceSymbol

/-- Control states of all three fixed reversible target tables. -/
abbrev TargetControl :=
  Lecerf.Machine.TwoTape.HistoryCompiler.Control SourceState SourceSymbol

/-- History alphabet of all three fixed reversible target tables. -/
abbrev HistoryMark :=
  Lecerf.Machine.TwoTape.HistoryCompiler.Mark SourceState SourceSymbol

/-- Configurations shared by the three fixed reversible target tables. -/
abbrev TargetConfig :=
  Lecerf.Machine.TwoTape.Config TargetControl SourceSymbol HistoryMark

/-- The common type of the three fixed finite target tables. -/
abbrev TargetMachine :=
  Lecerf.Machine.TwoTape.FiniteMachine TargetControl SourceSymbol HistoryMark

/-- Forward-only fixed history table. -/
def historyTable : TargetMachine :=
  Lecerf.Machine.TwoTape.HistoryCompiler.historyMachine
    Lecerf.Machine.Compiler.FiniteSource.machine

/-- Fixed open forward/turnaround/reverse table. -/
def turnaroundTable : TargetMachine :=
  Lecerf.Machine.TwoTape.HistoryCompiler.turnaroundMachine
    Lecerf.Machine.Compiler.FiniteSource.machine

/-- Fixed closed return table. -/
def returnTable : TargetMachine :=
  Lecerf.Machine.TwoTape.HistoryCompiler.returnMachine
    Lecerf.Machine.Compiler.FiniteSource.machine

/-- Source start for the universal run of `code` on the fixed input `0`. -/
def sourceStart (code : Nat.Partrec.Code) : SourceConfig :=
  Lecerf.Machine.Compiler.FiniteSource.initial
    (Lecerf.Machine.Compiler.UniversalSource.encodedInput code 0).1

/-- Fresh forward history checkpoint for the fixed universal run. -/
def startCheckpoint (code : Nat.Partrec.Code) : TargetConfig :=
  Lecerf.Machine.TwoTape.HistoryCompiler.checkpoint (sourceStart code)

/-- Reverse-phase checkpoint with the source start and empty history restored. -/
def reverseTargetCheckpoint (code : Nat.Partrec.Code) : TargetConfig :=
  Lecerf.Machine.TwoTape.HistoryCompiler.reverseCheckpoint (sourceStart code)

/-- Distinct exposed-bottom target of the open turnaround computation. -/
def bottomTarget (code : Nat.Partrec.Code) : TargetConfig :=
  Lecerf.Machine.TwoTape.HistoryCompiler.bottomTarget (sourceStart code)

/-- The fixed forward-only table has a finite syntactic reversibility
certificate. -/
theorem historyTable_syntacticallyReversible :
    historyTable.SyntacticallyReversible := by
  exact
    Lecerf.Machine.TwoTape.HistoryCompiler.historyMachine_syntacticallyReversible
      Lecerf.Machine.Compiler.FiniteSource.machine_tableDeterministic

/-- The fixed open table has a finite syntactic reversibility certificate. -/
theorem turnaroundTable_syntacticallyReversible :
    turnaroundTable.SyntacticallyReversible := by
  exact
    Lecerf.Machine.TwoTape.HistoryCompiler.turnaroundMachine_syntacticallyReversible
      Lecerf.Machine.Compiler.FiniteSource.machine_tableDeterministic

/-- The fixed closed table has a finite syntactic reversibility certificate. -/
theorem returnTable_syntacticallyReversible :
    returnTable.SyntacticallyReversible := by
  exact Lecerf.Machine.TwoTape.HistoryCompiler.returnMachine_syntacticallyReversible
    Lecerf.Machine.Compiler.FiniteSource.machine_tableDeterministic

/-- The fixed forward-only table is semantically deterministic and
reversible. -/
theorem historyTable_reversible : historyTable.Reversible := by
  exact Lecerf.Machine.TwoTape.HistoryCompiler.historyMachine_reversible
    Lecerf.Machine.Compiler.FiniteSource.machine_tableDeterministic

/-- The fixed open table is semantically deterministic and reversible. -/
theorem turnaroundTable_reversible : turnaroundTable.Reversible := by
  exact Lecerf.Machine.TwoTape.HistoryCompiler.turnaroundMachine_reversible
    Lecerf.Machine.Compiler.FiniteSource.machine_tableDeterministic

/-- The fixed closed table is semantically deterministic and reversible. -/
theorem returnTable_reversible : returnTable.Reversible := by
  exact Lecerf.Machine.TwoTape.HistoryCompiler.returnMachine_reversible
    Lecerf.Machine.Compiler.FiniteSource.machine_tableDeterministic

/-- The conventional source start varies primitive recursively with the
encoded partial-recursive program. -/
theorem sourceStart_primrec : Primrec sourceStart := by
  exact (Lecerf.Machine.Compiler.FiniteSource.initial_primrec 0).of_eq
    fun _ => rfl

/-- The varying forward checkpoint of the fixed history table is primitive
recursive. -/
theorem startCheckpoint_primrec : Primrec startCheckpoint := by
  exact (Lecerf.Machine.TwoTape.HistoryCompiler.checkpoint_primrec.comp
    sourceStart_primrec).of_eq fun _ => rfl

/-- The varying reverse checkpoint is primitive recursive as well. -/
theorem reverseTargetCheckpoint_primrec : Primrec reverseTargetCheckpoint := by
  exact (Lecerf.Machine.TwoTape.HistoryCompiler.reverseCheckpoint_primrec.comp
    sourceStart_primrec).of_eq fun _ => rfl

/-- The varying distinct bottom target of the open table is primitive
recursive. -/
theorem bottomTarget_primrec : Primrec bottomTarget := by
  exact (Lecerf.Machine.TwoTape.HistoryCompiler.bottomTarget_primrec.comp
    sourceStart_primrec).of_eq fun _ => rfl

/-- The open reduction's generated endpoints are structurally distinct for
every encoded program. -/
theorem startCheckpoint_ne_bottomTarget (code : Nat.Partrec.Code) :
    startCheckpoint code ≠ bottomTarget code := by
  simpa [startCheckpoint, bottomTarget] using
    (Lecerf.Machine.TwoTape.HistoryCompiler.checkpoint_ne_bottomTarget
      (sourceStart code))

/-- The fixed history table halts from its generated checkpoint exactly when
the encoded program halts on input zero. -/
theorem eval_dom_iff_history_halts (code : Nat.Partrec.Code) :
    (Nat.Partrec.Code.eval code 0).Dom ↔
      HaltsFrom historyTable.step (startCheckpoint code) := by
  calc
    (Nat.Partrec.Code.eval code 0).Dom ↔
        HaltsFrom Lecerf.Machine.Compiler.FiniteSource.machine.step
          (sourceStart code) := by
      simpa [HaltsFrom, sourceStart] using
        (Lecerf.Machine.Compiler.FiniteSource.halts_iff_eval_dom code 0).symm
    _ ↔ HaltsFrom historyTable.step (startCheckpoint code) := by
      simpa [historyTable, startCheckpoint] using
        (Lecerf.Machine.TwoTape.HistoryCompiler.historyMachine_haltsFrom_iff_source
          Lecerf.Machine.Compiler.FiniteSource.machine_tableDeterministic
          (sourceStart code)).symm

/-- The fixed open table reaches its distinct exposed-bottom target in a
positive number of steps exactly when the encoded program halts on input
zero. -/
theorem eval_dom_iff_turnaround_bottom_strictlyReachable
    (code : Nat.Partrec.Code) :
    (Nat.Partrec.Code.eval code 0).Dom ↔
      StrictlyReachable turnaroundTable.step
        (startCheckpoint code) (bottomTarget code) := by
  calc
    (Nat.Partrec.Code.eval code 0).Dom ↔
        HaltsFrom Lecerf.Machine.Compiler.FiniteSource.machine.step
          (sourceStart code) := by
      simpa [HaltsFrom, sourceStart] using
        (Lecerf.Machine.Compiler.FiniteSource.halts_iff_eval_dom code 0).symm
    _ ↔ StrictlyReachable turnaroundTable.step
          (startCheckpoint code) (bottomTarget code) := by
      simpa [turnaroundTable, startCheckpoint, bottomTarget] using
        (Lecerf.Machine.TwoTape.HistoryCompiler.turnaround_bottom_strictlyReachable_iff_source_halts
          Lecerf.Machine.Compiler.FiniteSource.machine_tableDeterministic
          (sourceStart code)).symm

/-- The fixed closed table has a positive return to its generated checkpoint
exactly when the encoded program halts on input zero. -/
theorem eval_dom_iff_return_positiveReturn (code : Nat.Partrec.Code) :
    (Nat.Partrec.Code.eval code 0).Dom ↔
      PositiveReturn returnTable.step (startCheckpoint code) := by
  calc
    (Nat.Partrec.Code.eval code 0).Dom ↔
        HaltsFrom Lecerf.Machine.Compiler.FiniteSource.machine.step
          (sourceStart code) := by
      simpa [HaltsFrom, sourceStart] using
        (Lecerf.Machine.Compiler.FiniteSource.halts_iff_eval_dom code 0).symm
    _ ↔ PositiveReturn returnTable.step (startCheckpoint code) := by
      simpa [returnTable, startCheckpoint] using
        (Lecerf.Machine.TwoTape.HistoryCompiler.return_positiveReturn_iff_source_halts
          Lecerf.Machine.Compiler.FiniteSource.machine_tableDeterministic
          (sourceStart code)).symm

end

end Lecerf.Machine.Compiler.ReversibleUniversal
