import Lecerf.Machine.Compiler.ReversibleUniversal
import Lecerf.Undecidability.ReversibleTwoTape.Problems
import Mathlib.Computability.Reduce

/-!
# Reductions to raw reversible two-tape decision problems

The three maps below reuse fixed closed finite tables. They are declared
`noncomputable` only because those constants contain the one-time finite
encoding, enumeration-order, and universal-program choices isolated by the
compiler. No target machine is selected from the varying source code: only
the primitive-recursive start and target configurations vary.
-/

namespace Lecerf.Undecidability.ReversibleTwoTape

open Lecerf.Transition
open Lecerf.Machine

/-- Mathlib's partial-recursive halting problem, specialized to input zero. -/
def PartrecHalts0 (code : Nat.Partrec.Code) : Prop :=
  (Nat.Partrec.Code.eval code 0).Dom

noncomputable section

/-- Raw halting instance using the fixed forward history table. -/
def compileHalting (code : Nat.Partrec.Code) : HaltingInput :=
  (Lecerf.Machine.Compiler.ReversibleUniversal.historyTable,
    Lecerf.Machine.Compiler.ReversibleUniversal.startCheckpoint code)

/-- Raw return instance using the fixed closed table. -/
def compileReturn (code : Nat.Partrec.Code) : ReturnInput :=
  (Lecerf.Machine.Compiler.ReversibleUniversal.returnTable,
    Lecerf.Machine.Compiler.ReversibleUniversal.startCheckpoint code)

/-- Raw reachability instance using the fixed open table and computed target. -/
def compileReachability (code : Nat.Partrec.Code) : ReachabilityInput :=
  (Lecerf.Machine.Compiler.ReversibleUniversal.turnaroundTable,
    Lecerf.Machine.Compiler.ReversibleUniversal.startCheckpoint code,
    Lecerf.Machine.Compiler.ReversibleUniversal.bottomTarget code)

theorem compileHalting_primrec : Primrec compileHalting := by
  exact (Primrec.const
    Lecerf.Machine.Compiler.ReversibleUniversal.historyTable).pair
      Lecerf.Machine.Compiler.ReversibleUniversal.startCheckpoint_primrec

theorem compileHalting_computable : Computable compileHalting :=
  compileHalting_primrec.to_comp

theorem compileReturn_primrec : Primrec compileReturn := by
  exact (Primrec.const
    Lecerf.Machine.Compiler.ReversibleUniversal.returnTable).pair
      Lecerf.Machine.Compiler.ReversibleUniversal.startCheckpoint_primrec

theorem compileReturn_computable : Computable compileReturn :=
  compileReturn_primrec.to_comp

theorem compileReachability_primrec : Primrec compileReachability := by
  exact (Primrec.const
    Lecerf.Machine.Compiler.ReversibleUniversal.turnaroundTable).pair
      (Lecerf.Machine.Compiler.ReversibleUniversal.startCheckpoint_primrec.pair
        Lecerf.Machine.Compiler.ReversibleUniversal.bottomTarget_primrec)

theorem compileReachability_computable : Computable compileReachability :=
  compileReachability_primrec.to_comp

/-- Every generated halting instance carries the required certificate. -/
theorem compileHalting_certified (code : Nat.Partrec.Code) :
    Certified (compileHalting code).1 := by
  exact
    Lecerf.Machine.Compiler.ReversibleUniversal.historyTable_syntacticallyReversible

theorem compileHalting_reversible (code : Nat.Partrec.Code) :
    (compileHalting code).1.Reversible := by
  exact Lecerf.Machine.Compiler.ReversibleUniversal.historyTable_reversible

/-- Every generated return instance carries the required certificate. -/
theorem compileReturn_certified (code : Nat.Partrec.Code) :
    Certified (compileReturn code).1 := by
  exact
    Lecerf.Machine.Compiler.ReversibleUniversal.returnTable_syntacticallyReversible

theorem compileReturn_reversible (code : Nat.Partrec.Code) :
    (compileReturn code).1.Reversible := by
  exact Lecerf.Machine.Compiler.ReversibleUniversal.returnTable_reversible

/-- Every generated reachability instance carries the required certificate. -/
theorem compileReachability_certified (code : Nat.Partrec.Code) :
    Certified (compileReachability code).1 := by
  exact
    Lecerf.Machine.Compiler.ReversibleUniversal.turnaroundTable_syntacticallyReversible

theorem compileReachability_reversible (code : Nat.Partrec.Code) :
    (compileReachability code).1.Reversible := by
  exact Lecerf.Machine.Compiler.ReversibleUniversal.turnaroundTable_reversible

/-- Computed reachability endpoints are distinct for every source code. -/
theorem compileReachability_start_ne_target (code : Nat.Partrec.Code) :
    (compileReachability code).2.1 ≠ (compileReachability code).2.2 := by
  exact Lecerf.Machine.Compiler.ReversibleUniversal.startCheckpoint_ne_bottomTarget
    code

/-- Source halting is preserved and reflected by guarded raw halting. -/
theorem partrecHalts0_iff_haltingYes (code : Nat.Partrec.Code) :
    PartrecHalts0 code ↔ HaltingYes (compileHalting code) := by
  constructor
  · intro halts
    exact ⟨compileHalting_certified code,
      (Lecerf.Machine.Compiler.ReversibleUniversal.eval_dom_iff_history_halts
        code).mp halts⟩
  · intro yes
    exact
      (Lecerf.Machine.Compiler.ReversibleUniversal.eval_dom_iff_history_halts
        code).mpr yes.2

/-- Source halting is preserved and reflected by guarded positive return. -/
theorem partrecHalts0_iff_returnYes (code : Nat.Partrec.Code) :
    PartrecHalts0 code ↔ ReturnYes (compileReturn code) := by
  constructor
  · intro halts
    exact ⟨compileReturn_certified code,
      (Lecerf.Machine.Compiler.ReversibleUniversal.eval_dom_iff_return_positiveReturn
        code).mp halts⟩
  · intro yes
    exact
      (Lecerf.Machine.Compiler.ReversibleUniversal.eval_dom_iff_return_positiveReturn
        code).mpr yes.2

/-- Source halting is preserved and reflected by guarded strict reachability
of the computed distinct target. -/
theorem partrecHalts0_iff_reachabilityYes (code : Nat.Partrec.Code) :
    PartrecHalts0 code ↔ ReachabilityYes (compileReachability code) := by
  constructor
  · intro halts
    exact ⟨compileReachability_certified code,
      compileReachability_start_ne_target code,
      (Lecerf.Machine.Compiler.ReversibleUniversal.eval_dom_iff_turnaround_bottom_strictlyReachable
        code).mp halts⟩
  · intro yes
    exact
      (Lecerf.Machine.Compiler.ReversibleUniversal.eval_dom_iff_turnaround_bottom_strictlyReachable
        code).mpr yes.2.2

theorem partrecHalts0_manyOne_haltingYes : PartrecHalts0 ≤₀ HaltingYes :=
  ⟨compileHalting, compileHalting_computable,
    partrecHalts0_iff_haltingYes⟩

theorem partrecHalts0_manyOne_returnYes : PartrecHalts0 ≤₀ ReturnYes :=
  ⟨compileReturn, compileReturn_computable,
    partrecHalts0_iff_returnYes⟩

theorem partrecHalts0_manyOne_reachabilityYes :
    PartrecHalts0 ≤₀ ReachabilityYes :=
  ⟨compileReachability, compileReachability_computable,
    partrecHalts0_iff_reachabilityYes⟩

/-- Certified halting for raw finite reversible two-tape tables is not
computable. -/
theorem haltingYes_not_computable : ¬ComputablePred HaltingYes := by
  intro targetComputable
  exact ComputablePred.halting_problem 0
    (ComputablePred.computable_of_manyOneReducible
      partrecHalts0_manyOne_haltingYes targetComputable)

/-- Certified positive return for raw finite reversible two-tape tables is
not computable. -/
theorem returnYes_not_computable : ¬ComputablePred ReturnYes := by
  intro targetComputable
  exact ComputablePred.halting_problem 0
    (ComputablePred.computable_of_manyOneReducible
      partrecHalts0_manyOne_returnYes targetComputable)

/-- Certified distinct-target strict reachability for raw finite reversible
two-tape tables is not computable. -/
theorem reachabilityYes_not_computable : ¬ComputablePred ReachabilityYes := by
  intro targetComputable
  exact ComputablePred.halting_problem 0
    (ComputablePred.computable_of_manyOneReducible
      partrecHalts0_manyOne_reachabilityYes targetComputable)

end

end Lecerf.Undecidability.ReversibleTwoTape
