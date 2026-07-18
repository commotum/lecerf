import Lecerf.Machine.Compiler.ReversibleUniversal
import Lecerf.Undecidability.EffectiveTransition
import Lecerf.Undecidability.ReversibleTwoTape.Problems
import Mathlib.Computability.Reduce

/-!
# Reductions to raw reversible two-tape decision problems

The three reduction maps below reuse fixed closed finite tables.  They are
declared `noncomputable` only because those constants contain the one-time
finite-enumeration and universal-code choices isolated by the compiler.  No
machine is selected from the varying source code: its only varying data are
the primitive-recursive start and target configurations.
-/

namespace Lecerf.Undecidability.ReversibleTwoTape

open Lecerf.Transition
open Lecerf.Machine

namespace Universal := Lecerf.Machine.Compiler.ReversibleUniversal
namespace SourceProblem := Lecerf.Undecidability.EffectiveTransition

/-- Raw certified-halting instance using the fixed forward history table.
Only the checkpoint depends on the source code. -/
noncomputable def compileHalting (code : Nat.Partrec.Code) : HaltingInput :=
  (Universal.historyTable, Universal.startCheckpoint code)

/-- Raw certified-return instance using the fixed closed return table.  Only
the checkpoint depends on the source code. -/
noncomputable def compileReturn (code : Nat.Partrec.Code) : ReturnInput :=
  (Universal.returnTable, Universal.startCheckpoint code)

/-- Raw certified-reachability instance using the fixed open turnaround
table.  Its checkpoint and exposed-bottom target are the only varying data. -/
noncomputable def compileReachability
    (code : Nat.Partrec.Code) : ReachabilityInput :=
  (Universal.turnaroundTable,
    Universal.startCheckpoint code, Universal.bottomTarget code)

/-- Pairing the fixed history table with the varying checkpoint is primitive
recursive. -/
theorem compileHalting_primrec : Primrec compileHalting := by
  exact ((Primrec.const Universal.historyTable).pair
    Universal.startCheckpoint_primrec).of_eq fun _ => rfl

/-- The raw halting reduction map is computable. -/
theorem compileHalting_computable : Computable compileHalting :=
  compileHalting_primrec.to_comp

/-- Pairing the fixed return table with the varying checkpoint is primitive
recursive. -/
theorem compileReturn_primrec : Primrec compileReturn := by
  exact ((Primrec.const Universal.returnTable).pair
    Universal.startCheckpoint_primrec).of_eq fun _ => rfl

/-- The raw positive-return reduction map is computable. -/
theorem compileReturn_computable : Computable compileReturn :=
  compileReturn_primrec.to_comp

/-- Pairing the fixed turnaround table with both varying endpoints is
primitive recursive. -/
theorem compileReachability_primrec : Primrec compileReachability := by
  exact ((Primrec.const Universal.turnaroundTable).pair
    (Universal.startCheckpoint_primrec.pair
      Universal.bottomTarget_primrec)).of_eq fun _ => rfl

/-- The raw distinct-target reachability reduction map is computable. -/
theorem compileReachability_computable : Computable compileReachability :=
  compileReachability_primrec.to_comp

/-- Every generated halting instance carries the finite syntactic
reversibility certificate required by the raw predicate. -/
theorem compileHalting_certified (code : Nat.Partrec.Code) :
    Certified (compileHalting code).1 := by
  simpa [Certified, compileHalting] using
    Universal.historyTable_syntacticallyReversible

/-- Consequently, every generated halting table is semantically reversible. -/
theorem compileHalting_reversible (code : Nat.Partrec.Code) :
    (compileHalting code).1.Reversible := by
  simpa [compileHalting] using Universal.historyTable_reversible

/-- Every generated return instance carries the finite syntactic
reversibility certificate required by the raw predicate. -/
theorem compileReturn_certified (code : Nat.Partrec.Code) :
    Certified (compileReturn code).1 := by
  simpa [Certified, compileReturn] using
    Universal.returnTable_syntacticallyReversible

/-- Consequently, every generated return table is semantically reversible. -/
theorem compileReturn_reversible (code : Nat.Partrec.Code) :
    (compileReturn code).1.Reversible := by
  simpa [compileReturn] using Universal.returnTable_reversible

/-- Every generated reachability instance carries the finite syntactic
reversibility certificate required by the raw predicate. -/
theorem compileReachability_certified (code : Nat.Partrec.Code) :
    Certified (compileReachability code).1 := by
  simpa [Certified, compileReachability] using
    Universal.turnaroundTable_syntacticallyReversible

/-- Consequently, every generated reachability table is semantically
reversible. -/
theorem compileReachability_reversible (code : Nat.Partrec.Code) :
    (compileReachability code).1.Reversible := by
  simpa [compileReachability] using Universal.turnaroundTable_reversible

/-- The generated reachability endpoints are structurally distinct for every
source code. -/
theorem compileReachability_start_ne_target (code : Nat.Partrec.Code) :
    (compileReachability code).2.1 ≠ (compileReachability code).2.2 := by
  simpa [compileReachability] using
    Universal.startCheckpoint_ne_bottomTarget code

/-- Partial-recursive halting on input zero is preserved and reflected by the
guarded raw halting predicate. -/
theorem partrecHalts0_iff_haltingYes (code : Nat.Partrec.Code) :
    SourceProblem.PartrecHalts0 code ↔ HaltingYes (compileHalting code) := by
  change (Nat.Partrec.Code.eval code 0).Dom ↔
    Certified Universal.historyTable ∧
      HaltsFrom Universal.historyTable.step (Universal.startCheckpoint code)
  constructor
  · intro halts
    exact ⟨Universal.historyTable_syntacticallyReversible,
      (Universal.eval_dom_iff_history_halts code).mp halts⟩
  · intro target
    exact (Universal.eval_dom_iff_history_halts code).mpr target.2

/-- Partial-recursive halting on input zero is preserved and reflected by the
guarded raw positive-return predicate. -/
theorem partrecHalts0_iff_returnYes (code : Nat.Partrec.Code) :
    SourceProblem.PartrecHalts0 code ↔ ReturnYes (compileReturn code) := by
  change (Nat.Partrec.Code.eval code 0).Dom ↔
    Certified Universal.returnTable ∧
      PositiveReturn Universal.returnTable.step (Universal.startCheckpoint code)
  constructor
  · intro halts
    exact ⟨Universal.returnTable_syntacticallyReversible,
      (Universal.eval_dom_iff_return_positiveReturn code).mp halts⟩
  · intro target
    exact (Universal.eval_dom_iff_return_positiveReturn code).mpr target.2

/-- Partial-recursive halting on input zero is preserved and reflected by the
guarded raw distinct-target reachability predicate. -/
theorem partrecHalts0_iff_reachabilityYes (code : Nat.Partrec.Code) :
    SourceProblem.PartrecHalts0 code ↔
      ReachabilityYes (compileReachability code) := by
  change (Nat.Partrec.Code.eval code 0).Dom ↔
    Certified Universal.turnaroundTable ∧
      Universal.startCheckpoint code ≠ Universal.bottomTarget code ∧
        StrictlyReachable Universal.turnaroundTable.step
          (Universal.startCheckpoint code) (Universal.bottomTarget code)
  constructor
  · intro halts
    exact ⟨Universal.turnaroundTable_syntacticallyReversible,
      Universal.startCheckpoint_ne_bottomTarget code,
      (Universal.eval_dom_iff_turnaround_bottom_strictlyReachable code).mp halts⟩
  · intro target
    exact (Universal.eval_dom_iff_turnaround_bottom_strictlyReachable code).mpr
      target.2.2

/-- Computable many-one reduction to certified finite reversible two-tape
halting. -/
theorem partrecHalts0_manyOne_haltingYes :
    SourceProblem.PartrecHalts0 ≤₀ HaltingYes :=
  ⟨compileHalting, compileHalting_computable, partrecHalts0_iff_haltingYes⟩

/-- Computable many-one reduction to certified positive return. -/
theorem partrecHalts0_manyOne_returnYes :
    SourceProblem.PartrecHalts0 ≤₀ ReturnYes :=
  ⟨compileReturn, compileReturn_computable, partrecHalts0_iff_returnYes⟩

/-- Computable many-one reduction to certified distinct-target strict
reachability. -/
theorem partrecHalts0_manyOne_reachabilityYes :
    SourceProblem.PartrecHalts0 ≤₀ ReachabilityYes :=
  ⟨compileReachability, compileReachability_computable,
    partrecHalts0_iff_reachabilityYes⟩

/-- Certified halting for raw finite reversible two-tape tables is not a
computable predicate. -/
theorem haltingYes_not_computable : ¬ComputablePred HaltingYes := by
  intro targetComputable
  exact ComputablePred.halting_problem 0
    (ComputablePred.computable_of_manyOneReducible
      partrecHalts0_manyOne_haltingYes targetComputable)

/-- Certified positive return for raw finite reversible two-tape tables is
not a computable predicate. -/
theorem returnYes_not_computable : ¬ComputablePred ReturnYes := by
  intro targetComputable
  exact ComputablePred.halting_problem 0
    (ComputablePred.computable_of_manyOneReducible
      partrecHalts0_manyOne_returnYes targetComputable)

/-- Certified distinct-target strict reachability for raw finite reversible
two-tape tables is not a computable predicate. -/
theorem reachabilityYes_not_computable : ¬ComputablePred ReachabilityYes := by
  intro targetComputable
  exact ComputablePred.halting_problem 0
    (ComputablePred.computable_of_manyOneReducible
      partrecHalts0_manyOne_reachabilityYes targetComputable)

end Lecerf.Undecidability.ReversibleTwoTape
