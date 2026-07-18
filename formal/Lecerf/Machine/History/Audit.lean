import Lecerf.Machine.History.Computable

/-!
# History-simulation diagnostics

Executable examples check merge disambiguation, malformed-history rejection,
and the precise limitation on checkpoint uniqueness for cyclic sources.  This
leaf is not imported by the public API.
-/

namespace Lecerf.Machine.History.Audit

open Lecerf.Transition

/-- A deterministic source with two distinct predecessors of state `2`. -/
def mergeStep : Step Nat
  | 0 => some 2
  | 1 => some 2
  | _ => none

example : mergeStep 0 = some 2 := rfl
example : mergeStep 1 = some 2 := rfl

theorem mergeStep_not_backwardUnique : ¬BackwardUnique mergeStep := by
  intro unique
  have first : StepRel mergeStep 0 2 := by rfl
  have second : StepRel mergeStep 1 2 := by rfl
  have impossible : (0 : Nat) = 1 := unique first second
  contradiction

/-- Full predecessor records distinguish the two branches of a source merge. -/
example : forward mergeStep (Config.encode 0 []) =
    some (Config.encode 2 [0]) := by
  native_decide

example : forward mergeStep (Config.encode 1 []) =
    some (Config.encode 2 [1]) := by
  native_decide

example : backward mergeStep (Config.encode 2 [0]) =
    some (Config.encode 0 []) := by
  native_decide

example : backward mergeStep (Config.encode 2 [1]) =
    some (Config.encode 1 []) := by
  native_decide

/-- A stored predecessor that does not actually produce the current state is
rejected rather than blindly popped. -/
theorem malformed_predecessor_rejected :
    backward mergeStep (Config.encode 2 [2]) = none := by
  native_decide

example : BackwardUnique (forward mergeStep) :=
  (reversible mergeStep).backwardUnique

/-- The malformed terminal state is outside the invariant generated from
source state `0`; exact reachability/invariant reflection therefore rules it
out as a spurious halting checkpoint. -/
theorem malformed_predecessor_not_valid :
    ¬Valid mergeStep 0 (Config.encode 2 [2]) := by
  intro malformed
  have proper : Valid mergeStep 0 (Config.encode 2 [0]) :=
    Valid.push Valid.initial rfl
  have equal := malformed.eq_of_history_length_eq proper (by decide)
  have historiesEqual := congrArg Config.history equal
  exact (by decide : ([2] : List Nat) ≠ [0]) historiesEqual

/-- A total two-cycle used to audit the scope of checkpoint uniqueness. -/
def toggleStep : Step Bool := fun state => some (!state)

theorem cycle_revisits_with_longer_history :
    Valid toggleStep false (Config.encode false [true, false]) := by
  apply Valid.push
  · apply Valid.push Valid.initial
    rfl
  · rfl

example : Valid toggleStep false (Config.encode false []) :=
  Valid.initial

/-- The same source state may occur at distinct elapsed times with different
valid histories, so uniqueness must retain a length qualifier. -/
theorem cyclic_checkpoints_differ :
    Config.encode false [] ≠ Config.encode false [true, false] := by
  native_decide

end Lecerf.Machine.History.Audit
