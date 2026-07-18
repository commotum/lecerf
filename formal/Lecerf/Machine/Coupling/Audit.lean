import Lecerf.Machine.Coupling.Computable

/-!
# Forward--reverse coupling diagnostics

Small executable sources check the two phase boundaries and the order of a
one-step computation.  Negative semantic tests use the proved iff theorems,
not a bounded search masquerading as reachability.
-/

namespace Lecerf.Machine.Coupling.Audit

open Lecerf.Transition

namespace History

open Lecerf.Machine.Coupling.History

/-- An already terminal source. -/
def haltNow : Step Nat := fun _ => none

/-- A source taking exactly one successful step from `0`. -/
def haltAfterOne : Step Nat
  | 0 => some 1
  | _ => none

/-- A source that loops forever at every state. -/
def loop : Step Nat := fun state => some state

example : (turnaroundStep haltNow).next (start 0) = some (target 0) := by
  decide

example : Terminal (turnaroundStep haltNow).next (target 0) := by
  exact terminal_target haltNow 0

example : (returnStep haltNow).next (target 0) = some (start 0) := by
  decide

def oneStepCheckpoint : Lecerf.Machine.History.Config Nat :=
  Lecerf.Machine.History.Config.encode 1 [0]

example : (turnaroundStep haltAfterOne).next (start 0) =
    some (Config.forward oneStepCheckpoint) := by
  decide

example : (turnaroundStep haltAfterOne).next
    (Config.forward oneStepCheckpoint) =
      some (Config.reverse oneStepCheckpoint) := by
  decide

example : (turnaroundStep haltAfterOne).next
    (Config.reverse oneStepCheckpoint) = some (target 0) := by
  decide

theorem haltNow_halts : HaltsFrom haltNow 0 :=
  (by rfl : Terminal haltNow 0).haltsFrom

example : PositiveReturn (returnStep haltNow).next (start 0) :=
  (positiveReturn_iff_halts haltNow 0).mpr haltNow_halts

theorem loop_does_not_halt : ¬HaltsFrom loop 0 := by
  rw [haltsFrom_iff_exists_reachable_terminal]
  rintro ⟨terminal, _, terminalState⟩
  simp [Terminal, loop] at terminalState

example : ¬StrictlyReachable (turnaroundStep loop).next (start 0) (target 0) := by
  simpa [target_strictlyReachable_iff_halts loop 0] using loop_does_not_halt

example : ¬PositiveReturn (returnStep loop).next (start 0) := by
  simpa [positiveReturn_iff_halts loop 0] using loop_does_not_halt

end History

#print axioms Lecerf.Machine.Coupling.turnaround
#print axioms Lecerf.Machine.Coupling.returnGadget
#print axioms Lecerf.Machine.Coupling.History.target_strictlyReachable_iff_halts
#print axioms Lecerf.Machine.Coupling.History.positiveReturn_iff_halts
#print axioms Lecerf.Machine.Coupling.History.universalReturnNext_primrec
#print axioms Lecerf.Machine.Coupling.History.universalTarget_strictlyReachable_iff_eval_dom
#print axioms Lecerf.Machine.Coupling.History.universalPositiveReturn_iff_eval_dom

end Lecerf.Machine.Coupling.Audit
