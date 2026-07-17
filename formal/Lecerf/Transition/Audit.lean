import Lecerf.Transition.Reversible

/-!
# Transition API audit examples

Finite checked examples separating zero-step reachability, positive return,
forward determinism, successful predecessor uniqueness, and local versus
global reversibility. This diagnostic module is not part of the public API.
-/

namespace Lecerf.Transition.Audit

open ReversibleStep

/-! ## A single partial reversible edge -/

def singleEdge : ReversibleStep Bool :=
  PEquiv.single false true

theorem singleEdge_forward : singleEdge.next false = some true := by
  simp [singleEdge, ReversibleStep.next]

theorem singleEdge_reverse : singleEdge.prev true = some false :=
  (next_eq_some_iff_prev_eq_some singleEdge).mp singleEdge_forward

theorem singleEdge_target_terminal : Terminal singleEdge.next true := by
  decide

theorem singleEdge_target_not_reverse_terminal : ¬Terminal singleEdge.prev true := by
  decide

theorem singleEdge_target_reachable_zero_steps : Reachable singleEdge.next true true :=
  Reachable.refl _ _

theorem singleEdge_target_not_positive_return : ¬PositiveReturn singleEdge.next true :=
  singleEdge_target_terminal.not_positiveReturn

/-! ## A genuine positive cycle -/

def toggleStep : ReversibleStep Bool :=
  (Equiv.swap false true).toPEquiv

theorem toggle_false : toggleStep.next false = some true := by
  decide

theorem toggle_true : toggleStep.next true = some false := by
  decide

theorem toggle_positiveReturn : PositiveReturn toggleStep.next false :=
  StrictlyReachable.trans (StrictlyReachable.single toggle_false)
    (StrictlyReachable.single toggle_true)

/-! ## Deterministic execution need not be reversible -/

inductive MergeState
  | left
  | right
  | join
  deriving DecidableEq, Repr

def mergeStep : Step MergeState
  | .left => some .join
  | .right => some .join
  | .join => none

theorem merge_not_backwardUnique : ¬BackwardUnique mergeStep := by
  intro h
  have hleft : StepRel mergeStep .left .join := by rfl
  have hright : StepRel mergeStep .right .join := by rfl
  have : MergeState.left = .right := h hleft hright
  cases this

theorem merge_no_reversibleStep :
    ¬∃ step : ReversibleStep MergeState, step.next = mergeStep := by
  rintro ⟨step, hstep⟩
  apply merge_not_backwardUnique
  rw [← hstep]
  exact step.backwardUnique

/-- Each branch is individually reversible as a partial edge. Their union is
the non-reversible merging transition above. -/
def leftRule : ReversibleStep MergeState :=
  PEquiv.single .left .join

def rightRule : ReversibleStep MergeState :=
  PEquiv.single .right .join

theorem leftRule_forward : leftRule.next .left = some .join := by
  simp [leftRule, ReversibleStep.next]

theorem rightRule_forward : rightRule.next .right = some .join := by
  simp [rightRule, ReversibleStep.next]

end Lecerf.Transition.Audit
