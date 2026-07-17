import Lecerf.Transition.Core
import Mathlib.Data.PEquiv

/-!
# Reversible partial transitions

A reversible step is a same-type `PEquiv`. Its forward and reverse functions
are deterministic partial transitions satisfying an exact inverse law on
successful steps.
-/

namespace Lecerf.Transition

universe u

/-- A deterministic partial transition with an explicit deterministic partial
inverse. -/
abbrev ReversibleStep (σ : Type u) := σ ≃. σ

namespace ReversibleStep

/-- Forward execution of a reversible step. -/
def next {σ : Type u} (step : ReversibleStep σ) : Step σ :=
  step

/-- Reverse execution of a reversible step. -/
def prev {σ : Type u} (step : ReversibleStep σ) : Step σ :=
  step.symm

@[simp]
theorem next_apply {σ : Type u} (step : ReversibleStep σ) (state : σ) :
    step.next state = step state :=
  rfl

@[simp]
theorem prev_apply {σ : Type u} (step : ReversibleStep σ) (state : σ) :
    step.prev state = step.symm state :=
  rfl

/-- Exact one-step forward/reverse correspondence. -/
theorem next_eq_some_iff_prev_eq_some {σ : Type u} (step : ReversibleStep σ)
    {source target : σ} :
    step.next source = some target ↔ step.prev target = some source := by
  change step source = some target ↔ step.symm target = some source
  exact (step.eq_some_iff (a := source) (b := target)).symm

/-- Relational form of the exact one-step inverse law. -/
theorem stepRel_iff_reverseStepRel {σ : Type u} (step : ReversibleStep σ)
    {source target : σ} :
    StepRel step.next source target ↔ StepRel step.prev target source := by
  change step source = some target ↔ step.symm target = some source
  exact (step.mem_iff_mem (a := source) (b := target)).symm

/-- A reversible step has at most one predecessor for each successful output.
This is deliberately weaker than `Function.Injective step.next`, which would
also compare the potentially many inputs mapped to `none`. -/
theorem backwardUnique {σ : Type u} (step : ReversibleStep σ) :
    BackwardUnique step.next := by
  intro source₁ source₂ target h₁ h₂
  exact step.inj h₁ h₂

/-- Successful execution of a reversible step is unique in both directions. -/
theorem stepRel_biUnique {σ : Type u} (step : ReversibleStep σ) :
    Relator.BiUnique (StepRel step.next) :=
  ⟨step.backwardUnique, Step.stepRel_rightUnique step.next⟩

/-- Reverse a finite, possibly empty, forward path. -/
theorem reachable_reverse {σ : Type u} (step : ReversibleStep σ) {source target : σ}
    (h : Reachable step.next source target) : Reachable step.prev target source := by
  exact h.swap.mono fun _ _ hxy => step.mem_iff_mem.mpr hxy

/-- Finite reflexive reachability is exactly reachability under the inverse
step with endpoints exchanged. -/
theorem reachable_iff_reverse_reachable {σ : Type u} (step : ReversibleStep σ)
    {source target : σ} :
    Reachable step.next source target ↔ Reachable step.prev target source := by
  constructor
  · exact step.reachable_reverse
  · intro h
    simpa only [prev, next, PEquiv.symm_symm] using reachable_reverse step.symm h

/-- Reverse a positive forward path. -/
theorem strictlyReachable_reverse {σ : Type u} (step : ReversibleStep σ)
    {source target : σ} (h : StrictlyReachable step.next source target) :
    StrictlyReachable step.prev target source := by
  exact h.swap.mono fun _ _ hxy => step.mem_iff_mem.mpr hxy

/-- Positive reachability is exactly positive reachability under the inverse
step with endpoints exchanged. -/
theorem strictlyReachable_iff_reverse_strictlyReachable {σ : Type u}
    (step : ReversibleStep σ) {source target : σ} :
    StrictlyReachable step.next source target ↔
      StrictlyReachable step.prev target source := by
  constructor
  · exact step.strictlyReachable_reverse
  · intro h
    simpa only [prev, next, PEquiv.symm_symm] using strictlyReachable_reverse step.symm h

/-- Positive return is invariant under reversal. -/
theorem positiveReturn_iff_reverse_positiveReturn {σ : Type u}
    (step : ReversibleStep σ) (state : σ) :
    PositiveReturn step.next state ↔ PositiveReturn step.prev state :=
  step.strictlyReachable_iff_reverse_strictlyReachable

/-- Forward halting can be described as reverse reachability from a forward
terminal endpoint. This does not claim that forward and reverse execution halt
from the same state. -/
theorem haltsFrom_iff_exists_terminal_reverseReachable {σ : Type u}
    (step : ReversibleStep σ) (start : σ) :
    HaltsFrom step.next start ↔
      ∃ target, Terminal step.next target ∧ Reachable step.prev target start := by
  rw [haltsFrom_iff_exists_reachable_terminal]
  constructor
  · rintro ⟨target, hreach, hterminal⟩
    exact ⟨target, hterminal, step.reachable_reverse hreach⟩
  · rintro ⟨target, hterminal, hreach⟩
    exact ⟨target, step.reachable_iff_reverse_reachable.mpr hreach, hterminal⟩

/-- Evaluation endpoints correspond under reversal when both required boundary
states are terminal in their respective directions. -/
theorem mem_eval_next_iff_mem_eval_prev {σ : Type u} (step : ReversibleStep σ)
    {start target : σ} (target_terminal : Terminal step.next target)
    (start_reverse_terminal : Terminal step.prev start) :
    target ∈ StateTransition.eval step.next start ↔
      start ∈ StateTransition.eval step.prev target := by
  rw [StateTransition.mem_eval, StateTransition.mem_eval]
  exact and_congr step.reachable_iff_reverse_reachable
    (iff_of_true target_terminal start_reverse_terminal)

end ReversibleStep

end Lecerf.Transition
