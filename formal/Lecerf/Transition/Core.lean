import Mathlib.Computability.StateTransition

/-!
# Partial transition systems

Named predicates and elementary facts for deterministic partial execution.
The transition function itself supplies forward determinism: each state has at
most one successor.
-/

namespace Lecerf.Transition

universe u

/-- A deterministic partial transition function. `none` means that execution
cannot take another step. -/
abbrev Step (σ : Type u) := σ → Option σ

/-- The successful-step relation induced by an option-valued transition. -/
def StepRel {σ : Type u} (next : Step σ) (source target : σ) : Prop :=
  target ∈ next source

/-- Successful transitions have at most one predecessor. Unlike function
injectivity of `next`, this ignores states at which `next` is `none`. -/
def BackwardUnique {σ : Type u} (next : Step σ) : Prop :=
  Relator.LeftUnique (StepRel next)

/-- A state with no outgoing transition. -/
def Terminal {σ : Type u} (next : Step σ) (state : σ) : Prop :=
  next state = none

/-- Termination of repeated execution from `start`. -/
def HaltsFrom {σ : Type u} (next : Step σ) (start : σ) : Prop :=
  (StateTransition.eval next start).Dom

/-- Reflexive finite reachability. Zero steps are permitted. -/
def Reachable {σ : Type u} (next : Step σ) (start target : σ) : Prop :=
  StateTransition.Reaches next start target

/-- Positive finite reachability. At least one step is required, but the two
endpoints may be equal when the run is a cycle. -/
def StrictlyReachable {σ : Type u} (next : Step σ) (start target : σ) : Prop :=
  StateTransition.Reaches₁ next start target

/-- A nonempty run returning to its initial state. -/
def PositiveReturn {σ : Type u} (next : Step σ) (start : σ) : Prop :=
  StrictlyReachable next start start

namespace Step

/-- Every option-valued transition is right-unique as a successful-step
relation. This is the forward determinism supplied by `Step` itself. -/
theorem stepRel_rightUnique {σ : Type u} (next : Step σ) :
    Relator.RightUnique (StepRel next) := by
  intro source target₁ target₂ h₁ h₂
  exact Option.mem_unique h₁ h₂

/-- Option-valued execution has at most one successful successor. -/
theorem successor_unique {σ : Type u} (next : Step σ) {state target₁ target₂ : σ}
    (h₁ : next state = some target₁) (h₂ : next state = some target₂) : target₁ = target₂ :=
  Option.some.inj (h₁.symm.trans h₂)

end Step

/-- Terminality means that there is no successful outgoing step. -/
theorem terminal_iff_forall_not_step {σ : Type u} (next : Step σ) (state : σ) :
    Terminal next state ↔ ∀ target, ¬StepRel next state target :=
  Option.eq_none_iff_forall_not_mem

namespace Reachable

@[refl]
theorem refl {σ : Type u} (next : Step σ) (state : σ) : Reachable next state state :=
  Relation.ReflTransGen.refl

theorem single {σ : Type u} {next : Step σ} {start target : σ}
    (h : next start = some target) : Reachable next start target :=
  Relation.ReflTransGen.single h

theorem trans {σ : Type u} {next : Step σ} {start middle target : σ}
    (h₁ : Reachable next start middle) (h₂ : Reachable next middle target) :
    Reachable next start target :=
  Relation.ReflTransGen.trans h₁ h₂

end Reachable

namespace StrictlyReachable

theorem single {σ : Type u} {next : Step σ} {start target : σ}
    (h : next start = some target) : StrictlyReachable next start target :=
  Relation.TransGen.single h

theorem trans {σ : Type u} {next : Step σ} {start middle target : σ}
    (h₁ : StrictlyReachable next start middle)
    (h₂ : StrictlyReachable next middle target) :
    StrictlyReachable next start target :=
  Relation.TransGen.trans h₁ h₂

theorem toReachable {σ : Type u} {next : Step σ} {start target : σ}
    (h : StrictlyReachable next start target) : Reachable next start target :=
  h.to_reflTransGen

end StrictlyReachable

/-- For distinct endpoints, reflexive reachability is already positive. -/
theorem reachable_iff_strictlyReachable_of_ne {σ : Type u} {next : Step σ}
    {start target : σ} (hne : start ≠ target) :
    Reachable next start target ↔ StrictlyReachable next start target := by
  constructor
  · intro h
    rcases Relation.reflTransGen_iff_eq_or_transGen.mp h with hEq | hPositive
    · exact False.elim (hne hEq.symm)
    · exact hPositive
  · exact StrictlyReachable.toReachable

/-- A computation halts exactly when it reaches a terminal state. -/
theorem haltsFrom_iff_exists_reachable_terminal {σ : Type u} {next : Step σ} {start : σ} :
    HaltsFrom next start ↔ ∃ target, Reachable next start target ∧ Terminal next target := by
  simp only [HaltsFrom, Part.dom_iff_mem, StateTransition.mem_eval, Reachable, Terminal]

/-- A terminal state halts immediately. -/
theorem Terminal.haltsFrom {σ : Type u} {next : Step σ} {state : σ}
    (h : Terminal next state) : HaltsFrom next state :=
  haltsFrom_iff_exists_reachable_terminal.mpr ⟨state, Reachable.refl next state, h⟩

/-- A deterministic run has at most one reachable terminal endpoint. -/
theorem reachable_terminal_unique {σ : Type u} {next : Step σ} {start target₁ target₂ : σ}
    (h₁ : Reachable next start target₁) (ht₁ : Terminal next target₁)
    (h₂ : Reachable next start target₂) (ht₂ : Terminal next target₂) : target₁ = target₂ :=
  Part.mem_unique (StateTransition.mem_eval.mpr ⟨h₁, ht₁⟩)
    (StateTransition.mem_eval.mpr ⟨h₂, ht₂⟩)

/-- No positive run can start at a terminal state. -/
theorem Terminal.not_strictlyReachable {σ : Type u} {next : Step σ} {start target : σ}
    (h : Terminal next start) : ¬StrictlyReachable next start target := by
  intro hreach
  obtain ⟨middle, hstep, _⟩ := Relation.TransGen.head'_iff.mp hreach
  rw [h] at hstep
  simp at hstep

/-- In particular, terminality rules out a positive return. -/
theorem Terminal.not_positiveReturn {σ : Type u} {next : Step σ} {state : σ}
    (h : Terminal next state) : ¬PositiveReturn next state :=
  h.not_strictlyReachable

end Lecerf.Transition
