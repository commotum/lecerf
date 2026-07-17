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

/-- A state with no outgoing transition. -/
def Terminal {σ : Type u} (next : Step σ) (state : σ) : Prop :=
  next state = none

/-- Termination of repeated execution from `start`. -/
def HaltsFrom {σ : Type u} (next : Step σ) (start : σ) : Prop :=
  (StateTransition.eval next start).Dom

/-- Reflexive finite reachability. Zero steps are permitted. -/
def Reachable {σ : Type u} (next : Step σ) (start target : σ) : Prop :=
  StateTransition.Reaches next start target

/-- Positive finite reachability. At least one step is required. -/
def StrictlyReachable {σ : Type u} (next : Step σ) (start target : σ) : Prop :=
  StateTransition.Reaches₁ next start target

/-- A nonempty run returning to its initial state. -/
def PositiveReturn {σ : Type u} (next : Step σ) (start : σ) : Prop :=
  StrictlyReachable next start start

namespace Step

/-- Option-valued execution has at most one successful successor. -/
theorem successor_unique {σ : Type u} (next : Step σ) {state target₁ target₂ : σ}
    (h₁ : next state = some target₁) (h₂ : next state = some target₂) : target₁ = target₂ :=
  Option.some.inj (h₁.symm.trans h₂)

end Step

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

/-- A computation halts exactly when it reaches a terminal state. -/
theorem haltsFrom_iff_exists_reachable_terminal {σ : Type u} {next : Step σ} {start : σ} :
    HaltsFrom next start ↔ ∃ target, Reachable next start target ∧ Terminal next target := by
  simp only [HaltsFrom, Part.dom_iff_mem, StateTransition.mem_eval, Reachable, Terminal]

/-- A terminal state halts immediately. -/
theorem Terminal.haltsFrom {σ : Type u} {next : Step σ} {state : σ}
    (h : Terminal next state) : HaltsFrom next state :=
  haltsFrom_iff_exists_reachable_terminal.mpr ⟨state, Reachable.refl next state, h⟩

/-- No positive run can start at a terminal state. -/
theorem Terminal.not_strictlyReachable {σ : Type u} {next : Step σ} {start target : σ}
    (h : Terminal next start) : ¬StrictlyReachable next start target := by
  intro hreach
  obtain ⟨middle, hstep, _⟩ := Relation.TransGen.head'_iff.mp hreach
  rw [h] at hstep
  simpa using hstep

/-- In particular, terminality rules out a positive return. -/
theorem Terminal.not_positiveReturn {σ : Type u} {next : Step σ} {state : σ}
    (h : Terminal next state) : ¬PositiveReturn next state :=
  h.not_strictlyReachable

end Lecerf.Transition
