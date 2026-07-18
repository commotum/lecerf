import Lecerf.Transition.API
import Mathlib.Computability.Primrec.List

/-!
# Forward--reverse coupling

This module supplies two executable couplings for an arbitrary reversible
partial transition.  Both run the transition forward, change phase exactly at
a forward-terminal state, and then run its checked inverse.

`turnaround` leaves an inverse-terminal state terminal.  `returnGadget`
instead closes every inverse-terminal boundary back to the matching forward
state.  Closing every component uniformly is what makes the latter an exact
ambient partial equivalence; the runtime never tests for a privileged start
configuration or consults a future execution trace.
-/

namespace Lecerf.Machine.Coupling

open Lecerf.Transition

universe u

/-- Which copy of a reversible state space is currently executing. -/
inductive Direction
  | forward
  | reverse
  deriving DecidableEq, Repr

namespace Direction

/-- A constructive two-element representation of execution directions. -/
def equivBool : Direction ≃ Bool where
  toFun
    | .forward => false
    | .reverse => true
  invFun
    | false => .forward
    | true => .reverse
  left_inv := by intro direction; cases direction <;> rfl
  right_inv := by intro bit; cases bit <;> rfl

end Direction

instance : Primcodable Direction :=
  Primcodable.ofEquiv Bool Direction.equivBool

/-- A state tagged by the direction in which its underlying reversible step
is being executed. -/
structure Config (σ : Type u) where
  direction : Direction
  state : σ
  deriving DecidableEq, Repr

namespace Config

variable {σ : Type u}

/-- The explicit product representation used by the constructive encoding. -/
def equivRep : Config σ ≃ Direction × σ where
  toFun config := (config.direction, config.state)
  invFun data := ⟨data.1, data.2⟩
  left_inv := by intro config; cases config; rfl
  right_inv := by intro data; cases data; rfl

instance [Primcodable σ] : Primcodable (Config σ) :=
  Primcodable.ofEquiv (Direction × σ) equivRep

/-- Enter the forward copy of a state. -/
def forward (state : σ) : Config σ :=
  ⟨.forward, state⟩

/-- Enter the reverse copy of a state. -/
def reverse (state : σ) : Config σ :=
  ⟨.reverse, state⟩

@[simp]
theorem forward_direction (state : σ) : (forward state).direction = .forward :=
  rfl

@[simp]
theorem reverse_direction (state : σ) : (reverse state).direction = .reverse :=
  rfl

@[simp]
theorem forward_state (state : σ) : (forward state).state = state :=
  rfl

@[simp]
theorem reverse_state (state : σ) : (reverse state).state = state :=
  rfl

@[simp]
theorem forward_ne_reverse (first second : σ) :
    forward first ≠ reverse second := by
  intro equal
  have := congrArg Config.direction equal
  contradiction

@[simp]
theorem reverse_ne_forward (first second : σ) :
    reverse first ≠ forward second := by
  exact Ne.symm (forward_ne_reverse second first)

@[simp]
theorem forward_inj {first second : σ} :
    forward first = forward second ↔ first = second := by
  constructor
  · exact fun equal => congrArg Config.state equal
  · exact congrArg forward

@[simp]
theorem reverse_inj {first second : σ} :
    reverse first = reverse second ↔ first = second := by
  constructor
  · exact fun equal => congrArg Config.state equal
  · exact congrArg reverse

end Config

/-- Open coupling: run forward; at a forward-terminal state cross to the
reverse copy; then run the inverse until it becomes terminal. -/
def turnaroundNext {σ : Type u} (step : ReversibleStep σ) : Step (Config σ)
  | ⟨.forward, state⟩ =>
      match step.next state with
      | some target => some (Config.forward target)
      | none => some (Config.reverse state)
  | ⟨.reverse, state⟩ =>
      (step.prev state).map Config.reverse

/-- Exact inverse transition for `turnaroundNext`. -/
def turnaroundPrev {σ : Type u} (step : ReversibleStep σ) : Step (Config σ)
  | ⟨.forward, state⟩ =>
      (step.prev state).map Config.forward
  | ⟨.reverse, state⟩ =>
      match step.next state with
      | some target => some (Config.reverse target)
      | none => some (Config.forward state)

/-- One-step execution of the open coupling has the stated checked inverse on
the whole tagged state space, including states outside any chosen orbit. -/
theorem turnaroundNext_eq_some_iff_turnaroundPrev_eq_some {σ : Type u}
    (step : ReversibleStep σ) (source target : Config σ) :
    turnaroundNext step source = some target ↔
      turnaroundPrev step target = some source := by
  rcases source with ⟨sourceDirection, source⟩
  rcases target with ⟨targetDirection, target⟩
  cases sourceDirection <;> cases targetDirection <;>
    simp [turnaroundNext, turnaroundPrev, Config.forward, Config.reverse,
      ReversibleStep.next, ReversibleStep.prev, step.eq_some_iff]

/-- The open coupling bundled as a reversible partial step. -/
def turnaround {σ : Type u} (step : ReversibleStep σ) :
    ReversibleStep (Config σ) where
  toFun := turnaroundNext step
  invFun := turnaroundPrev step
  inv source target :=
    (turnaroundNext_eq_some_iff_turnaroundPrev_eq_some step source target).symm

@[simp]
theorem turnaround_next {σ : Type u} (step : ReversibleStep σ) :
    (turnaround step).next = turnaroundNext step :=
  rfl

@[simp]
theorem turnaround_prev {σ : Type u} (step : ReversibleStep σ) :
    (turnaround step).prev = turnaroundPrev step :=
  rfl

/-- Closed coupling: as in `turnaroundNext`, except that an inverse-terminal
state crosses back to its matching forward copy. -/
def returnNext {σ : Type u} (step : ReversibleStep σ) : Step (Config σ)
  | ⟨.forward, state⟩ =>
      match step.next state with
      | some target => some (Config.forward target)
      | none => some (Config.reverse state)
  | ⟨.reverse, state⟩ =>
      match step.prev state with
      | some previous => some (Config.reverse previous)
      | none => some (Config.forward state)

/-- Exact inverse transition for `returnNext`. -/
def returnPrev {σ : Type u} (step : ReversibleStep σ) : Step (Config σ)
  | ⟨.forward, state⟩ =>
      match step.prev state with
      | some previous => some (Config.forward previous)
      | none => some (Config.reverse state)
  | ⟨.reverse, state⟩ =>
      match step.next state with
      | some target => some (Config.reverse target)
      | none => some (Config.forward state)

/-- One-step execution of the closed coupling has the stated checked inverse
on every tagged state, not only on generated history configurations. -/
theorem returnNext_eq_some_iff_returnPrev_eq_some {σ : Type u}
    (step : ReversibleStep σ) (source target : Config σ) :
    returnNext step source = some target ↔
      returnPrev step target = some source := by
  rcases source with ⟨sourceDirection, source⟩
  rcases target with ⟨targetDirection, target⟩
  cases sourceDirection <;> cases targetDirection <;>
    simp [returnNext, returnPrev, Config.forward, Config.reverse,
      ReversibleStep.next, ReversibleStep.prev, step.eq_some_iff]

/-- The uniformly closed return transition bundled as a reversible step. -/
def returnGadget {σ : Type u} (step : ReversibleStep σ) :
    ReversibleStep (Config σ) where
  toFun := returnNext step
  invFun := returnPrev step
  inv source target :=
    (returnNext_eq_some_iff_returnPrev_eq_some step source target).symm

@[simp]
theorem returnGadget_next {σ : Type u} (step : ReversibleStep σ) :
    (returnGadget step).next = returnNext step :=
  rfl

@[simp]
theorem returnGadget_prev {σ : Type u} (step : ReversibleStep σ) :
    (returnGadget step).prev = returnPrev step :=
  rfl

section BoundaryEquations

variable {σ : Type u} (step : ReversibleStep σ) (state target previous : σ)

@[simp]
theorem turnaroundNext_forward_of_step
    (h : step.next state = some target) :
    turnaroundNext step (Config.forward state) =
      some (Config.forward target) := by
  change step state = some target at h
  simp [turnaroundNext, Config.forward, h]

@[simp]
theorem turnaroundNext_forward_of_terminal
    (h : Terminal step.next state) :
    turnaroundNext step (Config.forward state) =
      some (Config.reverse state) := by
  change step state = none at h
  simp [turnaroundNext, Config.forward, Config.reverse, h]

@[simp]
theorem turnaroundNext_reverse_of_inverse_step
    (h : step.prev state = some previous) :
    turnaroundNext step (Config.reverse state) =
      some (Config.reverse previous) := by
  change step.symm state = some previous at h
  simp [turnaroundNext, Config.reverse, ReversibleStep.prev, h]

@[simp]
theorem turnaroundNext_reverse_of_inverse_terminal
    (h : Terminal step.prev state) :
    turnaroundNext step (Config.reverse state) = none := by
  change step.symm state = none at h
  simp [turnaroundNext, Config.reverse, ReversibleStep.prev, h]

@[simp]
theorem returnNext_forward_of_step
    (h : step.next state = some target) :
    returnNext step (Config.forward state) =
      some (Config.forward target) := by
  change step state = some target at h
  simp [returnNext, Config.forward, h]

@[simp]
theorem returnNext_forward_of_terminal
    (h : Terminal step.next state) :
    returnNext step (Config.forward state) =
      some (Config.reverse state) := by
  change step state = none at h
  simp [returnNext, Config.forward, Config.reverse, h]

@[simp]
theorem returnNext_reverse_of_inverse_step
    (h : step.prev state = some previous) :
    returnNext step (Config.reverse state) =
      some (Config.reverse previous) := by
  change step.symm state = some previous at h
  simp [returnNext, Config.reverse, ReversibleStep.prev, h]

@[simp]
theorem returnNext_reverse_of_inverse_terminal
    (h : Terminal step.prev state) :
    returnNext step (Config.reverse state) =
      some (Config.forward state) := by
  change step.symm state = none at h
  simp [returnNext, Config.forward, Config.reverse, ReversibleStep.prev, h]

end BoundaryEquations

end Lecerf.Machine.Coupling
