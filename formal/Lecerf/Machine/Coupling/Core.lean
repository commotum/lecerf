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

/-- Construct a tagged configuration from its explicit representation. -/
def encode (direction : Direction) (state : σ) : Config σ :=
  ⟨direction, state⟩

/-- Decode a tagged configuration without losing either component. -/
def decode (config : Config σ) : Direction × σ :=
  (config.direction, config.state)

@[simp]
theorem decode_encode (direction : Direction) (state : σ) :
    decode (encode direction state) = (direction, state) :=
  rfl

@[simp]
theorem encode_decode (config : Config σ) :
    encode config.decode.1 config.decode.2 = config := by
  cases config
  rfl

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
      match step state with
      | some target => some (Config.forward target)
      | none => some (Config.reverse state)
  | ⟨.reverse, state⟩ =>
      (step.symm state).map Config.reverse

/-- Exact inverse transition for `turnaroundNext`. -/
def turnaroundPrev {σ : Type u} (step : ReversibleStep σ) : Step (Config σ)
  | ⟨.forward, state⟩ =>
      (step.symm state).map Config.forward
  | ⟨.reverse, state⟩ =>
      match step state with
      | some target => some (Config.reverse target)
      | none => some (Config.forward state)

/-- One-step execution of the open coupling has the stated checked inverse on
the whole tagged state space, including states outside any chosen orbit. -/
theorem turnaroundNext_eq_some_iff_turnaroundPrev_eq_some {σ : Type u}
    (step : ReversibleStep σ) (source target : Config σ) :
    turnaroundNext step source = some target ↔
      turnaroundPrev step target = some source := by
  constructor
  · intro executed
    rcases source with ⟨direction, state⟩
    cases direction with
    | forward =>
        cases forwardStep : step state with
        | none =>
            have targetEq : target = Config.reverse state := by
              simpa [turnaroundNext, Config.forward, Config.reverse,
                ReversibleStep.next, forwardStep] using executed.symm
            subst target
            simp [turnaroundPrev, Config.forward, Config.reverse, forwardStep]
        | some nextState =>
            have targetEq : target = Config.forward nextState := by
              simpa [turnaroundNext, Config.forward, ReversibleStep.next,
                forwardStep] using executed.symm
            subst target
            have inverseStep : step.symm nextState = some state :=
              step.eq_some_iff.mpr forwardStep
            simp [turnaroundPrev, Config.forward, inverseStep]
    | reverse =>
        cases inverseStep : step.symm state with
        | none =>
            simp [turnaroundNext, inverseStep] at executed
        | some previous =>
            have targetEq : target = Config.reverse previous := by
              simpa [turnaroundNext, Config.reverse, ReversibleStep.prev,
                inverseStep] using executed.symm
            subst target
            have forwardStep : step previous = some state :=
              step.eq_some_iff.mp inverseStep
            simp [turnaroundPrev, Config.reverse, forwardStep]
  · intro reversed
    rcases target with ⟨direction, state⟩
    cases direction with
    | forward =>
        cases inverseStep : step.symm state with
        | none =>
            simp [turnaroundPrev, inverseStep] at reversed
        | some previous =>
            have sourceEq : source = Config.forward previous := by
              simpa [turnaroundPrev, Config.forward, ReversibleStep.prev,
                inverseStep] using reversed.symm
            subst source
            have forwardStep : step previous = some state :=
              step.eq_some_iff.mp inverseStep
            simp [turnaroundNext, Config.forward, forwardStep]
    | reverse =>
        cases forwardStep : step state with
        | none =>
            have sourceEq : source = Config.forward state := by
              simpa [turnaroundPrev, Config.forward, Config.reverse,
                ReversibleStep.next, forwardStep] using reversed.symm
            subst source
            simp [turnaroundNext, Config.forward, Config.reverse, forwardStep]
        | some nextState =>
            have sourceEq : source = Config.reverse nextState := by
              simpa [turnaroundPrev, Config.reverse, ReversibleStep.next,
                forwardStep] using reversed.symm
            subst source
            have inverseStep : step.symm nextState = some state :=
              step.eq_some_iff.mpr forwardStep
            simp [turnaroundNext, Config.reverse, inverseStep]

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
      match step state with
      | some target => some (Config.forward target)
      | none => some (Config.reverse state)
  | ⟨.reverse, state⟩ =>
      match step.symm state with
      | some previous => some (Config.reverse previous)
      | none => some (Config.forward state)

/-- Exact inverse transition for `returnNext`. -/
def returnPrev {σ : Type u} (step : ReversibleStep σ) : Step (Config σ)
  | ⟨.forward, state⟩ =>
      match step.symm state with
      | some previous => some (Config.forward previous)
      | none => some (Config.reverse state)
  | ⟨.reverse, state⟩ =>
      match step state with
      | some target => some (Config.reverse target)
      | none => some (Config.forward state)

/-- One-step execution of the closed coupling has the stated checked inverse
on every tagged state, not only on generated history configurations. -/
theorem returnNext_eq_some_iff_returnPrev_eq_some {σ : Type u}
    (step : ReversibleStep σ) (source target : Config σ) :
    returnNext step source = some target ↔
      returnPrev step target = some source := by
  constructor
  · intro executed
    rcases source with ⟨direction, state⟩
    cases direction with
    | forward =>
        cases forwardStep : step state with
        | none =>
            have targetEq : target = Config.reverse state := by
              simpa [returnNext, Config.forward, Config.reverse,
                ReversibleStep.next, forwardStep] using executed.symm
            subst target
            simp [returnPrev, Config.forward, Config.reverse, forwardStep]
        | some nextState =>
            have targetEq : target = Config.forward nextState := by
              simpa [returnNext, Config.forward, ReversibleStep.next,
                forwardStep] using executed.symm
            subst target
            have inverseStep : step.symm nextState = some state :=
              step.eq_some_iff.mpr forwardStep
            simp [returnPrev, Config.forward, inverseStep]
    | reverse =>
        cases inverseStep : step.symm state with
        | none =>
            have targetEq : target = Config.forward state := by
              simpa [returnNext, Config.forward, Config.reverse,
                ReversibleStep.prev, inverseStep] using executed.symm
            subst target
            simp [returnPrev, Config.forward, Config.reverse, inverseStep]
        | some previous =>
            have targetEq : target = Config.reverse previous := by
              simpa [returnNext, Config.reverse, ReversibleStep.prev,
                inverseStep] using executed.symm
            subst target
            have forwardStep : step previous = some state :=
              step.eq_some_iff.mp inverseStep
            simp [returnPrev, Config.reverse, forwardStep]
  · intro reversed
    rcases target with ⟨direction, state⟩
    cases direction with
    | forward =>
        cases inverseStep : step.symm state with
        | none =>
            have sourceEq : source = Config.reverse state := by
              simpa [returnPrev, Config.forward, Config.reverse,
                ReversibleStep.prev, inverseStep] using reversed.symm
            subst source
            simp [returnNext, Config.forward, Config.reverse, inverseStep]
        | some previous =>
            have sourceEq : source = Config.forward previous := by
              simpa [returnPrev, Config.forward, ReversibleStep.prev,
                inverseStep] using reversed.symm
            subst source
            have forwardStep : step previous = some state :=
              step.eq_some_iff.mp inverseStep
            simp [returnNext, Config.forward, forwardStep]
    | reverse =>
        cases forwardStep : step state with
        | none =>
            have sourceEq : source = Config.forward state := by
              simpa [returnPrev, Config.forward, Config.reverse,
                ReversibleStep.next, forwardStep] using reversed.symm
            subst source
            simp [returnNext, Config.forward, Config.reverse, forwardStep]
        | some nextState =>
            have sourceEq : source = Config.reverse nextState := by
              simpa [returnPrev, Config.reverse, ReversibleStep.next,
                forwardStep] using reversed.symm
            subst source
            have inverseStep : step.symm nextState = some state :=
              step.eq_some_iff.mpr forwardStep
            simp [returnNext, Config.reverse, inverseStep]

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

/-- Every state has a successful next step in the uniformly closed gadget. -/
theorem exists_returnNext {σ : Type u} (step : ReversibleStep σ)
    (config : Config σ) : ∃ target, returnNext step config = some target := by
  rcases config with ⟨direction, state⟩
  cases direction with
  | forward =>
      cases executed : step state <;>
        simp [returnNext, Config.forward, Config.reverse, executed]
  | reverse =>
      cases executed : step.symm state <;>
        simp [returnNext, Config.forward, Config.reverse, executed]

/-- The inverse transition of the uniformly closed gadget is total as well. -/
theorem exists_returnPrev {σ : Type u} (step : ReversibleStep σ)
    (config : Config σ) : ∃ source, returnPrev step config = some source := by
  rcases config with ⟨direction, state⟩
  cases direction with
  | forward =>
      cases executed : step.symm state <;>
        simp [returnPrev, Config.forward, Config.reverse, executed]
  | reverse =>
      cases executed : step state <;>
        simp [returnPrev, Config.forward, Config.reverse, executed]

/-- In particular, the closed gadget has no forward-terminal states. -/
theorem returnGadget_not_terminal {σ : Type u} (step : ReversibleStep σ)
    (config : Config σ) : ¬Terminal (returnGadget step).next config := by
  intro terminal
  obtain ⟨target, executed⟩ := exists_returnNext step config
  change returnNext step config = none at terminal
  rw [terminal] at executed
  contradiction

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
  simp [turnaroundNext, Config.reverse, h]

@[simp]
theorem turnaroundNext_reverse_of_inverse_terminal
    (h : Terminal step.prev state) :
    turnaroundNext step (Config.reverse state) = none := by
  change step.symm state = none at h
  simp [turnaroundNext, Config.reverse, h]

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
  simp [returnNext, Config.reverse, h]

@[simp]
theorem returnNext_reverse_of_inverse_terminal
    (h : Terminal step.prev state) :
    returnNext step (Config.reverse state) =
      some (Config.forward state) := by
  change step.symm state = none at h
  simp [returnNext, Config.forward, Config.reverse, h]

end BoundaryEquations

end Lecerf.Machine.Coupling
