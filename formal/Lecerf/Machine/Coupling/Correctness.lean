import Lecerf.Machine.Coupling.Core
import Lecerf.Machine.History.Correctness

/-!
# Correctness of forward--reverse coupling

Generic path-lifting lemmas explain the operational forward/turnaround/reverse
story for any partial equivalence.  Exact reflection theorems are then proved
for the full-predecessor history simulation: stored-history growth rules out a
forward-only return, and a generated-state invariant records that entering the
reverse phase witnesses source halting.
-/

namespace Lecerf.Machine.Coupling

open Lecerf.Transition

universe u

section GenericPaths

variable {σ : Type u} (step : ReversibleStep σ)

/-- A forward path lifts pointwise to the forward copy of the open coupling. -/
theorem turnaround_lift_forward_reachable {source target : σ}
    (reachable : Reachable step.next source target) :
    Reachable (turnaround step).next
      (Config.forward source) (Config.forward target) := by
  induction reachable with
  | refl => exact Reachable.refl _ _
  | tail reachable executed lifted =>
      change step.next _ = some _ at executed
      apply Reachable.trans lifted
      apply Reachable.single
      change turnaroundNext step (Config.forward _) = some (Config.forward _)
      exact turnaroundNext_forward_of_step step _ _ executed

/-- An inverse path lifts pointwise to the reverse copy of the open coupling. -/
theorem turnaround_lift_reverse_reachable {source target : σ}
    (reachable : Reachable step.prev source target) :
    Reachable (turnaround step).next
      (Config.reverse source) (Config.reverse target) := by
  induction reachable with
  | refl => exact Reachable.refl _ _
  | tail reachable executed lifted =>
      change step.prev _ = some _ at executed
      apply Reachable.trans lifted
      apply Reachable.single
      change turnaroundNext step (Config.reverse _) = some (Config.reverse _)
      exact turnaroundNext_reverse_of_inverse_step step _ _ executed

/-- A forward path lifts pointwise to the forward copy of the closed gadget. -/
theorem returnGadget_lift_forward_reachable {source target : σ}
    (reachable : Reachable step.next source target) :
    Reachable (returnGadget step).next
      (Config.forward source) (Config.forward target) := by
  induction reachable with
  | refl => exact Reachable.refl _ _
  | tail reachable executed lifted =>
      change step.next _ = some _ at executed
      apply Reachable.trans lifted
      apply Reachable.single
      change returnNext step (Config.forward _) = some (Config.forward _)
      exact returnNext_forward_of_step step _ _ executed

/-- An inverse path lifts pointwise to the reverse copy of the closed gadget. -/
theorem returnGadget_lift_reverse_reachable {source target : σ}
    (reachable : Reachable step.prev source target) :
    Reachable (returnGadget step).next
      (Config.reverse source) (Config.reverse target) := by
  induction reachable with
  | refl => exact Reachable.refl _ _
  | tail reachable executed lifted =>
      change step.prev _ = some _ at executed
      apply Reachable.trans lifted
      apply Reachable.single
      change returnNext step (Config.reverse _) = some (Config.reverse _)
      exact returnNext_reverse_of_inverse_step step _ _ executed

/-- If forward execution halts, the open coupling reaches the reverse copy of
its start after the terminal switch and inverse retracing. -/
theorem turnaround_reverseStart_reachable_of_halts (start : σ)
    (halts : HaltsFrom step.next start) :
    Reachable (turnaround step).next
      (Config.forward start) (Config.reverse start) := by
  rw [haltsFrom_iff_exists_reachable_terminal] at halts
  obtain ⟨terminal, forwardReachable, terminalForward⟩ := halts
  have reverseReachable : Reachable step.prev terminal start :=
    step.reachable_reverse forwardReachable
  exact Reachable.trans
    (turnaround_lift_forward_reachable step forwardReachable)
    (Reachable.trans
      (Reachable.single (by
        change turnaroundNext step (Config.forward terminal) =
          some (Config.reverse terminal)
        exact turnaroundNext_forward_of_terminal step terminal terminalForward))
      (turnaround_lift_reverse_reachable step reverseReachable))

/-- The same preservation path exists inside the uniformly closed gadget. -/
theorem returnGadget_reverseStart_reachable_of_halts (start : σ)
    (halts : HaltsFrom step.next start) :
    Reachable (returnGadget step).next
      (Config.forward start) (Config.reverse start) := by
  rw [haltsFrom_iff_exists_reachable_terminal] at halts
  obtain ⟨terminal, forwardReachable, terminalForward⟩ := halts
  have reverseReachable : Reachable step.prev terminal start :=
    step.reachable_reverse forwardReachable
  exact Reachable.trans
    (returnGadget_lift_forward_reachable step forwardReachable)
    (Reachable.trans
      (Reachable.single (by
        change returnNext step (Config.forward terminal) =
          some (Config.reverse terminal)
        exact returnNext_forward_of_terminal step terminal terminalForward))
      (returnGadget_lift_reverse_reachable step reverseReachable))

end GenericPaths

namespace History

open Lecerf.Machine.History

variable {σ : Type u}

/-- The open coupling applied to the reversible full-history simulation. -/
def turnaroundStep [DecidableEq σ] (source : Step σ) :
    ReversibleStep (Config (Lecerf.Machine.History.Config σ)) :=
  Coupling.turnaround (Lecerf.Machine.History.reversible source)

/-- The uniformly closed return coupling applied to the reversible
full-history simulation. -/
def returnStep [DecidableEq σ] (source : Step σ) :
    ReversibleStep (Config (Lecerf.Machine.History.Config σ)) :=
  Coupling.returnGadget (Lecerf.Machine.History.reversible source)

/-- The forward-tagged fresh history checkpoint. -/
def start (state : σ) : Config (Lecerf.Machine.History.Config σ) :=
  Config.forward (Lecerf.Machine.History.Config.initial state)

/-- The reverse-tagged fresh history checkpoint, corresponding to the paper's
starred initial configuration. -/
def target (state : σ) : Config (Lecerf.Machine.History.Config σ) :=
  Config.reverse (Lecerf.Machine.History.Config.initial state)

@[simp]
theorem start_ne_target (state : σ) : start state ≠ target state :=
  Config.forward_ne_reverse _ _

@[simp]
theorem target_ne_start (state : σ) : target state ≠ start state :=
  Config.reverse_ne_forward _ _

/-- Every nonempty history-forward path strictly increases the stored log. -/
theorem history_length_lt_of_strictlyReachable {source : Step σ}
    {first last : Lecerf.Machine.History.Config σ}
    (reachable : StrictlyReachable
      (Lecerf.Machine.History.forward source) first last) :
    first.history.length < last.history.length := by
  induction reachable with
  | single executed =>
      change Lecerf.Machine.History.forward source _ = some _ at executed
      rw [Lecerf.Machine.History.history_length_of_forward executed]
      exact Nat.lt_succ_self _
  | tail reachable executed growing =>
      change Lecerf.Machine.History.forward source _ = some _ at executed
      rw [Lecerf.Machine.History.history_length_of_forward executed]
      exact Nat.lt_trans growing (Nat.lt_succ_self _)

/-- In particular, the history-forward simulation has no positive return,
even when the projected source machine has a cycle. -/
theorem not_positiveReturn_forward (source : Step σ)
    (config : Lecerf.Machine.History.Config σ) :
    ¬PositiveReturn (Lecerf.Machine.History.forward source) config := by
  intro returned
  exact (Nat.lt_irrefl config.history.length)
    (history_length_lt_of_strictlyReachable returned)

/-- Checked backward execution preserves validity of a generated history. -/
theorem valid_of_backward [DecidableEq σ] {source : Step σ} {initial : σ}
    {config previous : Lecerf.Machine.History.Config σ}
    (valid : Lecerf.Machine.History.Valid source initial config)
    (executed : Lecerf.Machine.History.backward source config = some previous) :
    Lecerf.Machine.History.Valid source initial previous := by
  cases valid with
  | initial =>
      rw [Lecerf.Machine.History.backward_initial] at executed
      contradiction
  | @push current nextState history valid sourceStep =>
      have expected : Lecerf.Machine.History.backward source
          (Lecerf.Machine.History.Config.encode nextState (current :: history)) =
          some (Lecerf.Machine.History.Config.encode current history) :=
        (Lecerf.Machine.History.forward_eq_some_iff_backward_eq_some
          source _ _).mp
          (Lecerf.Machine.History.forward_of_source_step sourceStep)
      rw [expected] at executed
      cases executed
      exact valid

/-- Invariant for states generated by either coupling from `start initial`.
Entering the reverse phase retains a valid history and records the source
halting witness forced by the forward-terminal switch. -/
def Generated (source : Step σ) (initial : σ) :
    Config (Lecerf.Machine.History.Config σ) → Prop
  | ⟨.forward, config⟩ =>
      Lecerf.Machine.History.Valid source initial config
  | ⟨.reverse, config⟩ =>
      Lecerf.Machine.History.Valid source initial config ∧
        HaltsFrom source initial

theorem generated_start (source : Step σ) (initial : σ) :
    Generated source initial (start initial) :=
  Lecerf.Machine.History.Valid.initial

/-- The generated-state invariant is preserved by every successful open
coupling step. -/
theorem Generated.turnaround [DecidableEq σ] {source : Step σ} {initial : σ}
    {config nextConfig : Config (Lecerf.Machine.History.Config σ)}
    (generated : Generated source initial config)
    (executed : (turnaroundStep source).next config = some nextConfig) :
    Generated source initial nextConfig := by
  change Coupling.turnaroundNext
    (Lecerf.Machine.History.reversible source) config = some nextConfig at executed
  rcases config with ⟨direction, historyConfig⟩
  cases direction with
  | forward =>
      change Lecerf.Machine.History.Valid source initial historyConfig at generated
      cases historyStep : Lecerf.Machine.History.forward source historyConfig with
      | some nextHistory =>
          have nextEq : nextConfig = Config.forward nextHistory := by
            simpa [Coupling.turnaroundNext, Config.forward,
              Lecerf.Machine.History.reversible, historyStep] using executed.symm
          subst nextConfig
          exact generated.forward historyStep
      | none =>
          have nextEq : nextConfig = Config.reverse historyConfig := by
            simpa [Coupling.turnaroundNext, Config.forward, Config.reverse,
              Lecerf.Machine.History.reversible, historyStep] using executed.symm
          subst nextConfig
          refine ⟨generated, ?_⟩
          rw [haltsFrom_iff_exists_reachable_terminal]
          exact ⟨historyConfig.current, generated.current_reachable,
            (Lecerf.Machine.History.terminal_forward_iff
              source historyConfig).mp historyStep⟩
  | reverse =>
      rcases generated with ⟨valid, halts⟩
      change Coupling.turnaroundNext
        (Lecerf.Machine.History.reversible source)
          (Config.reverse historyConfig) = some nextConfig at executed
      cases historyStep : Lecerf.Machine.History.backward source historyConfig with
      | none =>
          have inverseTerminal : Terminal
              (Lecerf.Machine.History.reversible source).prev historyConfig := by
            change Lecerf.Machine.History.backward source historyConfig = none
            exact historyStep
          have runtime := Coupling.turnaroundNext_reverse_of_inverse_terminal
            (Lecerf.Machine.History.reversible source) historyConfig inverseTerminal
          rw [runtime] at executed
          contradiction
      | some previous =>
          have inverseStep :
              (Lecerf.Machine.History.reversible source).prev historyConfig =
                some previous := by
            change Lecerf.Machine.History.backward source historyConfig = some previous
            exact historyStep
          have runtime := Coupling.turnaroundNext_reverse_of_inverse_step
            (Lecerf.Machine.History.reversible source) historyConfig previous inverseStep
          have nextEq : nextConfig = Config.reverse previous := by
            rw [runtime] at executed
            exact (Option.some.inj executed).symm
          subst nextConfig
          exact ⟨valid_of_backward valid historyStep, halts⟩

/-- The generated-state invariant is preserved by every closed return-gadget
step. -/
theorem Generated.returnStep [DecidableEq σ] {source : Step σ} {initial : σ}
    {config nextConfig : Config (Lecerf.Machine.History.Config σ)}
    (generated : Generated source initial config)
    (executed : (History.returnStep source).next config = some nextConfig) :
    Generated source initial nextConfig := by
  change Coupling.returnNext
    (Lecerf.Machine.History.reversible source) config = some nextConfig at executed
  rcases config with ⟨direction, historyConfig⟩
  cases direction with
  | forward =>
      change Lecerf.Machine.History.Valid source initial historyConfig at generated
      cases historyStep : Lecerf.Machine.History.forward source historyConfig with
      | some nextHistory =>
          have nextEq : nextConfig = Config.forward nextHistory := by
            simpa [Coupling.returnNext, Config.forward,
              Lecerf.Machine.History.reversible, historyStep] using executed.symm
          subst nextConfig
          exact generated.forward historyStep
      | none =>
          have nextEq : nextConfig = Config.reverse historyConfig := by
            simpa [Coupling.returnNext, Config.forward, Config.reverse,
              Lecerf.Machine.History.reversible, historyStep] using executed.symm
          subst nextConfig
          refine ⟨generated, ?_⟩
          rw [haltsFrom_iff_exists_reachable_terminal]
          exact ⟨historyConfig.current, generated.current_reachable,
            (Lecerf.Machine.History.terminal_forward_iff
              source historyConfig).mp historyStep⟩
  | reverse =>
      rcases generated with ⟨valid, halts⟩
      change Coupling.returnNext
        (Lecerf.Machine.History.reversible source)
          (Config.reverse historyConfig) = some nextConfig at executed
      cases historyStep : Lecerf.Machine.History.backward source historyConfig with
      | some previous =>
          have inverseStep :
              (Lecerf.Machine.History.reversible source).prev historyConfig =
                some previous := by
            change Lecerf.Machine.History.backward source historyConfig = some previous
            exact historyStep
          have runtime := Coupling.returnNext_reverse_of_inverse_step
            (Lecerf.Machine.History.reversible source) historyConfig previous inverseStep
          have nextEq : nextConfig = Config.reverse previous := by
            rw [runtime] at executed
            exact (Option.some.inj executed).symm
          subst nextConfig
          exact ⟨valid_of_backward valid historyStep, halts⟩
      | none =>
          have inverseTerminal : Terminal
              (Lecerf.Machine.History.reversible source).prev historyConfig := by
            change Lecerf.Machine.History.backward source historyConfig = none
            exact historyStep
          have runtime := Coupling.returnNext_reverse_of_inverse_terminal
            (Lecerf.Machine.History.reversible source) historyConfig inverseTerminal
          have nextEq : nextConfig = Config.forward historyConfig := by
            rw [runtime] at executed
            exact (Option.some.inj executed).symm
          subst nextConfig
          exact valid

theorem generated_of_turnaround_reachable [DecidableEq σ]
    (source : Step σ) (initial : σ)
    {config : Config (Lecerf.Machine.History.Config σ)}
    (reachable : Reachable (turnaroundStep source).next (start initial) config) :
    Generated source initial config := by
  induction reachable with
  | refl => exact generated_start source initial
  | tail _ executed generated =>
      change (turnaroundStep source).next _ = some _ at executed
      exact generated.turnaround executed

theorem generated_of_return_reachable [DecidableEq σ]
    (source : Step σ) (initial : σ)
    {config : Config (Lecerf.Machine.History.Config σ)}
    (reachable : Reachable (returnStep source).next (start initial) config) :
    Generated source initial config := by
  induction reachable with
  | refl => exact generated_start source initial
  | tail _ executed generated =>
      change (returnStep source).next _ = some _ at executed
      exact generated.returnStep executed

/-- Reaching any reverse-tagged state in the open coupling reflects source
halting. -/
theorem turnaround_reverse_reachable_reflects_halts [DecidableEq σ]
    (source : Step σ) (initial : σ)
    {config : Lecerf.Machine.History.Config σ}
    (reachable : Reachable (turnaroundStep source).next
      (start initial) (Config.reverse config)) :
    HaltsFrom source initial :=
  (generated_of_turnaround_reachable source initial reachable).2

/-- Reaching any reverse-tagged state in the closed coupling likewise reflects
the terminal switch that has already occurred. -/
theorem return_reverse_reachable_reflects_halts [DecidableEq σ]
    (source : Step σ) (initial : σ)
    {config : Lecerf.Machine.History.Config σ}
    (reachable : Reachable (returnStep source).next
      (start initial) (Config.reverse config)) :
    HaltsFrom source initial :=
  (generated_of_return_reachable source initial reachable).2

/-- Source halting constructs the complete open forward/turnaround/retrace
path to the reverse-tagged initial checkpoint. -/
theorem target_reachable_of_halts [DecidableEq σ]
    (source : Step σ) (initial : σ) (halts : HaltsFrom source initial) :
    Reachable (turnaroundStep source).next (start initial) (target initial) := by
  apply turnaround_reverseStart_reachable_of_halts
  exact (Lecerf.Machine.History.haltsFrom_reversible_iff
    source initial).mpr halts

/-- Exact specified-target statement for the open coupling. -/
theorem target_strictlyReachable_iff_halts [DecidableEq σ]
    (source : Step σ) (initial : σ) :
    StrictlyReachable (turnaroundStep source).next
      (start initial) (target initial) ↔ HaltsFrom source initial := by
  constructor
  · intro reachable
    exact turnaround_reverse_reachable_reflects_halts source initial
      reachable.toReachable
  · intro halts
    exact (reachable_iff_strictlyReachable_of_ne
      (start_ne_target initial)).mp (target_reachable_of_halts source initial halts)

/-- The starred target is terminal for the open turnaround, because a fresh
history has no checked predecessor. -/
theorem terminal_target [DecidableEq σ] (source : Step σ) (initial : σ) :
    Terminal (turnaroundStep source).next (target initial) := by
  change Coupling.turnaroundNext
    (Lecerf.Machine.History.reversible source)
      (Config.reverse (Lecerf.Machine.History.Config.initial initial)) = none
  simpa using Coupling.turnaroundNext_reverse_of_inverse_terminal
    (Lecerf.Machine.History.reversible source)
    (Lecerf.Machine.History.Config.initial initial)
    (Lecerf.Machine.History.terminal_backward_initial source initial)

/-- The closed coupling reaches the same distinct reverse-initial checkpoint
whenever the source halts. -/
theorem return_target_reachable_of_halts [DecidableEq σ]
    (source : Step σ) (initial : σ) (halts : HaltsFrom source initial) :
    Reachable (returnStep source).next (start initial) (target initial) := by
  apply returnGadget_reverseStart_reachable_of_halts
  exact (Lecerf.Machine.History.haltsFrom_reversible_iff
    source initial).mpr halts

/-- The closed gadget's reverse-initial target takes one more step back to the
forward initial state. -/
theorem return_target_step [DecidableEq σ]
    (source : Step σ) (initial : σ) :
    (returnStep source).next (target initial) = some (start initial) := by
  change Coupling.returnNext
    (Lecerf.Machine.History.reversible source)
      (Config.reverse (Lecerf.Machine.History.Config.initial initial)) =
        some (Config.forward (Lecerf.Machine.History.Config.initial initial))
  simpa using Coupling.returnNext_reverse_of_inverse_terminal
    (Lecerf.Machine.History.reversible source)
    (Lecerf.Machine.History.Config.initial initial)
    (Lecerf.Machine.History.terminal_backward_initial source initial)

/-- Dually, the exact inverse of the start is the reverse-initial target. -/
theorem return_prev_start [DecidableEq σ]
    (source : Step σ) (initial : σ) :
    (returnStep source).prev (start initial) = some (target initial) :=
  (returnStep source).next_eq_some_iff_prev_eq_some.mp
    (return_target_step source initial)

/-- Therefore the reverse-initial target is the unique successful predecessor
of the forward initial state in the closed reversible transition. -/
theorem predecessor_of_start [DecidableEq σ]
    (source : Step σ) (initial : σ)
    {config : Config (Lecerf.Machine.History.Config σ)}
    (executed : (returnStep source).next config = some (start initial)) :
    config = target initial := by
  have inverse := (returnStep source).next_eq_some_iff_prev_eq_some.mp executed
  rw [return_prev_start source initial] at inverse
  exact (Option.some.inj inverse).symm

/-- Exact positive-return statement for the uniformly closed coupling. -/
theorem positiveReturn_iff_halts [DecidableEq σ]
    (source : Step σ) (initial : σ) :
    PositiveReturn (returnStep source).next (start initial) ↔
      HaltsFrom source initial := by
  constructor
  · intro returned
    obtain ⟨predecessor, reachable, finalStep⟩ :=
      Relation.TransGen.tail'_iff.mp returned
    have predecessorEq : predecessor = target initial :=
      predecessor_of_start source initial finalStep
    subst predecessor
    exact return_reverse_reachable_reflects_halts source initial reachable
  · intro halts
    have targetReachable := return_target_reachable_of_halts source initial halts
    have targetPositive : StrictlyReachable (returnStep source).next
        (start initial) (target initial) :=
      (reachable_iff_strictlyReachable_of_ne (start_ne_target initial)).mp
        targetReachable
    exact StrictlyReachable.trans targetPositive
      (StrictlyReachable.single (return_target_step source initial))

end History

end Lecerf.Machine.Coupling
