import Lecerf.Machine.History.Core

/-!
# Correctness of reversible history simulation

The generated-history invariant is exactly reachability from the fresh
simulator state.  This yields forward simulation, reflection, history growth,
terminality correspondence, and halting equivalence.
-/

namespace Lecerf.Machine.History

open Lecerf.Transition

universe u

/-- Every reachable simulator configuration carries a history generated from
the chosen source start. -/
theorem valid_of_reachable {σ : Type u} {next : Step σ} {start : σ}
    {config : Config σ}
    (reachable : Reachable (forward next) (Config.initial start) config) :
    Valid next start config := by
  induction reachable with
  | refl => exact Valid.initial
  | tail _ step valid =>
      change forward next _ = some _ at step
      exact valid.forward step

/-- Every generated history is reached by executable simulator steps. -/
theorem Valid.reachable {σ : Type u} {next : Step σ} {start : σ}
    {config : Config σ} (valid : Valid next start config) :
    Reachable (Lecerf.Machine.History.forward next)
      (Config.initial start) config := by
  induction valid with
  | initial => exact Reachable.refl _ _
  | push valid sourceStep reachable =>
      exact Reachable.trans reachable
        (Reachable.single (forward_of_source_step sourceStep))

/-- The history invariant is initialized and preserved precisely because it
characterizes reachability from the encoded initial source state. -/
theorem reachable_iff_valid {σ : Type u} (next : Step σ) (start : σ)
    (config : Config σ) :
    Reachable (forward next) (Config.initial start) config ↔
      Valid next start config :=
  ⟨valid_of_reachable, Valid.reachable⟩

/-- Projecting the current state of a valid history reflects a genuine source
run. -/
theorem Valid.current_reachable {σ : Type u} {next : Step σ} {start : σ}
    {config : Config σ} (valid : Valid next start config) :
    Reachable next start config.current := by
  induction valid with
  | initial => exact Reachable.refl _ _
  | push _ sourceStep reachable =>
      exact Reachable.trans reachable (Reachable.single sourceStep)

/-- Determinism makes generated checkpoints unique at a fixed elapsed step
count.  Equality of the current source state alone would be false for cyclic
computations, whose later visits carry longer histories. -/
theorem Valid.eq_of_history_length_eq {σ : Type u} {next : Step σ} {start : σ}
    {first second : Config σ} (firstValid : Valid next start first)
    (secondValid : Valid next start second)
    (lengthEq : first.history.length = second.history.length) : first = second := by
  induction firstValid generalizing second with
  | initial =>
      cases secondValid with
      | initial => rfl
      | @push current _ history _ _ =>
          change 0 = (current :: history).length at lengthEq
          simp at lengthEq
  | @push current firstTarget history firstValid firstStep ih =>
      cases secondValid with
      | initial =>
          change (current :: history).length = 0 at lengthEq
          simp at lengthEq
      | @push secondCurrent secondTarget secondHistory secondValid secondStep =>
          have tailLength : history.length = secondHistory.length := by
            change (current :: history).length =
              (secondCurrent :: secondHistory).length at lengthEq
            simpa using lengthEq
          have previousEq : Config.encode current history =
              Config.encode secondCurrent secondHistory :=
            ih secondValid tailLength
          have currentEq : current = secondCurrent :=
            congrArg Config.current previousEq
          have historyEq : history = secondHistory :=
            congrArg Config.history previousEq
          subst secondCurrent
          subst secondHistory
          have targetEq : firstTarget = secondTarget :=
            Step.successor_unique next firstStep secondStep
          subst secondTarget
          rfl

/-- Reachable simulator checkpoints at the same elapsed step count are equal. -/
theorem reachable_checkpoint_unique_of_history_length_eq {σ : Type u}
    {next : Step σ} {start : σ} {first second : Config σ}
    (firstReachable : Reachable (forward next) (Config.initial start) first)
    (secondReachable : Reachable (forward next) (Config.initial start) second)
    (lengthEq : first.history.length = second.history.length) : first = second :=
  (valid_of_reachable firstReachable).eq_of_history_length_eq
    (valid_of_reachable secondReachable) lengthEq

/-- A successful source step is one positive simulator step at every valid or
malformed history prefix; the runtime theorem itself needs no invariant. -/
theorem strictlyReachable_of_source_step {σ : Type u} {next : Step σ}
    {current target : σ} {history : List σ}
    (step : next current = some target) :
    StrictlyReachable (forward next)
      (Config.encode current history)
      (Config.encode target (current :: history)) :=
  StrictlyReachable.single (forward_of_source_step step)

/-- One successful simulator step increases the stored history length by
exactly one. -/
theorem history_length_of_forward {σ : Type u} {next : Step σ}
    {source target : Config σ}
    (step : forward next source = some target) :
    target.history.length = source.history.length + 1 := by
  obtain ⟨_, historyEq⟩ := (forward_eq_some_iff next source target).mp step
  rw [historyEq]
  simp

/-- Every source run generates some explicit history ending in its target. -/
theorem valid_checkpoint_of_source_reachable {σ : Type u} {next : Step σ}
    {start target : σ} (reachable : Reachable next start target) :
    ∃ history, Valid next start (Config.encode target history) := by
  induction reachable with
  | refl => exact ⟨[], Valid.initial⟩
  | @tail middle target _ sourceStep ih =>
      change next middle = some target at sourceStep
      obtain ⟨history, valid⟩ := ih
      exact ⟨middle :: history, Valid.push valid sourceStep⟩

/-- Every source run lifts to a reachable simulator checkpoint. -/
theorem reachable_checkpoint_of_source_reachable {σ : Type u}
    {next : Step σ} {start target : σ} (reachable : Reachable next start target) :
    ∃ history, Reachable (forward next) (Config.initial start)
      (Config.encode target history) := by
  obtain ⟨history, valid⟩ := valid_checkpoint_of_source_reachable reachable
  exact ⟨history, valid.reachable⟩

/-- Exact checkpoint reflection: the simulator reaches an encoded source
state with some history exactly when that source state is reachable. -/
theorem source_reachable_iff_exists_reachable_checkpoint {σ : Type u}
    (next : Step σ) (start target : σ) :
    Reachable next start target ↔
      ∃ history, Reachable (forward next) (Config.initial start)
        (Config.encode target history) := by
  constructor
  · exact reachable_checkpoint_of_source_reachable
  · rintro ⟨history, reachable⟩
    exact (valid_of_reachable reachable).current_reachable

/-- Simulator terminality depends only on terminality of its current source
state, never on the stored history. -/
theorem terminal_forward_iff {σ : Type u} (next : Step σ)
    (config : Config σ) :
    Terminal (forward next) config ↔ Terminal next config.current := by
  rcases config with ⟨current, history⟩
  simp [Terminal, forward]

/-- The reversible history simulator halts exactly when its source computation
halts.  Both preservation and reflection use reachable terminal checkpoints. -/
theorem haltsFrom_forward_iff {σ : Type u} (next : Step σ) (start : σ) :
    HaltsFrom (forward next) (Config.initial start) ↔ HaltsFrom next start := by
  rw [haltsFrom_iff_exists_reachable_terminal,
    haltsFrom_iff_exists_reachable_terminal]
  constructor
  · rintro ⟨config, reachable, terminal⟩
    exact ⟨config.current, (valid_of_reachable reachable).current_reachable,
      (terminal_forward_iff next config).mp terminal⟩
  · rintro ⟨target, reachable, terminal⟩
    obtain ⟨history, lifted⟩ := reachable_checkpoint_of_source_reachable reachable
    exact ⟨Config.encode target history, lifted,
      (terminal_forward_iff next _).mpr terminal⟩

/-- The same halting theorem through the bundled reversible transition. -/
theorem haltsFrom_reversible_iff {σ : Type u} [DecidableEq σ]
    (next : Step σ) (start : σ) :
    HaltsFrom (reversible next).next (Config.initial start) ↔
      HaltsFrom next start := by
  simpa using haltsFrom_forward_iff next start

end Lecerf.Machine.History
