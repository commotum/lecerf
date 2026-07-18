import Lecerf.Transition.Core

/-!
# Exact-length partial execution

This foundational leaf connects option-valued exact iteration with relational
reachability.  The iterator preserves failure with `Option.bind`; in
particular, an undefined intermediate state is never totalized.  Bridges to
the project-local iteration of a same-type `PEquiv` live separately in
`Lecerf.Transition.Exact` so generic transition clients need not import the
word layer.
-/

namespace Lecerf.Transition

universe u

/-- Execute exactly `n` successful applications of `next`.  Failure at any
intermediate application propagates to the result. -/
def exactIterate {σ : Type u} (next : Step σ) : Nat → Step σ
  | 0 => some
  | n + 1 => fun state => (exactIterate next n state).bind next

@[simp]
theorem exactIterate_zero {σ : Type u} (next : Step σ) (state : σ) :
    exactIterate next 0 state = some state :=
  rfl

theorem exactIterate_succ {σ : Type u} (next : Step σ) (n : Nat)
    (state : σ) :
    exactIterate next (n + 1) state =
      (exactIterate next n state).bind next :=
  rfl

/-- `target` is obtained from `source` after exactly `n` successful steps. -/
def ExactSteps {σ : Type u} (next : Step σ) (n : Nat)
    (source target : σ) : Prop :=
  exactIterate next n source = some target

@[simp]
theorem exactSteps_zero_iff {σ : Type u} (next : Step σ)
    (source target : σ) :
    ExactSteps next 0 source target ↔ source = target := by
  simp [ExactSteps]

theorem exactSteps_succ_iff {σ : Type u} (next : Step σ) (n : Nat)
    (source target : σ) :
    ExactSteps next (n + 1) source target ↔
      ∃ middle, ExactSteps next n source middle ∧
        next middle = some target := by
  simp only [ExactSteps, exactIterate_succ]
  exact Option.bind_eq_some_iff

/-- Exact iteration splits at an arbitrary sum of step counts. -/
theorem exactIterate_add {σ : Type u} (next : Step σ) (m n : Nat)
    (state : σ) :
    exactIterate next (m + n) state =
      (exactIterate next m state).bind (exactIterate next n) := by
  induction n with
  | zero => simp
  | succ n inductionHypothesis =>
      rw [Nat.add_succ, exactIterate_succ, inductionHypothesis]
      simp only [exactIterate, Option.bind_assoc]

/-- Concatenating exact runs adds their lengths. -/
theorem ExactSteps.trans {σ : Type u} {next : Step σ} {m n : Nat}
    {source middle target : σ}
    (first : ExactSteps next m source middle)
    (second : ExactSteps next n middle target) :
    ExactSteps next (m + n) source target := by
  unfold ExactSteps at first second ⊢
  rw [exactIterate_add, first]
  exact second

/-- Every exact run gives reflexive finite reachability. -/
theorem ExactSteps.reachable {σ : Type u} {next : Step σ} {n : Nat}
    {source target : σ} (run : ExactSteps next n source target) :
    Reachable next source target := by
  induction n generalizing target with
  | zero =>
      have equal := (exactSteps_zero_iff next source target).mp run
      subst target
      exact Reachable.refl next source
  | succ n inductionHypothesis =>
      rcases (exactSteps_succ_iff next n source target).mp run with
        ⟨middle, first, last⟩
      exact Reachable.trans (inductionHypothesis first)
        (Reachable.single last)

/-- An exact run with length represented as `n + 1` is a positive path. -/
theorem ExactSteps.strictlyReachable {σ : Type u} {next : Step σ} {n : Nat}
    {source target : σ} (run : ExactSteps next (n + 1) source target) :
    StrictlyReachable next source target := by
  induction n generalizing target with
  | zero =>
      exact StrictlyReachable.single (by
        simpa [ExactSteps, exactIterate] using run)
  | succ n inductionHypothesis =>
      rcases (exactSteps_succ_iff next (n + 1) source target).mp run with
        ⟨middle, first, last⟩
      exact StrictlyReachable.trans (inductionHypothesis first)
        (StrictlyReachable.single last)

/-- Reflexive reachability is precisely existence of a successful exact
iteration count. -/
theorem reachable_iff_exists_exactSteps {σ : Type u} (next : Step σ)
    (source target : σ) :
    Reachable next source target ↔
      ∃ n, ExactSteps next n source target := by
  constructor
  · intro reachable
    induction reachable with
    | refl => exact ⟨0, (exactSteps_zero_iff next source source).mpr rfl⟩
    | @tail middle target _ last inductionHypothesis =>
        rcases inductionHypothesis with ⟨n, first⟩
        exact ⟨n + 1,
          (exactSteps_succ_iff next n source target).mpr
            ⟨middle, first, last⟩⟩
  · rintro ⟨n, run⟩
    exact run.reachable

/-- Positive reachability is precisely existence of a successful positive
exact iteration count.  The witness `n` represents the exponent `n + 1`. -/
theorem strictlyReachable_iff_exists_exactSteps_succ {σ : Type u}
    (next : Step σ) (source target : σ) :
    StrictlyReachable next source target ↔
      ∃ n, ExactSteps next (n + 1) source target := by
  constructor
  · intro reachable
    induction reachable with
    | single step =>
        exact ⟨0, by simpa [ExactSteps, exactIterate] using step⟩
    | @tail middle target _ last inductionHypothesis =>
        rcases inductionHypothesis with ⟨n, first⟩
        exact ⟨n + 1,
          (exactSteps_succ_iff next (n + 1) source target).mpr
            ⟨middle, first, last⟩⟩
  · rintro ⟨n, run⟩
    exact run.strictlyReachable

/-- Equivalent positive-length formulation using an arbitrary nonzero natural
number rather than a predecessor witness. -/
theorem strictlyReachable_iff_exists_ne_zero_exactSteps {σ : Type u}
    (next : Step σ) (source target : σ) :
    StrictlyReachable next source target ↔
      ∃ n, n ≠ 0 ∧ ExactSteps next n source target := by
  rw [strictlyReachable_iff_exists_exactSteps_succ]
  constructor
  · rintro ⟨n, run⟩
    exact ⟨n + 1, Nat.succ_ne_zero n, run⟩
  · rintro ⟨n, nonzero, run⟩
    obtain ⟨k, rfl⟩ := Nat.exists_eq_succ_of_ne_zero nonzero
    exact ⟨k, run⟩

end Lecerf.Transition
