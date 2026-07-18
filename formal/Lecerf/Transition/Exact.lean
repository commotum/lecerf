import Lecerf.Transition.ExactCore
import Lecerf.Word.CodeMorphism

/-!
# Exact execution and partial-equivalence powers

This compatibility leaf re-exports the generic exact execution layer and
connects it to the project-local iteration of a same-type `PEquiv`.  Its Word
dependency is confined to those bridge theorems; generic transition clients
can import `Lecerf.Transition.ExactCore` instead.
-/

namespace Lecerf.Transition

universe u

/-! ## Bridge to partial-equivalence powers -/

/-- The generic exact iterator and `Lecerf.PEquiv.iterate` have identical
forward applications. -/
theorem exactIterate_eq_pequiv_iterate {X : Type u} (theta : X ≃. X)
    (n : Nat) (source : X) :
    exactIterate theta n source = Lecerf.PEquiv.iterate theta n source := by
  induction n with
  | zero => rfl
  | succ n inductionHypothesis =>
      rw [exactIterate_succ, Lecerf.PEquiv.iterate_succ_apply,
        inductionHypothesis]

/-- Exact-step predicate form of the partial-equivalence iteration bridge. -/
theorem pequiv_iterate_eq_some_iff_exactSteps {X : Type u}
    (theta : X ≃. X) (n : Nat) (source target : X) :
    Lecerf.PEquiv.iterate theta n source = some target ↔
      ExactSteps theta n source target := by
  rw [ExactSteps, exactIterate_eq_pequiv_iterate]

/-- The positive wrapper at index `k` executes exactly `k + 1` steps. -/
theorem pequiv_positiveIterate_eq_some_iff_exactSteps {X : Type u}
    (theta : X ≃. X) (k : Nat) (source target : X) :
    Lecerf.PEquiv.positiveIterate theta k source = some target ↔
      ExactSteps theta (k + 1) source target := by
  change Lecerf.PEquiv.iterate theta (k + 1) source = some target ↔ _
  exact pequiv_iterate_eq_some_iff_exactSteps theta (k + 1) source target

/-- A target lies on a positive partial-equivalence orbit exactly when it is
strictly reachable under the forward partial transition. -/
theorem pequiv_positiveIterate_iff_strictlyReachable {X : Type u}
    (theta : X ≃. X) (source target : X) :
    Lecerf.PEquiv.PositiveIterate theta source target ↔
      StrictlyReachable theta source target := by
  simpa only [Lecerf.PEquiv.PositiveIterate,
    pequiv_positiveIterate_eq_some_iff_exactSteps] using
      (strictlyReachable_iff_exists_exactSteps_succ theta source target).symm

end Lecerf.Transition
