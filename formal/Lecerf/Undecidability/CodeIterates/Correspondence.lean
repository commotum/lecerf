import Lecerf.Encoding.StepCode.Correctness
import Lecerf.Undecidability.CodeIterates.Problems

/-!
# Semantic correspondence for raw code-iterate problems

A valid runtime descriptor executes the same partial word map as its
successful-edge code isomorphism.  This module lifts that pointwise fact to
exact and positive iteration, then specializes it to canonical configuration
words.  No failed application is totalized: both sides use bind-preserving
partial iteration.

The final two theorems identify the raw code predicates on canonical words
with the already-separated reversible-machine return and reachability
predicates.  They do not use the universal compiler or any undecidability
reduction.
-/

namespace Lecerf.Undecidability.CodeIterates

open Lecerf.Encoding
open Lecerf.Encoding.StepCode
open Lecerf.Machine
open Lecerf.Transition
open Lecerf.Word

/-! ## Runtime iteration versus the semantic code isomorphism -/

/-- Exact checked iteration of a valid raw descriptor is literally iteration
of the partial equivalence underlying its successful-edge code isomorphism. -/
theorem checkedExactIterate_eq_stepCodeIso_iterate
    (descriptor : CodeDescriptor) (valid : descriptor.Valid)
    (n : Nat) (word : Word Bool) :
    exactIterate descriptor.checkedApply n word =
      Lecerf.PEquiv.iterate
        (stepCodeIso descriptor valid.reversible.2).toPEquiv n word := by
  have checkedAction : descriptor.checkedApply =
      (stepCodeIso descriptor valid.reversible.2).toPEquiv := by
    funext input
    exact descriptor.checkedApply_eq_stepCodeIso_toPEquiv valid input
  rw [checkedAction]
  exact exactIterate_eq_pequiv_iterate
    (stepCodeIso descriptor valid.reversible.2).toPEquiv n word

/-- Supplied-exponent equation form of checked/semantic correspondence. -/
theorem checkedExactSteps_iff_stepCodeIso_iterate_eq_some
    (descriptor : CodeDescriptor) (valid : descriptor.Valid)
    (n : Nat) (source target : Word Bool) :
    ExactSteps descriptor.checkedApply n source target ↔
      Lecerf.PEquiv.iterate
        (stepCodeIso descriptor valid.reversible.2).toPEquiv n source =
          some target := by
  rw [ExactSteps, checkedExactIterate_eq_stepCodeIso_iterate
    descriptor valid n source]

/-- Existence of a successful positive checked iterate is exactly positive
orbit membership for the semantic code isomorphism. -/
theorem checkedPositiveExactSteps_iff_stepCodeIso_positiveIterate
    (descriptor : CodeDescriptor) (valid : descriptor.Valid)
    (source target : Word Bool) :
    (∃ k : Nat,
        ExactSteps descriptor.checkedApply (k + 1) source target) ↔
      Lecerf.PEquiv.PositiveIterate
        (stepCodeIso descriptor valid.reversible.2).toPEquiv source target := by
  change (∃ k : Nat,
      ExactSteps descriptor.checkedApply (k + 1) source target) ↔
    ∃ k : Nat,
      Lecerf.PEquiv.iterate
        (stepCodeIso descriptor valid.reversible.2).toPEquiv (k + 1) source =
          some target
  simp only [checkedExactSteps_iff_stepCodeIso_iterate_eq_some
    descriptor valid]

/-! ## Problem-level semantic characterizations -/

/-- The positive fixed-orbit predicate is its intended semantic equation for
the code isomorphism presented by a valid raw descriptor. -/
theorem positiveFixedOrbitYes_iff_stepCodeIso_positiveIterate
    (input : FixedOrbitInput) :
    PositiveFixedOrbitYes input ↔
      ∃ valid : input.1.Valid,
        Lecerf.PEquiv.PositiveIterate
          (stepCodeIso input.1 valid.reversible.2).toPEquiv
          input.2 input.2 := by
  constructor
  · rintro ⟨valid, orbit⟩
    exact ⟨valid,
      (checkedPositiveExactSteps_iff_stepCodeIso_positiveIterate
        input.1 valid input.2 input.2).mp orbit⟩
  · rintro ⟨valid, orbit⟩
    exact ⟨valid,
      (checkedPositiveExactSteps_iff_stepCodeIso_positiveIterate
        input.1 valid input.2 input.2).mpr orbit⟩

/-- The distinct-orbit predicate is the semantic positive iterate equation,
together with the explicit inequality required by the paper's nontrivial
two-word problem. -/
theorem distinctOrbitYes_iff_stepCodeIso_positiveIterate
    (input : DistinctOrbitInput) :
    DistinctOrbitYes input ↔
      ∃ valid : input.1.Valid,
        input.2.1 ≠ input.2.2 ∧
          Lecerf.PEquiv.PositiveIterate
            (stepCodeIso input.1 valid.reversible.2).toPEquiv
            input.2.1 input.2.2 := by
  constructor
  · rintro ⟨valid, distinct, orbit⟩
    exact ⟨valid, distinct,
      (checkedPositiveExactSteps_iff_stepCodeIso_positiveIterate
        input.1 valid input.2.1 input.2.2).mp orbit⟩
  · rintro ⟨valid, distinct, orbit⟩
    exact ⟨valid, distinct,
      (checkedPositiveExactSteps_iff_stepCodeIso_positiveIterate
        input.1 valid input.2.1 input.2.2).mpr orbit⟩

/-- Recognition at a supplied exponent is also the literal semantic iterate
equation; positivity remains an explicit guard rather than being hidden in an
existential wrapper. -/
theorem positiveIterateAtYes_iff_stepCodeIso_iterate
    (input : SuppliedExponentInput) :
    PositiveIterateAtYes input ↔
      ∃ valid : input.1.Valid,
        input.2.1 ≠ 0 ∧
          Lecerf.PEquiv.iterate
            (stepCodeIso input.1 valid.reversible.2).toPEquiv input.2.1
              input.2.2.1 = some input.2.2.2 := by
  constructor
  · rintro ⟨valid, positive, exact⟩
    exact ⟨valid, positive,
      (checkedExactSteps_iff_stepCodeIso_iterate_eq_some
        input.1 valid input.2.1 input.2.2.1 input.2.2.2).mp exact⟩
  · rintro ⟨valid, positive, iterate⟩
    exact ⟨valid, positive,
      (checkedExactSteps_iff_stepCodeIso_iterate_eq_some
        input.1 valid input.2.1 input.2.2.1 input.2.2.2).mpr iterate⟩

/-! ## Canonical configuration words -/

/-- At a supplied exponent, checked iteration between canonical configuration
words is exactly machine execution for that many successful steps. -/
theorem encodedCheckedExactSteps_iff_exactSteps
    (descriptor : CodeDescriptor) (valid : descriptor.Valid)
    (n : Nat) (source target : ReversibleTwoTape.TargetConfig) :
    ExactSteps descriptor.checkedApply n
        (ConfigCode.encodeConfig source) (ConfigCode.encodeConfig target) ↔
      ExactSteps descriptor.step n source target := by
  rw [checkedExactSteps_iff_stepCodeIso_iterate_eq_some
    descriptor valid]
  exact stepCodeIso_iterate_eq_some_iff
    descriptor valid.reversible.2 n source target

/-- On canonical configuration words, positive checked word iteration is
equivalent to strict reachability under the machine table. -/
theorem encodedCheckedPositiveExactSteps_iff_strictlyReachable
    (descriptor : CodeDescriptor) (valid : descriptor.Valid)
    (source target : ReversibleTwoTape.TargetConfig) :
    (∃ k : Nat,
        ExactSteps descriptor.checkedApply (k + 1)
          (ConfigCode.encodeConfig source)
          (ConfigCode.encodeConfig target)) ↔
      StrictlyReachable descriptor.step source target := by
  rw [checkedPositiveExactSteps_iff_stepCodeIso_positiveIterate
    descriptor valid]
  exact stepCodeIso_positiveIterate_iff_strictlyReachable
    descriptor valid.reversible.2 source target

/-- Canonically encoding the checkpoint word turns the reversible-machine
positive-return predicate into the positive fixed-word equation. -/
theorem positiveFixedOrbitYes_encodeConfig_iff_returnYes
    (machine : ReversibleTwoTape.TargetMachine)
    (config : ReversibleTwoTape.TargetConfig) :
    PositiveFixedOrbitYes (machine, ConfigCode.encodeConfig config) ↔
      ReversibleTwoTape.ReturnYes (machine, config) := by
  change (machine.SyntacticallyReversible ∧
      ∃ k : Nat,
        ExactSteps (Descriptor.checkedApply machine) (k + 1)
          (ConfigCode.encodeConfig config)
          (ConfigCode.encodeConfig config)) ↔
    machine.SyntacticallyReversible ∧
      StrictlyReachable machine.step config config
  constructor
  · rintro ⟨valid, orbit⟩
    exact ⟨valid,
      (encodedCheckedPositiveExactSteps_iff_strictlyReachable
        machine valid config config).mp orbit⟩
  · rintro ⟨valid, reachable⟩
    exact ⟨valid,
      (encodedCheckedPositiveExactSteps_iff_strictlyReachable
        machine valid config config).mpr reachable⟩

/-- Canonically encoding both endpoints turns certified structurally distinct
machine reachability into the distinct positive word-orbit equation. -/
theorem distinctOrbitYes_encodeConfig_iff_reachabilityYes
    (machine : ReversibleTwoTape.TargetMachine)
    (source target : ReversibleTwoTape.TargetConfig) :
    DistinctOrbitYes
        (machine, ConfigCode.encodeConfig source,
          ConfigCode.encodeConfig target) ↔
      ReversibleTwoTape.ReachabilityYes (machine, source, target) := by
  change (machine.SyntacticallyReversible ∧
      ConfigCode.encodeConfig source ≠ ConfigCode.encodeConfig target ∧
        ∃ k : Nat,
          ExactSteps (Descriptor.checkedApply machine) (k + 1)
            (ConfigCode.encodeConfig source)
            (ConfigCode.encodeConfig target)) ↔
    machine.SyntacticallyReversible ∧ source ≠ target ∧
      StrictlyReachable machine.step source target
  constructor
  · rintro ⟨valid, encodedDistinct, orbit⟩
    have distinct : source ≠ target := by
      intro equal
      exact encodedDistinct (congrArg ConfigCode.encodeConfig equal)
    exact ⟨valid, distinct,
      (encodedCheckedPositiveExactSteps_iff_strictlyReachable
        machine valid source target).mp orbit⟩
  · rintro ⟨valid, distinct, reachable⟩
    have encodedDistinct :
        ConfigCode.encodeConfig source ≠ ConfigCode.encodeConfig target := by
      intro equal
      exact distinct
        (ConfigCode.encodeConfig_isIndexedCode.injective equal)
    exact ⟨valid, encodedDistinct,
      (encodedCheckedPositiveExactSteps_iff_strictlyReachable
        machine valid source target).mpr reachable⟩

end Lecerf.Undecidability.CodeIterates
