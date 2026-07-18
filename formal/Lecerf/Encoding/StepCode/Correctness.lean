import Lecerf.Encoding.StepCode.Core
import Lecerf.Transition.Exact

/-!
# Correctness of configuration-edge code isomorphisms

The semantic ambient action of `stepCodeIso` is defined on an encoded
configuration exactly when the underlying machine takes a successful step.
Every successful result is another canonical configuration word.  Iteration
therefore preserves and reflects exact machine execution without admitting
malformed intermediate words or totalizing a failed step.
-/

namespace Lecerf.Encoding.StepCode

open Lecerf.Machine
open Lecerf.Machine.TwoTape
open Lecerf.Transition
open Lecerf.Word

universe u v w

variable {Q : Type u} {Γ₁ : Type v} {Γ₂ : Type w}
  [Inhabited Γ₁] [Inhabited Γ₂]
  [Primcodable Q] [Primcodable Γ₁] [Primcodable Γ₂]
  [DecidableEq Q] [DecidableEq Γ₁] [DecidableEq Γ₂]

private theorem lift_sourceWord_eq_encodeConfigs
    {machine : FiniteMachine Q Γ₁ Γ₂} (indices : Word (Edge machine)) :
    FreeMonoid.lift (sourceWord (machine := machine)) indices =
      ConfigCode.encodeConfigs (indices.toList.map Edge.source) := by
  apply FreeMonoid.toList.injective
  rw [Lecerf.Word.toList_lift]
  simp [sourceWord, ConfigCode.encodeConfigs,
    ConfigCode.encodeConfigListBits, List.map_map, Function.comp_def]

private theorem lift_targetWord_eq_encodeConfigs
    {machine : FiniteMachine Q Γ₁ Γ₂} (indices : Word (Edge machine)) :
    FreeMonoid.lift (targetWord (machine := machine)) indices =
      ConfigCode.encodeConfigs (indices.toList.map Edge.target) := by
  apply FreeMonoid.toList.injective
  rw [Lecerf.Word.toList_lift]
  simp [targetWord, ConfigCode.encodeConfigs,
    ConfigCode.encodeConfigListBits, List.map_map, Function.comp_def]

private theorem encodeConfigs_single
    (config : Config Q Γ₁ Γ₂) :
    ConfigCode.encodeConfigs [config] = ConfigCode.encodeConfig config := by
  rw [ConfigCode.encodeConfigs_eq_lift]
  simp

private theorem exists_edge_of_lift_sourceWord_eq
    {machine : FiniteMachine Q Γ₁ Γ₂}
    (indices : Word (Edge machine)) (config : Config Q Γ₁ Γ₂)
    (factorization :
      FreeMonoid.lift (sourceWord (machine := machine)) indices =
        ConfigCode.encodeConfig config) :
    ∃ edge : Edge machine,
      indices = FreeMonoid.of edge ∧ edge.source = config := by
  have encodedListEq :
      ConfigCode.encodeConfigs (indices.toList.map Edge.source) =
        ConfigCode.encodeConfigs [config] := by
    rw [← lift_sourceWord_eq_encodeConfigs, factorization,
      encodeConfigs_single]
  have decodedEq := congrArg ConfigCode.decodeConfigs encodedListEq
  have sourceListEq : indices.toList.map Edge.source = [config] := by
    simpa using decodedEq
  cases indicesListEq : indices.toList with
  | nil => simp [indicesListEq] at sourceListEq
  | cons edge rest =>
      have parts : edge.source = config ∧ rest = [] := by
        simpa [indicesListEq] using sourceListEq
      refine ⟨edge, ?_, parts.1⟩
      apply FreeMonoid.toList.injective
      simp [indicesListEq, parts.2]

/-- Strong one-step reflection: from a canonical source, every successful
ambient output is exactly the canonical encoding of a machine successor. -/
theorem stepCodeIso_apply_eq_some_iff_exists
    (machine : FiniteMachine Q Γ₁ Γ₂)
    (backward : BackwardUnique machine.step)
    (source : Config Q Γ₁ Γ₂) (word : Word Bool) :
    (stepCodeIso machine backward).toPEquiv
        (ConfigCode.encodeConfig source) = some word ↔
      ∃ target, machine.step source = some target ∧
        word = ConfigCode.encodeConfig target := by
  let iso := stepCodeIso machine backward
  constructor
  · intro applied
    have defined :
        ConfigCode.encodeConfig source ∈ generated iso.source :=
      (iso.toPEquiv_isSome_iff (ConfigCode.encodeConfig source)).mp (by
        rw [applied]
        rfl)
    change ConfigCode.encodeConfig source ∈
      generated (sourceWord (machine := machine)) at defined
    rcases (mem_generated_iff_exists_lift
      (sourceWord (machine := machine))
      (ConfigCode.encodeConfig source)).mp defined with
      ⟨indices, factorization⟩
    rcases exists_edge_of_lift_sourceWord_eq indices source factorization with
      ⟨edge, _, edgeSource⟩
    refine ⟨edge.target, ?_, ?_⟩
    · simpa only [edgeSource] using edge.step_eq
    · have edgeApplied := stepCodeIso_edge machine backward edge
      rw [sourceWord, edgeSource] at edgeApplied
      have outputEq : word = targetWord edge :=
        Option.some.inj (applied.symm.trans edgeApplied)
      simpa only [targetWord] using outputEq
  · rintro ⟨target, step, rfl⟩
    let edge : Edge machine := ⟨source, target, step⟩
    simpa only [edge, sourceWord, targetWord] using
      stepCodeIso_edge machine backward edge

/-- Exact one-step preservation and reflection between machine configurations
and their Boolean codewords. -/
theorem stepCodeIso_apply_eq_some_iff
    (machine : FiniteMachine Q Γ₁ Γ₂)
    (backward : BackwardUnique machine.step)
    (source target : Config Q Γ₁ Γ₂) :
    (stepCodeIso machine backward).toPEquiv
        (ConfigCode.encodeConfig source) =
          some (ConfigCode.encodeConfig target) ↔
      machine.step source = some target := by
  constructor
  · intro applied
    rcases (stepCodeIso_apply_eq_some_iff_exists machine backward source
      (ConfigCode.encodeConfig target)).mp applied with
      ⟨actual, step, encodedEq⟩
    have actualEq : actual = target :=
      ConfigCode.encodeConfig_isIndexedCode.injective encodedEq.symm
    simpa only [actualEq] using step
  · intro step
    exact (stepCodeIso_apply_eq_some_iff_exists machine backward source
      (ConfigCode.encodeConfig target)).mpr ⟨target, step, rfl⟩

/-- Executable equation on canonical single-configuration words. -/
theorem stepCodeIso_apply_encodeConfig
    (machine : FiniteMachine Q Γ₁ Γ₂)
    (backward : BackwardUnique machine.step)
    (source : Config Q Γ₁ Γ₂) :
    (stepCodeIso machine backward).toPEquiv
        (ConfigCode.encodeConfig source) =
      (machine.step source).map ConfigCode.encodeConfig := by
  cases stepEq : machine.step source with
  | none =>
      cases appliedEq :
          (stepCodeIso machine backward).toPEquiv
            (ConfigCode.encodeConfig source) with
      | none => rfl
      | some word =>
          rcases (stepCodeIso_apply_eq_some_iff_exists machine backward source word).mp
            appliedEq with ⟨target, targetStep, _⟩
          rw [stepEq] at targetStep
          contradiction
  | some target =>
      simpa [stepEq] using
        (stepCodeIso_apply_eq_some_iff machine backward source target).mpr stepEq

/-- Terminality is represented by literal undefinedness, not identity or a
sink word. -/
theorem stepCodeIso_apply_eq_none_iff
    (machine : FiniteMachine Q Γ₁ Γ₂)
    (backward : BackwardUnique machine.step)
    (source : Config Q Γ₁ Γ₂) :
    (stepCodeIso machine backward).toPEquiv
        (ConfigCode.encodeConfig source) = none ↔
      machine.step source = none := by
  rw [stepCodeIso_apply_encodeConfig]
  cases machine.step source <;> simp

/-- Every supplied partial iterate on an encoded configuration is the encoded
result of the machine's exact bind-preserving iterator. -/
theorem stepCodeIso_iterate_encodeConfig
    (machine : FiniteMachine Q Γ₁ Γ₂)
    (backward : BackwardUnique machine.step)
    (n : Nat) (source : Config Q Γ₁ Γ₂) :
    Lecerf.PEquiv.iterate (stepCodeIso machine backward).toPEquiv n
        (ConfigCode.encodeConfig source) =
      (exactIterate machine.step n source).map ConfigCode.encodeConfig := by
  induction n with
  | zero => rfl
  | succ n inductionHypothesis =>
      rw [Lecerf.PEquiv.iterate_succ_apply, exactIterate_succ,
        inductionHypothesis]
      cases exactIterate machine.step n source with
      | none => rfl
      | some middle =>
          exact stepCodeIso_apply_encodeConfig machine backward middle

/-- Strong iterate reflection: successful iteration from a canonical source
can never produce a malformed ambient word. -/
theorem stepCodeIso_iterate_eq_some_iff_exists
    (machine : FiniteMachine Q Γ₁ Γ₂)
    (backward : BackwardUnique machine.step)
    (n : Nat) (source : Config Q Γ₁ Γ₂) (word : Word Bool) :
    Lecerf.PEquiv.iterate (stepCodeIso machine backward).toPEquiv n
        (ConfigCode.encodeConfig source) = some word ↔
      ∃ target, ExactSteps machine.step n source target ∧
        word = ConfigCode.encodeConfig target := by
  rw [stepCodeIso_iterate_encodeConfig]
  constructor
  · rw [Option.map_eq_some_iff]
    rintro ⟨target, exact, rfl⟩
    exact ⟨target, exact, rfl⟩
  · rintro ⟨target, exact, rfl⟩
    exact Option.map_eq_some_iff.mpr ⟨target, exact, rfl⟩

/-- Exact supplied-step correspondence for canonical endpoints. -/
theorem stepCodeIso_iterate_eq_some_iff
    (machine : FiniteMachine Q Γ₁ Γ₂)
    (backward : BackwardUnique machine.step)
    (n : Nat) (source target : Config Q Γ₁ Γ₂) :
    Lecerf.PEquiv.iterate (stepCodeIso machine backward).toPEquiv n
        (ConfigCode.encodeConfig source) =
          some (ConfigCode.encodeConfig target) ↔
      ExactSteps machine.step n source target := by
  constructor
  · intro applied
    rcases (stepCodeIso_iterate_eq_some_iff_exists machine backward n source
      (ConfigCode.encodeConfig target)).mp applied with
      ⟨actual, exact, encodedEq⟩
    have actualEq : actual = target :=
      ConfigCode.encodeConfig_isIndexedCode.injective encodedEq.symm
    simpa only [actualEq] using exact
  · intro exact
    exact (stepCodeIso_iterate_eq_some_iff_exists machine backward n source
      (ConfigCode.encodeConfig target)).mpr ⟨target, exact, rfl⟩

/-- Definedness at a supplied exponent is exactly existence of a machine
configuration reached in that many steps. -/
theorem stepCodeIso_definedAt_iff
    (machine : FiniteMachine Q Γ₁ Γ₂)
    (backward : BackwardUnique machine.step)
    (n : Nat) (source : Config Q Γ₁ Γ₂) :
    Lecerf.PEquiv.DefinedAt (stepCodeIso machine backward).toPEquiv n
        (ConfigCode.encodeConfig source) ↔
      ∃ target, ExactSteps machine.step n source target := by
  rw [Lecerf.PEquiv.definedAt_iff_exists]
  simp only [stepCodeIso_iterate_eq_some_iff_exists]
  constructor
  · rintro ⟨_, target, exact, _⟩
    exact ⟨target, exact⟩
  · rintro ⟨target, exact⟩
    exact ⟨ConfigCode.encodeConfig target, target, exact, rfl⟩

/-- For a semantically reversible table, code iteration agrees exactly with
iteration of the machine's checked partial equivalence. -/
theorem stepCodeIso_iterate_iff_machinePEquiv
    (machine : FiniteMachine Q Γ₁ Γ₂)
    (reversible : machine.Reversible)
    (n : Nat) (source target : Config Q Γ₁ Γ₂) :
    Lecerf.PEquiv.iterate (stepCodeIso machine reversible.2).toPEquiv n
        (ConfigCode.encodeConfig source) =
          some (ConfigCode.encodeConfig target) ↔
      Lecerf.PEquiv.iterate (machine.toPEquiv reversible) n source =
        some target := by
  rw [stepCodeIso_iterate_eq_some_iff,
    pequiv_iterate_eq_some_iff_exactSteps]
  rfl

/-- Positive code orbit reachability is exactly strict machine reachability;
the witness exponent is necessarily `k + 1`. -/
theorem stepCodeIso_positiveIterate_iff_strictlyReachable
    (machine : FiniteMachine Q Γ₁ Γ₂)
    (backward : BackwardUnique machine.step)
    (source target : Config Q Γ₁ Γ₂) :
    Lecerf.PEquiv.PositiveIterate (stepCodeIso machine backward).toPEquiv
        (ConfigCode.encodeConfig source) (ConfigCode.encodeConfig target) ↔
      StrictlyReachable machine.step source target := by
  change (∃ k,
      Lecerf.PEquiv.iterate (stepCodeIso machine backward).toPEquiv (k + 1)
        (ConfigCode.encodeConfig source) =
          some (ConfigCode.encodeConfig target)) ↔ _
  simpa only [stepCodeIso_iterate_eq_some_iff] using
    (strictlyReachable_iff_exists_exactSteps_succ
      machine.step source target).symm

end Lecerf.Encoding.StepCode
