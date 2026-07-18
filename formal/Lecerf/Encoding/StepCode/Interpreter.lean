import Lecerf.Encoding.StepCode.Core

/-!
# Executable interpretation of configuration-edge code maps

The semantic `CodeIso.toPEquiv` decides membership in an arbitrary generated
submonoid by classical choice.  Configuration frames have a canonical
executable parser, so a partial equivalence on configurations can instead be
lifted pointwise over every completely decoded frame sequence.

This file proves that the constructive lift is itself a partial equivalence.
For a reversible two-tape machine it then identifies the lift on *all* Boolean
words with the ambient partial action of `stepCodeIso`, not merely on single
configuration generators.
-/

namespace Lecerf.Encoding.StepCode

open Lecerf.Machine
open Lecerf.Machine.TwoTape
open Lecerf.Transition
open Lecerf.Word

universe u v w x y

/-! ## Pointwise executable lifting -/

/-- Traverse a list through an option-valued map, failing at the first
undefined entry. -/
def traverse {C : Type x} {D : Type y} (next : C → Option D) :
    List C → Option (List D)
  | [] => some []
  | config :: configs => do
      let target ← next config
      let targets ← traverse next configs
      pure (target :: targets)

@[simp]
theorem traverse_nil {C : Type x} {D : Type y} (next : C → Option D) :
    traverse next [] = some [] :=
  rfl

@[simp]
theorem traverse_cons_eq_some_iff {C : Type x} {D : Type y}
    (next : C → Option D) (config : C) (configs : List C)
    (target : D) (targets : List D) :
    traverse next (config :: configs) = some (target :: targets) ↔
      next config = some target ∧ traverse next configs = some targets := by
  simp only [traverse, Option.bind_eq_bind]
  cases first : next config with
  | none => simp
  | some actualTarget =>
      cases rest : traverse next configs with
      | none => simp
      | some actualTargets => simp

@[simp]
theorem traverse_cons_ne_some_nil {C : Type x} {D : Type y}
    (next : C → Option D) (config : C) (configs : List C) :
    traverse next (config :: configs) ≠ some [] := by
  unfold traverse
  cases next config with
  | none => simp
  | some target =>
      cases traverse next configs <;> simp

@[simp]
theorem traverse_eq_some_nil_iff {C : Type x} {D : Type y}
    (next : C → Option D) (configs : List C) :
    traverse next configs = some [] ↔ configs = [] := by
  cases configs <;> simp

/-- Pointwise traversal through the inverse partial equivalence exactly
reverses successful forward traversal. -/
theorem traverse_symm_eq_some_iff {C : Type x} (theta : C ≃. C)
    (sources targets : List C) :
    traverse theta.symm targets = some sources ↔
      traverse theta sources = some targets := by
  induction sources generalizing targets with
  | nil =>
      cases targets <;> simp
  | cons source sources ih =>
      cases targets with
      | nil => simp
      | cons target targets =>
          simp only [traverse_cons_eq_some_iff]
          exact and_congr theta.eq_some_iff (ih targets)

variable {C : Type x} [Primcodable C]

/-- Decode a Boolean word as configuration frames, apply a partial map to
every frame, and re-encode the resulting frame sequence. -/
def applyWord (next : C → Option C) (word : Word Bool) : Option (Word Bool) :=
  (ConfigCode.decodeConfigs (C := C) word).bind fun configs : List C =>
    (traverse next configs).map (ConfigCode.encodeConfigs (C := C))

/-- Exact successful-result characterization of the executable word
interpreter. -/
theorem applyWord_eq_some_iff (next : C → Option C)
    (source target : Word Bool) :
    applyWord next source = some target ↔
      ∃ sources targets,
        source = ConfigCode.encodeConfigs sources ∧
          traverse next sources = some targets ∧
          target = ConfigCode.encodeConfigs targets := by
  constructor
  · intro applied
    simp only [applyWord] at applied
    rcases Option.bind_eq_some_iff.mp applied with
      ⟨sources, decoded, afterDecode⟩
    rcases Option.map_eq_some_iff.mp afterDecode with
      ⟨targets, traversed, encoded⟩
    exact ⟨sources, targets,
      (ConfigCode.decodeConfigs_eq_some_iff.mp decoded), traversed,
      encoded.symm⟩
  · rintro ⟨sources, targets, rfl, traversed, rfl⟩
    simp [applyWord, traversed]

/-- The constructive pointwise lift of a configuration partial equivalence to
Boolean words. -/
def liftPEquiv (theta : C ≃. C) : Word Bool ≃. Word Bool where
  toFun := applyWord theta
  invFun := applyWord theta.symm
  inv source target := by
    rw [applyWord_eq_some_iff, applyWord_eq_some_iff]
    constructor
    · rintro ⟨targets, sources, targetEq, reverse, sourceEq⟩
      exact ⟨sources, targets, sourceEq,
        (traverse_symm_eq_some_iff theta sources targets).mp reverse,
        targetEq⟩
    · rintro ⟨sources, targets, sourceEq, forward, targetEq⟩
      exact ⟨targets, sources, targetEq,
        (traverse_symm_eq_some_iff theta sources targets).mpr forward,
        sourceEq⟩

@[simp]
theorem liftPEquiv_apply (theta : C ≃. C) (word : Word Bool) :
    liftPEquiv theta word = applyWord theta word :=
  rfl

@[simp]
theorem liftPEquiv_symm_apply (theta : C ≃. C) (word : Word Bool) :
    (liftPEquiv theta).symm word = applyWord theta.symm word :=
  rfl

@[simp]
theorem liftPEquiv_symm (theta : C ≃. C) :
    (liftPEquiv theta).symm = liftPEquiv theta.symm :=
  rfl

/-! ## Agreement with the semantic machine-edge code isomorphism -/

variable {Q : Type u} {Γ₁ : Type v} {Γ₂ : Type w}
  [Inhabited Γ₁] [Inhabited Γ₂]
  [Primcodable Q] [Primcodable Γ₁] [Primcodable Γ₂]
  [DecidableEq Q] [DecidableEq Γ₁] [DecidableEq Γ₂]

private theorem lift_generator_coe {A : Type x} {I : Type y}
    (codewords : I → Word A) (indices : Word I) :
    ((FreeMonoid.lift (generator codewords) indices : generated codewords) :
        Word A) =
      FreeMonoid.lift codewords indices := by
  induction indices using FreeMonoid.inductionOn' with
  | one => simp
  | mul_of index indices ih =>
      simp only [map_mul, FreeMonoid.lift_eval_of]
      exact congrArg (fun word : Word A => codewords index * word) ih

/-- A code isomorphism acts generatorwise on every finite word of indices. -/
private theorem codeIso_toPEquiv_lift {A : Type x} {I : Type y}
    (iso : CodeIso A I) (indices : Word I) :
    iso.toPEquiv (FreeMonoid.lift iso.source indices) =
      some (FreeMonoid.lift iso.target indices) := by
  classical
  have sourceMem :
      FreeMonoid.lift iso.source indices ∈ generated iso.source := by
    change FreeMonoid.lift iso.source indices ∈
      Submonoid.closure (Set.range iso.source)
    rw [← FreeMonoid.mrange_lift]
    exact ⟨indices, rfl⟩
  rw [iso.toPEquiv_apply_of_mem _ sourceMem]
  congr 1
  let sourceLift : Word I →* generated iso.source :=
    FreeMonoid.lift (generator iso.source)
  let targetLift : Word I →* generated iso.target :=
    FreeMonoid.lift (generator iso.target)
  have mappedLift : iso.toMulEquiv.toMonoidHom.comp sourceLift = targetLift := by
    apply FreeMonoid.hom_eq
    intro index
    exact iso.map_generator index
  have sourceEq :
      (⟨FreeMonoid.lift iso.source indices, sourceMem⟩ :
          generated iso.source) = sourceLift indices := by
    apply Subtype.ext
    exact (lift_generator_coe iso.source indices).symm
  rw [sourceEq]
  have mapped := congrArg (fun hom : Word I →* generated iso.target => hom indices)
    mappedLift
  change iso.toMulEquiv (sourceLift indices) = targetLift indices at mapped
  rw [mapped]
  exact lift_generator_coe iso.target indices

private theorem encodeEdgeSources {machine : FiniteMachine Q Γ₁ Γ₂}
    (edges : List (Edge machine)) :
    ConfigCode.encodeConfigs (edges.map Edge.source) =
      FreeMonoid.lift (sourceWord (machine := machine))
        (FreeMonoid.ofList edges) := by
  rw [ConfigCode.encodeConfigs_eq_lift]
  apply FreeMonoid.toList.injective
  rw [Lecerf.Word.toList_lift_ofList, Lecerf.Word.toList_lift_ofList]
  congr 1
  rw [List.map_map]
  rfl

private theorem encodeEdgeTargets {machine : FiniteMachine Q Γ₁ Γ₂}
    (edges : List (Edge machine)) :
    ConfigCode.encodeConfigs (edges.map Edge.target) =
      FreeMonoid.lift (targetWord (machine := machine))
        (FreeMonoid.ofList edges) := by
  rw [ConfigCode.encodeConfigs_eq_lift]
  apply FreeMonoid.toList.injective
  rw [Lecerf.Word.toList_lift_ofList, Lecerf.Word.toList_lift_ofList]
  congr 1
  rw [List.map_map]
  rfl

omit [Primcodable Q] [Primcodable Γ₁] [Primcodable Γ₂] in
private theorem traverse_machineStep_edges
    {machine : FiniteMachine Q Γ₁ Γ₂} (edges : List (Edge machine)) :
    traverse machine.step (edges.map Edge.source) =
      some (edges.map Edge.target) := by
  induction edges with
  | nil => rfl
  | cons edge edges ih =>
      exact traverse_cons_eq_some_iff _ _ _ _ _ |>.2 ⟨edge.step_eq, ih⟩

omit [Primcodable Q] [Primcodable Γ₁] [Primcodable Γ₂] in
private theorem traverse_machineStep_eq_some_iff_exists_edges
    (machine : FiniteMachine Q Γ₁ Γ₂)
    (sources targets : List (Config Q Γ₁ Γ₂)) :
    traverse machine.step sources = some targets ↔
      ∃ edges : List (Edge machine),
        sources = edges.map Edge.source ∧ targets = edges.map Edge.target := by
  constructor
  · intro traversed
    induction sources generalizing targets with
    | nil =>
        have targetsEq : targets = [] := Option.some.inj (by simpa using traversed.symm)
        subst targets
        exact ⟨[], rfl, rfl⟩
    | cons source sources ih =>
        cases targets with
        | nil => simp at traversed
        | cons target targets =>
            rcases (traverse_cons_eq_some_iff _ _ _ _ _).mp traversed with
              ⟨step, rest⟩
            rcases ih targets rest with ⟨edges, sourcesEq, targetsEq⟩
            exact ⟨⟨source, target, step⟩ :: edges,
              by simp [sourcesEq], by simp [targetsEq]⟩
  · rintro ⟨edges, rfl, rfl⟩
    exact traverse_machineStep_edges edges

private theorem semantic_apply_edgeWords
    (machine : FiniteMachine Q Γ₁ Γ₂)
    (backward : BackwardUnique machine.step) (edges : List (Edge machine)) :
    (stepCodeIso machine backward).toPEquiv
        (ConfigCode.encodeConfigs (edges.map Edge.source)) =
      some (ConfigCode.encodeConfigs (edges.map Edge.target)) := by
  rw [encodeEdgeSources, encodeEdgeTargets]
  exact codeIso_toPEquiv_lift (stepCodeIso machine backward)
    (FreeMonoid.ofList edges)

private theorem applyWord_machine_eq_some_iff_edges
    (machine : FiniteMachine Q Γ₁ Γ₂)
    (source target : Word Bool) :
    applyWord machine.step source = some target ↔
      ∃ edges : List (Edge machine),
        source = ConfigCode.encodeConfigs (edges.map Edge.source) ∧
          target = ConfigCode.encodeConfigs (edges.map Edge.target) := by
  rw [applyWord_eq_some_iff]
  constructor
  · rintro ⟨sources, targets, sourceEq, traversed, targetEq⟩
    rcases (traverse_machineStep_eq_some_iff_exists_edges machine
      sources targets).mp traversed with ⟨edges, rfl, rfl⟩
    exact ⟨edges, sourceEq, targetEq⟩
  · rintro ⟨edges, sourceEq, targetEq⟩
    exact ⟨edges.map Edge.source, edges.map Edge.target,
      sourceEq, traverse_machineStep_edges edges, targetEq⟩

private theorem semantic_machine_eq_some_iff_edges
    (machine : FiniteMachine Q Γ₁ Γ₂)
    (backward : BackwardUnique machine.step) (source target : Word Bool) :
    (stepCodeIso machine backward).toPEquiv source = some target ↔
      ∃ edges : List (Edge machine),
        source = ConfigCode.encodeConfigs (edges.map Edge.source) ∧
          target = ConfigCode.encodeConfigs (edges.map Edge.target) := by
  constructor
  · intro applied
    have sourceMem :
        source ∈ generated (stepCodeIso machine backward).source :=
      ((stepCodeIso machine backward).toPEquiv_isSome_iff source).mp (by
        rw [applied]
        rfl)
    change source ∈
      Submonoid.closure (Set.range (sourceWord (machine := machine))) at sourceMem
    rw [← FreeMonoid.mrange_lift] at sourceMem
    rcases sourceMem with ⟨indices, sourceLiftEq⟩
    let edges := indices.toList
    have indicesEq : FreeMonoid.ofList edges = indices :=
      FreeMonoid.ofList_toList indices
    have sourceEq :
        source = ConfigCode.encodeConfigs (edges.map Edge.source) := by
      rw [encodeEdgeSources, indicesEq]
      exact sourceLiftEq.symm
    have generatedAction := semantic_apply_edgeWords machine backward edges
    rw [← sourceEq, applied] at generatedAction
    exact ⟨edges, sourceEq, Option.some.inj generatedAction⟩
  · rintro ⟨edges, rfl, rfl⟩
    exact semantic_apply_edgeWords machine backward edges

/-- For a semantically reversible finite two-tape machine, the constructive
frame interpreter agrees on every Boolean word with the ambient partial action
of the successful-edge code isomorphism. -/
theorem liftPEquiv_machine_eq_stepCodeIso_toPEquiv
    (machine : FiniteMachine Q Γ₁ Γ₂) (reversible : machine.Reversible) :
    liftPEquiv (machine.toPEquiv reversible) =
      (stepCodeIso machine reversible.2).toPEquiv := by
  apply _root_.PEquiv.ext
  intro source
  change applyWord machine.step source =
    (stepCodeIso machine reversible.2).toPEquiv source
  cases executable : applyWord machine.step source with
  | none =>
      cases semantic : (stepCodeIso machine reversible.2).toPEquiv source with
      | none => rfl
      | some target =>
          have semanticEdges :=
            (semantic_machine_eq_some_iff_edges machine reversible.2 source target).mp
              semantic
          have executableSome :=
            (applyWord_machine_eq_some_iff_edges machine source target).mpr semanticEdges
          rw [executable] at executableSome
          contradiction
  | some target =>
      have executableEdges :=
        (applyWord_machine_eq_some_iff_edges machine source target).mp executable
      exact ((semantic_machine_eq_some_iff_edges machine reversible.2 source target).mpr
        executableEdges).symm

end Lecerf.Encoding.StepCode
