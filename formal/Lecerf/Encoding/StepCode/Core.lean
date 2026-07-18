import Lecerf.Encoding.ConfigCode
import Lecerf.Machine.TwoTape.Reversible
import Lecerf.Word.CodeMorphism

/-!
# Configuration-edge code maps

A successful edge of a conventional two-tape machine supplies one relation
between two self-delimiting Boolean configuration words.  The source edge
family is always an indexed code because an option-valued transition has a
unique successful output.  Mapping those edges into the full configuration
code therefore gives Lecerf's weaker `PaperCodeEpi` for every machine.

The edge-target family is an indexed code exactly when successful outputs have
unique predecessors.  Under that whole-step hypothesis the same relations
give a genuine `CodeIso`.  This is a uniformly finite-machine-described,
generally infinite relation schema; it is not claimed to be the paper's finite
local `alpha`/`omega`/`beta` table.
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

/-- A displayed successful edge of the deterministic two-tape transition. -/
structure Edge (machine : FiniteMachine Q Γ₁ Γ₂) where
  source : Config Q Γ₁ Γ₂
  target : Config Q Γ₁ Γ₂
  step_eq : machine.step source = some target

namespace Edge

variable {machine : FiniteMachine Q Γ₁ Γ₂}

omit [Primcodable Q] [Primcodable Γ₁] [Primcodable Γ₂] in
/-- A successful source determines its displayed edge. -/
theorem source_injective :
    Function.Injective (source : Edge machine → Config Q Γ₁ Γ₂) := by
  rintro ⟨firstSource, firstTarget, firstStep⟩
    ⟨secondSource, secondTarget, secondStep⟩ sourceEq
  change firstSource = secondSource at sourceEq
  subst secondSource
  have targetEq : firstTarget = secondTarget :=
    Option.some.inj (firstStep.symm.trans secondStep)
  subst secondTarget
  rfl

omit [Primcodable Q] [Primcodable Γ₁] [Primcodable Γ₂] in
/-- Successful-predecessor uniqueness makes the target projection injective. -/
theorem target_injective (backward : BackwardUnique machine.step) :
    Function.Injective (target : Edge machine → Config Q Γ₁ Γ₂) := by
  rintro ⟨firstSource, firstTarget, firstStep⟩
    ⟨secondSource, secondTarget, secondStep⟩ targetEq
  change firstTarget = secondTarget at targetEq
  subst secondTarget
  have sourceEq : firstSource = secondSource := backward firstStep secondStep
  subst secondSource
  rfl

end Edge

/-- Source relation word of a successful machine edge. -/
def sourceWord {machine : FiniteMachine Q Γ₁ Γ₂} (edge : Edge machine) :
    Word Bool :=
  ConfigCode.encodeConfig edge.source

/-- Target relation word of a successful machine edge. -/
def targetWord {machine : FiniteMachine Q Γ₁ Γ₂} (edge : Edge machine) :
    Word Bool :=
  ConfigCode.encodeConfig edge.target

/-- Successful source words always form an indexed code. -/
theorem sourceWord_isIndexedCode (machine : FiniteMachine Q Γ₁ Γ₂) :
    IsIndexedCode (sourceWord (machine := machine)) := by
  change IsIndexedCode
    (fun edge : Edge machine => ConfigCode.encodeConfig edge.source)
  exact (ConfigCode.encodeConfig_isIndexedCode
    (C := Config Q Γ₁ Γ₂)).comp (Edge.source_injective (machine := machine))

/-- Under backward uniqueness, successful target words form an indexed code. -/
theorem targetWord_isIndexedCode (machine : FiniteMachine Q Γ₁ Γ₂)
    (backward : BackwardUnique machine.step) :
    IsIndexedCode (targetWord (machine := machine)) := by
  change IsIndexedCode
    (fun edge : Edge machine => ConfigCode.encodeConfig edge.target)
  exact (ConfigCode.encodeConfig_isIndexedCode
    (C := Config Q Γ₁ Γ₂)).comp (Edge.target_injective backward)

/-- Target-edge codehood is exactly whole-step successful-predecessor
uniqueness.  Individual rule invertibility is not enough. -/
theorem targetWord_isIndexedCode_iff_backwardUnique
    (machine : FiniteMachine Q Γ₁ Γ₂) :
    IsIndexedCode (targetWord (machine := machine)) ↔
      BackwardUnique machine.step := by
  constructor
  · intro targetCode first second target firstStep secondStep
    let firstEdge : Edge machine := ⟨first, target, firstStep⟩
    let secondEdge : Edge machine := ⟨second, target, secondStep⟩
    have edgeEq : firstEdge = secondEdge := targetCode.injective (by
      simp only [targetWord, firstEdge, secondEdge])
    exact congrArg Edge.source edgeEq
  · exact targetWord_isIndexedCode machine

/-- Every deterministic option-valued machine step gives the paper's weaker
code epimorphism: edge sources map into the full configuration code, and
distinct edges may select the same target configuration. -/
noncomputable def stepCodeEpi (machine : FiniteMachine Q Γ₁ Γ₂) :
    PaperCodeEpi Bool (Edge machine) (Config Q Γ₁ Γ₂) :=
  PaperCodeEpi.ofCodes
    (sourceWord (machine := machine))
    (ConfigCode.encodeConfig : Config Q Γ₁ Γ₂ → Word Bool)
    Edge.target
    (sourceWord_isIndexedCode machine)
    (ConfigCode.encodeConfig_isIndexedCode (C := Config Q Γ₁ Γ₂))

/-- A backward-unique machine step induces a genuine isomorphism between its
successful source and target configuration codes. -/
noncomputable def stepCodeIso (machine : FiniteMachine Q Γ₁ Γ₂)
    (backward : BackwardUnique machine.step) :
    CodeIso Bool (Edge machine) :=
  CodeIso.ofCodes
    (sourceWord (machine := machine))
    (targetWord (machine := machine))
    (sourceWord_isIndexedCode machine)
    (targetWord_isIndexedCode machine backward)

@[simp]
theorem stepCodeIso_source (machine : FiniteMachine Q Γ₁ Γ₂)
    (backward : BackwardUnique machine.step) :
    (stepCodeIso machine backward).source =
      sourceWord (machine := machine) :=
  rfl

@[simp]
theorem stepCodeIso_target (machine : FiniteMachine Q Γ₁ Γ₂)
    (backward : BackwardUnique machine.step) :
    (stepCodeIso machine backward).target =
      targetWord (machine := machine) :=
  rfl

/-- The semantic code isomorphism maps every displayed successful edge. -/
@[simp]
theorem stepCodeIso_edge (machine : FiniteMachine Q Γ₁ Γ₂)
    (backward : BackwardUnique machine.step) (edge : Edge machine) :
    (stepCodeIso machine backward).toPEquiv (sourceWord edge) =
      some (targetWord edge) := by
  exact (stepCodeIso machine backward).toPEquiv_generator edge

end Lecerf.Encoding.StepCode
