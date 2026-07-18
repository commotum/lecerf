import Lecerf.Encoding.ConfigCodeEffectivity
import Lecerf.Encoding.StepCode.Interpreter
import Lecerf.Machine.TwoTape.Effectivity
import Lecerf.Machine.TwoTape.Validity

/-!
# Effective finite descriptors for configuration-edge code maps

The runtime descriptor is exactly a conventional finite two-tape rule table.
It stores no `Edge` family, proof, `CodeIso`, `PEquiv`, or function.  Its
forward word interpreter decodes canonical Boolean configuration frames,
executes the table on every frame, and re-encodes the results.  A checked view
rejects tables that fail the existing primitive-recursive syntactic
reversibility certificate.

Only the forward interpreter is certified primitive recursive here.  The
semantic inverse belongs to the proof-side `PEquiv`; no primitive-recursive
inverse claim is made.
-/

namespace Lecerf.Encoding.StepCode

open Lecerf.Machine
open Lecerf.Machine.TwoTape
open Lecerf.Transition
open Lecerf.Word

universe u v w

/-- A raw step-code descriptor is only a finite conventional two-tape table. -/
abbrev Descriptor (Q : Type u) (Γ₁ : Type v) (Γ₂ : Type w)
    [Inhabited Γ₁] [Inhabited Γ₂] :=
  FiniteMachine Q Γ₁ Γ₂

namespace Descriptor

variable {Q : Type u} {Γ₁ : Type v} {Γ₂ : Type w}
  [Inhabited Γ₁] [Inhabited Γ₂]
  [Primcodable Q] [Primcodable Γ₁] [Primcodable Γ₂]
  [DecidableEq Q] [DecidableEq Γ₁] [DecidableEq Γ₂]

/-- Executable validity guard for a raw finite descriptor. -/
def Valid (descriptor : Descriptor Q Γ₁ Γ₂) : Prop :=
  descriptor.SyntacticallyReversible

instance (descriptor : Descriptor Q Γ₁ Γ₂) : Decidable descriptor.Valid := by
  unfold Valid
  infer_instance

/-- Execute the descriptor pointwise on every canonical configuration frame. -/
def applyWord (descriptor : Descriptor Q Γ₁ Γ₂) (word : Word Bool) :
    Option (Word Bool) :=
  StepCode.applyWord descriptor.step word

/-- Execute a valid descriptor and reject an invalid raw table before reading
its word action. -/
def checkedApply (descriptor : Descriptor Q Γ₁ Γ₂) (word : Word Bool) :
    Option (Word Bool) :=
  if descriptor.Valid then descriptor.applyWord word else none

@[simp]
theorem checkedApply_of_valid (descriptor : Descriptor Q Γ₁ Γ₂)
    (word : Word Bool) (valid : descriptor.Valid) :
    descriptor.checkedApply word = descriptor.applyWord word := by
  simp [checkedApply, valid]

@[simp]
theorem checkedApply_of_not_valid (descriptor : Descriptor Q Γ₁ Γ₂)
    (word : Word Bool) (invalid : ¬descriptor.Valid) :
    descriptor.checkedApply word = none := by
  simp [checkedApply, invalid]

/-! ## Uniform primitive recursiveness -/

private theorem traverseStep_uniform_primrec :
    Primrec fun data :
        Descriptor Q Γ₁ Γ₂ × List (Config Q Γ₁ Γ₂) =>
      StepCode.traverse data.1.step data.2 := by
  let Input := Descriptor Q Γ₁ Γ₂ × List (Config Q Γ₁ Γ₂)
  let RecData :=
    (Input ×
      (Config Q Γ₁ Γ₂ × List (Config Q Γ₁ Γ₂) ×
        Option (List (Config Q Γ₁ Γ₂))))
  have headStep : Primrec fun data : RecData =>
      data.1.1.step data.2.1 := by
    exact FiniteMachine.step_uniform_primrec.comp
      (Primrec.pair (Primrec.fst.comp Primrec.fst)
        (Primrec.fst.comp Primrec.snd))
  have recursiveResult : Primrec fun data : RecData × Config Q Γ₁ Γ₂ =>
      data.1.2.2.2 :=
    Primrec.snd.comp (Primrec.snd.comp (Primrec.snd.comp
      Primrec.fst))
  have prependTarget : Primrec₂ fun
      (data : RecData × Config Q Γ₁ Γ₂)
      (targets : List (Config Q Γ₁ Γ₂)) => data.2 :: targets := by
    exact (Primrec.list_cons.comp
      (Primrec.snd.comp Primrec.fst) Primrec.snd).to₂
  have mappedRecursive : Primrec fun data : RecData × Config Q Γ₁ Γ₂ =>
      data.1.2.2.2.map (data.2 :: ·) :=
    Primrec.option_map recursiveResult prependTarget
  have body : Primrec₂ fun (input : Input)
      (recData : Config Q Γ₁ Γ₂ × List (Config Q Γ₁ Γ₂) ×
        Option (List (Config Q Γ₁ Γ₂))) =>
      (input.1.step recData.1).bind fun target =>
        recData.2.2.map (target :: ·) :=
    Primrec.option_bind headStep mappedRecursive.to₂ |>.to₂
  exact (Primrec.list_rec Primrec.snd
    (Primrec.const (some ([] : List (Config Q Γ₁ Γ₂)))) body).of_eq fun data => by
      induction data.2 with
      | nil => rfl
      | cons config configs ih =>
          have recursiveCongruence :=
            congrArg
              (fun rest : Option (List (Config Q Γ₁ Γ₂)) =>
                (data.1.step config).bind fun target =>
                  rest.map (target :: ·))
              ih
          refine recursiveCongruence.trans ?_
          simp only [StepCode.traverse]
          cases data.1.step config <;>
            cases StepCode.traverse data.1.step configs <;> rfl

/-- Forward word interpretation is primitive recursive uniformly in the raw
finite descriptor and Boolean word. -/
theorem applyWord_uniform_primrec :
    Primrec fun data : Descriptor Q Γ₁ Γ₂ × Word Bool =>
      data.1.applyWord data.2 := by
  have decoded : Primrec fun data : Descriptor Q Γ₁ Γ₂ × Word Bool =>
      ConfigCode.decodeConfigs (C := Config Q Γ₁ Γ₂) data.2 :=
    ConfigCode.decodeConfigs_primrec.comp Primrec.snd
  have traversed : Primrec fun data :
      (Descriptor Q Γ₁ Γ₂ × Word Bool) × List (Config Q Γ₁ Γ₂) =>
      StepCode.traverse data.1.1.step data.2 :=
    traverseStep_uniform_primrec.comp
      (Primrec.pair (Primrec.fst.comp Primrec.fst) Primrec.snd)
  have decodedAndTraversed :
      Primrec fun data : Descriptor Q Γ₁ Γ₂ × Word Bool =>
        (ConfigCode.decodeConfigs (C := Config Q Γ₁ Γ₂) data.2).bind
          fun configs => StepCode.traverse data.1.step configs :=
    Primrec.option_bind decoded traversed.to₂
  have encoded : Primrec₂ fun (_data : Descriptor Q Γ₁ Γ₂ × Word Bool)
      (configs : List (Config Q Γ₁ Γ₂)) =>
      ConfigCode.encodeConfigs configs :=
    (ConfigCode.encodeConfigs_primrec.comp Primrec.snd).to₂
  exact (Primrec.option_map decodedAndTraversed encoded).of_eq fun data => by
    simp [Descriptor.applyWord, StepCode.applyWord]

/-- Forward word interpretation is computable uniformly in the raw finite
descriptor and word. -/
theorem applyWord_uniform_computable :
    Computable fun data : Descriptor Q Γ₁ Γ₂ × Word Bool =>
      data.1.applyWord data.2 :=
  applyWord_uniform_primrec.to_comp

/-- Descriptor validity is primitive recursive in the raw finite table. -/
theorem valid_primrec :
    PrimrecPred (Valid : Descriptor Q Γ₁ Γ₂ → Prop) := by
  exact FiniteMachine.syntacticallyReversible_primrec

/-- The guarded forward interpreter is primitive recursive uniformly in its
raw descriptor and word. -/
theorem checkedApply_uniform_primrec :
    Primrec fun data : Descriptor Q Γ₁ Γ₂ × Word Bool =>
      data.1.checkedApply data.2 := by
  have validInput : PrimrecPred fun data : Descriptor Q Γ₁ Γ₂ × Word Bool =>
      data.1.Valid :=
    valid_primrec.comp Primrec.fst
  exact (Primrec.ite validInput applyWord_uniform_primrec
    (Primrec.const none)).of_eq fun data => by
      simp only [checkedApply]

/-- The guarded forward interpreter is computable uniformly in its raw
descriptor and word. -/
theorem checkedApply_uniform_computable :
    Computable fun data : Descriptor Q Γ₁ Γ₂ × Word Bool =>
      data.1.checkedApply data.2 :=
  checkedApply_uniform_primrec.to_comp

/-! ## Proof-side semantic agreement -/

/-- A valid raw descriptor's executable forward interpreter agrees pointwise
with the ambient action of its semantic successful-edge code isomorphism. -/
theorem applyWord_eq_stepCodeIso_toPEquiv
    (descriptor : Descriptor Q Γ₁ Γ₂) (valid : descriptor.Valid)
    (word : Word Bool) :
    descriptor.applyWord word =
      (stepCodeIso descriptor valid.reversible.2).toPEquiv word := by
  have lifted := liftPEquiv_machine_eq_stepCodeIso_toPEquiv
    descriptor valid.reversible
  exact congrArg (fun theta : Word Bool ≃. Word Bool => theta word) lifted

/-- The validity-checked interpreter has the same semantic action whenever its
raw table passes the guard. -/
theorem checkedApply_eq_stepCodeIso_toPEquiv
    (descriptor : Descriptor Q Γ₁ Γ₂) (valid : descriptor.Valid)
    (word : Word Bool) :
    descriptor.checkedApply word =
      (stepCodeIso descriptor valid.reversible.2).toPEquiv word := by
  rw [descriptor.checkedApply_of_valid word valid]
  exact descriptor.applyWord_eq_stepCodeIso_toPEquiv valid word

end Descriptor

end Lecerf.Encoding.StepCode
