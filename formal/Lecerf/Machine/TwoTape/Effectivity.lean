import Lecerf.Machine.Effectivity
import Lecerf.Machine.TwoTape.Core

/-!
# Effective execution for finite two-tape machines

The canonical two-tape configuration, individual rule application, and
first-match finite-table execution are primitive recursive uniformly in their
finite descriptions.  This module is intentionally independent of the later
history compiler: it supplies the executable substrate used by its reductions.
-/

namespace Lecerf.Machine.TwoTape

universe u v w

namespace Config

variable {Q : Type u} {Γ₁ : Type v} {Γ₂ : Type w}
  [Inhabited Γ₁] [Inhabited Γ₂]
  [Primcodable Q] [Primcodable Γ₁] [Primcodable Γ₂]
  [DecidableEq Γ₁] [DecidableEq Γ₂]

/-- The configuration-to-product representation is primitive recursive. -/
theorem equivRep_primrec :
    Primrec (equivRep : Config Q Γ₁ Γ₂ → Q × Tape Γ₁ × Tape Γ₂) :=
  Primrec.of_equiv

/-- Reconstruction from the configuration product is primitive recursive. -/
theorem equivRep_symm_primrec :
    Primrec (equivRep.symm : Q × Tape Γ₁ × Tape Γ₂ → Config Q Γ₁ Γ₂) :=
  Primrec.of_equiv_symm

end Config

namespace Rule

variable {Q : Type u} {Γ₁ : Type v} {Γ₂ : Type w}
  [Inhabited Γ₁] [Inhabited Γ₂]
  [Primcodable Q] [Primcodable Γ₁] [Primcodable Γ₂]
  [DecidableEq Q] [DecidableEq Γ₁] [DecidableEq Γ₂]

omit [Inhabited Γ₁] [Inhabited Γ₂] [DecidableEq Q]
    [DecidableEq Γ₁] [DecidableEq Γ₂] in
/-- The rule-to-product representation is primitive recursive. -/
theorem equivRep_primrec :
    Primrec (equivRep : Rule Q Γ₁ Γ₂ →
      Q × Γ₁ × Γ₂ × Q × Γ₁ × Tape.Move × Γ₂ × Tape.Move) :=
  Primrec.of_equiv

/-- Applying one simultaneous two-tape rule is primitive recursive jointly in
the rule and configuration. -/
theorem apply_uniform_primrec :
    Primrec fun data : Rule Q Γ₁ Γ₂ × Config Q Γ₁ Γ₂ =>
      data.1.apply data.2 := by
  have ruleRep : Primrec fun data : Rule Q Γ₁ Γ₂ × Config Q Γ₁ Γ₂ =>
      equivRep data.1 :=
    equivRep_primrec.comp Primrec.fst
  have configRep : Primrec fun data : Rule Q Γ₁ Γ₂ × Config Q Γ₁ Γ₂ =>
      Config.equivRep data.2 :=
    Config.equivRep_primrec.comp Primrec.snd
  have source : Primrec fun data : Rule Q Γ₁ Γ₂ × Config Q Γ₁ Γ₂ =>
      (equivRep data.1).1 :=
    Primrec.fst.comp ruleRep
  have read₁ : Primrec fun data : Rule Q Γ₁ Γ₂ × Config Q Γ₁ Γ₂ =>
      (equivRep data.1).2.1 :=
    Primrec.fst.comp (Primrec.snd.comp ruleRep)
  have read₂ : Primrec fun data : Rule Q Γ₁ Γ₂ × Config Q Γ₁ Γ₂ =>
      (equivRep data.1).2.2.1 :=
    Primrec.fst.comp (Primrec.snd.comp (Primrec.snd.comp ruleRep))
  have target : Primrec fun data : Rule Q Γ₁ Γ₂ × Config Q Γ₁ Γ₂ =>
      (equivRep data.1).2.2.2.1 :=
    Primrec.fst.comp
      (Primrec.snd.comp (Primrec.snd.comp (Primrec.snd.comp ruleRep)))
  have write₁ : Primrec fun data : Rule Q Γ₁ Γ₂ × Config Q Γ₁ Γ₂ =>
      (equivRep data.1).2.2.2.2.1 :=
    Primrec.fst.comp (Primrec.snd.comp
      (Primrec.snd.comp (Primrec.snd.comp (Primrec.snd.comp ruleRep))))
  have move₁ : Primrec fun data : Rule Q Γ₁ Γ₂ × Config Q Γ₁ Γ₂ =>
      (equivRep data.1).2.2.2.2.2.1 :=
    Primrec.fst.comp (Primrec.snd.comp (Primrec.snd.comp
      (Primrec.snd.comp (Primrec.snd.comp (Primrec.snd.comp ruleRep)))))
  have write₂ : Primrec fun data : Rule Q Γ₁ Γ₂ × Config Q Γ₁ Γ₂ =>
      (equivRep data.1).2.2.2.2.2.2.1 :=
    Primrec.fst.comp (Primrec.snd.comp (Primrec.snd.comp (Primrec.snd.comp
      (Primrec.snd.comp (Primrec.snd.comp (Primrec.snd.comp ruleRep))))))
  have move₂ : Primrec fun data : Rule Q Γ₁ Γ₂ × Config Q Γ₁ Γ₂ =>
      (equivRep data.1).2.2.2.2.2.2.2 :=
    Primrec.snd.comp (Primrec.snd.comp (Primrec.snd.comp (Primrec.snd.comp
      (Primrec.snd.comp (Primrec.snd.comp (Primrec.snd.comp ruleRep))))))
  have state : Primrec fun data : Rule Q Γ₁ Γ₂ × Config Q Γ₁ Γ₂ =>
      (Config.equivRep data.2).1 :=
    Primrec.fst.comp configRep
  have tape₁ : Primrec fun data : Rule Q Γ₁ Γ₂ × Config Q Γ₁ Γ₂ =>
      (Config.equivRep data.2).2.1 :=
    Primrec.fst.comp (Primrec.snd.comp configRep)
  have tape₂ : Primrec fun data : Rule Q Γ₁ Γ₂ × Config Q Γ₁ Γ₂ =>
      (Config.equivRep data.2).2.2 :=
    Primrec.snd.comp (Primrec.snd.comp configRep)
  have head₁ : Primrec fun data : Rule Q Γ₁ Γ₂ × Config Q Γ₁ Γ₂ =>
      data.2.tape₁.head :=
    Tape.head_primrec.comp tape₁
  have head₂ : Primrec fun data : Rule Q Γ₁ Γ₂ × Config Q Γ₁ Γ₂ =>
      data.2.tape₂.head :=
    Tape.head_primrec.comp tape₂
  have enabled : PrimrecPred fun data : Rule Q Γ₁ Γ₂ × Config Q Γ₁ Γ₂ =>
      data.2.state = data.1.source ∧ data.2.tape₁.head = data.1.read₁ ∧
        data.2.tape₂.head = data.1.read₂ :=
    (Primrec.eq.comp state source).and
      ((Primrec.eq.comp head₁ read₁).and (Primrec.eq.comp head₂ read₂))
  have acted₁ : Primrec fun data : Rule Q Γ₁ Γ₂ × Config Q Γ₁ Γ₂ =>
      data.2.tape₁.act data.1.write₁ data.1.move₁ :=
    (Tape.act_uniform_primrec.comp
      (Primrec.pair (Primrec.pair write₁ move₁) tape₁)).of_eq fun _ => rfl
  have acted₂ : Primrec fun data : Rule Q Γ₁ Γ₂ × Config Q Γ₁ Γ₂ =>
      data.2.tape₂.act data.1.write₂ data.1.move₂ :=
    (Tape.act_uniform_primrec.comp
      (Primrec.pair (Primrec.pair write₂ move₂) tape₂)).of_eq fun _ => rfl
  have result : Primrec fun data : Rule Q Γ₁ Γ₂ × Config Q Γ₁ Γ₂ =>
      some (⟨data.1.target,
        data.2.tape₁.act data.1.write₁ data.1.move₁,
        data.2.tape₂.act data.1.write₂ data.1.move₂⟩ : Config Q Γ₁ Γ₂) :=
    Primrec.option_some.comp (Config.equivRep_symm_primrec.comp
      (Primrec.pair target (Primrec.pair acted₁ acted₂)))
  exact (Primrec.ite enabled result (Primrec.const none)).of_eq fun data => by
    simp only [apply]

end Rule

namespace FiniteMachine

variable {Q : Type u} {Γ₁ : Type v} {Γ₂ : Type w}
  [Inhabited Γ₁] [Inhabited Γ₂]
  [Primcodable Q] [Primcodable Γ₁] [Primcodable Γ₂]
  [DecidableEq Q] [DecidableEq Γ₁] [DecidableEq Γ₂]

omit [Inhabited Γ₁] [Inhabited Γ₂] [DecidableEq Q]
    [DecidableEq Γ₁] [DecidableEq Γ₂] in
/-- The finite-table list representation is primitive recursive. -/
theorem equivRep_primrec :
    Primrec (equivRep : FiniteMachine Q Γ₁ Γ₂ → List (Rule Q Γ₁ Γ₂)) :=
  Primrec.of_equiv

/-- First-success execution is primitive recursive jointly in a two-tape
rule list and configuration. -/
theorem applyRules_uniform_primrec :
    Primrec fun data : List (Rule Q Γ₁ Γ₂) × Config Q Γ₁ Γ₂ =>
      applyRules data.1 data.2 := by
  have ruleStep : Primrec fun pair :
      (List (Rule Q Γ₁ Γ₂) × Config Q Γ₁ Γ₂) ×
        (Rule Q Γ₁ Γ₂ × List (Rule Q Γ₁ Γ₂) × Option (Config Q Γ₁ Γ₂)) =>
      pair.2.1.apply pair.1.2 :=
    Rule.apply_uniform_primrec.comp
      (Primrec.pair (Primrec.fst.comp Primrec.snd)
        (Primrec.snd.comp Primrec.fst))
  have inherited : Primrec fun pair :
      (List (Rule Q Γ₁ Γ₂) × Config Q Γ₁ Γ₂) ×
        (Rule Q Γ₁ Γ₂ × List (Rule Q Γ₁ Γ₂) × Option (Config Q Γ₁ Γ₂)) =>
      pair.2.2.2 :=
    Primrec.snd.comp (Primrec.snd.comp Primrec.snd)
  have body : Primrec₂ fun (data : List (Rule Q Γ₁ Γ₂) × Config Q Γ₁ Γ₂)
      (recData : Rule Q Γ₁ Γ₂ × List (Rule Q Γ₁ Γ₂) ×
        Option (Config Q Γ₁ Γ₂)) =>
      recData.1.apply data.2 <|> recData.2.2 :=
    (Primrec.option_orElse.comp ruleStep inherited).to₂
  exact (Primrec.list_rec Primrec.fst (Primrec.const none) body).of_eq
    fun data => by
      induction data.1 with
      | nil => rfl
      | cons rule rest ih =>
          simp only [applyRules]
          cases firstStep : rule.apply data.2 with
          | none => simpa using ih
          | some next => simp

/-- Finite two-tape execution is primitive recursive uniformly in the table
and input configuration. -/
theorem step_uniform_primrec :
    Primrec fun data : FiniteMachine Q Γ₁ Γ₂ × Config Q Γ₁ Γ₂ =>
      data.1.step data.2 := by
  exact (applyRules_uniform_primrec.comp
    (Primrec.pair (equivRep_primrec.comp Primrec.fst) Primrec.snd)).of_eq
      fun _ => rfl

end FiniteMachine

end Lecerf.Machine.TwoTape
