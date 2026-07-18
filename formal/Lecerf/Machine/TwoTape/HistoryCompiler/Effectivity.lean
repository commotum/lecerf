import Lecerf.Machine.Effectivity
import Lecerf.Machine.TwoTape.HistoryCompiler.Core
import Lecerf.Machine.TwoTape.Validity

/-!
# Effectivity of history-compiler data

The tagged history alphabet, compiler controls, and the varying configuration
maps used by reductions are primitive recursive in their inputs.  This module
does **not** claim that the generic rule-table generators are computable:
`boundaryRules`, `scanRules`, `inspectRules`, and `bottomRules` turn arbitrary
`Fintype` enumerations into ordered lists using `Finset.toList`, whose order is
chosen noncomputably.  Later reductions use a fixed closed compiled table and
the primitive-recursive checkpoint maps proved here.
-/

namespace Lecerf.Machine.TwoTape.HistoryCompiler

universe u v w

namespace Mark

variable {Q : Type u} {Γ : Type v}
  [Primcodable Q] [Primcodable Γ]

/-- Encoding a history symbol by its explicit nested-option representation is
primitive recursive. -/
theorem equivRep_primrec :
    Primrec (equivRep : Mark Q Γ →
      Option (Option (Lecerf.Machine.Rule Q Γ))) :=
  Primrec.of_equiv

/-- Decoding the explicit nested-option representation of a history symbol is
primitive recursive. -/
theorem equivRep_symm_primrec :
    Primrec (equivRep.symm :
      Option (Option (Lecerf.Machine.Rule Q Γ)) → Mark Q Γ) :=
  Primrec.of_equiv_symm

/-- The blank history symbol is a primitive-recursive constant. -/
theorem blank_primrec {α : Type w} [Primcodable α] :
    Primrec (fun _ : α => (Mark.blank : Mark Q Γ)) :=
  Primrec.const _

/-- The bottom history symbol is a primitive-recursive constant. -/
theorem bottom_primrec {α : Type w} [Primcodable α] :
    Primrec (fun _ : α => (Mark.bottom : Mark Q Γ)) :=
  Primrec.const _

/-- Recording a source rule as a history token is primitive recursive. -/
theorem token_primrec :
    Primrec (Mark.token : Lecerf.Machine.Rule Q Γ → Mark Q Γ) := by
  have nestedSome : Primrec fun rule : Lecerf.Machine.Rule Q Γ =>
      some (some rule) :=
    Primrec.option_some.comp Primrec.option_some
  exact (equivRep_symm_primrec.comp nestedSome).of_eq fun _ => rfl

end Mark

namespace Control

variable {Q : Type u} {Γ : Type v}
  [Primcodable Q] [Primcodable Γ]

/-- Encoding a compiler control by its explicit tagged sum is primitive
recursive. -/
theorem equivRep_primrec :
    Primrec (equivRep : Control Q Γ →
      Q ⊕ (Q ⊕ (Q ⊕ Lecerf.Machine.Rule Q Γ))) :=
  Primrec.of_equiv

/-- Decoding the explicit tagged-sum representation is primitive recursive. -/
theorem equivRep_symm_primrec :
    Primrec (equivRep.symm :
      Q ⊕ (Q ⊕ (Q ⊕ Lecerf.Machine.Rule Q Γ)) → Control Q Γ) :=
  Primrec.of_equiv_symm

/-- Entering forward control is primitive recursive in the source state. -/
theorem forward_primrec : Primrec (Control.forward : Q → Control Q Γ) := by
  have encoded : Primrec fun state : Q =>
      (Sum.inl state : Q ⊕ (Q ⊕ (Q ⊕ Lecerf.Machine.Rule Q Γ))) :=
    Primrec.sumInl
  exact (equivRep_symm_primrec.comp encoded).of_eq fun _ => rfl

/-- Entering reverse control is primitive recursive in the source state. -/
theorem reverse_primrec : Primrec (Control.reverse : Q → Control Q Γ) := by
  have inner : Primrec fun state : Q =>
      (Sum.inl state : Q ⊕ (Q ⊕ Lecerf.Machine.Rule Q Γ)) :=
    Primrec.sumInl
  have encoded : Primrec fun state : Q =>
      (Sum.inr (Sum.inl state) :
        Q ⊕ (Q ⊕ (Q ⊕ Lecerf.Machine.Rule Q Γ))) :=
    Primrec.sumInr.comp inner
  exact (equivRep_symm_primrec.comp encoded).of_eq fun _ => rfl

/-- Entering token-inspection control is primitive recursive in the source
state. -/
theorem inspect_primrec : Primrec (Control.inspect : Q → Control Q Γ) := by
  have inner : Primrec fun state : Q =>
      (Sum.inl state : Q ⊕ Lecerf.Machine.Rule Q Γ) :=
    Primrec.sumInl
  have middle : Primrec fun state : Q =>
      (Sum.inr (Sum.inl state) :
        Q ⊕ (Q ⊕ Lecerf.Machine.Rule Q Γ)) :=
    Primrec.sumInr.comp inner
  have encoded : Primrec fun state : Q =>
      (Sum.inr (Sum.inr (Sum.inl state)) :
        Q ⊕ (Q ⊕ (Q ⊕ Lecerf.Machine.Rule Q Γ))) :=
    Primrec.sumInr.comp middle
  exact (equivRep_symm_primrec.comp encoded).of_eq fun _ => rfl

/-- Entering symbol-restoration control is primitive recursive in the
recorded source rule. -/
theorem restore_primrec :
    Primrec (Control.restore :
      Lecerf.Machine.Rule Q Γ → Control Q Γ) := by
  have inner : Primrec fun rule : Lecerf.Machine.Rule Q Γ =>
      (Sum.inr rule : Q ⊕ Lecerf.Machine.Rule Q Γ) :=
    Primrec.sumInr
  have middle : Primrec fun rule : Lecerf.Machine.Rule Q Γ =>
      (Sum.inr (Sum.inr rule) :
        Q ⊕ (Q ⊕ Lecerf.Machine.Rule Q Γ)) :=
    Primrec.sumInr.comp inner
  have encoded : Primrec fun rule : Lecerf.Machine.Rule Q Γ =>
      (Sum.inr (Sum.inr (Sum.inr rule)) :
        Q ⊕ (Q ⊕ (Q ⊕ Lecerf.Machine.Rule Q Γ))) :=
    Primrec.sumInr.comp middle
  exact (equivRep_symm_primrec.comp encoded).of_eq fun _ => rfl

end Control

section ConfigurationMaps

variable {Q : Type u} {Γ : Type v}
  [Inhabited Γ] [Primcodable Q] [Primcodable Γ]
  [DecidableEq Q] [DecidableEq Γ]

omit [Inhabited Γ] in
/-- The canonical blank history tape with a bottom marker immediately to its
left is a primitive-recursive constant. -/
theorem initialHistory_primrec :
    Primrec (fun _ : Unit => (initialHistory : Tape (Mark Q Γ))) :=
  Primrec.const _

/-- The fresh forward checkpoint varies primitive recursively with its source
configuration. -/
theorem checkpoint_primrec :
    Primrec (checkpoint : Lecerf.Machine.Config Q Γ →
      TwoTape.Config (Control Q Γ) Γ (Mark Q Γ)) := by
  have sourceRep : Primrec fun config : Lecerf.Machine.Config Q Γ =>
      Lecerf.Machine.Config.equivRep config :=
    Lecerf.Machine.Config.equivRep_primrec
  have sourceState : Primrec fun config : Lecerf.Machine.Config Q Γ =>
      config.state :=
    Primrec.fst.comp sourceRep
  have sourceTape : Primrec fun config : Lecerf.Machine.Config Q Γ =>
      config.tape :=
    Primrec.snd.comp sourceRep
  have control : Primrec fun config : Lecerf.Machine.Config Q Γ =>
      Control.forward config.state :=
    Control.forward_primrec (Γ := Γ) |>.comp sourceState
  have history : Primrec fun _config : Lecerf.Machine.Config Q Γ =>
      (initialHistory : Tape (Mark Q Γ)) :=
    Primrec.const _
  exact (TwoTape.Config.equivRep_symm_primrec.comp
    (Primrec.pair control (Primrec.pair sourceTape history))).of_eq fun _ => rfl

/-- The reverse checkpoint also varies primitive recursively with its source
configuration. -/
theorem reverseCheckpoint_primrec :
    Primrec (reverseCheckpoint : Lecerf.Machine.Config Q Γ →
      TwoTape.Config (Control Q Γ) Γ (Mark Q Γ)) := by
  have sourceRep : Primrec fun config : Lecerf.Machine.Config Q Γ =>
      Lecerf.Machine.Config.equivRep config :=
    Lecerf.Machine.Config.equivRep_primrec
  have sourceState : Primrec fun config : Lecerf.Machine.Config Q Γ =>
      config.state :=
    Primrec.fst.comp sourceRep
  have sourceTape : Primrec fun config : Lecerf.Machine.Config Q Γ =>
      config.tape :=
    Primrec.snd.comp sourceRep
  have control : Primrec fun config : Lecerf.Machine.Config Q Γ =>
      Control.reverse config.state :=
    Control.reverse_primrec (Γ := Γ) |>.comp sourceState
  have history : Primrec fun _config : Lecerf.Machine.Config Q Γ =>
      (initialHistory : Tape (Mark Q Γ)) :=
    Primrec.const _
  exact (TwoTape.Config.equivRep_symm_primrec.comp
    (Primrec.pair control (Primrec.pair sourceTape history))).of_eq fun _ => rfl

/-- The distinct bottom-marker target used by the open coupling reduction is
primitive recursive in the source configuration. -/
theorem bottomTarget_primrec :
    Primrec (bottomTarget : Lecerf.Machine.Config Q Γ →
      TwoTape.Config (Control Q Γ) Γ (Mark Q Γ)) := by
  have sourceRep : Primrec fun config : Lecerf.Machine.Config Q Γ =>
      Lecerf.Machine.Config.equivRep config :=
    Lecerf.Machine.Config.equivRep_primrec
  have sourceState : Primrec fun config : Lecerf.Machine.Config Q Γ =>
      config.state :=
    Primrec.fst.comp sourceRep
  have sourceTape : Primrec fun config : Lecerf.Machine.Config Q Γ =>
      config.tape :=
    Primrec.snd.comp sourceRep
  have control : Primrec fun config : Lecerf.Machine.Config Q Γ =>
      Control.inspect config.state :=
    Control.inspect_primrec (Γ := Γ) |>.comp sourceState
  have history : Primrec fun _config : Lecerf.Machine.Config Q Γ =>
      Tape.move .left (initialHistory : Tape (Mark Q Γ)) :=
    Primrec.const _
  exact (TwoTape.Config.equivRep_symm_primrec.comp
    (Primrec.pair control (Primrec.pair sourceTape history))).of_eq fun _ => rfl

end ConfigurationMaps

end Lecerf.Machine.TwoTape.HistoryCompiler
