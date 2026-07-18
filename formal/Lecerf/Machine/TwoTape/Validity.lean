import Lecerf.Machine.TwoTape.Effectivity
import Lecerf.Machine.TwoTape.Reversible

/-!
# Effective validity checking for finite two-tape machines

The pairwise syntactic certificate from `TwoTape.Reversible` is primitive
recursive in a raw finite rule table.  Together with that module's semantic
soundness theorem, this gives later decision problems an executable validity
guard without pretending that the certificate characterizes every reversible
machine.
-/

namespace Lecerf.Machine.TwoTape

universe u v w

namespace Rule

variable {Q : Type u} {Γ₁ : Type v} {Γ₂ : Type w}
  [Primcodable Q] [Primcodable Γ₁] [Primcodable Γ₂]

theorem source_primrec : Primrec (Rule.source : Rule Q Γ₁ Γ₂ → Q) :=
  Primrec.fst.comp equivRep_primrec

theorem read₁_primrec : Primrec (Rule.read₁ : Rule Q Γ₁ Γ₂ → Γ₁) :=
  Primrec.fst.comp (Primrec.snd.comp equivRep_primrec)

theorem read₂_primrec : Primrec (Rule.read₂ : Rule Q Γ₁ Γ₂ → Γ₂) :=
  Primrec.fst.comp (Primrec.snd.comp (Primrec.snd.comp equivRep_primrec))

theorem target_primrec : Primrec (Rule.target : Rule Q Γ₁ Γ₂ → Q) :=
  Primrec.fst.comp
    (Primrec.snd.comp (Primrec.snd.comp (Primrec.snd.comp equivRep_primrec)))

theorem write₁_primrec : Primrec (Rule.write₁ : Rule Q Γ₁ Γ₂ → Γ₁) :=
  Primrec.fst.comp (Primrec.snd.comp
    (Primrec.snd.comp (Primrec.snd.comp (Primrec.snd.comp equivRep_primrec))))

theorem move₁_primrec : Primrec (Rule.move₁ : Rule Q Γ₁ Γ₂ → Tape.Move) :=
  Primrec.fst.comp (Primrec.snd.comp (Primrec.snd.comp
    (Primrec.snd.comp (Primrec.snd.comp (Primrec.snd.comp equivRep_primrec)))))

theorem write₂_primrec : Primrec (Rule.write₂ : Rule Q Γ₁ Γ₂ → Γ₂) :=
  Primrec.fst.comp (Primrec.snd.comp (Primrec.snd.comp (Primrec.snd.comp
    (Primrec.snd.comp (Primrec.snd.comp (Primrec.snd.comp equivRep_primrec))))))

theorem move₂_primrec : Primrec (Rule.move₂ : Rule Q Γ₁ Γ₂ → Tape.Move) :=
  Primrec.snd.comp (Primrec.snd.comp (Primrec.snd.comp (Primrec.snd.comp
    (Primrec.snd.comp (Primrec.snd.comp (Primrec.snd.comp equivRep_primrec))))))

end Rule

namespace FiniteMachine

variable {Q : Type u} {Γ₁ : Type v} {Γ₂ : Type w}
  [Inhabited Γ₁] [Inhabited Γ₂]
  [Primcodable Q] [Primcodable Γ₁] [Primcodable Γ₂]
  [DecidableEq Q] [DecidableEq Γ₁] [DecidableEq Γ₂]

private theorem pairwise_primrec
    {α : Type*} [Primcodable α]
    {R : α → α → Prop} [DecidableRel R] [Std.Refl R] [Std.Symm R]
    (relationPrimrec : PrimrecRel R) :
    PrimrecPred fun values : List α => values.Pairwise R := by
  have inner : PrimrecRel fun (values : List α) (first : α) =>
      ∀ second ∈ values, R second first :=
    relationPrimrec.forall_mem_list
  have outer : PrimrecRel fun (firsts seconds : List α) =>
      ∀ first ∈ firsts, ∀ second ∈ seconds, R second first :=
    inner.swap.forall_mem_list
  have diagonal : PrimrecPred fun values : List α =>
      ∀ first ∈ values, ∀ second ∈ values, R second first :=
    outer.comp Primrec.id Primrec.id
  exact diagonal.of_eq fun values => by
    constructor
    · intro all
      exact List.pairwise_of_reflexive_of_forall_ne fun first firstMem
        second secondMem _ => all second secondMem first firstMem
    · intro pairwise first firstMem second secondMem
      by_cases equal : second = first
      · subst first
        exact refl_of R second
      · exact pairwise.forall secondMem firstMem equal

omit [Inhabited Γ₁] [Inhabited Γ₂] [DecidableEq Q]
    [DecidableEq Γ₁] [DecidableEq Γ₂] in
private theorem forwardPairValid_primrec :
    PrimrecRel (@ForwardPairValid Q Γ₁ Γ₂) := by
  have ruleEq : PrimrecRel fun first second : Rule Q Γ₁ Γ₂ => first = second :=
    Primrec.eq
  have sourceNe : PrimrecRel fun first second : Rule Q Γ₁ Γ₂ =>
      first.source ≠ second.source :=
    (Primrec.eq.comp₂
      (Rule.source_primrec.comp₂ Primrec₂.left)
      (Rule.source_primrec.comp₂ Primrec₂.right)).not
  have read₁Ne : PrimrecRel fun first second : Rule Q Γ₁ Γ₂ =>
      first.read₁ ≠ second.read₁ :=
    (Primrec.eq.comp₂
      (Rule.read₁_primrec.comp₂ Primrec₂.left)
      (Rule.read₁_primrec.comp₂ Primrec₂.right)).not
  have read₂Ne : PrimrecRel fun first second : Rule Q Γ₁ Γ₂ =>
      first.read₂ ≠ second.read₂ :=
    (Primrec.eq.comp₂
      (Rule.read₂_primrec.comp₂ Primrec₂.left)
      (Rule.read₂_primrec.comp₂ Primrec₂.right)).not
  exact (ruleEq.or (sourceNe.or (read₁Ne.or read₂Ne))).of_eq fun
    | ⟨first, second⟩ => by
        change (first = second ∨ first.source ≠ second.source ∨
          first.read₁ ≠ second.read₁ ∨ first.read₂ ≠ second.read₂) ↔
            ForwardPairValid first second
        rfl

omit [Inhabited Γ₁] [Inhabited Γ₂] [DecidableEq Q]
    [DecidableEq Γ₁] [DecidableEq Γ₂] in
private theorem incomingSeparatedPair_primrec :
    PrimrecRel (@IncomingSeparatedPair Q Γ₁ Γ₂) := by
  have ruleEq : PrimrecRel fun first second : Rule Q Γ₁ Γ₂ => first = second :=
    Primrec.eq
  have targetNe : PrimrecRel fun first second : Rule Q Γ₁ Γ₂ =>
      first.target ≠ second.target :=
    (Primrec.eq.comp₂
      (Rule.target_primrec.comp₂ Primrec₂.left)
      (Rule.target_primrec.comp₂ Primrec₂.right)).not
  have move₁Eq : PrimrecRel fun first second : Rule Q Γ₁ Γ₂ =>
      first.move₁ = second.move₁ :=
    Primrec.eq.comp₂
      (Rule.move₁_primrec.comp₂ Primrec₂.left)
      (Rule.move₁_primrec.comp₂ Primrec₂.right)
  have write₁Ne : PrimrecRel fun first second : Rule Q Γ₁ Γ₂ =>
      first.write₁ ≠ second.write₁ :=
    (Primrec.eq.comp₂
      (Rule.write₁_primrec.comp₂ Primrec₂.left)
      (Rule.write₁_primrec.comp₂ Primrec₂.right)).not
  have move₂Eq : PrimrecRel fun first second : Rule Q Γ₁ Γ₂ =>
      first.move₂ = second.move₂ :=
    Primrec.eq.comp₂
      (Rule.move₂_primrec.comp₂ Primrec₂.left)
      (Rule.move₂_primrec.comp₂ Primrec₂.right)
  have write₂Ne : PrimrecRel fun first second : Rule Q Γ₁ Γ₂ =>
      first.write₂ ≠ second.write₂ :=
    (Primrec.eq.comp₂
      (Rule.write₂_primrec.comp₂ Primrec₂.left)
      (Rule.write₂_primrec.comp₂ Primrec₂.right)).not
  exact (ruleEq.or (targetNe.or
    ((move₁Eq.and write₁Ne).or (move₂Eq.and write₂Ne)))).of_eq fun
      | ⟨first, second⟩ => by
          change (first = second ∨ first.target ≠ second.target ∨
            (first.move₁ = second.move₁ ∧ first.write₁ ≠ second.write₁) ∨
            (first.move₂ = second.move₂ ∧ first.write₂ ≠ second.write₂)) ↔
              IncomingSeparatedPair first second
          rfl

omit [Inhabited Γ₁] [Inhabited Γ₂] in
/-- The whole finite two-tape validity certificate is primitive recursive in
the raw table. -/
theorem syntacticallyReversible_primrec :
    PrimrecPred
      (SyntacticallyReversible : FiniteMachine Q Γ₁ Γ₂ → Prop) := by
  have forward : PrimrecPred fun rules : List (Rule Q Γ₁ Γ₂) =>
      rules.Pairwise ForwardPairValid :=
    pairwise_primrec forwardPairValid_primrec
  have backward : PrimrecPred fun rules : List (Rule Q Γ₁ Γ₂) =>
      rules.Pairwise IncomingSeparatedPair :=
    pairwise_primrec incomingSeparatedPair_primrec
  exact (forward.and backward).comp equivRep_primrec

end FiniteMachine

end Lecerf.Machine.TwoTape
