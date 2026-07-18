import Lecerf.Machine.Effectivity
import Lecerf.Machine.Reversible

/-!
# Decidable syntactic validity for reversible finite machines

The semantic predicate `FiniteMachine.Reversible` quantifies over all
configurations.  This file packages a stronger pairwise rule-table condition
that is decidable and primitive recursive from the finite description, and
proves that it implies semantic reversibility.
-/

namespace Lecerf.Machine

universe u v

namespace Rule

variable {Q : Type u} {Γ : Type v}
  [Primcodable Q] [Primcodable Γ]

theorem source_primrec : Primrec (Rule.source : Rule Q Γ → Q) :=
  Primrec.fst.comp equivRep_primrec

theorem read_primrec : Primrec (Rule.read : Rule Q Γ → Γ) :=
  Primrec.fst.comp (Primrec.snd.comp equivRep_primrec)

theorem target_primrec : Primrec (Rule.target : Rule Q Γ → Q) :=
  Primrec.fst.comp (Primrec.snd.comp (Primrec.snd.comp equivRep_primrec))

theorem write_primrec : Primrec (Rule.write : Rule Q Γ → Γ) :=
  Primrec.fst.comp
    (Primrec.snd.comp (Primrec.snd.comp (Primrec.snd.comp equivRep_primrec)))

theorem move_primrec : Primrec (Rule.move : Rule Q Γ → Tape.Move) :=
  Primrec.snd.comp
    (Primrec.snd.comp (Primrec.snd.comp (Primrec.snd.comp equivRep_primrec)))

end Rule

namespace FiniteMachine

variable {Q : Type u} {Γ : Type v} [Inhabited Γ]
  [Primcodable Q] [Primcodable Γ] [DecidableEq Q] [DecidableEq Γ]

/-- Two rules can coexist in a deterministic table: either they are the same
entry, or their forward lookup keys differ. -/
def ForwardPairValid (first second : Rule Q Γ) : Prop :=
  first = second ∨ first.source ≠ second.source ∨ first.read ≠ second.read

/-- Two rules can coexist in the checked reversible subclass: equal entries
are harmless; distinct rules with a common target use the same movement and
write different symbols. -/
def ReversePairValid (first second : Rule Q Γ) : Prop :=
  first = second ∨ first.target ≠ second.target ∨
    (first.move = second.move ∧ first.write ≠ second.write)

private instance forwardPairValidRefl : Std.Refl (@ForwardPairValid Q Γ) where
  refl _ := Or.inl rfl

private instance forwardPairValidSymm : Std.Symm (@ForwardPairValid Q Γ) where
  symm first second := by
    rintro (equal | sourceNe | readNe)
    · exact Or.inl equal.symm
    · exact Or.inr (Or.inl sourceNe.symm)
    · exact Or.inr (Or.inr readNe.symm)

private instance reversePairValidRefl : Std.Refl (@ReversePairValid Q Γ) where
  refl _ := Or.inl rfl

private instance reversePairValidSymm : Std.Symm (@ReversePairValid Q Γ) where
  symm first second := by
    rintro (equal | targetNe | ⟨moveEq, writeNe⟩)
    · exact Or.inl equal.symm
    · exact Or.inr (Or.inl targetNe.symm)
    · exact Or.inr (Or.inr ⟨moveEq.symm, writeNe.symm⟩)

/-- A wholly finite, decidable rule-table certificate. This is intentionally
stronger than semantic reversibility; no converse is asserted. -/
def SyntacticallyReversible (machine : FiniteMachine Q Γ) : Prop :=
  machine.rules.Pairwise ForwardPairValid ∧
    machine.rules.Pairwise ReversePairValid

instance (machine : FiniteMachine Q Γ) : Decidable machine.SyntacticallyReversible :=
  inferInstance

theorem pairwise_forwardPairValid_iff_tableDeterministic
    (machine : FiniteMachine Q Γ) :
    machine.rules.Pairwise ForwardPairValid ↔ machine.TableDeterministic := by
  constructor
  · intro pairwise first firstMem second secondMem sourceEq readEq
    by_cases equal : first = second
    · exact equal
    · rcases pairwise.forall firstMem secondMem equal with
        equal | sourceNe | readNe
      · exact equal
      · exact False.elim (sourceNe sourceEq)
      · exact False.elim (readNe readEq)
  · intro deterministic
    apply List.pairwise_of_reflexive_of_forall_ne
    intro first firstMem second secondMem _
    by_cases sourceEq : first.source = second.source
    · by_cases readEq : first.read = second.read
      · exact Or.inl (deterministic firstMem secondMem sourceEq readEq)
      · exact Or.inr (Or.inr readEq)
    · exact Or.inr (Or.inl sourceEq)

theorem pairwise_reversePairValid_iff_reverseTableCompatible
    (machine : FiniteMachine Q Γ) :
    machine.rules.Pairwise ReversePairValid ↔
      machine.ReverseTableCompatible := by
  constructor
  · intro pairwise first firstMem second secondMem rulesNe targetEq
    rcases pairwise.forall firstMem secondMem rulesNe with
      equal | targetNe | compatible
    · exact False.elim (rulesNe equal)
    · exact False.elim (targetNe targetEq)
    · exact compatible
  · intro compatible
    apply List.pairwise_of_reflexive_of_forall_ne
    intro first firstMem second secondMem rulesNe
    by_cases targetEq : first.target = second.target
    · exact Or.inr (Or.inr (compatible firstMem secondMem rulesNe targetEq))
    · exact Or.inr (Or.inl targetEq)

theorem syntacticallyReversible_iff (machine : FiniteMachine Q Γ) :
    machine.SyntacticallyReversible ↔
      machine.TableDeterministic ∧ machine.ReverseTableCompatible := by
  exact and_congr
    (pairwise_forwardPairValid_iff_tableDeterministic machine)
    (pairwise_reversePairValid_iff_reverseTableCompatible machine)

/-- The finite syntactic certificate implies the semantic whole-machine
reversibility predicate. -/
theorem SyntacticallyReversible.reversible
    {machine : FiniteMachine Q Γ}
    (valid : machine.SyntacticallyReversible) : machine.Reversible := by
  obtain ⟨deterministic, reverseCompatible⟩ :=
    (syntacticallyReversible_iff machine).mp valid
  refine ⟨deterministic, ?_⟩
  exact (machine.backwardCompatible_iff_backwardUnique deterministic).mp
    (reverseTableCompatible_backwardCompatible reverseCompatible)

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
        exact refl_of _
      · exact pairwise.forall secondMem firstMem equal

private theorem forwardPairValid_primrec :
    PrimrecRel (@ForwardPairValid Q Γ) := by
  have ruleEq : PrimrecRel fun first second : Rule Q Γ => first = second :=
    Primrec.eq
  have sourceNe : PrimrecRel fun first second : Rule Q Γ =>
      first.source ≠ second.source :=
    (Primrec.eq.comp₂
      (Rule.source_primrec.comp₂ Primrec₂.left)
      (Rule.source_primrec.comp₂ Primrec₂.right)).not
  have readNe : PrimrecRel fun first second : Rule Q Γ =>
      first.read ≠ second.read :=
    (Primrec.eq.comp₂
      (Rule.read_primrec.comp₂ Primrec₂.left)
      (Rule.read_primrec.comp₂ Primrec₂.right)).not
  exact (ruleEq.or (sourceNe.or readNe)).of_eq fun _ _ => by
    simp [ForwardPairValid, or_assoc]

private theorem reversePairValid_primrec :
    PrimrecRel (@ReversePairValid Q Γ) := by
  have ruleEq : PrimrecRel fun first second : Rule Q Γ => first = second :=
    Primrec.eq
  have targetNe : PrimrecRel fun first second : Rule Q Γ =>
      first.target ≠ second.target :=
    (Primrec.eq.comp₂
      (Rule.target_primrec.comp₂ Primrec₂.left)
      (Rule.target_primrec.comp₂ Primrec₂.right)).not
  have moveEq : PrimrecRel fun first second : Rule Q Γ =>
      first.move = second.move :=
    Primrec.eq.comp₂
      (Rule.move_primrec.comp₂ Primrec₂.left)
      (Rule.move_primrec.comp₂ Primrec₂.right)
  have writeNe : PrimrecRel fun first second : Rule Q Γ =>
      first.write ≠ second.write :=
    (Primrec.eq.comp₂
      (Rule.write_primrec.comp₂ Primrec₂.left)
      (Rule.write_primrec.comp₂ Primrec₂.right)).not
  exact (ruleEq.or (targetNe.or (moveEq.and writeNe))).of_eq fun _ _ => by
    simp [ReversePairValid, or_assoc]

/-- The finite syntactic validity predicate is primitive recursive uniformly
in the raw rule-table description. -/
theorem syntacticallyReversible_primrec :
    PrimrecPred
      (SyntacticallyReversible : FiniteMachine Q Γ → Prop) := by
  have forward : PrimrecPred fun rules : List (Rule Q Γ) =>
      rules.Pairwise ForwardPairValid :=
    pairwise_primrec forwardPairValid_primrec
  have reverse : PrimrecPred fun rules : List (Rule Q Γ) =>
      rules.Pairwise ReversePairValid :=
    pairwise_primrec reversePairValid_primrec
  exact (forward.and reverse).comp equivRep_primrec

end FiniteMachine

end Lecerf.Machine
