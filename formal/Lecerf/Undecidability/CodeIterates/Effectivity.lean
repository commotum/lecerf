import Lecerf.Transition.ExactEffectivity
import Lecerf.Undecidability.CodeIterates.Problems
import Mathlib.Computability.RE

/-!
# Effectivity of positive code-iterate problems

Checking a supplied positive exponent is primitive recursive uniformly in the
raw finite descriptor, exponent, and words.  Existential orbit membership is
kept separate: its positive witnesses can be searched for by a partial
recursive procedure, so both existential predicates are recursively
enumerable, but this module supplies no total existence decider.
-/

namespace Lecerf.Undecidability.CodeIterates

open Lecerf.Encoding.StepCode
open Lecerf.Transition
open Lecerf.Word

noncomputable section

/-- Exact checked word iteration is primitive recursive jointly in the raw
finite descriptor, starting word, and exponent. -/
theorem checkedExactIterate_uniform_primrec :
    Primrec fun data : (CodeDescriptor × Word Bool) × Nat =>
      exactIterate (Descriptor.checkedApply data.1.1)
        data.2 data.1.2 := by
  exact exactIterate_uniform_primrec
    (fun descriptor word => Descriptor.checkedApply descriptor word)
    Descriptor.checkedApply_uniform_primrec

/-- The supplied-positive-exponent predicate is primitive recursive.  In
particular, this checks the actual bind-preserving partial iterate rather than
a totalized approximation. -/
theorem positiveIterateAtYes_primrec :
    PrimrecPred PositiveIterateAtYes := by
  have exponent : Primrec fun input : SuppliedExponentInput => input.2.1 :=
    Primrec.fst.comp Primrec.snd
  have start : Primrec fun input : SuppliedExponentInput => input.2.2.1 :=
    Primrec.fst.comp (Primrec.snd.comp Primrec.snd)
  have target : Primrec fun input : SuppliedExponentInput => input.2.2.2 :=
    Primrec.snd.comp (Primrec.snd.comp Primrec.snd)
  have descriptorAndStart :
      Primrec fun input : SuppliedExponentInput =>
        (input.1, input.2.2.1) :=
    Primrec.pair Primrec.fst start
  have iterated : Primrec fun input : SuppliedExponentInput =>
      exactIterate (Descriptor.checkedApply input.1)
        input.2.1 input.2.2.1 :=
    checkedExactIterate_uniform_primrec.comp
      (Primrec.pair descriptorAndStart exponent)
  have expected : Primrec fun input : SuppliedExponentInput =>
      some input.2.2.2 :=
    Primrec.option_some.comp target
  have valid : PrimrecPred fun input : SuppliedExponentInput =>
      input.1.Valid :=
    Descriptor.valid_primrec.comp Primrec.fst
  have positive : PrimrecPred fun input : SuppliedExponentInput =>
      input.2.1 ≠ 0 :=
    (Primrec.eq.comp exponent (Primrec.const 0)).not
  have successful : PrimrecPred fun input : SuppliedExponentInput =>
      ExactSteps input.1.checkedApply input.2.1
        input.2.2.1 input.2.2.2 := by
    exact Primrec.eq.comp iterated expected
  exact valid.and (positive.and successful)

/-- A supplied positive exponent can be recognized by a total computable
predicate. -/
theorem positiveIterateAtYes_computablePred :
    ComputablePred PositiveIterateAtYes :=
  positiveIterateAtYes_primrec.computablePred

/-- A positive fixed-orbit witness stores its predecessor exponent `k`; the
actual exponent checked is `k + 1`. -/
def FixedOrbitWitnessYes (input : FixedOrbitInput × Nat) : Prop :=
  input.1.1.Valid ∧
    ExactSteps input.1.1.checkedApply (input.2 + 1)
      input.1.2 input.1.2

/-- Positive fixed-orbit witnesses form a primitive-recursive relation. -/
theorem fixedOrbitWitnessYes_primrec :
    PrimrecPred FixedOrbitWitnessYes := by
  have iterated : Primrec fun input : FixedOrbitInput × Nat =>
      exactIterate (Descriptor.checkedApply input.1.1)
        (input.2 + 1) input.1.2 :=
    checkedExactIterate_uniform_primrec.comp
      (Primrec.pair Primrec.fst (Primrec.succ.comp Primrec.snd))
  have expected : Primrec fun input : FixedOrbitInput × Nat =>
      some input.1.2 :=
    Primrec.option_some.comp (Primrec.snd.comp Primrec.fst)
  have valid : PrimrecPred fun input : FixedOrbitInput × Nat =>
      input.1.1.Valid :=
    Descriptor.valid_primrec.comp (Primrec.fst.comp Primrec.fst)
  have successful : PrimrecPred fun input : FixedOrbitInput × Nat =>
      ExactSteps input.1.1.checkedApply (input.2 + 1)
        input.1.2 input.1.2 := by
    exact Primrec.eq.comp iterated expected
  exact valid.and successful

theorem fixedOrbitWitnessYes_computablePred :
    ComputablePred FixedOrbitWitnessYes :=
  fixedOrbitWitnessYes_primrec.computablePred

/-- A distinct-orbit witness stores the predecessor exponent `k`; validity and
word inequality are checked as part of the finite witness relation. -/
def DistinctOrbitWitnessYes (input : DistinctOrbitInput × Nat) : Prop :=
  input.1.1.Valid ∧ input.1.2.1 ≠ input.1.2.2 ∧
    ExactSteps input.1.1.checkedApply (input.2 + 1)
      input.1.2.1 input.1.2.2

/-- Distinct-orbit witnesses form a primitive-recursive relation. -/
theorem distinctOrbitWitnessYes_primrec :
    PrimrecPred DistinctOrbitWitnessYes := by
  have descriptor : Primrec fun input : DistinctOrbitInput × Nat =>
      input.1.1 :=
    Primrec.fst.comp Primrec.fst
  have start : Primrec fun input : DistinctOrbitInput × Nat =>
      input.1.2.1 :=
    Primrec.fst.comp (Primrec.snd.comp Primrec.fst)
  have target : Primrec fun input : DistinctOrbitInput × Nat =>
      input.1.2.2 :=
    Primrec.snd.comp (Primrec.snd.comp Primrec.fst)
  have descriptorAndStart :
      Primrec fun input : DistinctOrbitInput × Nat =>
        (input.1.1, input.1.2.1) :=
    Primrec.pair descriptor start
  have iterated : Primrec fun input : DistinctOrbitInput × Nat =>
      exactIterate (Descriptor.checkedApply input.1.1)
        (input.2 + 1) input.1.2.1 :=
    checkedExactIterate_uniform_primrec.comp
      (Primrec.pair descriptorAndStart (Primrec.succ.comp Primrec.snd))
  have expected : Primrec fun input : DistinctOrbitInput × Nat =>
      some input.1.2.2 :=
    Primrec.option_some.comp target
  have valid : PrimrecPred fun input : DistinctOrbitInput × Nat =>
      input.1.1.Valid :=
    Descriptor.valid_primrec.comp descriptor
  have distinct : PrimrecPred fun input : DistinctOrbitInput × Nat =>
      input.1.2.1 ≠ input.1.2.2 :=
    (Primrec.eq.comp start target).not
  have successful : PrimrecPred fun input : DistinctOrbitInput × Nat =>
      ExactSteps input.1.1.checkedApply (input.2 + 1)
        input.1.2.1 input.1.2.2 := by
    exact Primrec.eq.comp iterated expected
  exact valid.and (distinct.and successful)

theorem distinctOrbitWitnessYes_computablePred :
    ComputablePred DistinctOrbitWitnessYes :=
  distinctOrbitWitnessYes_primrec.computablePred

/-- Pull the descriptor guard inside the existential fixed-orbit witness. -/
theorem positiveFixedOrbitYes_iff_exists_witness
    (input : FixedOrbitInput) :
    PositiveFixedOrbitYes input ↔
      ∃ k, FixedOrbitWitnessYes (input, k) := by
  constructor
  · rintro ⟨valid, k, orbit⟩
    exact ⟨k, valid, orbit⟩
  · rintro ⟨k, valid, orbit⟩
    exact ⟨valid, k, orbit⟩

/-- Pull validity and word inequality inside the existential distinct-orbit
witness. -/
theorem distinctOrbitYes_iff_exists_witness
    (input : DistinctOrbitInput) :
    DistinctOrbitYes input ↔
      ∃ k, DistinctOrbitWitnessYes (input, k) := by
  constructor
  · rintro ⟨valid, distinct, k, orbit⟩
    exact ⟨k, valid, distinct, orbit⟩
  · rintro ⟨k, valid, distinct, orbit⟩
    exact ⟨valid, distinct, k, orbit⟩

/-- Existential projection of a total computable natural-number witness
relation is recursively enumerable.  The resulting finder is partial: its
domain is exactly the existence predicate. -/
private theorem exists_nat_re
    {A : Type*} [Primcodable A] {R : A → Nat → Prop}
    (relationComputable :
      ComputablePred fun data : A × Nat => R data.1 data.2) :
    REPred fun input => ∃ n, R input n := by
  rcases relationComputable with ⟨decider, deciderComputable⟩
  letI : DecidableRel R := fun input n => decider (input, n)
  have searchPartrec :
      Partrec fun input => Nat.rfind fun n =>
        Part.some (decide (R input n)) :=
    Partrec.rfind deciderComputable.partrec
  exact (Partrec.dom_re searchPartrec).of_eq fun input => by
    rw [Nat.rfind_dom]
    simp

/-- Positive fixed-orbit existence is semidecidable by partial search over
strictly positive exponents. -/
theorem positiveFixedOrbitYes_re : REPred PositiveFixedOrbitYes := by
  apply REPred.of_eq
    (exists_nat_re
      (R := fun input k => FixedOrbitWitnessYes (input, k))
      fixedOrbitWitnessYes_computablePred)
  intro input
  exact (positiveFixedOrbitYes_iff_exists_witness input).symm

/-- Distinct-word positive orbit existence is semidecidable by partial search
over strictly positive exponents. -/
theorem distinctOrbitYes_re : REPred DistinctOrbitYes := by
  apply REPred.of_eq
    (exists_nat_re
      (R := fun input k => DistinctOrbitWitnessYes (input, k))
      distinctOrbitWitnessYes_computablePred)
  intro input
  exact (distinctOrbitYes_iff_exists_witness input).symm

end

end Lecerf.Undecidability.CodeIterates
