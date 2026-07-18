import Lecerf.Transition.ExactCore
import Mathlib.Computability.Primrec.Basic

/-!
# Effective exact iteration

This leaf proves uniform primitive recursiveness of finite exact iteration for
an option-valued transition supplied by a finite description.  The recursive
state remains an `Option`; an undefined intermediate transition is propagated
by `Option.bind` and is never replaced by a sink or identity step.
-/

namespace Lecerf.Transition

universe u v

/-- Exact iteration is primitive recursive jointly in a description, starting
state, and exponent whenever one described transition is primitive recursive.

The input layout is `((description, state), exponent)`. -/
theorem exactIterate_uniform_primrec
    {D : Type u} {X : Type v} [Primcodable D] [Primcodable X]
    (next : D → X → Option X)
    (next_primrec :
      Primrec fun data : D × X => next data.1 data.2) :
    Primrec fun data : (D × X) × Nat =>
      exactIterate (next data.1.1) data.2 data.1.2 := by
  have initial : Primrec fun data : (D × X) × Nat =>
      some data.1.2 :=
    Primrec.option_some.comp (Primrec.snd.comp Primrec.fst)
  have previous : Primrec fun data :
      ((D × X) × Nat) × (Nat × Option X) => data.2.2 :=
    Primrec.snd.comp Primrec.snd
  have nextAt : Primrec₂ fun
      (data : ((D × X) × Nat) × (Nat × Option X))
      (state : X) => next data.1.1.1 state := by
    exact next_primrec.comp
      (Primrec.pair
        (Primrec.fst.comp (Primrec.fst.comp (Primrec.fst.comp Primrec.fst)))
        Primrec.snd) |>.to₂
  have body' : Primrec fun data :
      ((D × X) × Nat) × (Nat × Option X) =>
      data.2.2.bind (next data.1.1.1) :=
    Primrec.option_bind previous nextAt
  have body : Primrec₂ fun (input : (D × X) × Nat)
      (recData : Nat × Option X) =>
      recData.2.bind (next input.1.1) :=
    body'.to₂
  exact (Primrec.nat_rec' Primrec.snd initial body).of_eq fun data => by
    induction data.2 with
    | zero => rfl
    | succ n inductionHypothesis =>
        simp [exactIterate, inductionHypothesis]

end Lecerf.Transition
