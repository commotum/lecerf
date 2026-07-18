import Lecerf.Transition.Core
import Mathlib.Computability.PartrecCode

/-!
# Effective universal halting source

This module exposes a fixed primitive-recursive transition system derived from
the bounded evaluator for `Nat.Partrec.Code`. It is the checked replacement
source for the later history simulation. It does not claim that mathlib's
existential Turing-machine constructions provide an effective compiler to the
finite machine syntax in `Lecerf.Machine.Core`.
-/

namespace Lecerf.Machine.Source

open Lecerf.Transition

/-- Structural equality for source programs, needed by checked reverse history
execution of the fixed universal source. -/
deriving instance DecidableEq for Nat.Partrec.Code

/-- One bounded evaluator attempt per transition. The state is the next bound
to try; a successful attempt makes that bound terminal. -/
def evalSearchStep (code : Nat.Partrec.Code) (input : Nat) : Step Nat :=
  fun bound =>
    match Nat.Partrec.Code.evaln bound code input with
    | none => some (bound + 1)
    | some _ => none

/-- Configuration of the fixed universal search system. -/
abbrev EvalSearchConfig := (Nat.Partrec.Code × Nat) × Nat

/-- A single fixed transition, with program and input carried in its state. -/
def universalEvalSearchStep : Step EvalSearchConfig := fun config =>
  (evalSearchStep config.1.1 config.1.2 config.2).map fun nextBound =>
    (config.1, nextBound)

/-- Effective start-state encoding for the fixed search system. -/
def evalSearchStart (code : Nat.Partrec.Code) (input : Nat) : EvalSearchConfig :=
  ((code, input), 0)

@[simp]
theorem evalSearchStep_of_none {code : Nat.Partrec.Code} {input bound : Nat}
    (h : Nat.Partrec.Code.evaln bound code input = none) :
    evalSearchStep code input bound = some (bound + 1) := by
  simp [evalSearchStep, h]

@[simp]
theorem evalSearchStep_of_some {code : Nat.Partrec.Code} {input bound value : Nat}
    (h : Nat.Partrec.Code.evaln bound code input = some value) :
    evalSearchStep code input bound = none := by
  simp [evalSearchStep, h]

theorem evalSearchStep_terminal_iff {code : Nat.Partrec.Code} {input bound : Nat} :
    Terminal (evalSearchStep code input) bound ↔
      ∃ value, value ∈ Nat.Partrec.Code.evaln bound code input := by
  unfold Terminal evalSearchStep
  cases Nat.Partrec.Code.evaln bound code input <;> simp

theorem evalSearchStep_reachable_of_all_none
    {code : Nat.Partrec.Code} {input bound : Nat}
    (h : ∀ smaller < bound, Nat.Partrec.Code.evaln smaller code input = none) :
    Reachable (evalSearchStep code input) 0 bound := by
  induction bound with
  | zero => exact Reachable.refl _ _
  | succ bound ih =>
      apply Reachable.trans
        (ih fun smaller hsmaller => h smaller (Nat.lt_succ_of_lt hsmaller))
      exact Reachable.single
        (evalSearchStep_of_none (h bound (Nat.lt_succ_self bound)))

theorem evalSearchStep_halts_iff_exists_evaln
    {code : Nat.Partrec.Code} {input : Nat} :
    HaltsFrom (evalSearchStep code input) 0 ↔
      ∃ bound value, value ∈ Nat.Partrec.Code.evaln bound code input := by
  rw [haltsFrom_iff_exists_reachable_terminal]
  constructor
  · rintro ⟨bound, _, terminal⟩
    exact ⟨bound, evalSearchStep_terminal_iff.mp terminal⟩
  · rintro ⟨bound, value, valueAtBound⟩
    let existsSuccess : ∃ bound, Nat.Partrec.Code.evaln bound code input ≠ none :=
      ⟨bound, fun equalNone => by rw [equalNone] at valueAtBound; simp at valueAtBound⟩
    let first := Nat.find existsSuccess
    have firstNe : Nat.Partrec.Code.evaln first code input ≠ none :=
      Nat.find_spec existsSuccess
    have firstValue : ∃ value, value ∈ Nat.Partrec.Code.evaln first code input := by
      cases h : Nat.Partrec.Code.evaln first code input with
      | none => exact False.elim (firstNe h)
      | some value => exact ⟨value, rfl⟩
    have earlierNone : ∀ smaller < first,
        Nat.Partrec.Code.evaln smaller code input = none := by
      intro smaller smallerLt
      cases smallerResult : Nat.Partrec.Code.evaln smaller code input with
      | none => rfl
      | some value =>
          exact False.elim ((Nat.find_min existsSuccess smallerLt) (by simp [smallerResult]))
    exact ⟨first, evalSearchStep_reachable_of_all_none earlierNone,
      evalSearchStep_terminal_iff.mpr firstValue⟩

/-- The budget search halts exactly when the partial-recursive source program
is defined on the supplied input. -/
theorem evalSearchStep_halts_iff_eval_dom (code : Nat.Partrec.Code) (input : Nat) :
    HaltsFrom (evalSearchStep code input) 0 ↔
      (Nat.Partrec.Code.eval code input).Dom := by
  rw [evalSearchStep_halts_iff_exists_evaln]
  simp only [Part.dom_iff_mem]
  constructor
  · rintro ⟨bound, value, valueAtBound⟩
    exact ⟨value, Nat.Partrec.Code.evaln_sound valueAtBound⟩
  · rintro ⟨value, valueInEval⟩
    obtain ⟨bound, valueAtBound⟩ := Nat.Partrec.Code.evaln_complete.mp valueInEval
    exact ⟨bound, value, valueAtBound⟩

/-- The fixed system has the same halting semantics; only its start state
depends on the source code and input. -/
theorem universalEvalSearchStep_halts_iff_eval_dom
    (code : Nat.Partrec.Code) (input : Nat) :
    HaltsFrom universalEvalSearchStep (evalSearchStart code input) ↔
      (Nat.Partrec.Code.eval code input).Dom := by
  let embedBound : Nat → EvalSearchConfig := fun bound => ((code, input), bound)
  have respects : StateTransition.Respects (evalSearchStep code input)
      universalEvalSearchStep fun bound config => embedBound bound = config := by
    rw [StateTransition.fun_respects]
    intro bound
    unfold StateTransition.FRespects universalEvalSearchStep embedBound
    cases h : evalSearchStep code input bound with
    | none => simp
    | some next =>
        simp only
        exact StrictlyReachable.single (by simp [h])
  change (StateTransition.eval universalEvalSearchStep (embedBound 0)).Dom ↔ _
  rw [StateTransition.tr_eval_dom respects rfl]
  exact evalSearchStep_halts_iff_eval_dom code input

/-- The parameterized search transition is uniformly primitive recursive. -/
theorem evalSearchStep_uniform_primrec :
    Primrec fun data : (Nat.Partrec.Code × Nat) × Nat =>
      evalSearchStep data.1.1 data.1.2 data.2 := by
  let evalAtBound : Primrec fun data : (Nat.Partrec.Code × Nat) × Nat =>
      Nat.Partrec.Code.evaln data.2 data.1.1 data.1.2 := by
    exact Nat.Partrec.Code.primrec_evaln.comp
      ((Primrec.snd.pair (Primrec.fst.comp Primrec.fst)).pair
        (Primrec.snd.comp Primrec.fst))
  exact (Primrec.option_casesOn evalAtBound
    (Primrec.option_some.comp (Primrec.succ.comp Primrec.snd))
    (Primrec.const Option.none).to₂).of_eq fun data => by
      simp only [evalSearchStep]
      cases Nat.Partrec.Code.evaln data.2 data.1.1 data.1.2 <;> rfl

theorem evalSearchStep_uniform_computable :
    Computable fun data : (Nat.Partrec.Code × Nat) × Nat =>
      evalSearchStep data.1.1 data.1.2 data.2 :=
  evalSearchStep_uniform_primrec.to_comp

/-- The fixed universal transition itself is primitive recursive. -/
theorem universalEvalSearchStep_primrec : Primrec universalEvalSearchStep := by
  exact (Primrec.option_map evalSearchStep_uniform_primrec
    ((Primrec.fst.comp Primrec.fst).pair Primrec.snd).to₂).of_eq fun config => by
      simp [universalEvalSearchStep]

/-- For fixed input, the map from source programs to universal start states is
primitive recursive. -/
theorem evalSearchStart_primrec (input : Nat) :
    Primrec fun code : Nat.Partrec.Code => evalSearchStart code input :=
  ((Primrec.id.pair (Primrec.const input)).pair (Primrec.const 0)).of_eq fun _ => rfl

/-- Program and input may both vary computably in the start-state map. -/
theorem evalSearchStart_joint_primrec :
    Primrec fun data : Nat.Partrec.Code × Nat => evalSearchStart data.1 data.2 :=
  ((Primrec.fst.pair Primrec.snd).pair (Primrec.const 0)).of_eq fun _ => rfl

end Lecerf.Machine.Source
