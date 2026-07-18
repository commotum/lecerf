import Lecerf.Machine.Compiler.FiniteSource
import Lecerf.Machine.Effectivity

/-!
# Computable input map for the fixed finite source machine

The machine and its finite-support encodings in `FiniteSource` are closed
constants.  This module proves independently that the only varying part of
the reduction--the canonical initial tape--is primitive recursive in the
source `Nat.Partrec.Code` and input.
-/

namespace Lecerf.Machine.Compiler.FiniteSource

open Turing

noncomputable instance sourceSymbolPrimcodable :
    Primcodable Turing.PartrecToTM2.Γ' :=
  Primcodable.ofEquiv
    (Fin (Fintype.card Turing.PartrecToTM2.Γ'))
    (Fintype.equivFin Turing.PartrecToTM2.Γ')

/-- Binary numerals used by mathlib's universal machine satisfy the expected
division-by-two recurrence. -/
theorem trNat_rec (n : Nat) :
    Turing.PartrecToTM2.trNat n =
      if n = 0 then [] else
        (if n.bodd then Turing.PartrecToTM2.Γ'.bit1
          else Turing.PartrecToTM2.Γ'.bit0) ::
          Turing.PartrecToTM2.trNat n.div2 := by
  unfold Turing.PartrecToTM2.trNat
  generalize h : (n : Num) = numeral
  cases numeral with
  | zero =>
      have hn : n = 0 := by
        simpa using congrArg ((↑) : Num → Nat) h
      simp [hn, Turing.PartrecToTM2.trNum]
  | pos positive =>
      have hn : n = (positive : Nat) := by
        simpa using congrArg ((↑) : Num → Nat) h
      subst n
      cases positive with
      | one =>
          simp [Turing.PartrecToTM2.trNum, Turing.PartrecToTM2.trPosNum]
      | bit0 positive =>
          have hp : (positive : Nat) ≠ 0 :=
            Nat.ne_of_gt (PosNum.to_nat_pos positive)
          simp [Turing.PartrecToTM2.trNum,
            Turing.PartrecToTM2.trPosNum, hp]
          change Turing.PartrecToTM2.trPosNum positive =
            Turing.PartrecToTM2.trNum
              (((positive : Nat) + (positive : Nat)).div2)
          rw [show ((positive : Nat) + (positive : Nat)).div2 =
              (positive : Nat) by
            simpa [two_mul] using Nat.div2_bit0 (positive : Nat)]
          simp [Turing.PartrecToTM2.trNum]
      | bit1 positive =>
          have hp : (positive : Nat) ≠ 0 :=
            Nat.ne_of_gt (PosNum.to_nat_pos positive)
          simp [Turing.PartrecToTM2.trNum,
            Turing.PartrecToTM2.trPosNum, hp]
          change Turing.PartrecToTM2.trPosNum positive =
            Turing.PartrecToTM2.trNum
              (((positive : Nat) + (positive : Nat)).div2)
          rw [show ((positive : Nat) + (positive : Nat)).div2 =
              (positive : Nat) by
            simpa [two_mul] using Nat.div2_bit0 (positive : Nat)]
          simp [Turing.PartrecToTM2.trNum]

/-- Strong-recursion body used to certify the binary numeral encoder. -/
private def trNatBody (_ : Unit)
    (values : List (List Turing.PartrecToTM2.Γ')) :
    Option (List Turing.PartrecToTM2.Γ') :=
  let n := values.length
  if n = 0 then some [] else
    (values[n.div2]?).map fun tail =>
      (if n.bodd then Turing.PartrecToTM2.Γ'.bit1
        else Turing.PartrecToTM2.Γ'.bit0) :: tail

private theorem trNatBody_primrec : Primrec₂ trNatBody := by
  unfold trNatBody
  have length : Primrec fun data :
      Unit × List (List Turing.PartrecToTM2.Γ') => data.2.length :=
    Primrec.list_length.comp Primrec.snd
  have previous : Primrec fun data :
      Unit × List (List Turing.PartrecToTM2.Γ') =>
        data.2[data.2.length.div2]? :=
    Primrec.list_getElem?.comp Primrec.snd
      (Primrec.nat_div2.comp length)
  have symbol : Primrec fun data :
      Unit × List (List Turing.PartrecToTM2.Γ') =>
        if data.2.length.bodd then Turing.PartrecToTM2.Γ'.bit1
          else Turing.PartrecToTM2.Γ'.bit0 :=
    (Primrec.cond (Primrec.nat_bodd.comp length)
      (Primrec.const Turing.PartrecToTM2.Γ'.bit1)
      (Primrec.const Turing.PartrecToTM2.Γ'.bit0)).of_eq fun data => by
        cases data.2.length.bodd <;> rfl
  have nonzero : Primrec fun data :
      Unit × List (List Turing.PartrecToTM2.Γ') =>
        (data.2[data.2.length.div2]?).map fun tail =>
          (if data.2.length.bodd then Turing.PartrecToTM2.Γ'.bit1
            else Turing.PartrecToTM2.Γ'.bit0) :: tail :=
    Primrec.option_map previous
      ((Primrec.list_cons.comp (symbol.comp Primrec.fst) Primrec.snd).to₂)
  exact (Primrec.ite (Primrec.eq.comp length (Primrec.const 0))
    (Primrec.const (some [])) nonzero).to₂.of_eq fun _ _ => rfl

/-- Mathlib's binary natural-number tape encoder is primitive recursive. -/
theorem trNat_primrec : Primrec Turing.PartrecToTM2.trNat := by
  have joint : Primrec₂
      (fun (_ : Unit) n => Turing.PartrecToTM2.trNat n) :=
    Primrec.nat_strong_rec
      (fun (_ : Unit) n => Turing.PartrecToTM2.trNat n)
      trNatBody_primrec (by
        intro _ n
        rw [trNat_rec]
        by_cases hn : n = 0
        · subst n
          rfl
        · have hdiv : n.div2 < n := by
            rw [Nat.div2_val]
            exact Nat.div_lt_self (Nat.pos_of_ne_zero hn) (by decide)
          simp only [trNatBody, List.length_map, List.length_range,
            hn, if_false]
          rw [List.getElem?_map, List.getElem?_range hdiv]
          rfl)
  exact joint.comp (Primrec.const Unit.unit) Primrec.id

/-- Encoding a list of naturals in the universal TM2 alphabet is primitive
recursive. -/
theorem trList_primrec : Primrec Turing.PartrecToTM2.trList := by
  have step : Primrec fun data :
      List Nat × (Nat × List Turing.PartrecToTM2.Γ') =>
        Turing.PartrecToTM2.trNat data.2.1 ++
          Turing.PartrecToTM2.Γ'.cons :: data.2.2 := by
    have encodedPrefix : Primrec fun data :
        List Nat × (Nat × List Turing.PartrecToTM2.Γ') =>
          Turing.PartrecToTM2.trNat data.2.1 :=
      trNat_primrec.comp (Primrec.fst.comp Primrec.snd)
    have suffix : Primrec fun data :
        List Nat × (Nat × List Turing.PartrecToTM2.Γ') =>
          Turing.PartrecToTM2.Γ'.cons :: data.2.2 :=
      Primrec.list_cons.comp
        (Primrec.const Turing.PartrecToTM2.Γ'.cons)
        (Primrec.snd.comp Primrec.snd)
    exact Primrec.list_append.comp encodedPrefix suffix
  exact (Primrec.list_foldr Primrec.id (Primrec.const []) step.to₂).of_eq
    fun input => by
      induction input with
      | nil => rfl
      | cons head tail ih =>
          simp only [List.foldr_cons, Turing.PartrecToTM2.trList]
          rw [ih]

/-- One source alphabet cell embedded in the fixed four-stack tape track. -/
private def stackCell (symbol : Turing.PartrecToTM2.Γ') : Symbol :=
  (false, Function.update (fun _ => none)
    Turing.PartrecToTM2.K'.main (some symbol))

private theorem stackCell_primrec : Primrec stackCell :=
  Primrec.dom_finite stackCell

/-- Mark the first multiplexed cell as the common stack bottom. -/
private def markBottom (cell : Symbol) : Symbol :=
  (true, cell.2)

private theorem markBottom_primrec : Primrec markBottom :=
  Primrec.dom_finite markBottom

/-- The fixed TM2-to-TM1 input translation is primitive recursive. -/
theorem translatedInput_primrec : Primrec translatedInput := by
  have reversed : Primrec fun input : List Nat =>
      (Turing.PartrecToTM2.trList input).reverse :=
    Primrec.list_reverse.comp trList_primrec
  have cells : Primrec fun input : List Nat =>
      (Turing.PartrecToTM2.trList input).reverse.map stackCell :=
    Primrec.list_map reversed
      ((stackCell_primrec.comp Primrec.snd).to₂)
  have tail : Primrec fun input : List Nat =>
      ((Turing.PartrecToTM2.trList input).reverse.map stackCell).tail :=
    Primrec.list_tail.comp cells
  have first : Primrec fun input : List Nat =>
      markBottom
        ((Turing.PartrecToTM2.trList input).reverse.map stackCell).headI :=
    markBottom_primrec.comp (Primrec.list_headI.comp cells)
  exact (Primrec.list_cons.comp first tail).of_eq fun input => by
    simp only [translatedInput, Turing.TM2to1.trInit]
    rfl

/-- Canonical local tape with a supplied list extending to the right. -/
noncomputable def tapeFromList (symbols : List Symbol) : Tape Symbol :=
  ⟨symbols.headI, none, Side.ofList symbols.tail⟩

private theorem sideOfList_primrec :
    Primrec (Side.ofList : List Symbol → Side Symbol) := by
  have step : Primrec fun data :
      List Symbol × (Symbol × Side Symbol) =>
        Side.cons data.2.1 data.2.2 :=
    Side.cons_uniform_primrec.comp
      ((Primrec.fst.comp Primrec.snd).pair
        (Primrec.snd.comp Primrec.snd))
  exact (Primrec.list_foldr Primrec.id (Primrec.const none) step.to₂).of_eq
    fun symbols => by
      induction symbols with
      | nil => rfl
      | cons head tail ih =>
          simp only [List.foldr_cons, Side.ofList]
          rw [ih]

/-- Building the canonical right-extending tape is primitive recursive. -/
theorem tapeFromList_primrec : Primrec tapeFromList := by
  have head : Primrec fun symbols : List Symbol => symbols.headI :=
    Primrec.list_headI
  have right : Primrec fun symbols : List Symbol => Side.ofList symbols.tail :=
    sideOfList_primrec.comp Primrec.list_tail
  exact (Tape.equivRep_symm_primrec.comp
    (head.pair ((Primrec.const none).pair right))).of_eq fun _ => rfl

/-- The executable canonical tape constructor agrees with the semantic tape
bridge used in `FiniteSource.initial`. -/
theorem tapeFromList_eq (symbols : List Symbol) :
    tapeFromList symbols =
      TapeBridge.tapeToLocal (Turing.Tape.mk₁ symbols) := by
  cases symbols with
  | nil => rfl
  | cons head tail => rfl

/-- `initial` is the executable canonical-list constructor after expanding
the fixed input translation. -/
theorem initial_eq_tapeFromList (input : List Nat) :
    initial input =
      (⟨initialState, tapeFromList (translatedInput input)⟩ :
        Config State Symbol) := by
  apply congrArg (fun tape => (⟨initialState, tape⟩ : Config State Symbol))
  exact (tapeFromList_eq (translatedInput input)).symm

/-- Initial configuration generation is primitive recursive jointly in a
source program and its natural-number input. -/
theorem initial_joint_primrec :
    Primrec fun data : Nat.Partrec.Code × Nat =>
      initial (UniversalSource.encodedInput data.1 data.2).1 := by
  have input : Primrec fun data : Nat.Partrec.Code × Nat =>
      translatedInput (UniversalSource.encodedInput data.1 data.2).1 :=
    translatedInput_primrec.comp
      (Primrec.vector_toList.comp UniversalSource.encodedInput_joint_primrec)
  have tape : Primrec fun data : Nat.Partrec.Code × Nat =>
      tapeFromList
        (translatedInput (UniversalSource.encodedInput data.1 data.2).1) :=
    tapeFromList_primrec.comp input
  have config : Primrec fun data : Nat.Partrec.Code × Nat =>
      (⟨initialState,
        tapeFromList
          (translatedInput (UniversalSource.encodedInput data.1 data.2).1)⟩ :
        Config State Symbol) :=
    Config.equivRep_symm_primrec.comp
      ((Primrec.const initialState).pair tape)
  exact config.of_eq fun data =>
    (initial_eq_tapeFromList
      (UniversalSource.encodedInput data.1 data.2).1).symm

/-- Initial configuration generation is computable jointly in source program
and input. -/
theorem initial_joint_computable :
    Computable fun data : Nat.Partrec.Code × Nat =>
      initial (UniversalSource.encodedInput data.1 data.2).1 :=
  initial_joint_primrec.to_comp

/-- The fixed-input start map used by the halting reduction is primitive
recursive. -/
theorem initial_primrec (input : Nat) :
    Primrec fun code : Nat.Partrec.Code =>
      initial (UniversalSource.encodedInput code input).1 :=
  by
    have composed := initial_joint_primrec.comp
      (Primrec.id.pair (Primrec.const input))
    exact composed.of_eq fun _ => rfl

end Lecerf.Machine.Compiler.FiniteSource
