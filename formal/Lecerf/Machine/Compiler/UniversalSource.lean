import Mathlib.Computability.TuringMachine.ToPartrec

/-!
# A fixed universal partial-recursive TM2 program

This module isolates the one nonconstructive choice used to obtain a fixed
`Turing.ToPartrec.Code` which interprets `Nat.Partrec.Code` programs.  The
chosen program is a closed constant: source programs and their inputs are not
compiled by choice, but are supplied through the primitive-recursive encoder
`encodedInput`.

The exact code semantics and the induced TM2 halting semantics are both
recorded below.  This does **not** yet compile mathlib's TM2 program to
`Lecerf.Machine.FiniteMachine`; that separate finite-syntax compiler must
preserve the equivalences proved here.
-/

namespace Lecerf.Machine.Compiler.UniversalSource

open Encodable Denumerable
open Turing

/-- The binary partial function interpreted by the fixed universal program.
The first component is decoded as a `Nat.Partrec.Code`; the second is its
input. -/
def universalNatEval (input : List.Vector Nat 2) : Part Nat :=
  Nat.Partrec.Code.eval
    (ofNat Nat.Partrec.Code input.head)
    input.tail.head

/-- The universal evaluator is partial recursive in its two natural-number
arguments. -/
theorem universalNatEval_partrec' : Nat.Partrec' universalNatEval := by
  have h : Partrec₂ fun code : Nat => fun input : Nat =>
      Nat.Partrec.Code.eval (ofNat Nat.Partrec.Code code) input :=
    Nat.Partrec.Code.eval_part.comp
      ((Computable.ofNat Nat.Partrec.Code).comp Computable.fst)
      Computable.snd
  exact (Nat.Partrec'.part_iff₂.mpr h).of_eq fun input => rfl

/-- A `ToPartrec.Code` exists which implements `universalNatEval`. -/
theorem exists_universalCode :
    ∃ universal : Turing.ToPartrec.Code,
      ∀ input : List.Vector Nat 2,
        universal.eval input.1 = pure <$> universalNatEval input :=
  Turing.ToPartrec.Code.exists_code universalNatEval_partrec'

/-- A single fixed universal `ToPartrec.Code`.

This is the only classical choice in this module.  It selects one closed
program once; it is not a noncomputable map from source codes to target
machines. -/
noncomputable def universalCode : Turing.ToPartrec.Code :=
  Classical.choose exists_universalCode

/-- Specification inherited from the witness selected by `universalCode`. -/
theorem universalCode_spec (input : List.Vector Nat 2) :
    universalCode.eval input.1 = pure <$> universalNatEval input :=
  Classical.choose_spec exists_universalCode input

/-- Encode a source program and its input as the two natural numbers expected
by `universalCode`. -/
def encodedInput (code : Nat.Partrec.Code) (input : Nat) : List.Vector Nat 2 :=
  encode code ::ᵥ input ::ᵥ List.Vector.nil

@[simp]
theorem encodedInput_head (code : Nat.Partrec.Code) (input : Nat) :
    (encodedInput code input).head = encode code :=
  rfl

@[simp]
theorem encodedInput_tail_head (code : Nat.Partrec.Code) (input : Nat) :
    (encodedInput code input).tail.head = input :=
  rfl

/-- Encoding both a source program and its input is primitive recursive. -/
theorem encodedInput_joint_primrec :
    Primrec fun data : Nat.Partrec.Code × Nat =>
      encodedInput data.1 data.2 := by
  have tail : Primrec (fun data : Nat.Partrec.Code × Nat =>
      (data.2 ::ᵥ List.Vector.nil : List.Vector Nat 1)) :=
    Primrec.vector_cons.comp Primrec.snd
      (Primrec.const (List.Vector.nil : List.Vector Nat 0))
  exact (Primrec.vector_cons.comp
    (Primrec.encode.comp Primrec.fst) tail).of_eq fun _ => rfl

/-- Encoding both a source program and its input is computable. -/
theorem encodedInput_joint_computable :
    Computable fun data : Nat.Partrec.Code × Nat =>
      encodedInput data.1 data.2 :=
  encodedInput_joint_primrec.to_comp

/-- With an input fixed, source-program encoding remains primitive recursive. -/
theorem encodedInput_primrec (input : Nat) :
    Primrec fun code : Nat.Partrec.Code => encodedInput code input :=
  encodedInput_joint_primrec.comp
    (Primrec.id.pair (Primrec.const input))

/-- With a source program fixed, input encoding remains primitive recursive. -/
theorem encodedInput_forCode_primrec (code : Nat.Partrec.Code) :
    Primrec (encodedInput code) :=
  encodedInput_joint_primrec.comp
    ((Primrec.const code).pair Primrec.id)

/-- The selected universal code evaluates an encoded source program exactly:
its singleton output is the source program's partial output. -/
theorem universalCode_eval (code : Nat.Partrec.Code) (input : Nat) :
    universalCode.eval (encodedInput code input).1 =
      pure <$> Nat.Partrec.Code.eval code input := by
  simpa [universalNatEval, encodedInput] using
    universalCode_spec (encodedInput code input)

/-- Code-level definedness is preserved and reflected by the fixed universal
program. -/
theorem universalCode_eval_dom_iff (code : Nat.Partrec.Code) (input : Nat) :
    (universalCode.eval (encodedInput code input).1).Dom ↔
      (Nat.Partrec.Code.eval code input).Dom := by
  rw [universalCode_eval]
  simp

/-- Initial TM2 configuration for the selected universal program on an
encoded source program and input. -/
noncomputable def initialConfig
    (code : Nat.Partrec.Code) (input : Nat) : Turing.PartrecToTM2.Cfg' :=
  Turing.PartrecToTM2.init universalCode (encodedInput code input).1

/-- Exact evaluation of the fixed TM2 program.  The two maps wrap the source
result first as a singleton list and then as the canonical halting TM2
configuration. -/
theorem tm2_eval (code : Nat.Partrec.Code) (input : Nat) :
    StateTransition.eval
        (Turing.TM2.step Turing.PartrecToTM2.tr)
        (initialConfig code input) =
      Turing.PartrecToTM2.halt <$>
        (pure <$> Nat.Partrec.Code.eval code input) := by
  rw [initialConfig, Turing.PartrecToTM2.tr_eval, universalCode_eval]

/-- The fixed TM2 program halts exactly when the supplied
`Nat.Partrec.Code` halts on its supplied input. -/
theorem tm2_halts_iff_eval_dom (code : Nat.Partrec.Code) (input : Nat) :
    (StateTransition.eval
      (Turing.TM2.step Turing.PartrecToTM2.tr)
      (initialConfig code input)).Dom ↔
        (Nat.Partrec.Code.eval code input).Dom := by
  rw [tm2_eval]
  simp

end Lecerf.Machine.Compiler.UniversalSource
