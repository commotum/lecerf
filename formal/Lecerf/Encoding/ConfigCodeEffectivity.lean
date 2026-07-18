import Lecerf.Encoding.ConfigCode
import Mathlib.Computability.Partrec

/-!
# Effectivity of self-delimiting configuration codes

The executable codec in `Lecerf.Encoding.ConfigCode` is uniformly primitive
recursive.  This leaf also installs the `Primcodable` structure on free-monoid
words induced by their definitional equivalence with lists; word-valued
effectivity statements below use exactly that representation.
-/

namespace Lecerf.Encoding.ConfigCode

open Lecerf.Word

universe u

/-- Free-monoid words inherit the primitive-recursive list representation. -/
instance wordPrimcodable (A : Type u) [Primcodable A] : Primcodable (Word A) :=
  Primcodable.ofEquiv (List A) FreeMonoid.toList

/-- Converting a word to its list representation is primitive recursive. -/
theorem wordToList_primrec {A : Type u} [Primcodable A] :
    Primrec (FreeMonoid.toList : Word A → List A) := by
  exact Primrec.of_equiv

/-- Converting a list to the corresponding word is primitive recursive. -/
theorem wordOfList_primrec {A : Type u} [Primcodable A] :
    Primrec (FreeMonoid.ofList : List A → Word A) := by
  exact Primrec.of_equiv_symm

/-- Canonical unary framing is primitive recursive. -/
theorem unaryFrame_primrec : Primrec unaryFrame := by
  have htrue : Primrec (fun n : Nat ↦ (List.range n).map fun _ ↦ true) :=
    Primrec.list_map Primrec.list_range (Primrec.const true).to₂
  exact (Primrec.list_concat.comp htrue (Primrec.const false)).of_eq fun n ↦ by
    simp [unaryFrame_eq_replicate_append]

private theorem unaryFrame_length (n : Nat) : (unaryFrame n).length = n + 1 := by
  induction n with
  | zero => rfl
  | succ n ih => simp [unaryFrame, ih]

/-- Exact unary-frame decoding is primitive recursive. -/
theorem decodeUnaryFrame_primrec : Primrec decodeUnaryFrame := by
  let candidate : List Bool → Nat := fun bits ↦ bits.length.pred
  have hcandidate : Primrec candidate :=
    Primrec.pred.comp Primrec.list_length
  have hcanonical : PrimrecPred fun bits : List Bool ↦
      bits = unaryFrame (candidate bits) :=
    Primrec.eq.comp Primrec.id (unaryFrame_primrec.comp hcandidate)
  have hrhs : Primrec fun bits : List Bool ↦
      if bits = unaryFrame (candidate bits) then some (candidate bits) else none :=
    Primrec.ite hcanonical (Primrec.option_some.comp hcandidate)
      (Primrec.const none)
  exact hrhs.of_eq fun bits ↦ by
    by_cases hcanonicalBits : bits = unaryFrame (candidate bits)
    · rw [if_pos hcanonicalBits]
      conv_rhs => rw [hcanonicalBits]
      simp
    · rw [if_neg hcanonicalBits]
      cases hdecode : decodeUnaryFrame bits with
      | none => rfl
      | some n =>
          exfalso
          have hbits : bits = unaryFrame n :=
            decodeUnaryFrame_eq_some_iff.mp hdecode
          apply hcanonicalBits
          rw [hbits]
          simp [candidate, unaryFrame_length]

variable {C : Type u} [Primcodable C]

/-- Configuration bit-list encoding is primitive recursive. -/
theorem encodeConfigBits_primrec :
    Primrec (encodeConfigBits : C → List Bool) := by
  exact unaryFrame_primrec.comp Primrec.encode

/-- Exact configuration bit-list decoding is primitive recursive. -/
theorem decodeConfigBits_primrec :
    Primrec (decodeConfigBits : List Bool → Option C) := by
  exact Primrec.option_bind decodeUnaryFrame_primrec
    (Primrec.decode₂.comp Primrec.snd).to₂

/-- Word-valued configuration encoding is primitive recursive. -/
theorem encodeConfig_primrec :
    Primrec (encodeConfig : C → Word Bool) := by
  exact wordOfList_primrec.comp encodeConfigBits_primrec

/-- Exact word-valued configuration decoding is primitive recursive. -/
theorem decodeConfig_primrec :
    Primrec (decodeConfig : Word Bool → Option C) := by
  exact decodeConfigBits_primrec.comp wordToList_primrec

/-- Encoding a list of configurations as concatenated bit frames is primitive
recursive. -/
theorem encodeConfigListBits_primrec :
    Primrec (encodeConfigListBits : List C → List Bool) := by
  exact Primrec.list_flatten.comp <|
    Primrec.list_map Primrec.id
      (encodeConfigBits_primrec.comp Primrec.snd).to₂

/-- Word-valued concatenated encoding is primitive recursive. -/
theorem encodeConfigs_primrec :
    Primrec (encodeConfigs : List C → Word Bool) := by
  exact wordOfList_primrec.comp encodeConfigListBits_primrec

/-! ## A primitive-recursive fold realization of the concatenation parser -/

private abbrev DecodeFoldState (C : Type u) := Option (List C) × Nat

/-- Left-to-right parser transition.  The list component is stored in reverse
order so that accepting a decoded frame uses only `List.cons`. -/
private def decodeFoldStep (state : DecodeFoldState C) (bit : Bool) :
    DecodeFoldState C :=
  if bit then
    (state.1, state.2 + 1)
  else
    match state.1, Encodable.decode₂ C state.2 with
    | some configs, some config => (some (config :: configs), 0)
    | _, _ => (none, 0)

/-- Accept only at a frame boundary and restore source order. -/
private def finishDecodeFold (state : DecodeFoldState C) : Option (List C) :=
  if state.2 = 0 then state.1.map List.reverse else none

/-- Fold-based realization used solely to certify primitive recursiveness of
the structurally recursive public decoder. -/
private def decodeConfigListBitsFold (bits : List Bool) : Option (List C) :=
  finishDecodeFold (bits.foldl decodeFoldStep (some [], 0))

private theorem finishDecodeFold_foldl_none (bits : List Bool) (count : Nat) :
    finishDecodeFold
        (bits.foldl decodeFoldStep ((none, count) : DecodeFoldState C)) = none := by
  induction bits generalizing count with
  | nil => simp [finishDecodeFold]
  | cons bit bits ih =>
      cases bit <;> simp [decodeFoldStep, ih]

private theorem finishDecodeFold_foldl_some
    (bits : List Bool) (configsRev : List C) (count : Nat) :
    finishDecodeFold
        (bits.foldl decodeFoldStep (some configsRev, count)) =
      (decodeConfigListBitsAux count bits).map
        (fun configs ↦ configsRev.reverse ++ configs) := by
  induction bits generalizing configsRev count with
  | nil =>
      cases count <;> simp [finishDecodeFold, decodeConfigListBitsAux]
  | cons bit bits ih =>
      cases bit with
      | true =>
          simpa [decodeFoldStep, decodeConfigListBitsAux] using
            ih configsRev (count + 1)
      | false =>
          cases hdecode : Encodable.decode₂ C count with
          | none =>
              simp [decodeFoldStep, decodeConfigListBitsAux, hdecode,
                finishDecodeFold_foldl_none]
          | some config =>
              simpa [decodeFoldStep, decodeConfigListBitsAux, hdecode,
                List.reverse_cons, List.append_assoc, Function.comp_apply] using
                ih (config :: configsRev) 0

private theorem decodeConfigListBitsFold_eq (bits : List Bool) :
    decodeConfigListBitsFold (C := C) bits = decodeConfigListBits bits := by
  simpa [decodeConfigListBitsFold, decodeConfigListBits] using
    finishDecodeFold_foldl_some (C := C) bits [] 0

end Lecerf.Encoding.ConfigCode
