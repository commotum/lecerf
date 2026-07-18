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
              simp only [List.foldl_cons, decodeFoldStep, Bool.false_eq_true,
                if_false, hdecode, decodeConfigListBitsAux]
              rw [ih (config :: configsRev) 0]
              cases decodeConfigListBitsAux (C := C) 0 bits <;>
                simp [List.reverse_cons, List.append_assoc]

private theorem decodeConfigListBitsFold_eq (bits : List Bool) :
    decodeConfigListBitsFold (C := C) bits = decodeConfigListBits bits := by
  simpa [decodeConfigListBitsFold, decodeConfigListBits] using
    finishDecodeFold_foldl_some (C := C) bits [] 0

private theorem decodeFoldStep_primrec :
    Primrec₂ (decodeFoldStep (C := C)) := by
  have hdecoded : Primrec fun data : DecodeFoldState C × List C ↦
      Encodable.decode₂ C data.1.2 :=
    Primrec.decode₂.comp (Primrec.snd.comp Primrec.fst)
  have hprepend : Primrec₂ fun (data : DecodeFoldState C × List C)
      (config : C) ↦ config :: data.2 :=
    (Primrec.list_cons.comp Primrec.snd
      (Primrec.snd.comp Primrec.fst)).to₂
  have hdecodeAndPrepend : Primrec fun data : DecodeFoldState C × List C ↦
      (Encodable.decode₂ C data.1.2).map fun config ↦ config :: data.2 :=
    Primrec.option_map hdecoded hprepend
  have haccept : Primrec fun state : DecodeFoldState C ↦
      state.1.bind fun configs ↦
        (Encodable.decode₂ C state.2).map fun config ↦ config :: configs :=
    Primrec.option_bind Primrec.fst hdecodeAndPrepend.to₂
  have hfalse : Primrec fun state : DecodeFoldState C ↦
      (state.1.bind (fun configs ↦
          (Encodable.decode₂ C state.2).map fun config ↦ config :: configs), 0) :=
    Primrec.pair haccept (Primrec.const 0)
  have htrue : Primrec fun state : DecodeFoldState C ↦
      (state.1, state.2 + 1) :=
    Primrec.pair Primrec.fst (Primrec.succ.comp Primrec.snd)
  apply Primrec₂.uncurry.mp
  exact (Primrec.cond Primrec.snd (htrue.comp Primrec.fst)
    (hfalse.comp Primrec.fst)).of_eq fun data ↦ by
      rcases data with ⟨state, bit⟩
      cases bit with
      | false =>
          cases hconfigs : state.1 <;>
            cases hconfig : Encodable.decode₂ C state.2 <;>
              simp [decodeFoldStep, hconfigs, hconfig]
      | true => rfl

private theorem finishDecodeFold_primrec :
    Primrec (finishDecodeFold (C := C)) := by
  have hboundary : PrimrecPred fun state : DecodeFoldState C ↦ state.2 = 0 :=
    Primrec.eq.comp Primrec.snd (Primrec.const 0)
  have haccept : Primrec fun state : DecodeFoldState C ↦
      state.1.map List.reverse :=
    Primrec.option_map Primrec.fst
      (Primrec.list_reverse.comp Primrec.snd).to₂
  exact (Primrec.ite hboundary haccept (Primrec.const none)).of_eq fun state ↦ by
    simp [finishDecodeFold]

private theorem decodeConfigListBitsFold_primrec :
    Primrec (decodeConfigListBitsFold (C := C)) := by
  have hfoldStep : Primrec₂ fun (_bits : List Bool)
      (data : DecodeFoldState C × Bool) ↦
      decodeFoldStep data.1 data.2 :=
    (decodeFoldStep_primrec.comp
      (Primrec.fst.comp Primrec.snd)
      (Primrec.snd.comp Primrec.snd)).to₂
  have hfold : Primrec fun bits : List Bool ↦
      bits.foldl decodeFoldStep ((some [], 0) : DecodeFoldState C) :=
    Primrec.list_foldl Primrec.id (Primrec.const (some [], 0)) hfoldStep
  exact finishDecodeFold_primrec.comp hfold

/-- Decoding an entire concatenation of configuration frames is primitive
recursive. -/
theorem decodeConfigListBits_primrec :
    Primrec (decodeConfigListBits : List Bool → Option (List C)) :=
  decodeConfigListBitsFold_primrec.of_eq decodeConfigListBitsFold_eq

/-- Decoding a word as an entire configuration-frame concatenation is
primitive recursive. -/
theorem decodeConfigs_primrec :
    Primrec (decodeConfigs : Word Bool → Option (List C)) := by
  exact decodeConfigListBits_primrec.comp wordToList_primrec

/-! ## Computability corollaries -/

theorem unaryFrame_computable : Computable unaryFrame :=
  unaryFrame_primrec.to_comp

theorem decodeUnaryFrame_computable : Computable decodeUnaryFrame :=
  decodeUnaryFrame_primrec.to_comp

theorem encodeConfigBits_computable :
    Computable (encodeConfigBits : C → List Bool) :=
  encodeConfigBits_primrec.to_comp

theorem decodeConfigBits_computable :
    Computable (decodeConfigBits : List Bool → Option C) :=
  decodeConfigBits_primrec.to_comp

theorem encodeConfig_computable :
    Computable (encodeConfig : C → Word Bool) :=
  encodeConfig_primrec.to_comp

theorem decodeConfig_computable :
    Computable (decodeConfig : Word Bool → Option C) :=
  decodeConfig_primrec.to_comp

theorem encodeConfigListBits_computable :
    Computable (encodeConfigListBits : List C → List Bool) :=
  encodeConfigListBits_primrec.to_comp

theorem decodeConfigListBits_computable :
    Computable (decodeConfigListBits : List Bool → Option (List C)) :=
  decodeConfigListBits_primrec.to_comp

theorem encodeConfigs_computable :
    Computable (encodeConfigs : List C → Word Bool) :=
  encodeConfigs_primrec.to_comp

theorem decodeConfigs_computable :
    Computable (decodeConfigs : Word Bool → Option (List C)) :=
  decodeConfigs_primrec.to_comp

end Lecerf.Encoding.ConfigCode
