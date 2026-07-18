import Lecerf.Word.API

/-!
# Audit checks for words, codes, and partial iteration

These examples are intentionally kept out of the public API.  They check the
distinctions most vulnerable to accidental weakening: indexed duplicates,
empty codewords, the paper's nonstandard epimorphism, partial ambient action,
and zero versus positive iteration.
-/

namespace Lecerf.Word.Audit

open Lecerf

/-! Indexed families remember duplicate indices. -/

example :
    ¬IsIndexedCode (fun _ : Bool ↦ (FreeMonoid.of () : Word Unit)) := by
  intro code
  have false_eq_true : false = true := code.injective rfl
  exact Bool.false_ne_true false_eq_true

/-! An empty generator is forbidden even for a singleton index type. -/

example : ¬IsIndexedCode (fun _ : Unit ↦ (1 : Word Bool)) := by
  intro code
  exact code.ne_one () rfl

/-! The paper's selector may repeat targets and omit other target generators. -/

private def sourceLetter : Bool → Fin 3
  | false => 0
  | true => 1

private theorem sourceLetter_injective : Function.Injective sourceLetter := by
  intro first second equal
  cases first <;> cases second <;> simp_all [sourceLetter]

private def sourceCodewords : Bool → Word (Fin 3) :=
  fun index ↦ FreeMonoid.of (sourceLetter index)

private def targetCodewords : Fin 3 → Word (Fin 3) :=
  FreeMonoid.of

private def repeatedSelector : Bool → Fin 3 :=
  fun _ ↦ 0

private theorem sourceCodewords_code : IsIndexedCode sourceCodewords :=
  (isIndexedCode_singleton_iff sourceLetter).mpr sourceLetter_injective

private theorem targetCodewords_code : IsIndexedCode targetCodewords :=
  isIndexedCode_of

private noncomputable def repeatedOmittingEpi : PaperCodeEpi (Fin 3) Bool (Fin 3) :=
  PaperCodeEpi.ofCodes sourceCodewords targetCodewords repeatedSelector
    sourceCodewords_code targetCodewords_code

example : repeatedOmittingEpi.selector false = repeatedOmittingEpi.selector true :=
  rfl

example : ∀ index, repeatedOmittingEpi.selector index ≠ (1 : Fin 3) := by
  intro index
  cases index <;> decide

/-! A code isomorphism acts only on its source-generated submonoid. -/

private def falseCodewords : Unit → Word Bool :=
  fun _ ↦ FreeMonoid.of false

private def trueCodewords : Unit → Word Bool :=
  fun _ ↦ FreeMonoid.of true

private theorem constantUnit_injective {X : Type} (value : X) :
    Function.Injective (fun _ : Unit ↦ value) := by
  intro first second _
  cases first
  cases second
  rfl

private theorem falseCodewords_code : IsIndexedCode falseCodewords :=
  (isIndexedCode_singleton_iff (fun _ : Unit ↦ false)).mpr
    (constantUnit_injective false)

private theorem trueCodewords_code : IsIndexedCode trueCodewords :=
  (isIndexedCode_singleton_iff (fun _ : Unit ↦ true)).mpr
    (constantUnit_injective true)

private noncomputable def falseToTrueIso : CodeIso Bool Unit :=
  CodeIso.ofCodes falseCodewords trueCodewords
    falseCodewords_code trueCodewords_code

private def containsNoTrue : Submonoid (Word Bool) where
  carrier := { word | true ∉ word }
  one_mem' := FreeMonoid.notMem_one
  mul_mem' := by
    intro left right leftFresh rightFresh
    intro member
    rcases FreeMonoid.mem_mul.mp member with leftMember | rightMember
    · exact leftFresh leftMember
    · exact rightFresh rightMember

private theorem true_not_mem_generated_false :
    FreeMonoid.of true ∉ generated falseCodewords := by
  intro member
  have generated_le : generated falseCodewords ≤ containsNoTrue := by
    apply Submonoid.closure_le.mpr
    rintro word ⟨index, rfl⟩
    change true ∉ falseCodewords index
    simp [falseCodewords]
  have fresh := generated_le member
  exact fresh FreeMonoid.mem_of_self

example : falseToTrueIso.toPEquiv (FreeMonoid.of true) = none := by
  apply CodeIso.toPEquiv_apply_of_not_mem
  change FreeMonoid.of true ∉ generated falseCodewords
  exact true_not_mem_generated_false

/-! Zero iteration is total reflexivity; positive iteration is not. -/

example :
    Lecerf.PEquiv.iterate (⊥ : Bool ≃. Bool) 0 true = some true :=
  rfl

example :
    Lecerf.PEquiv.positiveIterate (⊥ : Bool ≃. Bool) 0 true = none := by
  simp

end Lecerf.Word.Audit

#print axioms Lecerf.Word.isIndexedCode_iff_injective_and_uniquelyDecodable
#print axioms Lecerf.Word.isIndexedCode_prependMarkerExtension
#print axioms Lecerf.Word.isIndexedCode_appendMarkerExtension
#print axioms Lecerf.Word.CodeIso.toPEquiv_generator
#print axioms Lecerf.PEquiv.iterate_symm
#print axioms Lecerf.PEquiv.positiveIterate
#print axioms Lecerf.PEquiv.positiveIterate_symm
