import Lecerf.Word.Code
import Mathlib.Data.List.Infix

/-!
# Prefix and suffix codes

This module formalizes the fresh-marker criterion used in Lecerf's paper.
The paper's "right prefix-code" is modern prefix-freeness, and its left-handed
version is modern suffix-freeness.

Pairwise prefix- or suffix-freeness alone is not codehood: a singleton family
whose word is empty satisfies the pairwise condition.  `IsPrefixCode` and
`IsSuffixCode` therefore record nonemptiness explicitly.  The fresh-marker
extension theorems use the sharper hypotheses: the auxiliary family need only
be prefix- or suffix-free, because adjoining the marker makes all of its
extended words nonempty.
-/

namespace Lecerf.Word

universe u v w

variable {A : Type u} {I : Type v} {J : Type w}

/-- A letter is fresh for an indexed family when it occurs in none of its
words. -/
def FreshFor (marker : A) (c : I → Word A) : Prop :=
  ∀ i, marker ∉ c i

/-- Indexed prefix-freeness.  Equal words force equal indices as a special
case, but the empty word is not excluded. -/
def IsPrefixFree (c : I → Word A) : Prop :=
  ∀ ⦃i j : I⦄, (c i).toList <+: (c j).toList → i = j

/-- Indexed suffix-freeness.  Equal words force equal indices as a special
case, but the empty word is not excluded. -/
def IsSuffixFree (c : I → Word A) : Prop :=
  ∀ ⦃i j : I⦄, (c i).toList <:+ (c j).toList → i = j

/-- A genuine indexed prefix code: prefix-free with no empty generator. -/
def IsPrefixCode (c : I → Word A) : Prop :=
  IsPrefixFree c ∧ ∀ i, c i ≠ 1

/-- A genuine indexed suffix code: suffix-free with no empty generator. -/
def IsSuffixCode (c : I → Word A) : Prop :=
  IsSuffixFree c ∧ ∀ i, c i ≠ 1

/-- Add a fresh marker on the left of every word in the second family and take
the indexed disjoint union with the first family. -/
def prependMarkerExtension (marker : A) (c : I → Word A) (k : J → Word A) :
    I ⊕ J → Word A
  | Sum.inl i => c i
  | Sum.inr j => FreeMonoid.of marker * k j

/-- Add a fresh marker on the right of every word in the second family and take
the indexed disjoint union with the first family. -/
def appendMarkerExtension (marker : A) (c : I → Word A) (k : J → Word A) :
    I ⊕ J → Word A
  | Sum.inl i => c i
  | Sum.inr j => k j * FreeMonoid.of marker

/-- Word reversal, used to transfer the prefix construction to its suffix
dual. -/
def reverse (word : Word A) : Word A :=
  FreeMonoid.ofList word.toList.reverse

@[simp]
theorem toList_reverse (word : Word A) :
    (reverse word).toList = word.toList.reverse :=
  rfl

@[simp]
theorem reverse_reverse (word : Word A) : reverse (reverse word) = word := by
  apply FreeMonoid.toList.injective
  simp

@[simp]
theorem reverse_one : reverse (1 : Word A) = 1 := by
  apply FreeMonoid.toList.injective
  simp

@[simp]
theorem reverse_mul (left right : Word A) :
    reverse (left * right) = reverse right * reverse left := by
  apply FreeMonoid.toList.injective
  simp

@[simp]
theorem reverse_of (a : A) : reverse (FreeMonoid.of a) = FreeMonoid.of a := by
  apply FreeMonoid.toList.injective
  simp

private def flattenCode (c : I → Word A) (indices : List I) : List A :=
  (indices.map fun i ↦ (c i).toList).flatten

private theorem flattenCode_append (c : I → Word A) (xs ys : List I) :
    flattenCode c (xs ++ ys) = flattenCode c xs ++ flattenCode c ys := by
  simp [flattenCode]

private theorem isIndexedCode_iff_flattenCode_injective {c : I → Word A} :
    IsIndexedCode c ↔ Function.Injective (flattenCode c) := by
  constructor
  · intro hc xs ys hxy
    apply FreeMonoid.ofList.injective
    apply hc
    apply FreeMonoid.toList.injective
    simpa only [toList_lift_ofList, flattenCode] using hxy
  · intro hc xs ys hxy
    apply FreeMonoid.toList.injective
    apply hc
    simpa only [toList_lift, flattenCode] using
      congrArg FreeMonoid.toList hxy

private theorem flattenCode_reverse (c : I → Word A) (indices : List I) :
    flattenCode (fun i ↦ reverse (c i)) indices =
      (flattenCode c indices.reverse).reverse := by
  induction indices with
  | nil => simp [flattenCode]
  | cons i indices ih =>
      rw [List.reverse_cons, flattenCode_append, List.reverse_append]
      simpa only [flattenCode, List.map_cons, List.flatten_cons,
        List.map_nil, List.flatten_nil, List.append_nil, List.reverse_append,
        toList_reverse, List.reverse_reverse] using
        congrArg ((c i).toList.reverse ++ ·) ih

/-- Reversing every generator preserves indexed codehood. -/
theorem IsIndexedCode.reverse {c : I → Word A} (hc : IsIndexedCode c) :
    IsIndexedCode (fun i ↦ reverse (c i)) := by
  rw [isIndexedCode_iff_flattenCode_injective] at hc ⊢
  intro xs ys hxy
  rw [flattenCode_reverse, flattenCode_reverse] at hxy
  have hrev : flattenCode c xs.reverse = flattenCode c ys.reverse :=
    List.reverse_injective hxy
  exact List.reverse_injective (hc hrev)

/-- Reversing every generator preserves and reflects indexed codehood. -/
theorem isIndexedCode_reverse_iff {c : I → Word A} :
    IsIndexedCode (fun i ↦ reverse (c i)) ↔ IsIndexedCode c := by
  constructor
  · intro hc
    simpa only [reverse_reverse] using hc.reverse
  · exact IsIndexedCode.reverse

end Lecerf.Word
