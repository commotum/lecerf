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

namespace IsPrefixCode

/-- A prefix code is prefix-free. -/
theorem prefixFree {c : I → Word A} (hc : IsPrefixCode c) :
    IsPrefixFree c :=
  hc.1

/-- A prefix code has no empty generator. -/
theorem ne_one {c : I → Word A} (hc : IsPrefixCode c) (i : I) :
    c i ≠ 1 :=
  hc.2 i

/-- Every indexed prefix code is an indexed code. -/
theorem isIndexedCode {c : I → Word A} (hc : IsPrefixCode c) :
    IsIndexedCode c := by
  rw [isIndexedCode_iff_flattenCode_injective]
  intro xs
  induction xs with
  | nil =>
      intro ys hxy
      cases ys with
      | nil => rfl
      | cons j ys =>
          simp only [flattenCode, List.map_nil, List.flatten_nil,
            List.map_cons, List.flatten_cons] at hxy
          have hjnil : (c j).toList = [] :=
            (List.append_eq_nil_iff.mp hxy.symm).1
          exact False.elim <| hc.ne_one j <|
            FreeMonoid.toList.injective <| by simpa using hjnil
  | cons i xs ih =>
      intro ys hxy
      cases ys with
      | nil =>
          simp only [flattenCode, List.map_nil, List.flatten_nil,
            List.map_cons, List.flatten_cons] at hxy
          have hinil : (c i).toList = [] :=
            (List.append_eq_nil_iff.mp hxy).1
          exact False.elim <| hc.ne_one i <|
            FreeMonoid.toList.injective <| by simpa using hinil
      | cons j ys =>
          simp only [flattenCode, List.map_cons, List.flatten_cons] at hxy
          have hij : i = j := by
            by_cases hlength : (c i).toList.length ≤ (c j).toList.length
            · apply hc.prefixFree
              apply (List.isPrefix_append_of_length hlength).mp
              rw [← hxy]
              exact List.prefix_append _ _
            · have hlength' : (c j).toList.length ≤ (c i).toList.length :=
                Nat.le_of_lt (Nat.lt_of_not_ge hlength)
              symm
              apply hc.prefixFree
              apply (List.isPrefix_append_of_length hlength').mp
              rw [hxy]
              exact List.prefix_append _ _
          subst j
          congr 1
          exact ih (List.append_cancel_left hxy)

end IsPrefixCode

namespace IsSuffixCode

/-- A suffix code is suffix-free. -/
theorem suffixFree {c : I → Word A} (hc : IsSuffixCode c) :
    IsSuffixFree c :=
  hc.1

/-- A suffix code has no empty generator. -/
theorem ne_one {c : I → Word A} (hc : IsSuffixCode c) (i : I) :
    c i ≠ 1 :=
  hc.2 i

/-- Every indexed suffix code is an indexed code. -/
theorem isIndexedCode {c : I → Word A} (hc : IsSuffixCode c) :
    IsIndexedCode c := by
  have hprefix : IsPrefixCode (fun i ↦ reverse (c i)) := by
    constructor
    · intro i j hij
      exact hc.suffixFree (List.reverse_prefix.mp hij)
    · intro i hi
      apply hc.ne_one i
      have := congrArg reverse hi
      simpa only [reverse_reverse, reverse_one] using this
  exact isIndexedCode_reverse_iff.mp hprefix.isIndexedCode

end IsSuffixCode

/-! ## Fresh-marker extensions -/

/-- The initial run of indices from the left summand. -/
private def leadingLeft : List (I ⊕ J) → List I
  | [] => []
  | Sum.inl i :: rest => i :: leadingLeft rest
  | Sum.inr _ :: _ => []

/-- The first right-summand index and the unconsumed tail, if one exists. -/
private def firstRight : List (I ⊕ J) → Option (J × List (I ⊕ J))
  | [] => none
  | Sum.inl _ :: rest => firstRight rest
  | Sum.inr j :: rest => some (j, rest)

private theorem leadingLeft_firstRight_reconstruct (indices : List (I ⊕ J)) :
    (leadingLeft indices).map (Sum.inl : I → I ⊕ J) ++
        match firstRight indices with
        | none => []
        | some (j, rest) => Sum.inr j :: rest =
      indices := by
  induction indices with
  | nil => rfl
  | cons index indices ih =>
      cases index with
      | inl i =>
          simp only [leadingLeft, firstRight, List.map_cons, List.cons_append]
          rw [ih]
      | inr j => rfl

private theorem firstRight_tail_length_lt {indices : List (I ⊕ J)}
    {j : J} {rest : List (I ⊕ J)}
    (h : firstRight indices = some (j, rest)) : rest.length < indices.length := by
  induction indices with
  | nil => simp [firstRight] at h
  | cons index indices ih =>
      cases index with
      | inl i =>
          simp only [firstRight] at h
          exact Nat.lt.step (ih h)
      | inr j' =>
          simp only [firstRight, Option.some.injEq, Prod.mk.injEq] at h
          rcases h with ⟨_, rfl⟩
          simp

private theorem marker_not_mem_flattenCode {marker : A} {c : I → Word A}
    (hfresh : FreshFor marker c) (indices : List I) :
    marker ∉ flattenCode c indices := by
  induction indices with
  | nil => simp [flattenCode]
  | cons i indices ih =>
      simp only [flattenCode, List.map_cons, List.flatten_cons,
        List.mem_append, not_or]
      exact ⟨hfresh i, ih⟩

private theorem flattenCode_prependMarkerExtension
    (marker : A) (c : I → Word A) (k : J → Word A)
    (indices : List (I ⊕ J)) :
    flattenCode (prependMarkerExtension marker c k) indices =
      flattenCode c (leadingLeft indices) ++
        match firstRight indices with
        | none => []
        | some (j, rest) =>
            marker :: ((k j).toList ++
              flattenCode (prependMarkerExtension marker c k) rest) := by
  induction indices with
  | nil => simp [flattenCode, leadingLeft, firstRight]
  | cons index indices ih =>
      cases index with
      | inl i =>
          simp only [flattenCode, prependMarkerExtension, leadingLeft,
            firstRight, List.map_cons, List.flatten_cons]
          rw [ih]
          simp only [List.append_assoc]
      | inr j =>
          simp [flattenCode, prependMarkerExtension, leadingLeft, firstRight]

private theorem append_marker_unique
    {marker : A} {left right left' right' : List A}
    (hfresh : marker ∉ left) (hfresh' : marker ∉ left')
    (h : left ++ marker :: right = left' ++ marker :: right') :
    left = left' ∧ right = right' := by
  induction left generalizing left' with
  | nil =>
      cases left' with
      | nil =>
          simp only [List.nil_append, List.cons.injEq, true_and] at h ⊢
          exact h
      | cons a left' =>
          simp only [List.nil_append, List.cons_append, List.cons.injEq] at h
          exact False.elim <| hfresh' <| by simp [← h.1]
  | cons a left ih =>
      cases left' with
      | nil =>
          simp only [List.cons_append, List.nil_append, List.cons.injEq] at h
          exact False.elim <| hfresh <| by simp [h.1]
      | cons b left' =>
          simp only [List.cons_append, List.cons.injEq] at h
          have hfreshTail : marker ∉ left := by
            simpa only [List.mem_cons, not_or] using hfresh |>.2
          have hfreshTail' : marker ∉ left' := by
            simpa only [List.mem_cons, not_or] using hfresh' |>.2
          rcases ih hfreshTail hfreshTail' h.2 with ⟨hle, hre⟩
          exact ⟨by simp [h.1, hle], hre⟩

end Lecerf.Word
