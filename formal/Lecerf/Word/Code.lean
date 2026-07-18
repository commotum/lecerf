import Mathlib.Algebra.FreeMonoid.Basic
import Mathlib.InformationTheory.Coding.UniquelyDecodable

/-!
# Indexed codes in a free monoid

This file keeps two notions of code distinct:

* `IsIndexedCode c` says that the substitution homomorphism induced by the
  indexed family `c` is injective; and
* `InformationTheory.UniquelyDecodable` is mathlib's predicate on a *set* of
  list-valued codewords.

A set forgets repeated indices.  Consequently the exact bridge between the
two predicates includes injectivity of the indexing map `c` as a separate
conjunct.
-/

namespace Lecerf

universe u v w

/-- A word over `A`, represented by mathlib's free monoid. -/
abbrev Word (A : Type u) := FreeMonoid A

namespace Word

variable {A : Type u} {I : Type v} {J : Type w}

/-- An indexed family of words is a code when substitution of its generators
extends to an injective homomorphism of free monoids. -/
def IsIndexedCode (c : I → Word A) : Prop :=
  Function.Injective (FreeMonoid.lift c)

/-- The set of underlying lists of an indexed family of codewords.

Unlike the indexed family itself, this set deliberately forgets duplicate
indices. -/
def codewordSet (c : I → Word A) : Set (List A) :=
  Set.range fun i ↦ (c i).toList

@[simp]
theorem mem_codewordSet_iff {c : I → Word A} {w : List A} :
    w ∈ codewordSet c ↔ ∃ i, (c i).toList = w :=
  Iff.rfl

/-- Expanding a list of generator indices and then viewing the result as a
list is the flattening of the corresponding list-valued codewords. -/
theorem toList_lift_ofList (c : I → Word A) (indices : List I) :
    (FreeMonoid.lift c (FreeMonoid.ofList indices)).toList =
      (indices.map fun i ↦ (c i).toList).flatten := by
  rw [FreeMonoid.lift_ofList, FreeMonoid.toList_prod]
  simp only [List.map_map, Function.comp_def]

/-- List form of substitution for an arbitrary word of indices. -/
theorem toList_lift (c : I → Word A) (indices : Word I) :
    (FreeMonoid.lift c indices).toList =
      (indices.toList.map fun i ↦ (c i).toList).flatten := by
  rw [FreeMonoid.lift_apply, FreeMonoid.toList_prod]
  simp only [List.map_map, Function.comp_def]

/-- Codehood already forces the indexed generator map to be injective. -/
theorem IsIndexedCode.injective {c : I → Word A} (hc : IsIndexedCode c) :
    Function.Injective c := by
  intro i j hij
  apply FreeMonoid.of_injective
  apply hc
  simpa only [FreeMonoid.lift_eval_of] using hij

/-- No generator of an indexed code can represent the empty word. -/
theorem IsIndexedCode.ne_one {c : I → Word A} (hc : IsIndexedCode c) (i : I) :
    c i ≠ 1 := by
  intro hi
  have heq : (FreeMonoid.of i : Word I) = 1 := by
    apply hc
    simp only [FreeMonoid.lift_eval_of, map_one, hi]
  exact FreeMonoid.of_ne_one i heq

private theorem exists_index_list
    (c : I → Word A) (words : List (List A))
    (hwords : ∀ w ∈ words, w ∈ codewordSet c) :
    ∃ indices : List I, (indices.map fun i ↦ (c i).toList) = words := by
  induction words with
  | nil => exact ⟨[], rfl⟩
  | cons w words ih =>
      rcases (mem_codewordSet_iff.mp (hwords w (by simp))) with ⟨i, hi⟩
      rcases ih (fun x hx ↦ hwords x (by simp [hx])) with ⟨indices, hindices⟩
      refine ⟨i :: indices, ?_⟩
      simp only [List.map_cons]
      rw [hi, hindices]

/-- An indexed code gives a uniquely decodable set of underlying codewords. -/
theorem IsIndexedCode.uniquelyDecodable {c : I → Word A} (hc : IsIndexedCode c) :
    InformationTheory.UniquelyDecodable (codewordSet c) := by
  intro words₁ words₂ hwords₁ hwords₂ hflatten
  rcases exists_index_list c words₁ hwords₁ with ⟨indices₁, hindices₁⟩
  rcases exists_index_list c words₂ hwords₂ with ⟨indices₂, hindices₂⟩
  have hlift :
      FreeMonoid.lift c (FreeMonoid.ofList indices₁) =
        FreeMonoid.lift c (FreeMonoid.ofList indices₂) := by
    apply FreeMonoid.toList.injective
    rw [toList_lift_ofList, toList_lift_ofList, hindices₁, hindices₂]
    exact hflatten
  have hindices : indices₁ = indices₂ :=
    FreeMonoid.ofList.injective (hc hlift)
  calc
    words₁ = indices₁.map (fun i ↦ (c i).toList) := hindices₁.symm
    _ = indices₂.map (fun i ↦ (c i).toList) := congrArg _ hindices
    _ = words₂ := hindices₂

/-- Injectivity of the indexed family together with unique decodability of its
underlying set recovers injectivity of the induced free-monoid homomorphism. -/
theorem isIndexedCode_of_injective_of_uniquelyDecodable
    {c : I → Word A} (hc : Function.Injective c)
    (hud : InformationTheory.UniquelyDecodable (codewordSet c)) :
    IsIndexedCode c := by
  intro indices₁ indices₂ hlift
  have hflatten :
      (indices₁.toList.map fun i ↦ (c i).toList).flatten =
        (indices₂.toList.map fun i ↦ (c i).toList).flatten := by
    simpa only [toList_lift] using congrArg FreeMonoid.toList hlift
  have hmem₁ :
      ∀ w ∈ indices₁.toList.map (fun i ↦ (c i).toList), w ∈ codewordSet c := by
    intro w hw
    rcases List.mem_map.mp hw with ⟨i, _, rfl⟩
    exact ⟨i, rfl⟩
  have hmem₂ :
      ∀ w ∈ indices₂.toList.map (fun i ↦ (c i).toList), w ∈ codewordSet c := by
    intro w hw
    rcases List.mem_map.mp hw with ⟨i, _, rfl⟩
    exact ⟨i, rfl⟩
  have hmapped := hud _ _ hmem₁ hmem₂ hflatten
  have hwordLists : Function.Injective (fun i ↦ (c i).toList) :=
    FreeMonoid.toList.injective.comp hc
  exact FreeMonoid.toList.injective (hwordLists.list_map hmapped)

/-- Exact bridge from indexed codehood to mathlib's set-based predicate.

The first conjunct is essential: `codewordSet` identifies duplicate indices,
whereas `IsIndexedCode` must distinguish the corresponding generators. -/
theorem isIndexedCode_iff_injective_and_uniquelyDecodable {c : I → Word A} :
    IsIndexedCode c ↔
      Function.Injective c ∧
        InformationTheory.UniquelyDecodable
          (Set.range fun i ↦ (c i).toList) := by
  change IsIndexedCode c ↔
    Function.Injective c ∧ InformationTheory.UniquelyDecodable (codewordSet c)
  constructor
  · intro hc
    exact ⟨hc.injective, hc.uniquelyDecodable⟩
  · rintro ⟨hc, hud⟩
    exact isIndexedCode_of_injective_of_uniquelyDecodable hc hud

/-- Mapping letters through a function gives an injective free-monoid map
exactly when the function on letters is injective. -/
theorem freeMonoidMap_injective_iff (f : I → A) :
    Function.Injective (FreeMonoid.map f) ↔ Function.Injective f := by
  constructor
  · intro h i j hij
    apply FreeMonoid.of_injective
    apply h
    simpa only [FreeMonoid.map_of] using congrArg FreeMonoid.of hij
  · intro h x y hxy
    apply FreeMonoid.toList.injective
    apply h.list_map
    simpa only [FreeMonoid.toList_map] using congrArg FreeMonoid.toList hxy

/-- A family of one-letter words is a code exactly when its letter map is
injective. -/
theorem isIndexedCode_singleton_iff (f : I → A) :
    IsIndexedCode (fun i ↦ FreeMonoid.of (f i)) ↔ Function.Injective f := by
  unfold IsIndexedCode
  rw [FreeMonoid.lift_of_comp_eq_map]
  exact freeMonoidMap_injective_iff f

/-- The canonical one-letter family is an indexed code. -/
theorem isIndexedCode_of :
    IsIndexedCode (FreeMonoid.of : I → Word I) := by
  simpa using (isIndexedCode_singleton_iff (id : I → I)).2 Function.injective_id

/-- Reindexing before substitution is substitution after mapping the index
word. -/
theorem lift_map (c : I → Word A) (f : J → I) (indices : Word J) :
    FreeMonoid.lift c (FreeMonoid.map f indices) =
      FreeMonoid.lift (fun j ↦ c (f j)) indices := by
  have homEq :
      (FreeMonoid.lift c).comp (FreeMonoid.map f) =
        FreeMonoid.lift (fun j ↦ c (f j)) := by
    apply FreeMonoid.hom_eq
    intro j
    simp
  exact DFunLike.ext_iff.mp homEq indices

/-- Substituting through an injective reindexing preserves indexed codehood. -/
theorem IsIndexedCode.comp {c : I → Word A} (hc : IsIndexedCode c)
    {f : J → I} (hf : Function.Injective f) :
    IsIndexedCode (fun j ↦ c (f j)) := by
  intro x y hxy
  apply (freeMonoidMap_injective_iff f).2 hf
  apply hc
  simpa only [lift_map] using hxy

end Word

end Lecerf
