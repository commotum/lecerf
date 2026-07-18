import Lecerf.Machine.Tape
import Mathlib.Computability.TuringMachine.Tape

/-!
# Bridge from mathlib tapes to canonical project tapes

Mathlib represents a one-sided tape as a quotient of finite lists by trailing
blank extension.  The project instead stores the unique finite-support normal
form.  This module proves that the two representations are equivalent and
that the equivalence commutes with reading, writing, and both head moves.
-/

namespace Lecerf.Machine.Compiler.TapeBridge

variable {Γ : Type*} [Inhabited Γ] [DecidableEq Γ]

theorem side_ofList_replicate_blank (count : ℕ) :
    Side.ofList (List.replicate count (default : Γ)) = none := by
  induction count with
  | zero => rfl
  | succ count ih => simp [List.replicate_succ, Side.ofList, Side.cons, ih]

theorem side_ofList_append_blanks (cells : List Γ) (count : ℕ) :
    Side.ofList (cells ++ List.replicate count (default : Γ)) = Side.ofList cells := by
  induction cells with
  | nil => exact side_ofList_replicate_blank count
  | cons head tail ih => simp only [List.cons_append, Side.ofList]; rw [ih]

/-- Canonicalize a quotient half-tape into the project's finite-support side. -/
def blankToSide (blank : Turing.ListBlank Γ) : Side Γ := by
  refine blank.liftOn Side.ofList ?_
  intro first second hExt
  rcases hExt with ⟨count, rfl⟩
  exact (side_ofList_append_blanks first count).symm

/-- Embed the project's canonical side into mathlib's quotient half-tape. -/
def sideToBlank (side : Side Γ) : Turing.ListBlank Γ :=
  Turing.ListBlank.mk side.cells

@[simp]
theorem blankToSide_mk (cells : List Γ) :
    blankToSide (Turing.ListBlank.mk cells) = Side.ofList cells := rfl

@[simp]
theorem blankToSide_sideToBlank (side : Side Γ) :
    blankToSide (sideToBlank side) = side := by
  simp [sideToBlank, Side.ofList_cells]

@[simp]
theorem sideToBlank_blankToSide (blank : Turing.ListBlank Γ) :
    sideToBlank (blankToSide blank) = blank := by
  induction blank using Turing.ListBlank.induction_on with
  | h cells =>
      simp only [blankToSide_mk, sideToBlank]
      apply Quotient.sound'
      apply Or.inl
      -- `Side.ofList` removes exactly a finite suffix of blanks.
      induction cells with
      | nil => exact ⟨0, rfl⟩
      | cons head tail ih =>
          rcases ih with ⟨count, ih⟩
          cases sideResult : Side.ofList tail with
          | none =>
              have tailEq : tail = List.replicate count (default : Γ) := by
                simpa [sideResult, Side.cells] using ih
              by_cases headBlank : head = default
              · subst head
                refine ⟨count + 1, ?_⟩
                rw [Side.ofList, sideResult]
                rw [show Side.cons (default : Γ) (none : Side Γ) = none by
                  simp [Side.cons]]
                simp only [Side.cells, List.nil_append]
                simpa only [List.replicate_succ] using
                  congrArg (List.cons (default : Γ)) tailEq
              · refine ⟨count, ?_⟩
                rw [Side.ofList, sideResult]
                simp only [Side.cons, dif_neg headBlank, Side.cells, List.nil_append,
                  List.singleton_append]
                exact congrArg (List.cons head) tailEq
          | some side =>
              rcases side with ⟨far, near⟩
              refine ⟨count, ?_⟩
              simpa [Side.ofList, Side.cons, sideResult, Side.cells,
                List.cons_append] using congrArg (List.cons head) ih

/-- Equivalence between mathlib quotient half-tapes and canonical project
half-tapes. -/
def sideEquiv : Turing.ListBlank Γ ≃ Side Γ where
  toFun := blankToSide
  invFun := sideToBlank
  left_inv := sideToBlank_blankToSide
  right_inv := blankToSide_sideToBlank

@[simp]
theorem blankToSide_head (blank : Turing.ListBlank Γ) :
    Side.head (blankToSide blank) = blank.head := by
  induction blank using Turing.ListBlank.induction_on with
  | h cells =>
      cases cells with
      | nil => rfl
      | cons head tail =>
          change Side.head (Side.ofList (head :: tail)) = _
          rw [Side.ofList]
          exact Side.head_cons head (Side.ofList tail)

@[simp]
theorem blankToSide_cons (head : Γ) (blank : Turing.ListBlank Γ) :
    blankToSide (blank.cons head) = Side.cons head (blankToSide blank) := by
  induction blank using Turing.ListBlank.induction_on with
  | h cells => rfl

@[simp]
theorem blankToSide_tail (blank : Turing.ListBlank Γ) :
    Side.tail (blankToSide blank) = blankToSide blank.tail := by
  rw [← blank.cons_head_tail]
  simp only [Turing.ListBlank.tail_cons, blankToSide_cons, Side.tail_cons]

@[simp]
theorem sideToBlank_head (side : Side Γ) :
    (sideToBlank side).head = Side.head side := by
  simpa using (blankToSide_head (sideToBlank side)).symm

@[simp]
theorem sideToBlank_cons (head : Γ) (side : Side Γ) :
    sideToBlank (Side.cons head side) = (sideToBlank side).cons head := by
  apply sideEquiv.injective
  change blankToSide (sideToBlank (Side.cons head side)) =
    blankToSide ((sideToBlank side).cons head)
  rw [blankToSide_sideToBlank, blankToSide_cons,
    blankToSide_sideToBlank]

@[simp]
theorem sideToBlank_tail (side : Side Γ) :
    sideToBlank (Side.tail side) = (sideToBlank side).tail := by
  apply sideEquiv.injective
  change blankToSide (sideToBlank (Side.tail side)) =
    blankToSide (sideToBlank side).tail
  rw [blankToSide_sideToBlank, ← blankToSide_tail,
    blankToSide_sideToBlank]

/-- Canonicalize both sides of a mathlib tape. -/
def tapeToLocal (tape : Turing.Tape Γ) : Tape Γ :=
  ⟨tape.head, blankToSide tape.left, blankToSide tape.right⟩

/-- Embed a canonical project tape into mathlib's quotient representation. -/
def tapeToMathlib (tape : Tape Γ) : Turing.Tape Γ :=
  ⟨tape.head, sideToBlank tape.left, sideToBlank tape.right⟩

@[simp]
theorem tapeToMathlib_head (tape : Tape Γ) :
    (tapeToMathlib tape).head = tape.head :=
  rfl

/-- Equivalence between complete mathlib and project tapes. -/
def tapeEquiv : Turing.Tape Γ ≃ Tape Γ where
  toFun := tapeToLocal
  invFun := tapeToMathlib
  left_inv := by intro tape; cases tape; simp [tapeToLocal, tapeToMathlib]
  right_inv := by intro tape; cases tape; simp [tapeToLocal, tapeToMathlib]

@[simp]
theorem tapeToLocal_tapeToMathlib (tape : Tape Γ) :
    tapeToLocal (tapeToMathlib tape) = tape :=
  tapeEquiv.apply_symm_apply tape

@[simp]
theorem tapeToMathlib_tapeToLocal (tape : Turing.Tape Γ) :
    tapeToMathlib (tapeToLocal tape) = tape :=
  tapeEquiv.symm_apply_apply tape

@[simp]
theorem tapeToLocal_write (symbol : Γ) (tape : Turing.Tape Γ) :
    tapeToLocal (tape.write symbol) = Tape.write symbol (tapeToLocal tape) := by
  cases tape
  rfl

@[simp]
theorem tapeToMathlib_write (symbol : Γ) (tape : Tape Γ) :
    tapeToMathlib (Tape.write symbol tape) =
      (tapeToMathlib tape).write symbol := by
  cases tape
  rfl

@[simp]
theorem tapeToLocal_move_left (tape : Turing.Tape Γ) :
    tapeToLocal (tape.move Turing.Dir.left) = Tape.move .left (tapeToLocal tape) := by
  cases tape
  simp [tapeToLocal, Turing.Tape.move, Tape.move,
    blankToSide_head, blankToSide_tail]

@[simp]
theorem tapeToMathlib_move_left (tape : Tape Γ) :
    tapeToMathlib (Tape.move .left tape) =
      (tapeToMathlib tape).move Turing.Dir.left := by
  cases tape
  simp [tapeToMathlib, Tape.move, Turing.Tape.move]

@[simp]
theorem tapeToLocal_move_right (tape : Turing.Tape Γ) :
    tapeToLocal (tape.move Turing.Dir.right) = Tape.move .right (tapeToLocal tape) := by
  cases tape
  simp [tapeToLocal, Turing.Tape.move, Tape.move,
    blankToSide_head, blankToSide_tail]

@[simp]
theorem tapeToMathlib_move_right (tape : Tape Γ) :
    tapeToMathlib (Tape.move .right tape) =
      (tapeToMathlib tape).move Turing.Dir.right := by
  cases tape
  simp [tapeToMathlib, Tape.move, Turing.Tape.move]

end Lecerf.Machine.Compiler.TapeBridge
