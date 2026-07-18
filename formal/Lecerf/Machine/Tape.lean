import Mathlib.Computability.Primrec.List

/-!
# Canonical finite-support tapes

The alphabet's `default` value is blank. A half-tape is either entirely blank
or stores a nearest-first finite prefix whose farthest stored cell is
certifiably nonblank. Thus infinitely many trailing blanks have one structural
representative rather than a quotient representation.
-/

namespace Lecerf.Machine

/-- A tape symbol certified not to be blank. -/
abbrev Nonblank (Γ : Type*) [Inhabited Γ] := { symbol : Γ // symbol ≠ default }

instance nonblankPrimcodable (Γ : Type*) [Inhabited Γ] [Primcodable Γ]
    [DecidableEq Γ] : Primcodable (Nonblank Γ) :=
  Primcodable.subtype ((Primrec.eq.comp Primrec.id (Primrec.const default)).not)

/-- A canonical half-tape. `some (far, near)` denotes the nearest-first cells
`near ++ [far]`; `far` is structurally nonblank. -/
abbrev Side (Γ : Type*) [Inhabited Γ] := Option (Nonblank Γ × List Γ)

namespace Side

variable {Γ : Type*} [Inhabited Γ]

/-- The finite nearest-first cell list represented by a side. -/
def cells : Side Γ → List Γ
  | none => []
  | some (far, near) => near ++ [far.1]

/-- The nearest cell, or blank for an empty side. -/
def head : Side Γ → Γ
  | none => default
  | some (far, []) => far.1
  | some (_, symbol :: _) => symbol

/-- Remove the nearest cell. -/
def tail : Side Γ → Side Γ
  | none => none
  | some (_, []) => none
  | some (far, _ :: near) => some (far, near)

/-- Add a nearest cell, normalizing a lone blank back to the empty side. -/
def cons [DecidableEq Γ] (symbol : Γ) : Side Γ → Side Γ
  | none => if h : symbol = default then none else some (⟨symbol, h⟩, [])
  | some (far, near) => some (far, symbol :: near)

@[simp]
theorem head_cons [DecidableEq Γ] (symbol : Γ) (side : Side Γ) :
    head (cons symbol side) = symbol := by
  rcases side with _ | ⟨far, near⟩
  · simp only [cons]
    split <;> simp_all [head]
  · rfl

@[simp]
theorem tail_cons [DecidableEq Γ] (symbol : Γ) (side : Side Γ) :
    tail (cons symbol side) = side := by
  rcases side with _ | ⟨far, near⟩
  · simp only [cons]
    split <;> simp_all [tail]
  · rfl

@[simp]
theorem cons_head_tail [DecidableEq Γ] (side : Side Γ) :
    cons (head side) (tail side) = side := by
  rcases side with _ | ⟨far, near⟩
  · simp [head, tail, cons]
  · cases near with
    | nil => simp [head, tail, cons, far.2]
    | cons _ _ => rfl

/-- Normalize a finite nearest-first list by deleting its trailing blanks. -/
def ofList [DecidableEq Γ] : List Γ → Side Γ
  | [] => none
  | symbol :: rest => cons symbol (ofList rest)

@[simp]
theorem ofList_cells [DecidableEq Γ] (side : Side Γ) :
    ofList (cells side) = side := by
  rcases side with _ | ⟨far, near⟩
  · rfl
  · induction near with
    | nil => simp [cells, ofList, cons, far.2]
    | cons symbol near ih =>
        simp only [cells, List.cons_append, ofList]
        change ofList (near ++ [far.1]) = some (far, near) at ih
        rw [ih]
        rfl

theorem cells_injective [DecidableEq Γ] :
    Function.Injective (cells : Side Γ → List Γ) :=
  Function.LeftInverse.injective ofList_cells

end Side

/-- A doubly infinite tape with finite nonblank support. The two sides are
stored nearest-cell first. -/
structure Tape (Γ : Type*) [Inhabited Γ] where
  head : Γ
  left : Side Γ
  right : Side Γ
  deriving DecidableEq

namespace Tape

variable {Γ : Type*} [Inhabited Γ]

/-- Structural representation used to obtain a computable code for tapes. -/
def equivRep : Tape Γ ≃ Γ × Side Γ × Side Γ where
  toFun tape := (tape.head, tape.left, tape.right)
  invFun data := ⟨data.1, data.2.1, data.2.2⟩
  left_inv := by intro tape; cases tape; rfl
  right_inv := by intro data; rcases data with ⟨head, left, right⟩; rfl

instance [Primcodable Γ] [DecidableEq Γ] : Primcodable (Tape Γ) :=
  Primcodable.ofEquiv (Γ × Side Γ × Side Γ) equivRep

/-- Head movement after the read/write phase. -/
inductive Move
  | left
  | stay
  | right
  deriving DecidableEq, Inhabited, Repr

namespace Move

/-- Opposite movement. -/
def reverse : Move → Move
  | .left => .right
  | .stay => .stay
  | .right => .left

@[simp]
theorem reverse_reverse (direction : Move) : direction.reverse.reverse = direction := by
  cases direction <;> rfl

/-- A computable three-element representation of movements. -/
def equivOptionBool : Move ≃ Option Bool where
  toFun
    | .left => none
    | .stay => some false
    | .right => some true
  invFun
    | none => .left
    | some false => .stay
    | some true => .right
  left_inv := by intro direction; cases direction <;> rfl
  right_inv := by intro code; cases code with
    | none => rfl
    | some bit => cases bit <;> rfl

end Move

instance : Primcodable Move :=
  Primcodable.ofEquiv (Option Bool) Move.equivOptionBool

/-- Shift the head without changing tape contents. -/
def move [DecidableEq Γ] : Move → Tape Γ → Tape Γ
  | .left, ⟨symbol, left, right⟩ =>
      ⟨left.head, left.tail, right.cons symbol⟩
  | .stay, tape => tape
  | .right, ⟨symbol, left, right⟩ =>
      ⟨right.head, left.cons symbol, right.tail⟩

/-- Replace the scanned symbol without moving. -/
def write (symbol : Γ) (tape : Tape Γ) : Tape Γ := { tape with head := symbol }

/-- The paper convention: write first, then move. -/
def act [DecidableEq Γ] (writeSymbol : Γ) (direction : Move) (tape : Tape Γ) : Tape Γ :=
  move direction (write writeSymbol tape)

@[simp]
theorem move_left_right [DecidableEq Γ] (tape : Tape Γ) :
    move .right (move .left tape) = tape := by
  rcases tape with ⟨symbol, left, right⟩
  simp [move]

@[simp]
theorem move_right_left [DecidableEq Γ] (tape : Tape Γ) :
    move .left (move .right tape) = tape := by
  rcases tape with ⟨symbol, left, right⟩
  simp [move]

@[simp]
theorem move_stay [DecidableEq Γ] (tape : Tape Γ) : move .stay tape = tape := rfl

@[simp]
theorem move_reverse_move [DecidableEq Γ] (direction : Move) (tape : Tape Γ) :
    move direction.reverse (move direction tape) = tape := by
  cases direction <;> simp [Move.reverse]

@[simp]
theorem move_move_reverse [DecidableEq Γ] (direction : Move) (tape : Tape Γ) :
    move direction (move direction.reverse tape) = tape := by
  cases direction <;> simp [Move.reverse]

@[simp]
theorem write_head (symbol : Γ) (tape : Tape Γ) : (write symbol tape).head = symbol := rfl

@[simp]
theorem write_self (tape : Tape Γ) : write tape.head tape = tape := by
  cases tape
  rfl

@[simp]
theorem write_write (first second : Γ) (tape : Tape Γ) :
    write second (write first tape) = write second tape := by
  cases tape
  rfl

@[simp]
theorem write_restore (symbol : Γ) (tape : Tape Γ) :
    write tape.head (write symbol tape) = tape := by
  cases tape
  rfl

/-- Undoing a write/move action requires moving back before restoring the old
scanned symbol. -/
theorem undo_act [DecidableEq Γ] (symbol : Γ) (direction : Move) (tape : Tape Γ) :
    write tape.head (move direction.reverse (act symbol direction tape)) = tape := by
  rw [act, move_reverse_move, write_restore]

/-- Canonical cell lists and the scanned symbol determine a tape. -/
theorem ext_cells [DecidableEq Γ] {first second : Tape Γ}
    (head : first.head = second.head)
    (left : first.left.cells = second.left.cells)
    (right : first.right.cells = second.right.cells) : first = second := by
  have hleft := Side.cells_injective left
  have hright := Side.cells_injective right
  cases first
  cases second
  simp_all

end Tape

end Lecerf.Machine
