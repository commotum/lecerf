import Lecerf.Machine.Core
import Lecerf.Machine.TwoTape.Reversible
import Mathlib.Data.Fintype.Option
import Mathlib.Data.Fintype.Prod
import Mathlib.Data.Fintype.Sum

/-!
# Finite two-tape history compiler

This module gives only the finite syntax of a history-recording simulation.
The first tape is the source work tape.  The second tape starts with a bottom
marker immediately to the left of its blank head and records one complete
source rule per successful source step.  Separate control states make each
microstep locally visible for the later reversibility and reachability proofs.
-/

namespace Lecerf.Machine.TwoTape.HistoryCompiler

open Lecerf.Machine

universe u v

/-- History symbols: blank, the left boundary, or a recorded source rule. -/
inductive Mark (Q : Type u) (Γ : Type v)
  | blank
  | bottom
  | token (rule : Lecerf.Machine.Rule Q Γ)

namespace Mark

variable {Q : Type u} {Γ : Type v}

/-- A sum-free representation used for all constructive instances below. -/
def equivRep : Mark Q Γ ≃ Option (Option (Lecerf.Machine.Rule Q Γ)) where
  toFun
    | .blank => none
    | .bottom => some none
    | .token rule => some (some rule)
  invFun
    | none => .blank
    | some none => .bottom
    | some (some rule) => .token rule
  left_inv := by intro mark; cases mark <;> rfl
  right_inv := by
    intro rep
    rcases rep with _ | (_ | rule) <;> rfl

instance [DecidableEq Q] [DecidableEq Γ] : DecidableEq (Mark Q Γ) :=
  equivRep.decidableEq

instance : Inhabited (Mark Q Γ) := ⟨.blank⟩

instance : Fintype Tape.Move :=
  Fintype.ofEquiv (Option Bool) Tape.Move.equivOptionBool.symm

instance [Fintype Q] [Fintype Γ] : Fintype (Lecerf.Machine.Rule Q Γ) :=
  Fintype.ofEquiv
    (Q × Γ × Q × Γ × Tape.Move) Lecerf.Machine.Rule.equivRep.symm

instance [Fintype Q] [Fintype Γ] : Fintype (Mark Q Γ) :=
  Fintype.ofEquiv
    (Option (Option (Lecerf.Machine.Rule Q Γ))) equivRep.symm

instance [Primcodable Q] [Primcodable Γ] : Primcodable (Mark Q Γ) :=
  Primcodable.ofEquiv
    (Option (Option (Lecerf.Machine.Rule Q Γ))) equivRep

end Mark

@[simp]
theorem default_mark {Q : Type u} {Γ : Type v} :
    (default : Mark Q Γ) = .blank :=
  rfl

/-- Control phases of the compiled history machine. -/
inductive Control (Q : Type u) (Γ : Type v)
  | forward (state : Q)
  | reverse (state : Q)
  | inspect (state : Q)
  | restore (rule : Lecerf.Machine.Rule Q Γ)

namespace Control

variable {Q : Type u} {Γ : Type v}

/-- Explicit tagged-sum representation of compiler control states. -/
def equivRep : Control Q Γ ≃
    Q ⊕ (Q ⊕ (Q ⊕ Lecerf.Machine.Rule Q Γ)) where
  toFun
    | .forward state => Sum.inl state
    | .reverse state => Sum.inr (Sum.inl state)
    | .inspect state => Sum.inr (Sum.inr (Sum.inl state))
    | .restore rule => Sum.inr (Sum.inr (Sum.inr rule))
  invFun
    | Sum.inl state => .forward state
    | Sum.inr (Sum.inl state) => .reverse state
    | Sum.inr (Sum.inr (Sum.inl state)) => .inspect state
    | Sum.inr (Sum.inr (Sum.inr rule)) => .restore rule
  left_inv := by intro control; cases control <;> rfl
  right_inv := by
    intro rep
    rcases rep with state | (state | (state | rule)) <;> rfl

instance [DecidableEq Q] [DecidableEq Γ] : DecidableEq (Control Q Γ) :=
  equivRep.decidableEq

instance [Fintype Q] [Fintype Γ] : Fintype (Control Q Γ) :=
  Fintype.ofEquiv
    (Q ⊕ (Q ⊕ (Q ⊕ Lecerf.Machine.Rule Q Γ))) equivRep.symm

instance [Primcodable Q] [Primcodable Γ] : Primcodable (Control Q Γ) :=
  Primcodable.ofEquiv
    (Q ⊕ (Q ⊕ (Q ⊕ Lecerf.Machine.Rule Q Γ))) equivRep

end Control

variable {Q : Type u} {Γ : Type v}

/-- Lift a source step while appending its complete rule to the history tape. -/
def forwardRule (rule : Lecerf.Machine.Rule Q Γ) :
    TwoTape.Rule (Control Q Γ) Γ (Mark Q Γ) where
  source := .forward rule.source
  read₁ := rule.read
  read₂ := .blank
  target := .forward rule.target
  write₁ := rule.write
  move₁ := rule.move
  write₂ := .token rule
  move₂ := .right

/-- Switch from the terminal source checkpoint into reverse execution. -/
def boundaryRule (state : Q) (symbol : Γ) :
    TwoTape.Rule (Control Q Γ) Γ (Mark Q Γ) where
  source := .forward state
  read₁ := symbol
  read₂ := .blank
  target := .reverse state
  write₁ := symbol
  move₁ := .stay
  write₂ := .blank
  move₂ := .stay

/-- Move the history head left to inspect the newest recorded token. -/
def scanRule (state : Q) (symbol : Γ) :
    TwoTape.Rule (Control Q Γ) Γ (Mark Q Γ) where
  source := .reverse state
  read₁ := symbol
  read₂ := .blank
  target := .inspect state
  write₁ := symbol
  move₁ := .stay
  write₂ := .blank
  move₂ := .left

/-- Select the predecessor rule from its recorded token and move the work
head back before restoring the overwritten symbol. -/
def inspectRule (rule : Lecerf.Machine.Rule Q Γ) (symbol : Γ) :
    TwoTape.Rule (Control Q Γ) Γ (Mark Q Γ) where
  source := .inspect rule.target
  read₁ := symbol
  read₂ := .token rule
  target := .restore rule
  write₁ := symbol
  move₁ := rule.move.reverse
  write₂ := .token rule
  move₂ := .stay

/-- Restore the old source symbol, erase the consumed history token, and
resume scanning in the predecessor state. -/
def restoreRule (rule : Lecerf.Machine.Rule Q Γ) :
    TwoTape.Rule (Control Q Γ) Γ (Mark Q Γ) where
  source := .restore rule
  read₁ := rule.write
  read₂ := .token rule
  target := .reverse rule.source
  write₁ := rule.read
  move₁ := .stay
  write₂ := .blank
  move₂ := .stay

/-- Close the return gadget at the bottom marker. -/
def bottomRule (state : Q) (symbol : Γ) :
    TwoTape.Rule (Control Q Γ) Γ (Mark Q Γ) where
  source := .inspect state
  read₁ := symbol
  read₂ := .bottom
  target := .forward state
  write₁ := symbol
  move₁ := .stay
  write₂ := .bottom
  move₂ := .right

section Enumeration

variable [Fintype Q] [Fintype Γ] [DecidableEq Q] [DecidableEq Γ]

/-- One lifted forward instruction for every source-table entry. -/
def forwardRules (machine : Lecerf.Machine.FiniteMachine Q Γ) :
    List (TwoTape.Rule (Control Q Γ) Γ (Mark Q Γ)) :=
  machine.rules.map forwardRule

/-- Terminal switches, enumerated exactly at absent source lookup keys. -/
noncomputable def boundaryRules (machine : Lecerf.Machine.FiniteMachine Q Γ) :
    List (TwoTape.Rule (Control Q Γ) Γ (Mark Q Γ)) :=
  (Finset.univ : Finset Q).toList.flatMap fun state =>
    (Finset.univ : Finset Γ).toList.filterMap fun symbol =>
      if machine.lookup state symbol = none then
        some (boundaryRule state symbol)
      else
        none

/-- Scan rules for every finite state/symbol pair. -/
noncomputable def scanRules : List (TwoTape.Rule (Control Q Γ) Γ (Mark Q Γ)) :=
  (Finset.univ : Finset Q).toList.flatMap fun state =>
    (Finset.univ : Finset Γ).toList.map fun symbol => scanRule state symbol

/-- Token-inspection rules for every source entry and possible scanned work
symbol. -/
noncomputable def inspectRules (machine : Lecerf.Machine.FiniteMachine Q Γ) :
    List (TwoTape.Rule (Control Q Γ) Γ (Mark Q Γ)) :=
  machine.rules.flatMap fun rule =>
    (Finset.univ : Finset Γ).toList.map fun symbol => inspectRule rule symbol

/-- One restoration instruction for every source-table entry. -/
def restoreRules (machine : Lecerf.Machine.FiniteMachine Q Γ) :
    List (TwoTape.Rule (Control Q Γ) Γ (Mark Q Γ)) :=
  machine.rules.map restoreRule

/-- Bottom-marker closure rules for every finite state/symbol pair. -/
noncomputable def bottomRules : List (TwoTape.Rule (Control Q Γ) Γ (Mark Q Γ)) :=
  (Finset.univ : Finset Q).toList.flatMap fun state =>
    (Finset.univ : Finset Γ).toList.map fun symbol => bottomRule state symbol

/-- The forward-only history-recording simulation. -/
def historyMachine (machine : Lecerf.Machine.FiniteMachine Q Γ) :
    TwoTape.FiniteMachine (Control Q Γ) Γ (Mark Q Γ) :=
  ⟨forwardRules machine⟩

/-- The open forward/turnaround/reverse machine.  It stops when the bottom
marker is exposed. -/
noncomputable def turnaroundMachine (machine : Lecerf.Machine.FiniteMachine Q Γ) :
    TwoTape.FiniteMachine (Control Q Γ) Γ (Mark Q Γ) :=
  ⟨forwardRules machine ++ boundaryRules machine ++ scanRules ++
    inspectRules machine ++ restoreRules machine⟩

/-- The closed return machine, obtained by adding the bottom-marker rules. -/
noncomputable def returnMachine (machine : Lecerf.Machine.FiniteMachine Q Γ) :
    TwoTape.FiniteMachine (Control Q Γ) Γ (Mark Q Γ) :=
  ⟨(turnaroundMachine machine).rules ++ bottomRules⟩

end Enumeration

/-- Blank history tape with its bottom marker immediately to the left. -/
def initialHistory [DecidableEq Q] [DecidableEq Γ] : Tape (Mark Q Γ) where
  head := .blank
  left := Side.cons .bottom none
  right := none

/-- Fresh forward checkpoint for a source configuration. -/
def checkpoint [Inhabited Γ] [DecidableEq Q] [DecidableEq Γ]
    (config : Lecerf.Machine.Config Q Γ) :
    TwoTape.Config (Control Q Γ) Γ (Mark Q Γ) where
  state := .forward config.state
  tape₁ := config.tape
  tape₂ := initialHistory

/-- Reverse checkpoint reached after all recorded source rules are undone. -/
def reverseCheckpoint [Inhabited Γ] [DecidableEq Q] [DecidableEq Γ]
    (config : Lecerf.Machine.Config Q Γ) :
    TwoTape.Config (Control Q Γ) Γ (Mark Q Γ) where
  state := .reverse config.state
  tape₁ := config.tape
  tape₂ := initialHistory

/-- Open-machine target obtained by scanning left from the reverse checkpoint
onto the bottom marker. -/
def bottomTarget [Inhabited Γ] [DecidableEq Q] [DecidableEq Γ]
    (config : Lecerf.Machine.Config Q Γ) :
    TwoTape.Config (Control Q Γ) Γ (Mark Q Γ) where
  state := .inspect config.state
  tape₁ := config.tape
  tape₂ := Tape.move .left initialHistory

@[simp] theorem initialHistory_head [DecidableEq Q] [DecidableEq Γ] :
    (initialHistory : Tape (Mark Q Γ)).head = .blank := rfl

@[simp] theorem checkpoint_state [Inhabited Γ] [DecidableEq Q] [DecidableEq Γ]
    (config : Lecerf.Machine.Config Q Γ) :
    (checkpoint config).state = .forward config.state := rfl

@[simp] theorem checkpoint_tape₁ [Inhabited Γ] [DecidableEq Q] [DecidableEq Γ]
    (config : Lecerf.Machine.Config Q Γ) :
    (checkpoint config).tape₁ = config.tape := rfl

@[simp] theorem reverseCheckpoint_state [Inhabited Γ]
    [DecidableEq Q] [DecidableEq Γ]
    (config : Lecerf.Machine.Config Q Γ) :
    (reverseCheckpoint config).state = .reverse config.state := rfl

@[simp] theorem bottomTarget_state [Inhabited Γ]
    [DecidableEq Q] [DecidableEq Γ]
    (config : Lecerf.Machine.Config Q Γ) :
    (bottomTarget config).state = .inspect config.state := rfl

@[simp] theorem bottomTarget_history_head [Inhabited Γ]
    [DecidableEq Q] [DecidableEq Γ]
    (config : Lecerf.Machine.Config Q Γ) :
    (bottomTarget config).tape₂.head = .bottom := by
  simp [bottomTarget, initialHistory, Tape.move]

@[simp] theorem forwardRules_rules [Fintype Q] [Fintype Γ]
    [DecidableEq Q] [DecidableEq Γ]
    (machine : Lecerf.Machine.FiniteMachine Q Γ) :
    (historyMachine machine).rules = machine.rules.map forwardRule := rfl

@[simp] theorem returnMachine_rules [Fintype Q] [Fintype Γ]
    [DecidableEq Q] [DecidableEq Γ]
    (machine : Lecerf.Machine.FiniteMachine Q Γ) :
    (returnMachine machine).rules =
      (turnaroundMachine machine).rules ++ bottomRules := rfl

end Lecerf.Machine.TwoTape.HistoryCompiler
