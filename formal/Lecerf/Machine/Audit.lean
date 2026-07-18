import Lecerf.Machine.Reversible

/-!
# Machine-semantics diagnostics

Concrete checks for canonical blank normalization, read-write-move execution,
the failure of the paper's printed tuple inverse, and the distinction between
individually reversible rules and a reversible whole table.
-/

namespace Lecerf.Machine.Audit

open Lecerf.Transition

/-- The paper's printed inverse tuple: exchange source/target and read/write,
then reverse the movement sign. This is syntax for the audit only. -/
def printedInverse {Q Γ : Type*} (rule : Rule Q Γ) : Rule Q Γ :=
  ⟨rule.target, rule.write, rule.source, rule.read, rule.move.reverse⟩

example : Side.ofList [true, false, false] = Side.ofList [true] := by
  decide

def movingRule : Rule Bool Bool :=
  ⟨false, false, true, true, .right⟩

def start : Config Bool Bool := Config.blank false

def afterMove : Config Bool Bool :=
  ⟨true, ⟨false, some (⟨true, by decide⟩, []), none⟩⟩

/-- The selected convention really is read, then write, then move right. -/
example : movingRule.apply start = some afterMove := by
  decide

/-- The repaired semantic inverse moves left before checking/restoring. -/
example : movingRule.undo afterMove = some start := by
  decide

/-- The printed tuple tries to read the written symbol before moving back, so
it is not enabled on the actual successor configuration. -/
theorem printedInverse_fails_on_moving_rule :
    (printedInverse movingRule).apply afterMove = none := by
  decide

def firstMergeRule : Rule Bool Bool :=
  ⟨false, false, true, false, .stay⟩

def secondMergeRule : Rule Bool Bool :=
  ⟨true, false, true, false, .stay⟩

def mergeMachine : FiniteMachine Bool Bool :=
  ⟨[firstMergeRule, secondMergeRule]⟩

def firstPredecessor : Config Bool Bool := Config.blank false
def secondPredecessor : Config Bool Bool := Config.blank true
def merged : Config Bool Bool := Config.blank true

example : mergeMachine.TableDeterministic := by
  intro first firstMem second secondMem sourceEq readEq
  simp [mergeMachine] at firstMem secondMem
  rcases firstMem with rfl | rfl <;> rcases secondMem with rfl | rfl
  · rfl
  · simp [firstMergeRule, secondMergeRule] at sourceEq
  · simp [firstMergeRule, secondMergeRule] at sourceEq
  · rfl

example : mergeMachine.step firstPredecessor = some merged := by
  decide

example : mergeMachine.step secondPredecessor = some merged := by
  decide

/-- Both table entries are individually partial equivalences, but their union
merges two configurations and is therefore not a reversible machine. -/
theorem mergeMachine_not_reversible : ¬mergeMachine.Reversible := by
  intro reversible
  have firstStep : StepRel mergeMachine.step firstPredecessor merged := by
    change merged ∈ mergeMachine.step firstPredecessor
    rw [show mergeMachine.step firstPredecessor = some merged by decide]
    simp
  have secondStep : StepRel mergeMachine.step secondPredecessor merged := by
    change merged ∈ mergeMachine.step secondPredecessor
    rw [show mergeMachine.step secondPredecessor = some merged by decide]
    simp
  have predecessorsEqual : firstPredecessor = secondPredecessor :=
    reversible.2 firstStep secondStep
  have statesEqual := congrArg Config.state predecessorsEqual
  exact Bool.false_ne_true statesEqual

end Lecerf.Machine.Audit
