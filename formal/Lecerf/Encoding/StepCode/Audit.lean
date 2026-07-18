import Lecerf.Encoding.StepCode.Correctness
import Lecerf.Encoding.StepCode.Interpreter
import Lecerf.Encoding.ConfigCodeEffectivity

/-!
# Machine-step code diagnostics

Non-public checks for the executable Boolean framing, all three movement
constructors of concrete one-rule two-tape machines, canonical blank
extension, terminal undefinedness, and the target-code boundary at a
deterministic but backward-nonunique merge.
-/

namespace Lecerf.Encoding.StepCode.Audit

open Lecerf.Machine
open Lecerf.Machine.TwoTape
open Lecerf.Transition
open Lecerf.Word

abbrev TestConfig := Lecerf.Machine.TwoTape.Config Bool Bool Bool
abbrev TestRule := Lecerf.Machine.TwoTape.Rule Bool Bool Bool
abbrev TestMachine := Lecerf.Machine.TwoTape.FiniteMachine Bool Bool Bool

/-! ## Frame diagnostics -/

/-- A run of `true` bits without its terminating `false` is rejected. -/
example : ConfigCode.decodeUnaryFrame [true, true] = none := by
  decide

/-- The exact single-frame decoder rejects data after a terminator. -/
example : ConfigCode.decodeUnaryFrame [false, true] = none := by
  decide

/-- Canonical unary frames decode to their supplied value. -/
example : ConfigCode.decodeUnaryFrame (ConfigCode.unaryFrame 4) = some 4 := by
  decide

/-- This is a syntactically complete unary frame, but natural code `1` is not
in the range of the pinned `Primcodable` representation of `TestConfig`.  The
configuration decoder therefore rejects it as noncanonical data. -/
example :
    ConfigCode.decodeConfigBits (C := TestConfig)
        (ConfigCode.unaryFrame 1) = none := by
  decide

def initial : TestConfig :=
  Lecerf.Machine.TwoTape.Config.blank false

/-- A canonical complete configuration frame round-trips. -/
example :
    ConfigCode.decodeConfig (ConfigCode.encodeConfig initial) = some initial := by
  exact ConfigCode.decodeConfig_encodeConfig initial

/-- The concatenated-frame parser also rejects an unterminated final frame. -/
example :
    ConfigCode.decodeConfigs (C := TestConfig)
        (FreeMonoid.ofList [true, true]) = none := by
  decide

/-- Canonical concatenated frames round-trip as a whole input. -/
example :
    ConfigCode.decodeConfigs
        (ConfigCode.encodeConfigs [initial, initial]) =
      some [initial, initial] := by
  simp

/-! ## All movement constructors -/

/-- One uniform rule shape, instantiated below at every tape movement.  Tape
two deliberately stays put, so the observed change on tape one isolates the
selected constructor. -/
def movementRule (direction : Tape.Move) : TestRule :=
  ⟨false, false, false, true, true, direction, false, .stay⟩

def movementMachine (direction : Tape.Move) : TestMachine :=
  ⟨[movementRule direction]⟩

def leftMachine : TestMachine := movementMachine .left
def stayMachine : TestMachine := movementMachine .stay
def rightMachine : TestMachine := movementMachine .right

/-- Expected result of the concrete one-rule machine at a supplied movement. -/
def movementTarget (direction : Tape.Move) : TestConfig :=
  ⟨true, initial.tape₁.act true direction,
    initial.tape₂.act false .stay⟩

theorem leftMachine_step :
    leftMachine.step initial = some (movementTarget .left) := by
  decide

theorem stayMachine_step :
    stayMachine.step initial = some (movementTarget .stay) := by
  decide

theorem rightMachine_step :
    rightMachine.step initial = some (movementTarget .right) := by
  decide

theorem leftMachine_reversible : leftMachine.Reversible :=
  (show leftMachine.SyntacticallyReversible by decide).reversible

theorem stayMachine_reversible : stayMachine.Reversible :=
  (show stayMachine.SyntacticallyReversible by decide).reversible

theorem rightMachine_reversible : rightMachine.Reversible :=
  (show rightMachine.SyntacticallyReversible by decide).reversible

/-- The semantic code isomorphism represents the `.left` machine step. -/
example :
    (stepCodeIso leftMachine leftMachine_reversible.2).toPEquiv
        (ConfigCode.encodeConfig initial) =
      some (ConfigCode.encodeConfig (movementTarget .left)) :=
  (stepCodeIso_apply_eq_some_iff leftMachine leftMachine_reversible.2
    initial (movementTarget .left)).mpr leftMachine_step

/-- The semantic code isomorphism represents the `.stay` machine step. -/
example :
    (stepCodeIso stayMachine stayMachine_reversible.2).toPEquiv
        (ConfigCode.encodeConfig initial) =
      some (ConfigCode.encodeConfig (movementTarget .stay)) :=
  (stepCodeIso_apply_eq_some_iff stayMachine stayMachine_reversible.2
    initial (movementTarget .stay)).mpr stayMachine_step

/-- The semantic code isomorphism represents the `.right` machine step. -/
example :
    (stepCodeIso rightMachine rightMachine_reversible.2).toPEquiv
        (ConfigCode.encodeConfig initial) =
      some (ConfigCode.encodeConfig (movementTarget .right)) :=
  (stepCodeIso_apply_eq_some_iff rightMachine rightMachine_reversible.2
    initial (movementTarget .right)).mpr rightMachine_step

/-- The executable frame interpreter covers the same concrete left move. -/
example :
    applyWord leftMachine.step (ConfigCode.encodeConfigs [initial]) =
      some (ConfigCode.encodeConfigs [movementTarget .left]) := by
  apply (applyWord_eq_some_iff leftMachine.step _ _).mpr
  exact ⟨[initial], [movementTarget .left], rfl,
    by simpa using leftMachine_step, rfl⟩

/-- The executable frame interpreter covers the same concrete stay move. -/
example :
    applyWord stayMachine.step (ConfigCode.encodeConfigs [initial]) =
      some (ConfigCode.encodeConfigs [movementTarget .stay]) := by
  apply (applyWord_eq_some_iff stayMachine.step _ _).mpr
  exact ⟨[initial], [movementTarget .stay], rfl,
    by simpa using stayMachine_step, rfl⟩

/-- The executable frame interpreter covers the same concrete right move. -/
example :
    applyWord rightMachine.step (ConfigCode.encodeConfigs [initial]) =
      some (ConfigCode.encodeConfigs [movementTarget .right]) := by
  apply (applyWord_eq_some_iff rightMachine.step _ _).mpr
  exact ⟨[initial], [movementTarget .right], rfl,
    by simpa using rightMachine_step, rfl⟩

/-! ## Blank extension and terminal failure -/

/-- Writing on an all-blank tape and moving right exposes a new blank scanned
cell while retaining the written nonblank cell on the normalized left side. -/
theorem rightMachine_blank_extension :
    (movementTarget .right).tape₁.head = false ∧
      (movementTarget .right).tape₁.left.cells = [true] := by
  decide

/-- The sole rule has source state `false`, so its target is terminal. -/
theorem rightMachine_target_terminal :
    rightMachine.step (movementTarget .right) = none := by
  decide

/-- Terminality is literal undefinedness of the semantic code action. -/
example :
    (stepCodeIso rightMachine rightMachine_reversible.2).toPEquiv
        (ConfigCode.encodeConfig (movementTarget .right)) = none :=
  (stepCodeIso_apply_eq_none_iff rightMachine rightMachine_reversible.2
    (movementTarget .right)).mpr rightMachine_target_terminal

/-- Terminality also remains failure in the executable frame interpreter. -/
example :
    applyWord rightMachine.step
        (ConfigCode.encodeConfigs [movementTarget .right]) = none := by
  have failed :
      traverse rightMachine.step [movementTarget .right] = none := by
    unfold traverse
    rw [rightMachine_target_terminal]
    rfl
  simp [applyWord, failed]

/-! ## Deterministic merge: target codehood really needs backward uniqueness -/

def firstMergeRule : TestRule :=
  ⟨false, false, false, true, false, .stay, false, .stay⟩

def secondMergeRule : TestRule :=
  ⟨true, false, false, true, false, .stay, false, .stay⟩

def mergeMachine : TestMachine :=
  ⟨[firstMergeRule, secondMergeRule]⟩

def firstPredecessor : TestConfig :=
  Lecerf.Machine.TwoTape.Config.blank false

def secondPredecessor : TestConfig :=
  Lecerf.Machine.TwoTape.Config.blank true

def merged : TestConfig :=
  Lecerf.Machine.TwoTape.Config.blank true

/-- The two rules have distinct forward states, hence distinct lookup keys. -/
theorem mergeMachine_deterministic : mergeMachine.TableDeterministic :=
  (FiniteMachine.pairwise_forwardPairValid_iff_tableDeterministic
    mergeMachine).mp (by decide)

theorem mergeMachine_first_step :
    mergeMachine.step firstPredecessor = some merged := by
  decide

theorem mergeMachine_second_step :
    mergeMachine.step secondPredecessor = some merged := by
  decide

/-- The deterministic first-match transition nevertheless merges two
successful predecessors. -/
theorem mergeMachine_not_backwardUnique :
    ¬BackwardUnique mergeMachine.step := by
  intro backward
  have firstStep : StepRel mergeMachine.step firstPredecessor merged := by
    change merged ∈ mergeMachine.step firstPredecessor
    rw [mergeMachine_first_step]
    simp
  have secondStep : StepRel mergeMachine.step secondPredecessor merged := by
    change merged ∈ mergeMachine.step secondPredecessor
    rw [mergeMachine_second_step]
    simp
  have predecessorsEqual : firstPredecessor = secondPredecessor :=
    backward firstStep secondStep
  exact Bool.false_ne_true (congrArg
    Lecerf.Machine.TwoTape.Config.state predecessorsEqual)

/-- Forward determinism still makes the merge's source-edge family a code. -/
example : IsIndexedCode (sourceWord (machine := mergeMachine)) :=
  sourceWord_isIndexedCode mergeMachine

/-- Its repeated successful target destroys indexed target codehood exactly
as characterized by the whole-step theorem. -/
theorem mergeMachine_targetWord_not_isIndexedCode :
    ¬IsIndexedCode (targetWord (machine := mergeMachine)) := by
  intro targetCode
  exact mergeMachine_not_backwardUnique
    ((targetWord_isIndexedCode_iff_backwardUnique mergeMachine).mp targetCode)

/-! ## Representative trust audit -/

#print axioms Lecerf.Encoding.ConfigCode.decodeConfigs_eq_some_iff
#print axioms Lecerf.Encoding.ConfigCode.encodeConfig_isIndexedCode
#print axioms Lecerf.Encoding.ConfigCode.encodeConfigs_primrec
#print axioms Lecerf.Encoding.ConfigCode.decodeConfigs_primrec
#print axioms Lecerf.Encoding.StepCode.targetWord_isIndexedCode_iff_backwardUnique
#print axioms Lecerf.Encoding.StepCode.stepCodeIso_apply_eq_some_iff_exists
#print axioms Lecerf.Encoding.StepCode.stepCodeIso_iterate_eq_some_iff
#print axioms Lecerf.Encoding.StepCode.liftPEquiv_machine_eq_stepCodeIso_toPEquiv
#print axioms Lecerf.Transition.pequiv_positiveIterate_iff_strictlyReachable

end Lecerf.Encoding.StepCode.Audit
