import Lecerf.Machine.Core
import Lecerf.Transition.Reversible

/-!
# Reversible machine semantics

An individually enabled rule is a partial equivalence. Its inverse moves the
head back before checking and restoring the overwritten symbol. A finite table
is reversible only when these local partial equivalences are globally
compatible; first-match functionality alone does not provide predecessor
uniqueness.
-/

namespace Lecerf.Machine

open Lecerf.Transition

universe u v

namespace Tape

variable {Γ : Type v} [Inhabited Γ] [DecidableEq Γ]

/-- A checked write is a partial equivalence between tapes scanning `old` and
tapes scanning `new`. -/
def checkedWrite (old new : Γ) : Tape Γ ≃. Tape Γ where
  toFun tape := if tape.head = old then some (write new tape) else none
  invFun tape := if tape.head = new then some (write old tape) else none
  inv source target := by
    by_cases sourceHead : source.head = old
    · by_cases targetHead : target.head = new
      · rw [if_pos targetHead, if_pos sourceHead]
        simp only [Option.some.injEq]
        constructor
        · intro restored
          calc
            write new source = write new (write old target) := congrArg (write new) restored.symm
            _ = write new target := by rw [write_write]
            _ = target := write_eq_self_of_head_eq targetHead
        · intro written
          calc
            write old target = write old (write new source) := congrArg (write old) written.symm
            _ = write old source := by rw [write_write]
            _ = source := write_eq_self_of_head_eq sourceHead
      · rw [if_neg targetHead, if_pos sourceHead]
        simp only [reduceCtorEq, false_iff]
        intro written
        apply targetHead
        exact (congrArg Tape.head (Option.some.inj written)).symm.trans
          (write_head _ _)
    · by_cases targetHead : target.head = new
      · rw [if_pos targetHead, if_neg sourceHead]
        simp only [reduceCtorEq, iff_false]
        intro restored
        apply sourceHead
        exact (congrArg Tape.head (Option.some.inj restored)).symm.trans
          (write_head _ _)
      · rw [if_neg targetHead, if_neg sourceHead]
        simp

/-- Movement is a total equivalence; its inverse uses the opposite direction. -/
def moveEquiv (direction : Move) : Tape Γ ≃ Tape Γ where
  toFun := move direction
  invFun := move direction.reverse
  left_inv := move_reverse_move direction
  right_inv := move_move_reverse direction

end Tape

namespace Rule

variable {Q : Type u} {Γ : Type v} [Inhabited Γ] [DecidableEq Q] [DecidableEq Γ]

/-- The tape portion of a rule, explicitly compiled as checked-write followed
by movement. -/
def tapeAction (rule : Rule Q Γ) : Tape Γ ≃. Tape Γ :=
  (Tape.checkedWrite rule.read rule.write).trans (Tape.moveEquiv rule.move).toPEquiv

omit [DecidableEq Q] in
theorem tapeAction_apply (rule : Rule Q Γ) (tape : Tape Γ) :
    rule.tapeAction tape =
      if tape.head = rule.read then some (tape.act rule.write rule.move) else none := by
  by_cases read_eq : tape.head = rule.read
  · simp [tapeAction, Tape.checkedWrite, Tape.act, PEquiv.trans, read_eq,
      Tape.moveEquiv]
  · simp [tapeAction, Tape.checkedWrite, PEquiv.trans, read_eq]

/-- Reverse execution of a conventional rule: check the target control state,
move back, check the symbol written by the forward rule, restore the old
symbol, and return to the source control state. -/
def undo (rule : Rule Q Γ) (config : Config Q Γ) : Option (Config Q Γ) :=
  let oldHead := Tape.move rule.move.reverse config.tape
  if config.state = rule.target ∧ oldHead.head = rule.write then
    some ⟨rule.source, oldHead.write rule.read⟩
  else
    none

/-- Exact local inverse law. The movement order is part of the definitions,
not hidden in a syntactic sign change. -/
theorem apply_eq_some_iff_undo_eq_some (rule : Rule Q Γ) (config next : Config Q Γ) :
    rule.apply config = some next ↔ rule.undo next = some config := by
  rcases config with ⟨state, tape⟩
  rcases next with ⟨nextState, nextTape⟩
  rcases rule with ⟨source, read, target, written, direction⟩
  simp only [apply, undo]
  by_cases enabled : state = source ∧ tape.head = read
  · rcases enabled with ⟨rfl, read_eq⟩
    simp only [read_eq, and_self, if_true, Option.some.injEq]
    constructor
    · intro result_eq
      cases result_eq
      simp [Tape.act, Tape.write_eq_self_of_head_eq read_eq]
    · intro inverse_eq
      split at inverse_eq
      · rename_i inverse_enabled
        cases inverse_eq
        rcases inverse_enabled with ⟨rfl, written_eq⟩
        apply congrArg (fun restored =>
          (⟨nextState, restored⟩ : Config Q Γ))
        rw [Tape.act, Tape.write_write,
          Tape.write_eq_self_of_head_eq written_eq,
          Tape.move_move_reverse]
      · contradiction
  · simp only [enabled, if_false, reduceCtorEq, false_iff]
    intro inverse_eq
    split at inverse_eq
    · rename_i inverse_enabled
      cases inverse_eq
      apply enabled
      rcases inverse_enabled with ⟨rfl, _⟩
      exact ⟨rfl, Tape.write_head _ _⟩
    · contradiction

/-- Each single rule is an individually reversible partial transition. -/
def toPEquiv (rule : Rule Q Γ) : Config Q Γ ≃. Config Q Γ where
  toFun := rule.apply
  invFun := rule.undo
  inv config next := (rule.apply_eq_some_iff_undo_eq_some config next).symm

@[simp]
theorem toPEquiv_apply (rule : Rule Q Γ) (config : Config Q Γ) :
    rule.toPEquiv config = rule.apply config := rfl

@[simp]
theorem toPEquiv_symm_apply (rule : Rule Q Γ) (config : Config Q Γ) :
    rule.toPEquiv.symm config = rule.undo config := rfl

/-- The direct rule semantics is exactly state checking around the compiled
checked-write/move tape phases. -/
theorem apply_eq_tapeAction_map (rule : Rule Q Γ) (config : Config Q Γ) :
    rule.apply config =
      if config.state = rule.source then
        (rule.tapeAction config.tape).map fun tape => ⟨rule.target, tape⟩
      else none := by
  rw [tapeAction_apply]
  by_cases state_eq : config.state = rule.source <;>
    by_cases read_eq : config.tape.head = rule.read <;>
    simp [Rule.apply, state_eq, read_eq]

end Rule

namespace FiniteMachine

variable {Q : Type u} {Γ : Type v} [Inhabited Γ] [DecidableEq Q] [DecidableEq Γ]

/-- First successful inverse rule application. -/
def undoRules : List (Rule Q Γ) → Config Q Γ → Option (Config Q Γ)
  | [], _ => none
  | rule :: rest, config =>
      match rule.undo config with
      | some previous => some previous
      | none => undoRules rest config

/-- Executable reverse-table transition. -/
def reverseStep (machine : FiniteMachine Q Γ) : Step (Config Q Γ) :=
  undoRules machine.rules

/-- Successful forward applications of entries in the same table agree. -/
def ForwardCompatible (machine : FiniteMachine Q Γ) : Prop :=
  ∀ ⦃config firstNext secondNext first second⦄,
    first ∈ machine.rules → second ∈ machine.rules →
    first.apply config = some firstNext → second.apply config = some secondNext →
    firstNext = secondNext

/-- Successful inverse applications of entries in the same table agree. This
is the exact local compatibility condition needed by first-match reversal. -/
def BackwardCompatible (machine : FiniteMachine Q Γ) : Prop :=
  ∀ ⦃config firstPrev secondPrev first second⦄,
    first ∈ machine.rules → second ∈ machine.rules →
    first.undo config = some firstPrev → second.undo config = some secondPrev →
    firstPrev = secondPrev

/-- Pairwise, distinct incoming rules use one common direction and write
different symbols. This is a convenient finite-table sufficient condition for
backward compatibility. -/
def ReverseTableCompatible (machine : FiniteMachine Q Γ) : Prop :=
  ∀ ⦃first⦄, first ∈ machine.rules → ∀ ⦃second⦄, second ∈ machine.rules →
    first ≠ second → first.target = second.target →
      first.move = second.move ∧ first.write ≠ second.write

theorem tableDeterministic_forwardCompatible {machine : FiniteMachine Q Γ}
    (deterministic : machine.TableDeterministic) : machine.ForwardCompatible := by
  intro config firstNext secondNext first second firstMem secondMem firstStep secondStep
  have firstEnabled := (first.apply_eq_some_iff config firstNext).mp firstStep
  have secondEnabled := (second.apply_eq_some_iff config secondNext).mp secondStep
  have rules_eq : first = second := deterministic firstMem secondMem
    (firstEnabled.1.symm.trans secondEnabled.1)
    (firstEnabled.2.1.symm.trans secondEnabled.2.1)
  subst second
  exact Option.some.inj (firstStep.symm.trans secondStep)

theorem reverseTableCompatible_backwardCompatible {machine : FiniteMachine Q Γ}
    (compatible : machine.ReverseTableCompatible) : machine.BackwardCompatible := by
  intro config firstPrev secondPrev first second firstMem secondMem firstUndo secondUndo
  by_cases rules_eq : first = second
  · subst second
    exact Option.some.inj (firstUndo.symm.trans secondUndo)
  · have firstForward := (first.apply_eq_some_iff_undo_eq_some firstPrev config).mpr firstUndo
    have secondForward := (second.apply_eq_some_iff_undo_eq_some secondPrev config).mpr secondUndo
    have target_eq : first.target = second.target := by
      have firstResult := (first.apply_eq_some_iff firstPrev config).mp firstForward
      have secondResult := (second.apply_eq_some_iff secondPrev config).mp secondForward
      have firstState := congrArg Config.state firstResult.2.2
      have secondState := congrArg Config.state secondResult.2.2
      exact firstState.symm.trans secondState
    obtain ⟨move_eq, write_ne⟩ := compatible firstMem secondMem rules_eq target_eq
    have firstResult := (first.apply_eq_some_iff firstPrev config).mp firstForward
    have secondResult := (second.apply_eq_some_iff secondPrev config).mp secondForward
    have tape_eq : firstPrev.tape.act first.write first.move =
        secondPrev.tape.act second.write second.move := by
      exact congrArg Config.tape (firstResult.2.2.symm.trans secondResult.2.2)
    have write_eq : first.write = second.write := by
      have shifted := congrArg (fun tape =>
        (Tape.move first.move.reverse tape).head) tape_eq
      simpa [move_eq, Tape.act] using shifted
    exact False.elim (write_ne write_eq)

theorem applyRules_eq_some_exists {rules : List (Rule Q Γ)} {config next : Config Q Γ}
    (h : applyRules rules config = some next) :
    ∃ rule ∈ rules, rule.apply config = some next := by
  induction rules with
  | nil => simp [applyRules] at h
  | cons first rest ih =>
      simp only [applyRules] at h
      cases firstStep : first.apply config with
      | some firstNext =>
          rw [firstStep] at h
          exact ⟨first, List.mem_cons_self, firstStep.trans h⟩
      | none =>
          rw [firstStep] at h
          obtain ⟨rule, ruleMem, ruleStep⟩ := ih h
          exact ⟨rule, List.mem_cons_of_mem first ruleMem, ruleStep⟩

theorem undoRules_eq_some_exists {rules : List (Rule Q Γ)} {config previous : Config Q Γ}
    (h : undoRules rules config = some previous) :
    ∃ rule ∈ rules, rule.undo config = some previous := by
  induction rules with
  | nil => simp [undoRules] at h
  | cons first rest ih =>
      simp only [undoRules] at h
      cases firstUndo : first.undo config with
      | some firstPrev =>
          rw [firstUndo] at h
          exact ⟨first, List.mem_cons_self, firstUndo.trans h⟩
      | none =>
          rw [firstUndo] at h
          obtain ⟨rule, ruleMem, ruleUndo⟩ := ih h
          exact ⟨rule, List.mem_cons_of_mem first ruleMem, ruleUndo⟩

theorem applyRules_eq_some_of_mem_of_compatible
    {rules : List (Rule Q Γ)}
    (compatible : ∀ ⦃config firstNext secondNext first second⦄,
      first ∈ rules → second ∈ rules →
      first.apply config = some firstNext → second.apply config = some secondNext →
      firstNext = secondNext)
    {rule : Rule Q Γ} {config next : Config Q Γ}
    (ruleMem : rule ∈ rules) (ruleStep : rule.apply config = some next) :
    applyRules rules config = some next := by
  induction rules with
  | nil => simp at ruleMem
  | cons first rest ih =>
      cases firstStep : first.apply config with
      | some firstNext =>
          have next_eq := compatible List.mem_cons_self ruleMem firstStep ruleStep
          subst firstNext
          simp [applyRules, firstStep]
      | none =>
          rcases List.mem_cons.mp ruleMem with rules_eq | ruleMem
          · subst first
            rw [firstStep] at ruleStep
            contradiction
          · rw [applyRules, firstStep]
            have compatibleRest : ∀ ⦃config firstNext secondNext firstRule secondRule⦄,
                firstRule ∈ rest → secondRule ∈ rest →
                firstRule.apply config = some firstNext →
                secondRule.apply config = some secondNext → firstNext = secondNext := by
              intro config firstNext secondNext firstRule secondRule firstMem secondMem
              exact compatible (List.mem_cons_of_mem first firstMem)
                (List.mem_cons_of_mem first secondMem)
            exact ih compatibleRest ruleMem

theorem undoRules_eq_some_of_mem_of_compatible
    {rules : List (Rule Q Γ)}
    (compatible : ∀ ⦃config firstPrev secondPrev first second⦄,
      first ∈ rules → second ∈ rules →
      first.undo config = some firstPrev → second.undo config = some secondPrev →
      firstPrev = secondPrev)
    {rule : Rule Q Γ} {config previous : Config Q Γ}
    (ruleMem : rule ∈ rules) (ruleUndo : rule.undo config = some previous) :
    undoRules rules config = some previous := by
  induction rules with
  | nil => simp at ruleMem
  | cons first rest ih =>
      cases firstUndo : first.undo config with
      | some firstPrev =>
          have previous_eq := compatible List.mem_cons_self ruleMem firstUndo ruleUndo
          subst firstPrev
          simp [undoRules, firstUndo]
      | none =>
          rcases List.mem_cons.mp ruleMem with rules_eq | ruleMem
          · subst first
            rw [firstUndo] at ruleUndo
            contradiction
          · rw [undoRules, firstUndo]
            have compatibleRest : ∀ ⦃config firstPrev secondPrev firstRule secondRule⦄,
                firstRule ∈ rest → secondRule ∈ rest →
                firstRule.undo config = some firstPrev →
                secondRule.undo config = some secondPrev → firstPrev = secondPrev := by
              intro config firstPrev secondPrev firstRule secondRule firstMem secondMem
              exact compatible (List.mem_cons_of_mem first firstMem)
                (List.mem_cons_of_mem first secondMem)
            exact ih compatibleRest ruleMem

/-- Under the two table-compatibility conditions, first-match forward and
reverse execution are exact partial inverses. -/
theorem step_eq_some_iff_reverseStep_eq_some (machine : FiniteMachine Q Γ)
    (forward : machine.ForwardCompatible) (backward : machine.BackwardCompatible)
    (config next : Config Q Γ) :
    machine.step config = some next ↔ machine.reverseStep next = some config := by
  constructor
  · intro machineStep
    obtain ⟨rule, ruleMem, ruleStep⟩ := applyRules_eq_some_exists machineStep
    have ruleUndo := (rule.apply_eq_some_iff_undo_eq_some config next).mp ruleStep
    exact undoRules_eq_some_of_mem_of_compatible backward ruleMem ruleUndo
  · intro machineUndo
    obtain ⟨rule, ruleMem, ruleUndo⟩ := undoRules_eq_some_exists machineUndo
    have ruleStep := (rule.apply_eq_some_iff_undo_eq_some config next).mpr ruleUndo
    exact applyRules_eq_some_of_mem_of_compatible forward ruleMem ruleStep

/-- A deterministic table is semantically reversible exactly when its
successful forward step has unique predecessors. -/
theorem backwardCompatible_iff_backwardUnique (machine : FiniteMachine Q Γ)
    (deterministic : machine.TableDeterministic) :
    machine.BackwardCompatible ↔ BackwardUnique machine.step := by
  constructor
  · intro backward
    let reversible : ReversibleStep (Config Q Γ) := {
      toFun := machine.step
      invFun := machine.reverseStep
      inv := fun config next =>
        (machine.step_eq_some_iff_reverseStep_eq_some
          (tableDeterministic_forwardCompatible deterministic) backward config next).symm
    }
    exact reversible.backwardUnique
  · intro unique config firstPrev secondPrev first second firstMem secondMem firstUndo secondUndo
    have firstRuleStep := (first.apply_eq_some_iff_undo_eq_some firstPrev config).mpr firstUndo
    have secondRuleStep := (second.apply_eq_some_iff_undo_eq_some secondPrev config).mpr secondUndo
    have forward := tableDeterministic_forwardCompatible deterministic
    have firstMachineStep := applyRules_eq_some_of_mem_of_compatible
      forward firstMem firstRuleStep
    have secondMachineStep := applyRules_eq_some_of_mem_of_compatible
      forward secondMem secondRuleStep
    exact unique firstMachineStep secondMachineStep

/-- Whole-machine reversibility keeps table determinism separate from
successful predecessor uniqueness. -/
def Reversible (machine : FiniteMachine Q Γ) : Prop :=
  machine.TableDeterministic ∧ BackwardUnique machine.step

/-- A valid reversible finite table yields the reusable `PEquiv` semantics. -/
def toPEquiv (machine : FiniteMachine Q Γ) (reversible : machine.Reversible) :
    ReversibleStep (Config Q Γ) where
  toFun := machine.step
  invFun := machine.reverseStep
  inv config next := by
    have backward :=
      (machine.backwardCompatible_iff_backwardUnique reversible.1).mpr reversible.2
    exact (machine.step_eq_some_iff_reverseStep_eq_some
      (tableDeterministic_forwardCompatible reversible.1) backward config next).symm

@[simp]
theorem toPEquiv_next (machine : FiniteMachine Q Γ) (reversible : machine.Reversible)
    (config : Config Q Γ) :
    (machine.toPEquiv reversible).next config = machine.step config := rfl

@[simp]
theorem toPEquiv_prev (machine : FiniteMachine Q Γ) (reversible : machine.Reversible)
    (config : Config Q Γ) :
    (machine.toPEquiv reversible).prev config = machine.reverseStep config := rfl

end FiniteMachine

end Lecerf.Machine
