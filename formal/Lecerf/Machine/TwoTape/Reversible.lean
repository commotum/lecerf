import Lecerf.Machine.TwoTape.Core
import Lecerf.Transition.Reversible

/-!
# Reversibility for conventional two-tape machines

The inverse of one rule moves both heads back before checking the symbols
written by the forward rule and restoring both overwritten symbols.  Whole
tables additionally require deterministic forward keys and compatible
incoming rules; individual rule invertibility alone is not enough.
-/

namespace Lecerf.Machine.TwoTape

open Lecerf.Transition

universe u v w

namespace Rule

variable {Q : Type u} {Γ₁ : Type v} {Γ₂ : Type w}
  [Inhabited Γ₁] [Inhabited Γ₂]
  [DecidableEq Q] [DecidableEq Γ₁] [DecidableEq Γ₂]

/-- Reverse one rule.  Each head is moved back before the written symbol is
checked and the old scanned symbol is restored. -/
def undo (rule : Rule Q Γ₁ Γ₂) (config : Config Q Γ₁ Γ₂) :
    Option (Config Q Γ₁ Γ₂) :=
  let oldTape₁ := Tape.move rule.move₁.reverse config.tape₁
  let oldTape₂ := Tape.move rule.move₂.reverse config.tape₂
  if config.state = rule.target ∧ oldTape₁.head = rule.write₁ ∧
      oldTape₂.head = rule.write₂ then
    some ⟨rule.source, oldTape₁.write rule.read₁, oldTape₂.write rule.read₂⟩
  else
    none

/-- Exact local inverse law for simultaneous two-tape execution. -/
theorem apply_eq_some_iff_undo_eq_some
    (rule : Rule Q Γ₁ Γ₂) (config next : Config Q Γ₁ Γ₂) :
    rule.apply config = some next ↔ rule.undo next = some config := by
  rcases config with ⟨state, tape₁, tape₂⟩
  rcases next with ⟨nextState, nextTape₁, nextTape₂⟩
  rcases rule with
    ⟨source, read₁, read₂, target, write₁, move₁, write₂, move₂⟩
  simp only [apply, undo]
  by_cases enabled : state = source ∧ tape₁.head = read₁ ∧ tape₂.head = read₂
  · rcases enabled with ⟨rfl, read₁_eq, read₂_eq⟩
    simp only [read₁_eq, read₂_eq, and_self, if_true, Option.some.injEq]
    constructor
    · intro result_eq
      cases result_eq
      simp [Tape.act, Tape.write_eq_self_of_head_eq read₁_eq,
        Tape.write_eq_self_of_head_eq read₂_eq]
    · intro inverse_eq
      split at inverse_eq
      · rename_i inverse_enabled
        cases inverse_eq
        rcases inverse_enabled with ⟨rfl, written₁_eq, written₂_eq⟩
        congr 1
        · rw [Tape.act, Tape.write_write,
            Tape.write_eq_self_of_head_eq written₁_eq,
            Tape.move_move_reverse]
        · rw [Tape.act, Tape.write_write,
            Tape.write_eq_self_of_head_eq written₂_eq,
            Tape.move_move_reverse]
      · contradiction
  · simp only [enabled, if_false, reduceCtorEq, false_iff]
    intro inverse_eq
    split at inverse_eq
    · rename_i inverse_enabled
      cases inverse_eq
      apply enabled
      rcases inverse_enabled with ⟨rfl, _, _⟩
      exact ⟨rfl, Tape.write_head _ _, Tape.write_head _ _⟩
    · contradiction

/-- Each rule is an individually reversible partial transition. -/
def toPEquiv (rule : Rule Q Γ₁ Γ₂) : Config Q Γ₁ Γ₂ ≃. Config Q Γ₁ Γ₂ where
  toFun := rule.apply
  invFun := rule.undo
  inv config next := (rule.apply_eq_some_iff_undo_eq_some config next).symm

@[simp]
theorem toPEquiv_apply (rule : Rule Q Γ₁ Γ₂) (config : Config Q Γ₁ Γ₂) :
    rule.toPEquiv config = rule.apply config := rfl

@[simp]
theorem toPEquiv_symm_apply (rule : Rule Q Γ₁ Γ₂) (config : Config Q Γ₁ Γ₂) :
    rule.toPEquiv.symm config = rule.undo config := rfl

end Rule

namespace FiniteMachine

variable {Q : Type u} {Γ₁ : Type v} {Γ₂ : Type w}
  [Inhabited Γ₁] [Inhabited Γ₂]
  [DecidableEq Q] [DecidableEq Γ₁] [DecidableEq Γ₂]

/-- First successful inverse rule application. -/
def undoRules :
    List (Rule Q Γ₁ Γ₂) → Config Q Γ₁ Γ₂ → Option (Config Q Γ₁ Γ₂)
  | [], _ => none
  | rule :: rest, config =>
      match rule.undo config with
      | some previous => some previous
      | none => undoRules rest config

/-- Executable reverse-table transition. -/
def reverseStep (machine : FiniteMachine Q Γ₁ Γ₂) : Step (Config Q Γ₁ Γ₂) :=
  undoRules machine.rules

/-- Successful applications of entries in the same table agree. -/
def ForwardCompatible (machine : FiniteMachine Q Γ₁ Γ₂) : Prop :=
  ∀ ⦃config firstNext secondNext first second⦄,
    first ∈ machine.rules → second ∈ machine.rules →
    first.apply config = some firstNext → second.apply config = some secondNext →
    firstNext = secondNext

/-- Successful inverse applications of entries in the same table agree. -/
def BackwardCompatible (machine : FiniteMachine Q Γ₁ Γ₂) : Prop :=
  ∀ ⦃config firstPrev secondPrev first second⦄,
    first ∈ machine.rules → second ∈ machine.rules →
    first.undo config = some firstPrev → second.undo config = some secondPrev →
    firstPrev = secondPrev

/-- Distinct incoming rules with a common target are separated on at least
one tape: on that tape they use the same head movement but write different
symbols.  Thus both inverse checks cannot succeed at the same output. -/
def IncomingSeparatedPair (first second : Rule Q Γ₁ Γ₂) : Prop :=
  first = second ∨ first.target ≠ second.target ∨
    (first.move₁ = second.move₁ ∧ first.write₁ ≠ second.write₁) ∨
    (first.move₂ = second.move₂ ∧ first.write₂ ≠ second.write₂)

/-- Pairwise incoming separation for a finite table. -/
def OutputSeparated (machine : FiniteMachine Q Γ₁ Γ₂) : Prop :=
  machine.rules.Pairwise IncomingSeparatedPair

private instance incomingSeparatedPairRefl :
    Std.Refl (@IncomingSeparatedPair Q Γ₁ Γ₂) where
  refl _ := Or.inl rfl

private instance incomingSeparatedPairSymm :
    Std.Symm (@IncomingSeparatedPair Q Γ₁ Γ₂) where
  symm first second := by
    rintro (equal | targetNe | tape₁Separated | tape₂Separated)
    · exact Or.inl equal.symm
    · exact Or.inr (Or.inl targetNe.symm)
    · exact Or.inr (Or.inr (Or.inl
        ⟨tape₁Separated.1.symm, tape₁Separated.2.symm⟩))
    · exact Or.inr (Or.inr (Or.inr
        ⟨tape₂Separated.1.symm, tape₂Separated.2.symm⟩))

private instance incomingSeparatedPairDecidable :
    DecidableRel (@IncomingSeparatedPair Q Γ₁ Γ₂) :=
  fun _ _ => by
    unfold IncomingSeparatedPair
    infer_instance

instance (machine : FiniteMachine Q Γ₁ Γ₂) : Decidable machine.OutputSeparated := by
  unfold OutputSeparated
  infer_instance

/-- Pair validity for deterministic forward lookup. -/
def ForwardPairValid (first second : Rule Q Γ₁ Γ₂) : Prop :=
  first = second ∨ first.source ≠ second.source ∨
    first.read₁ ≠ second.read₁ ∨ first.read₂ ≠ second.read₂

private instance forwardPairValidRefl : Std.Refl (@ForwardPairValid Q Γ₁ Γ₂) where
  refl _ := Or.inl rfl

private instance forwardPairValidSymm : Std.Symm (@ForwardPairValid Q Γ₁ Γ₂) where
  symm first second := by
    rintro (equal | sourceNe | read₁Ne | read₂Ne)
    · exact Or.inl equal.symm
    · exact Or.inr (Or.inl sourceNe.symm)
    · exact Or.inr (Or.inr (Or.inl read₁Ne.symm))
    · exact Or.inr (Or.inr (Or.inr read₂Ne.symm))

private instance forwardPairValidDecidable :
    DecidableRel (@ForwardPairValid Q Γ₁ Γ₂) :=
  fun _ _ => by
    unfold ForwardPairValid
    infer_instance

/-- A wholly finite certificate for deterministic reversible execution. -/
def SyntacticallyReversible (machine : FiniteMachine Q Γ₁ Γ₂) : Prop :=
  machine.rules.Pairwise ForwardPairValid ∧ machine.OutputSeparated

instance (machine : FiniteMachine Q Γ₁ Γ₂) :
    Decidable machine.SyntacticallyReversible := by
  unfold SyntacticallyReversible
  infer_instance

omit [Inhabited Γ₁] [Inhabited Γ₂] in
theorem pairwise_forwardPairValid_iff_tableDeterministic
    (machine : FiniteMachine Q Γ₁ Γ₂) :
    machine.rules.Pairwise ForwardPairValid ↔ machine.TableDeterministic := by
  constructor
  · intro pairwise first firstMem second secondMem sourceEq read₁Eq read₂Eq
    by_cases equal : first = second
    · exact equal
    · rcases pairwise.forall firstMem secondMem equal with
        equal | sourceNe | read₁Ne | read₂Ne
      · exact equal
      · exact False.elim (sourceNe sourceEq)
      · exact False.elim (read₁Ne read₁Eq)
      · exact False.elim (read₂Ne read₂Eq)
  · intro deterministic
    apply List.pairwise_of_reflexive_of_forall_ne
    intro first firstMem second secondMem _
    by_cases sourceEq : first.source = second.source
    · by_cases read₁Eq : first.read₁ = second.read₁
      · by_cases read₂Eq : first.read₂ = second.read₂
        · exact Or.inl (deterministic firstMem secondMem sourceEq read₁Eq read₂Eq)
        · exact Or.inr (Or.inr (Or.inr read₂Eq))
      · exact Or.inr (Or.inr (Or.inl read₁Eq))
    · exact Or.inr (Or.inl sourceEq)

theorem tableDeterministic_forwardCompatible {machine : FiniteMachine Q Γ₁ Γ₂}
    (deterministic : machine.TableDeterministic) : machine.ForwardCompatible := by
  intro config firstNext secondNext first second firstMem secondMem firstStep secondStep
  have firstEnabled := (first.apply_eq_some_iff config firstNext).mp firstStep
  have secondEnabled := (second.apply_eq_some_iff config secondNext).mp secondStep
  have rules_eq : first = second := deterministic firstMem secondMem
    (firstEnabled.1.symm.trans secondEnabled.1)
    (firstEnabled.2.1.symm.trans secondEnabled.2.1)
    (firstEnabled.2.2.1.symm.trans secondEnabled.2.2.1)
  subst second
  exact Option.some.inj (firstStep.symm.trans secondStep)

theorem outputSeparated_backwardCompatible {machine : FiniteMachine Q Γ₁ Γ₂}
    (separated : machine.OutputSeparated) : machine.BackwardCompatible := by
  intro config firstPrev secondPrev first second firstMem secondMem firstUndo secondUndo
  by_cases rulesEq : first = second
  · subst second
    exact Option.some.inj (firstUndo.symm.trans secondUndo)
  · have firstForward :=
      (first.apply_eq_some_iff_undo_eq_some firstPrev config).mpr firstUndo
    have secondForward :=
      (second.apply_eq_some_iff_undo_eq_some secondPrev config).mpr secondUndo
    have firstResult := (first.apply_eq_some_iff firstPrev config).mp firstForward
    have secondResult := (second.apply_eq_some_iff secondPrev config).mp secondForward
    have targetEq : first.target = second.target := by
      have firstState := congrArg Config.state firstResult.2.2.2
      have secondState := congrArg Config.state secondResult.2.2.2
      exact firstState.symm.trans secondState
    rcases separated.forall firstMem secondMem rulesEq with
      equal | targetNe | tape₁Separated | tape₂Separated
    · exact False.elim (rulesEq equal)
    · exact False.elim (targetNe targetEq)
    · have tapeEq : firstPrev.tape₁.act first.write₁ first.move₁ =
          secondPrev.tape₁.act second.write₁ second.move₁ := by
        exact congrArg Config.tape₁ (firstResult.2.2.2.symm.trans secondResult.2.2.2)
      have writeEq : first.write₁ = second.write₁ := by
        have shifted := congrArg
          (fun tape => (Tape.move first.move₁.reverse tape).head) tapeEq
        simpa [tape₁Separated.1, Tape.act] using shifted
      exact False.elim (tape₁Separated.2 writeEq)
    · have tapeEq : firstPrev.tape₂.act first.write₂ first.move₂ =
          secondPrev.tape₂.act second.write₂ second.move₂ := by
        exact congrArg Config.tape₂ (firstResult.2.2.2.symm.trans secondResult.2.2.2)
      have writeEq : first.write₂ = second.write₂ := by
        have shifted := congrArg
          (fun tape => (Tape.move first.move₂.reverse tape).head) tapeEq
        simpa [tape₂Separated.1, Tape.act] using shifted
      exact False.elim (tape₂Separated.2 writeEq)

theorem applyRules_eq_some_exists
    {rules : List (Rule Q Γ₁ Γ₂)} {config next : Config Q Γ₁ Γ₂}
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

theorem undoRules_eq_some_exists
    {rules : List (Rule Q Γ₁ Γ₂)} {config previous : Config Q Γ₁ Γ₂}
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
    {rules : List (Rule Q Γ₁ Γ₂)}
    (compatible : ∀ ⦃config firstNext secondNext first second⦄,
      first ∈ rules → second ∈ rules →
      first.apply config = some firstNext → second.apply config = some secondNext →
      firstNext = secondNext)
    {rule : Rule Q Γ₁ Γ₂} {config next : Config Q Γ₁ Γ₂}
    (ruleMem : rule ∈ rules) (ruleStep : rule.apply config = some next) :
    applyRules rules config = some next := by
  induction rules with
  | nil => simp at ruleMem
  | cons first rest ih =>
      cases firstStep : first.apply config with
      | some firstNext =>
          have nextEq := compatible List.mem_cons_self ruleMem firstStep ruleStep
          subst firstNext
          simp [applyRules, firstStep]
      | none =>
          rcases List.mem_cons.mp ruleMem with rulesEq | ruleMem
          · subst first
            rw [firstStep] at ruleStep
            contradiction
          · rw [applyRules, firstStep]
            have compatibleRest :
                ∀ ⦃config firstNext secondNext firstRule secondRule⦄,
                  firstRule ∈ rest → secondRule ∈ rest →
                  firstRule.apply config = some firstNext →
                  secondRule.apply config = some secondNext → firstNext = secondNext := by
              intro config firstNext secondNext firstRule secondRule firstMem secondMem
              exact compatible (List.mem_cons_of_mem first firstMem)
                (List.mem_cons_of_mem first secondMem)
            exact ih compatibleRest ruleMem

theorem undoRules_eq_some_of_mem_of_compatible
    {rules : List (Rule Q Γ₁ Γ₂)}
    (compatible : ∀ ⦃config firstPrev secondPrev first second⦄,
      first ∈ rules → second ∈ rules →
      first.undo config = some firstPrev → second.undo config = some secondPrev →
      firstPrev = secondPrev)
    {rule : Rule Q Γ₁ Γ₂} {config previous : Config Q Γ₁ Γ₂}
    (ruleMem : rule ∈ rules) (ruleUndo : rule.undo config = some previous) :
    undoRules rules config = some previous := by
  induction rules with
  | nil => simp at ruleMem
  | cons first rest ih =>
      cases firstUndo : first.undo config with
      | some firstPrev =>
          have previousEq := compatible List.mem_cons_self ruleMem firstUndo ruleUndo
          subst firstPrev
          simp [undoRules, firstUndo]
      | none =>
          rcases List.mem_cons.mp ruleMem with rulesEq | ruleMem
          · subst first
            rw [firstUndo] at ruleUndo
            contradiction
          · rw [undoRules, firstUndo]
            have compatibleRest :
                ∀ ⦃config firstPrev secondPrev firstRule secondRule⦄,
                  firstRule ∈ rest → secondRule ∈ rest →
                  firstRule.undo config = some firstPrev →
                  secondRule.undo config = some secondPrev → firstPrev = secondPrev := by
              intro config firstPrev secondPrev firstRule secondRule firstMem secondMem
              exact compatible (List.mem_cons_of_mem first firstMem)
                (List.mem_cons_of_mem first secondMem)
            exact ih compatibleRest ruleMem

/-- Compatible forward and inverse tables are exact partial inverses. -/
theorem step_eq_some_iff_reverseStep_eq_some (machine : FiniteMachine Q Γ₁ Γ₂)
    (forward : machine.ForwardCompatible) (backward : machine.BackwardCompatible)
    (config next : Config Q Γ₁ Γ₂) :
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

/-- For a deterministic table, inverse compatibility is equivalent to
successful-predecessor uniqueness of the whole first-match transition. -/
theorem backwardCompatible_iff_backwardUnique (machine : FiniteMachine Q Γ₁ Γ₂)
    (deterministic : machine.TableDeterministic) :
    machine.BackwardCompatible ↔ BackwardUnique machine.step := by
  constructor
  · intro backward
    let reversible : ReversibleStep (Config Q Γ₁ Γ₂) := {
      toFun := machine.step
      invFun := machine.reverseStep
      inv := fun config next =>
        (machine.step_eq_some_iff_reverseStep_eq_some
          (tableDeterministic_forwardCompatible deterministic) backward config next).symm
    }
    exact reversible.backwardUnique
  · intro unique config firstPrev secondPrev first second
      firstMem secondMem firstUndo secondUndo
    have firstRuleStep :=
      (first.apply_eq_some_iff_undo_eq_some firstPrev config).mpr firstUndo
    have secondRuleStep :=
      (second.apply_eq_some_iff_undo_eq_some secondPrev config).mpr secondUndo
    have forward := tableDeterministic_forwardCompatible deterministic
    have firstMachineStep :=
      applyRules_eq_some_of_mem_of_compatible forward firstMem firstRuleStep
    have secondMachineStep :=
      applyRules_eq_some_of_mem_of_compatible forward secondMem secondRuleStep
    exact unique firstMachineStep secondMachineStep

/-- Incoming separation plus deterministic forward lookup gives successful
predecessor uniqueness for the executable table transition. -/
theorem OutputSeparated.backwardUnique
    {machine : FiniteMachine Q Γ₁ Γ₂}
    (separated : machine.OutputSeparated)
    (deterministic : machine.TableDeterministic) :
    BackwardUnique machine.step :=
  (machine.backwardCompatible_iff_backwardUnique deterministic).mp
    (outputSeparated_backwardCompatible separated)

/-- Semantic whole-machine reversibility: deterministic forward lookup and
unique successful predecessors. -/
def Reversible (machine : FiniteMachine Q Γ₁ Γ₂) : Prop :=
  machine.TableDeterministic ∧ BackwardUnique machine.step

/-- The decidable finite certificate implies semantic reversibility. -/
theorem SyntacticallyReversible.reversible
    {machine : FiniteMachine Q Γ₁ Γ₂}
    (valid : machine.SyntacticallyReversible) : machine.Reversible := by
  obtain ⟨forwardPairwise, separated⟩ := valid
  have deterministic :=
    (pairwise_forwardPairValid_iff_tableDeterministic machine).mp forwardPairwise
  refine ⟨deterministic, ?_⟩
  exact (machine.backwardCompatible_iff_backwardUnique deterministic).mp
    (outputSeparated_backwardCompatible separated)

/-- Reusable `PEquiv` semantics of a semantically reversible table. -/
def toPEquiv (machine : FiniteMachine Q Γ₁ Γ₂) (reversible : machine.Reversible) :
    ReversibleStep (Config Q Γ₁ Γ₂) where
  toFun := machine.step
  invFun := machine.reverseStep
  inv config next := by
    have backward :=
      (machine.backwardCompatible_iff_backwardUnique reversible.1).mpr reversible.2
    exact (machine.step_eq_some_iff_reverseStep_eq_some
      (tableDeterministic_forwardCompatible reversible.1) backward config next).symm

@[simp]
theorem toPEquiv_next (machine : FiniteMachine Q Γ₁ Γ₂)
    (reversible : machine.Reversible) (config : Config Q Γ₁ Γ₂) :
    (machine.toPEquiv reversible).next config = machine.step config := rfl

@[simp]
theorem toPEquiv_prev (machine : FiniteMachine Q Γ₁ Γ₂)
    (reversible : machine.Reversible) (config : Config Q Γ₁ Γ₂) :
    (machine.toPEquiv reversible).prev config = machine.reverseStep config := rfl

end FiniteMachine

end Lecerf.Machine.TwoTape
