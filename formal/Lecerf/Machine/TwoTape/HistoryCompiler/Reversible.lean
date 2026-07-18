import Lecerf.Machine.TwoTape.HistoryCompiler.Basic

/-!
# Reversibility of the finite history compiler

All generated tables are deterministic and globally reversible whenever the
source table is deterministic.  The proof classifies entries by their six
rule families.  In particular, it does not infer whole-machine reversibility
merely from the local invertibility of individual rules.
-/

namespace Lecerf.Machine.TwoTape.HistoryCompiler

open Lecerf.Machine
open Lecerf.Transition

universe u v

variable {Q : Type u} {Γ : Type v}
  [Fintype Q] [Fintype Γ] [DecidableEq Q] [DecidableEq Γ]

/-- Proof-side classification of all six compiler rule families. -/
inductive Generated (machine : Lecerf.Machine.FiniteMachine Q Γ) :
    TwoTape.Rule (Control Q Γ) Γ (Mark Q Γ) → Prop
  | forward (rule) (ruleMem : rule ∈ machine.rules) :
      Generated machine (forwardRule rule)
  | boundary (state symbol) (terminal : machine.lookup state symbol = none) :
      Generated machine (boundaryRule state symbol)
  | scan (state symbol) : Generated machine (scanRule state symbol)
  | inspect (rule) (ruleMem : rule ∈ machine.rules) (symbol) :
      Generated machine (inspectRule rule symbol)
  | restore (rule) (ruleMem : rule ∈ machine.rules) :
      Generated machine (restoreRule rule)
  | bottom (state symbol) : Generated machine (bottomRule state symbol)

theorem generated_iff_mem_returnMachine
    {machine : Lecerf.Machine.FiniteMachine Q Γ}
    {entry : TwoTape.Rule (Control Q Γ) Γ (Mark Q Γ)} :
    Generated machine entry ↔ entry ∈ (returnMachine machine).rules := by
  constructor
  · intro generated
    rw [mem_returnMachine_expanded_iff]
    cases generated with
    | forward rule ruleMem =>
        exact Or.inl (mem_forwardRules_iff.mpr ⟨rule, ruleMem, rfl⟩)
    | boundary state symbol terminal =>
        exact Or.inr (Or.inl
          (mem_boundaryRules_iff.mpr ⟨state, symbol, terminal, rfl⟩))
    | scan state symbol =>
        exact Or.inr (Or.inr (Or.inl
          (mem_scanRules_iff.mpr ⟨state, symbol, rfl⟩)))
    | inspect rule ruleMem symbol =>
        exact Or.inr (Or.inr (Or.inr (Or.inl
          (mem_inspectRules_iff.mpr ⟨rule, ruleMem, symbol, rfl⟩))))
    | restore rule ruleMem =>
        exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl
          (mem_restoreRules_iff.mpr ⟨rule, ruleMem, rfl⟩)))))
    | bottom state symbol =>
        exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr
          (mem_bottomRules_iff.mpr ⟨state, symbol, rfl⟩)))))
  · rw [mem_returnMachine_expanded_iff]
    rintro (forward | boundary | scan | inspect | restore | bottom)
    · obtain ⟨rule, ruleMem, rfl⟩ := mem_forwardRules_iff.mp forward
      exact .forward rule ruleMem
    · obtain ⟨state, symbol, terminal, rfl⟩ :=
        mem_boundaryRules_iff.mp boundary
      exact .boundary state symbol terminal
    · obtain ⟨state, symbol, rfl⟩ := mem_scanRules_iff.mp scan
      exact .scan state symbol
    · obtain ⟨rule, ruleMem, symbol, rfl⟩ :=
        mem_inspectRules_iff.mp inspect
      exact .inspect rule ruleMem symbol
    · obtain ⟨rule, ruleMem, rfl⟩ := mem_restoreRules_iff.mp restore
      exact .restore rule ruleMem
    · obtain ⟨state, symbol, rfl⟩ := mem_bottomRules_iff.mp bottom
      exact .bottom state symbol

omit [Fintype Q] [Fintype Γ] in
theorem lookup_ne_none_of_mem_of_key
    {source : Lecerf.Machine.FiniteMachine Q Γ}
    {state : Q} {symbol : Γ} {rule : Lecerf.Machine.Rule Q Γ}
    (ruleMem : rule ∈ source.rules)
    (sourceEq : rule.source = state) (readEq : rule.read = symbol) :
    source.lookup state symbol ≠ none := by
  subst state
  subst symbol
  exact Lecerf.Machine.FiniteMachine.lookupRules_ne_none_of_mem ruleMem

private theorem generated_forward_key_unique
    {machine : Lecerf.Machine.FiniteMachine Q Γ}
    (sourceDeterministic : machine.TableDeterministic)
    {first second : TwoTape.Rule (Control Q Γ) Γ (Mark Q Γ)}
    (firstGenerated : Generated machine first)
    (secondGenerated : Generated machine second)
    (sourceEq : first.source = second.source)
    (read₁Eq : first.read₁ = second.read₁)
    (read₂Eq : first.read₂ = second.read₂) :
    first = second := by
  cases firstGenerated <;> cases secondGenerated <;>
    simp_all [forwardRule, boundaryRule, scanRule, inspectRule,
      restoreRule, bottomRule]
  case forward.forward first firstMem second secondMem =>
    have ruleEq := sourceDeterministic firstMem secondMem sourceEq read₁Eq
    subst second
    simp [forwardRule]
  case forward.boundary rule ruleMem state symbol terminal =>
    exact False.elim
      ((lookup_ne_none_of_mem_of_key ruleMem sourceEq read₁Eq) terminal)
  case boundary.forward state symbol rule terminal ruleMem =>
    exact False.elim
      ((lookup_ne_none_of_mem_of_key ruleMem rfl rfl) terminal)

private theorem generated_incoming_separated
    {machine : Lecerf.Machine.FiniteMachine Q Γ}
    (sourceDeterministic : machine.TableDeterministic)
    {first second : TwoTape.Rule (Control Q Γ) Γ (Mark Q Γ)}
    (firstGenerated : Generated machine first)
    (secondGenerated : Generated machine second) :
    TwoTape.FiniteMachine.IncomingSeparatedPair first second := by
  cases firstGenerated <;> cases secondGenerated <;>
    simp_all [TwoTape.FiniteMachine.IncomingSeparatedPair, forwardRule,
      boundaryRule, scanRule, inspectRule, restoreRule, bottomRule]
  all_goals grind [lookup_ne_none_of_mem_of_key,
    Lecerf.Machine.FiniteMachine.TableDeterministic]

private theorem tableDeterministic_of_mem_return
    {machine : Lecerf.Machine.FiniteMachine Q Γ}
    (sourceDeterministic : machine.TableDeterministic)
    (compiled : TwoTape.FiniteMachine (Control Q Γ) Γ (Mark Q Γ))
    (toReturn : ∀ {entry}, entry ∈ compiled.rules →
      entry ∈ (returnMachine machine).rules) :
    compiled.TableDeterministic := by
  intro first firstMem second secondMem sourceEq read₁Eq read₂Eq
  exact generated_forward_key_unique sourceDeterministic
    (generated_iff_mem_returnMachine.mpr (toReturn firstMem))
    (generated_iff_mem_returnMachine.mpr (toReturn secondMem))
    sourceEq read₁Eq read₂Eq

private theorem outputSeparated_of_mem_return
    {machine : Lecerf.Machine.FiniteMachine Q Γ}
    (sourceDeterministic : machine.TableDeterministic)
    (compiled : TwoTape.FiniteMachine (Control Q Γ) Γ (Mark Q Γ))
    (toReturn : ∀ {entry}, entry ∈ compiled.rules →
      entry ∈ (returnMachine machine).rules) :
    compiled.OutputSeparated := by
  apply List.pairwise_of_reflexive_of_forall_ne
  intro first firstMem second secondMem _
  exact generated_incoming_separated sourceDeterministic
    (generated_iff_mem_returnMachine.mpr (toReturn firstMem))
    (generated_iff_mem_returnMachine.mpr (toReturn secondMem))

theorem returnMachine_tableDeterministic
    {machine : Lecerf.Machine.FiniteMachine Q Γ}
    (sourceDeterministic : machine.TableDeterministic) :
    (returnMachine machine).TableDeterministic :=
  tableDeterministic_of_mem_return sourceDeterministic _ (fun h => h)

theorem returnMachine_outputSeparated
    {machine : Lecerf.Machine.FiniteMachine Q Γ}
    (sourceDeterministic : machine.TableDeterministic) :
    (returnMachine machine).OutputSeparated :=
  outputSeparated_of_mem_return sourceDeterministic _ (fun h => h)

theorem turnaroundMachine_tableDeterministic
    {machine : Lecerf.Machine.FiniteMachine Q Γ}
    (sourceDeterministic : machine.TableDeterministic) :
    (turnaroundMachine machine).TableDeterministic := by
  apply tableDeterministic_of_mem_return sourceDeterministic
  intro entry entryMem
  change entry ∈ (turnaroundMachine machine).rules ++ bottomRules
  exact List.mem_append_left _ entryMem

theorem turnaroundMachine_outputSeparated
    {machine : Lecerf.Machine.FiniteMachine Q Γ}
    (sourceDeterministic : machine.TableDeterministic) :
    (turnaroundMachine machine).OutputSeparated := by
  apply outputSeparated_of_mem_return sourceDeterministic
  intro entry entryMem
  change entry ∈ (turnaroundMachine machine).rules ++ bottomRules
  exact List.mem_append_left _ entryMem

theorem historyMachine_tableDeterministic
    {machine : Lecerf.Machine.FiniteMachine Q Γ}
    (sourceDeterministic : machine.TableDeterministic) :
    (historyMachine machine).TableDeterministic := by
  apply tableDeterministic_of_mem_return sourceDeterministic
  intro entry entryMem
  have turnMem : entry ∈ (turnaroundMachine machine).rules :=
    mem_turnaroundMachine_iff.mpr (Or.inl entryMem)
  change entry ∈ (turnaroundMachine machine).rules ++ bottomRules
  exact List.mem_append_left _ turnMem

theorem historyMachine_outputSeparated
    {machine : Lecerf.Machine.FiniteMachine Q Γ}
    (sourceDeterministic : machine.TableDeterministic) :
    (historyMachine machine).OutputSeparated := by
  apply outputSeparated_of_mem_return sourceDeterministic
  intro entry entryMem
  have turnMem : entry ∈ (turnaroundMachine machine).rules :=
    mem_turnaroundMachine_iff.mpr (Or.inl entryMem)
  change entry ∈ (turnaroundMachine machine).rules ++ bottomRules
  exact List.mem_append_left _ turnMem

theorem returnMachine_syntacticallyReversible
    {machine : Lecerf.Machine.FiniteMachine Q Γ}
    (sourceDeterministic : machine.TableDeterministic) :
    (returnMachine machine).SyntacticallyReversible := by
  exact ⟨(TwoTape.FiniteMachine.pairwise_forwardPairValid_iff_tableDeterministic _).mpr
      (returnMachine_tableDeterministic sourceDeterministic),
    returnMachine_outputSeparated sourceDeterministic⟩

theorem turnaroundMachine_syntacticallyReversible
    {machine : Lecerf.Machine.FiniteMachine Q Γ}
    (sourceDeterministic : machine.TableDeterministic) :
    (turnaroundMachine machine).SyntacticallyReversible := by
  exact ⟨(TwoTape.FiniteMachine.pairwise_forwardPairValid_iff_tableDeterministic _).mpr
      (turnaroundMachine_tableDeterministic sourceDeterministic),
    turnaroundMachine_outputSeparated sourceDeterministic⟩

theorem historyMachine_syntacticallyReversible
    {machine : Lecerf.Machine.FiniteMachine Q Γ}
    (sourceDeterministic : machine.TableDeterministic) :
    (historyMachine machine).SyntacticallyReversible := by
  exact ⟨(TwoTape.FiniteMachine.pairwise_forwardPairValid_iff_tableDeterministic _).mpr
      (historyMachine_tableDeterministic sourceDeterministic),
    historyMachine_outputSeparated sourceDeterministic⟩

/-- The closed compiler is semantically deterministic and reversible. -/
theorem returnMachine_reversible
    {machine : Lecerf.Machine.FiniteMachine Q Γ}
    (sourceDeterministic : machine.TableDeterministic) :
    (returnMachine machine).Reversible :=
  (returnMachine_syntacticallyReversible sourceDeterministic).reversible

/-- The open turnaround compiler is semantically deterministic and
reversible. -/
theorem turnaroundMachine_reversible
    {machine : Lecerf.Machine.FiniteMachine Q Γ}
    (sourceDeterministic : machine.TableDeterministic) :
    (turnaroundMachine machine).Reversible :=
  (turnaroundMachine_syntacticallyReversible sourceDeterministic).reversible

/-- The forward-only history compiler is semantically deterministic and
reversible. -/
theorem historyMachine_reversible
    {machine : Lecerf.Machine.FiniteMachine Q Γ}
    (sourceDeterministic : machine.TableDeterministic) :
    (historyMachine machine).Reversible :=
  (historyMachine_syntacticallyReversible sourceDeterministic).reversible

/-- Exact partial-equivalence semantics of the closed return compiler. -/
def returnReversibleStep
    (machine : Lecerf.Machine.FiniteMachine Q Γ)
    (sourceDeterministic : machine.TableDeterministic) :
    ReversibleStep (TwoTape.Config (Control Q Γ) Γ (Mark Q Γ)) :=
  (returnMachine machine).toPEquiv
    (returnMachine_reversible sourceDeterministic)

end Lecerf.Machine.TwoTape.HistoryCompiler
