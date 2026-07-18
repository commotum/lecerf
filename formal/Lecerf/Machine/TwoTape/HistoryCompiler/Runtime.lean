import Lecerf.Machine.TwoTape.HistoryCompiler.Reversible
import Lecerf.Machine.TwoTape.HistoryCompiler.Trace

/-!
# Executable equations for the finite history compiler

This leaf proves the one-step equations followed by canonical forward and
reverse executions.  Successful steps are justified by membership of the
concrete generated rule and forward compatibility of the compiled table.
The two absent-step results classify every possible generated rule.
-/

namespace Lecerf.Machine.TwoTape.HistoryCompiler

open Lecerf.Machine
open Lecerf.Transition

universe u v

variable {Q : Type u} {Γ : Type v}
  [Fintype Q] [Fintype Γ] [Inhabited Γ]
  [DecidableEq Q] [DecidableEq Γ]

omit [Fintype Q] [Fintype Γ] in
private theorem step_eq_some_of_rule
    (compiled : TwoTape.FiniteMachine (Control Q Γ) Γ (Mark Q Γ))
    (compatible : compiled.ForwardCompatible)
    {entry : TwoTape.Rule (Control Q Γ) Γ (Mark Q Γ)}
    {config next : TargetConfig Q Γ}
    (entryMem : entry ∈ compiled.rules)
    (entryStep : entry.apply config = some next) :
    compiled.step config = some next :=
  TwoTape.FiniteMachine.applyRules_eq_some_of_mem_of_compatible
    compatible entryMem entryStep

omit [Fintype Q] [Fintype Γ] in
private theorem forwardRule_applies
    {source : SourceMachine Q Γ} {config : SourceConfig Q Γ}
    {rules : List (SourceRule Q Γ)} {rule : SourceRule Q Γ}
    (selected : source.lookup config.state config.tape.head = some rule) :
    (forwardRule rule).apply (forwardConfiguration config rules) =
      some (forwardConfiguration (advance rule config) (rule :: rules)) := by
  have key := Lecerf.Machine.FiniteMachine.lookup_eq_some_key selected
  rw [TwoTape.Rule.apply_eq_some_iff]
  refine ⟨?_, ?_, ?_, ?_⟩
  · simpa [forwardConfiguration, forwardRule] using key.1.symm
  · simpa [forwardConfiguration, forwardRule] using key.2.symm
  · simpa [forwardConfiguration, forwardRule] using historyTape_head rules
  simp [forwardRule, forwardConfiguration, advance, historyTape]

omit [Fintype Q] [Fintype Γ] in
private theorem boundaryRule_applies
    (config : SourceConfig Q Γ) (rules : List (SourceRule Q Γ)) :
    (boundaryRule config.state config.tape.head).apply
        (forwardConfiguration config rules) =
      some (reverseConfiguration config rules) := by
  rw [TwoTape.Rule.apply_eq_some_iff]
  refine ⟨rfl, rfl, ?_, ?_⟩
  · exact historyTape_head rules
  · simp [boundaryRule, forwardConfiguration, reverseConfiguration, Tape.act,
      Tape.write_eq_self_of_head_eq (historyTape_head rules)]

omit [Fintype Q] [Fintype Γ] in
private theorem scanRule_applies_cons
    (rule : SourceRule Q Γ) (previous : SourceConfig Q Γ)
    (rest : List (SourceRule Q Γ)) :
    (scanRule rule.target (advance rule previous).tape.head).apply
        (reverseConfiguration (advance rule previous) (rule :: rest)) =
      some (inspectionConfiguration rule previous rest) := by
  rw [TwoTape.Rule.apply_eq_some_iff]
  refine ⟨rfl, rfl, ?_, ?_⟩
  · exact historyTape_head (rule :: rest)
  · congr 1
    · rfl
    · simp [scanRule, reverseConfiguration, inspectionConfiguration, Tape.act]
    · change tokenView rule rest =
        (historyTape (rule :: rest)).act .blank .left
      rw [Tape.act,
        Tape.write_eq_self_of_head_eq (historyTape_head (rule :: rest)),
        scan_historyTape_cons]

omit [Fintype Q] [Fintype Γ] in
private theorem scanRule_applies_nil (config : SourceConfig Q Γ) :
    (scanRule config.state config.tape.head).apply
        (reverseConfiguration config []) =
      some (bottomTarget config) := by
  rw [TwoTape.Rule.apply_eq_some_iff]
  refine ⟨rfl, rfl, ?_, ?_⟩
  · exact historyTape_head []
  · congr 1
    · rfl
    · simp [scanRule, reverseConfiguration, bottomTarget, Tape.act]
    · change Tape.move .left initialHistory =
        (historyTape ([] : List (SourceRule Q Γ))).act .blank .left
      rw [Tape.act,
        Tape.write_eq_self_of_head_eq
          (historyTape_head ([] : List (SourceRule Q Γ)))]

/-- A selected source rule is executed and recorded by the forward-only
history machine. -/
theorem historyMachine_step_forward
    {source : SourceMachine Q Γ} (sourceDeterministic : source.TableDeterministic)
    {config : SourceConfig Q Γ} {rules : List (SourceRule Q Γ)}
    {rule : SourceRule Q Γ}
    (selected : source.lookup config.state config.tape.head = some rule) :
    (historyMachine source).step (forwardConfiguration config rules) =
      some (forwardConfiguration (advance rule config) (rule :: rules)) := by
  apply step_eq_some_of_rule _
    (TwoTape.FiniteMachine.tableDeterministic_forwardCompatible
      (historyMachine_tableDeterministic sourceDeterministic))
  · exact mem_forwardRules_iff.mpr
      ⟨rule, Lecerf.Machine.FiniteMachine.lookup_eq_some_mem selected, rfl⟩
  · exact forwardRule_applies selected

/-- The open turnaround machine has the same selected forward step. -/
theorem turnaroundMachine_step_forward
    {source : SourceMachine Q Γ} (sourceDeterministic : source.TableDeterministic)
    {config : SourceConfig Q Γ} {rules : List (SourceRule Q Γ)}
    {rule : SourceRule Q Γ}
    (selected : source.lookup config.state config.tape.head = some rule) :
    (turnaroundMachine source).step (forwardConfiguration config rules) =
      some (forwardConfiguration (advance rule config) (rule :: rules)) := by
  apply step_eq_some_of_rule _
    (TwoTape.FiniteMachine.tableDeterministic_forwardCompatible
      (turnaroundMachine_tableDeterministic sourceDeterministic))
  · exact mem_turnaroundMachine_iff.mpr <| Or.inl <|
      mem_forwardRules_iff.mpr
        ⟨rule, Lecerf.Machine.FiniteMachine.lookup_eq_some_mem selected, rfl⟩
  · exact forwardRule_applies selected

/-- The closed return machine has the same selected forward step. -/
theorem returnMachine_step_forward
    {source : SourceMachine Q Γ} (sourceDeterministic : source.TableDeterministic)
    {config : SourceConfig Q Γ} {rules : List (SourceRule Q Γ)}
    {rule : SourceRule Q Γ}
    (selected : source.lookup config.state config.tape.head = some rule) :
    (returnMachine source).step (forwardConfiguration config rules) =
      some (forwardConfiguration (advance rule config) (rule :: rules)) := by
  apply step_eq_some_of_rule _
    (TwoTape.FiniteMachine.tableDeterministic_forwardCompatible
      (returnMachine_tableDeterministic sourceDeterministic))
  · exact mem_returnMachine_iff.mpr <| Or.inl <|
      mem_turnaroundMachine_iff.mpr <| Or.inl <|
        mem_forwardRules_iff.mpr
          ⟨rule, Lecerf.Machine.FiniteMachine.lookup_eq_some_mem selected, rfl⟩
  · exact forwardRule_applies selected

/-- If the source lookup is absent, the forward-only history machine has no
enabled generated rule. -/
theorem historyMachine_step_forward_of_lookup_none
    {source : SourceMachine Q Γ} {config : SourceConfig Q Γ}
    {rules : List (SourceRule Q Γ)}
    (terminal : source.lookup config.state config.tape.head = none) :
    (historyMachine source).step (forwardConfiguration config rules) = none := by
  cases machineStep :
      (historyMachine source).step (forwardConfiguration config rules) with
  | none => rfl
  | some next =>
      exfalso
      obtain ⟨entry, entryMem, entryStep⟩ :=
        TwoTape.FiniteMachine.applyRules_eq_some_exists machineStep
      obtain ⟨rule, ruleMem, entryEq⟩ := mem_forwardRules_iff.mp entryMem
      subst entry
      have enabled :=
        ((forwardRule rule).apply_eq_some_iff
          (forwardConfiguration config rules) next).mp entryStep
      have sourceEq : rule.source = config.state := by
        simpa [forwardRule, forwardConfiguration] using enabled.1.symm
      have readEq : rule.read = config.tape.head := by
        simpa [forwardRule, forwardConfiguration] using enabled.2.1.symm
      exact (lookup_ne_none_of_mem_of_key ruleMem sourceEq readEq) terminal

/-- At an absent source lookup, the open compiler crosses its explicit
forward/reverse boundary. -/
theorem turnaroundMachine_step_boundary
    {source : SourceMachine Q Γ} (sourceDeterministic : source.TableDeterministic)
    {config : SourceConfig Q Γ} {rules : List (SourceRule Q Γ)}
    (terminal : source.lookup config.state config.tape.head = none) :
    (turnaroundMachine source).step (forwardConfiguration config rules) =
      some (reverseConfiguration config rules) := by
  apply step_eq_some_of_rule _
    (TwoTape.FiniteMachine.tableDeterministic_forwardCompatible
      (turnaroundMachine_tableDeterministic sourceDeterministic))
  · exact mem_turnaroundMachine_iff.mpr <| Or.inr <| Or.inl <|
      mem_boundaryRules_iff.mpr
        ⟨config.state, config.tape.head, terminal, rfl⟩
  · exact boundaryRule_applies config rules

/-- At an absent source lookup, the closed compiler crosses the same
forward/reverse boundary. -/
theorem returnMachine_step_boundary
    {source : SourceMachine Q Γ} (sourceDeterministic : source.TableDeterministic)
    {config : SourceConfig Q Γ} {rules : List (SourceRule Q Γ)}
    (terminal : source.lookup config.state config.tape.head = none) :
    (returnMachine source).step (forwardConfiguration config rules) =
      some (reverseConfiguration config rules) := by
  apply step_eq_some_of_rule _
    (TwoTape.FiniteMachine.tableDeterministic_forwardCompatible
      (returnMachine_tableDeterministic sourceDeterministic))
  · exact mem_returnMachine_iff.mpr <| Or.inl <|
      mem_turnaroundMachine_iff.mpr <| Or.inr <| Or.inl <|
        mem_boundaryRules_iff.mpr
          ⟨config.state, config.tape.head, terminal, rfl⟩
  · exact boundaryRule_applies config rules

/-- In open reverse execution, scanning a nonempty history exposes its newest
source-rule token. -/
theorem turnaroundMachine_step_reverse_cons
    {source : SourceMachine Q Γ} (sourceDeterministic : source.TableDeterministic)
    (rule : SourceRule Q Γ) (previous : SourceConfig Q Γ)
    (rest : List (SourceRule Q Γ)) :
    (turnaroundMachine source).step
        (reverseConfiguration (advance rule previous) (rule :: rest)) =
      some (inspectionConfiguration rule previous rest) := by
  apply step_eq_some_of_rule _
    (TwoTape.FiniteMachine.tableDeterministic_forwardCompatible
      (turnaroundMachine_tableDeterministic sourceDeterministic))
  · exact mem_turnaroundMachine_iff.mpr <| Or.inr <| Or.inr <| Or.inl <|
      mem_scanRules_iff.mpr
        ⟨rule.target, (advance rule previous).tape.head, rfl⟩
  · exact scanRule_applies_cons rule previous rest

/-- The closed machine has the same nonempty-history scan step. -/
theorem returnMachine_step_reverse_cons
    {source : SourceMachine Q Γ} (sourceDeterministic : source.TableDeterministic)
    (rule : SourceRule Q Γ) (previous : SourceConfig Q Γ)
    (rest : List (SourceRule Q Γ)) :
    (returnMachine source).step
        (reverseConfiguration (advance rule previous) (rule :: rest)) =
      some (inspectionConfiguration rule previous rest) := by
  apply step_eq_some_of_rule _
    (TwoTape.FiniteMachine.tableDeterministic_forwardCompatible
      (returnMachine_tableDeterministic sourceDeterministic))
  · exact mem_returnMachine_iff.mpr <| Or.inl <|
      mem_turnaroundMachine_iff.mpr <| Or.inr <| Or.inr <| Or.inl <|
        mem_scanRules_iff.mpr
          ⟨rule.target, (advance rule previous).tape.head, rfl⟩
  · exact scanRule_applies_cons rule previous rest

/-- With no recorded token left, the open machine scans onto the bottom
marker. -/
theorem turnaroundMachine_step_reverse_nil
    {source : SourceMachine Q Γ} (sourceDeterministic : source.TableDeterministic)
    (config : SourceConfig Q Γ) :
    (turnaroundMachine source).step (reverseConfiguration config []) =
      some (bottomTarget config) := by
  apply step_eq_some_of_rule _
    (TwoTape.FiniteMachine.tableDeterministic_forwardCompatible
      (turnaroundMachine_tableDeterministic sourceDeterministic))
  · exact mem_turnaroundMachine_iff.mpr <| Or.inr <| Or.inr <| Or.inl <|
      mem_scanRules_iff.mpr ⟨config.state, config.tape.head, rfl⟩
  · exact scanRule_applies_nil config

/-- The closed machine performs the same scan onto the bottom marker. -/
theorem returnMachine_step_reverse_nil
    {source : SourceMachine Q Γ} (sourceDeterministic : source.TableDeterministic)
    (config : SourceConfig Q Γ) :
    (returnMachine source).step (reverseConfiguration config []) =
      some (bottomTarget config) := by
  apply step_eq_some_of_rule _
    (TwoTape.FiniteMachine.tableDeterministic_forwardCompatible
      (returnMachine_tableDeterministic sourceDeterministic))
  · exact mem_returnMachine_iff.mpr <| Or.inl <|
      mem_turnaroundMachine_iff.mpr <| Or.inr <| Or.inr <| Or.inl <|
        mem_scanRules_iff.mpr ⟨config.state, config.tape.head, rfl⟩
  · exact scanRule_applies_nil config

end Lecerf.Machine.TwoTape.HistoryCompiler
