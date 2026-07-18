import Lecerf.Machine.TwoTape.HistoryCompiler.Runtime

/-!
# Correctness of the finite two-tape history compiler

The concrete compiler follows exactly the source trace while recording rules
newest first.  At a terminal source checkpoint it crosses an explicit
boundary, undoes every recorded rule through visible scan/inspect/restore
microsteps, and exposes the bottom marker beside the restored source start.

The central invariant classifies every reachable configuration of the open
and closed gadgets.  It is intentionally stronger than the three final
equivalences: reverse-phase states carry both a genuine source prefix and a
proof that the source run halts.  This makes the reflection arguments
independent of informal claims about the runtime's intended phase.
-/

namespace Lecerf.Machine.TwoTape.HistoryCompiler

open Lecerf.Machine
open Lecerf.Transition

universe u v

variable {Q : Type u} {Γ : Type v}
  [Fintype Q] [Fintype Γ] [Inhabited Γ]
  [DecidableEq Q] [DecidableEq Γ]

omit [Fintype Q] [Fintype Γ] in
/-- A generated source trace ending at an absent lookup witnesses source
halting from the trace's start. -/
theorem source_halts_of_trace_of_lookup_none
    {source : SourceMachine Q Γ} {start config : SourceConfig Q Γ}
    {rules : List (SourceRule Q Γ)}
    (trace : Trace source start rules config)
    (terminal : source.lookup config.state config.tape.head = none) :
    HaltsFrom source.step start := by
  rw [haltsFrom_iff_exists_reachable_terminal]
  exact ⟨config, trace.current_reachable,
    (source.haltsAt_iff_lookup_eq_none config).mpr terminal⟩

/-- Canonical shapes reachable during a complete history-compiler run.
Forward states carry only a genuine source trace.  Every reverse-side state
also records that the source run has reached a terminal checkpoint. -/
inductive CanonicalRun (source : SourceMachine Q Γ) (start : SourceConfig Q Γ) :
    TargetConfig Q Γ → Prop
  | forward {config rules} (trace : Trace source start rules config) :
      CanonicalRun source start (forwardConfiguration config rules)
  | reversing {config rules} (trace : Trace source start rules config)
      (halts : HaltsFrom source.step start) :
      CanonicalRun source start (reverseConfiguration config rules)
  | inspecting {rule previous rest}
      (trace : Trace source start rest previous)
      (selected : source.lookup previous.state previous.tape.head = some rule)
      (halts : HaltsFrom source.step start) :
      CanonicalRun source start (inspectionConfiguration rule previous rest)
  | restoring {rule previous rest}
      (trace : Trace source start rest previous)
      (selected : source.lookup previous.state previous.tape.head = some rule)
      (halts : HaltsFrom source.step start) :
      CanonicalRun source start (restorationConfiguration rule previous rest)
  | bottom (halts : HaltsFrom source.step start) :
      CanonicalRun source start (bottomTarget start)

/-- Every successful open-machine step preserves the canonical run
classification. -/
theorem turnaround_preserves_canonical
    {source : SourceMachine Q Γ} (sourceDeterministic : source.TableDeterministic)
    {start : SourceConfig Q Γ} {current next : TargetConfig Q Γ}
    (canonical : CanonicalRun source start current)
    (executed : (turnaroundMachine source).step current = some next) :
    CanonicalRun source start next := by
  cases canonical with
  | forward trace =>
      cases selected : source.lookup _ _ with
      | none =>
          rw [turnaroundMachine_step_boundary sourceDeterministic selected] at executed
          cases Option.some.inj executed
          exact .reversing trace
            (source_halts_of_trace_of_lookup_none trace selected)
      | some rule =>
          rw [turnaroundMachine_step_forward sourceDeterministic selected] at executed
          cases Option.some.inj executed
          exact .forward (Trace.push trace selected)
  | @reversing config rules trace halts =>
      cases rules with
      | nil =>
          have configEq := trace.nil_eq_start
          subst config
          rw [turnaroundMachine_step_reverse_nil sourceDeterministic] at executed
          cases Option.some.inj executed
          exact .bottom halts
      | cons rule rest =>
          cases trace with
          | push previousTrace selected =>
              rw [turnaroundMachine_step_reverse_cons sourceDeterministic] at executed
              cases Option.some.inj executed
              exact .inspecting previousTrace selected halts
  | @inspecting rule previous rest trace selected halts =>
      rw [turnaroundMachine_step_inspect sourceDeterministic
        (Lecerf.Machine.FiniteMachine.lookup_eq_some_mem selected)] at executed
      cases Option.some.inj executed
      exact .restoring trace selected halts
  | @restoring rule previous rest trace selected halts =>
      rw [turnaroundMachine_step_restore sourceDeterministic rest selected] at executed
      cases Option.some.inj executed
      exact .reversing trace halts
  | bottom halts =>
      rw [turnaroundMachine_step_bottomTarget] at executed
      contradiction

/-- Every successful closed-machine step preserves the canonical run
classification; the bottom step returns to the fresh forward checkpoint. -/
theorem return_preserves_canonical
    {source : SourceMachine Q Γ} (sourceDeterministic : source.TableDeterministic)
    {start : SourceConfig Q Γ} {current next : TargetConfig Q Γ}
    (canonical : CanonicalRun source start current)
    (executed : (returnMachine source).step current = some next) :
    CanonicalRun source start next := by
  cases canonical with
  | forward trace =>
      cases selected : source.lookup _ _ with
      | none =>
          rw [returnMachine_step_boundary sourceDeterministic selected] at executed
          cases Option.some.inj executed
          exact .reversing trace
            (source_halts_of_trace_of_lookup_none trace selected)
      | some rule =>
          rw [returnMachine_step_forward sourceDeterministic selected] at executed
          cases Option.some.inj executed
          exact .forward (Trace.push trace selected)
  | @reversing config rules trace halts =>
      cases rules with
      | nil =>
          have configEq := trace.nil_eq_start
          subst config
          rw [returnMachine_step_reverse_nil sourceDeterministic] at executed
          cases Option.some.inj executed
          exact .bottom halts
      | cons rule rest =>
          cases trace with
          | push previousTrace selected =>
              rw [returnMachine_step_reverse_cons sourceDeterministic] at executed
              cases Option.some.inj executed
              exact .inspecting previousTrace selected halts
  | @inspecting rule previous rest trace selected halts =>
      rw [returnMachine_step_inspect sourceDeterministic
        (Lecerf.Machine.FiniteMachine.lookup_eq_some_mem selected)] at executed
      cases Option.some.inj executed
      exact .restoring trace selected halts
  | @restoring rule previous rest trace selected halts =>
      rw [returnMachine_step_restore sourceDeterministic rest selected] at executed
      cases Option.some.inj executed
      exact .reversing trace halts
  | bottom halts =>
      rw [returnMachine_step_bottomTarget sourceDeterministic] at executed
      cases Option.some.inj executed
      exact .forward Trace.nil

/-- Every state reachable in the open compiler has a canonical source-trace
interpretation. -/
theorem turnaround_reachable_canonical
    {source : SourceMachine Q Γ} (sourceDeterministic : source.TableDeterministic)
    {start : SourceConfig Q Γ} {target : TargetConfig Q Γ}
    (reachable : Reachable (turnaroundMachine source).step
      (checkpoint start) target) :
    CanonicalRun source start target := by
  induction reachable with
  | refl => exact .forward Trace.nil
  | tail _ executed canonical =>
      exact turnaround_preserves_canonical sourceDeterministic canonical executed

/-- Every state reachable in the closed compiler has a canonical source-trace
interpretation. -/
theorem return_reachable_canonical
    {source : SourceMachine Q Γ} (sourceDeterministic : source.TableDeterministic)
    {start : SourceConfig Q Γ} {target : TargetConfig Q Γ}
    (reachable : Reachable (returnMachine source).step (checkpoint start) target) :
    CanonicalRun source start target := by
  induction reachable with
  | refl => exact .forward Trace.nil
  | tail _ executed canonical =>
      exact return_preserves_canonical sourceDeterministic canonical executed

omit [Fintype Q] [Fintype Γ] in
/-- If a canonical state equals the exposed bottom target, its reverse-side
halting witness proves that the source halts. -/
theorem CanonicalRun.halts_of_eq_bottomTarget
    {source : SourceMachine Q Γ} {start : SourceConfig Q Γ}
    {target : TargetConfig Q Γ} (canonical : CanonicalRun source start target)
    (targetEq : target = bottomTarget start) : HaltsFrom source.step start := by
  cases canonical with
  | forward trace =>
      have stateEq := congrArg (fun config => config.state) targetEq
      simp [forwardConfiguration, bottomTarget] at stateEq
  | reversing trace halts =>
      have stateEq := congrArg (fun config => config.state) targetEq
      simp [reverseConfiguration, bottomTarget] at stateEq
  | inspecting trace selected halts =>
      have headEq := congrArg (fun config => config.tape₂.head) targetEq
      simp [inspectionConfiguration] at headEq
  | restoring trace selected halts =>
      have stateEq := congrArg (fun config => config.state) targetEq
      simp [restorationConfiguration, bottomTarget] at stateEq
  | bottom halts => exact halts

omit [Fintype Q] [Fintype Γ] in
/-- Reaching the canonical exposed-bottom configuration reflects source
halting. -/
theorem CanonicalRun.bottom_halts
    {source : SourceMachine Q Γ} {start : SourceConfig Q Γ}
    (canonical : CanonicalRun source start (bottomTarget start)) :
    HaltsFrom source.step start :=
  canonical.halts_of_eq_bottomTarget rfl

/-- A source trace is reproduced exactly by the forward phase of the open
compiler. -/
theorem turnaround_forward_reachable
    {source : SourceMachine Q Γ} (sourceDeterministic : source.TableDeterministic)
    {start config : SourceConfig Q Γ} {rules : List (SourceRule Q Γ)}
    (trace : Trace source start rules config) :
    Reachable (turnaroundMachine source).step (checkpoint start)
      (forwardConfiguration config rules) := by
  induction trace with
  | nil => exact Reachable.refl _ _
  | push trace selected reachable =>
      exact Reachable.trans reachable <| Reachable.single <|
        turnaroundMachine_step_forward sourceDeterministic selected

/-- A source trace is reproduced exactly by the forward phase of the closed
compiler. -/
theorem return_forward_reachable
    {source : SourceMachine Q Γ} (sourceDeterministic : source.TableDeterministic)
    {start config : SourceConfig Q Γ} {rules : List (SourceRule Q Γ)}
    (trace : Trace source start rules config) :
    Reachable (returnMachine source).step (checkpoint start)
      (forwardConfiguration config rules) := by
  induction trace with
  | nil => exact Reachable.refl _ _
  | push trace selected reachable =>
      exact Reachable.trans reachable <| Reachable.single <|
        returnMachine_step_forward sourceDeterministic selected

/-- The open compiler consumes a genuine rule trace through three explicit
microsteps per rule and reaches the restored start at the bottom marker. -/
theorem turnaround_reverse_reachable_bottom
    {source : SourceMachine Q Γ} (sourceDeterministic : source.TableDeterministic)
    {start config : SourceConfig Q Γ} {rules : List (SourceRule Q Γ)}
    (trace : Trace source start rules config) :
    Reachable (turnaroundMachine source).step
      (reverseConfiguration config rules) (bottomTarget start) := by
  induction trace with
  | nil =>
      exact Reachable.single
        (turnaroundMachine_step_reverse_nil sourceDeterministic start)
  | @push rules config rule trace selected reachable =>
      exact Reachable.trans
        (Reachable.single
          (turnaroundMachine_step_reverse_cons sourceDeterministic rule config rules)) <|
        Reachable.trans
          (Reachable.single
            (turnaroundMachine_step_inspect sourceDeterministic
              (Lecerf.Machine.FiniteMachine.lookup_eq_some_mem selected)
              config rules)) <|
          Reachable.trans
            (Reachable.single
              (turnaroundMachine_step_restore sourceDeterministic rules selected))
            reachable

/-- The closed compiler has the same explicit reverse path to the bottom
marker. -/
theorem return_reverse_reachable_bottom
    {source : SourceMachine Q Γ} (sourceDeterministic : source.TableDeterministic)
    {start config : SourceConfig Q Γ} {rules : List (SourceRule Q Γ)}
    (trace : Trace source start rules config) :
    Reachable (returnMachine source).step
      (reverseConfiguration config rules) (bottomTarget start) := by
  induction trace with
  | nil =>
      exact Reachable.single
        (returnMachine_step_reverse_nil sourceDeterministic start)
  | @push rules config rule trace selected reachable =>
      exact Reachable.trans
        (Reachable.single
          (returnMachine_step_reverse_cons sourceDeterministic rule config rules)) <|
        Reachable.trans
          (Reachable.single
            (returnMachine_step_inspect sourceDeterministic
              (Lecerf.Machine.FiniteMachine.lookup_eq_some_mem selected)
              config rules)) <|
          Reachable.trans
            (Reachable.single
              (returnMachine_step_restore sourceDeterministic rules selected))
            reachable

/-- A terminal source trace yields the full open forward-boundary-reverse
path to the exposed bottom marker. -/
theorem turnaround_bottom_reachable_of_terminal_trace
    {source : SourceMachine Q Γ} (sourceDeterministic : source.TableDeterministic)
    {start config : SourceConfig Q Γ} {rules : List (SourceRule Q Γ)}
    (trace : Trace source start rules config)
    (terminal : source.lookup config.state config.tape.head = none) :
    Reachable (turnaroundMachine source).step
      (checkpoint start) (bottomTarget start) := by
  exact Reachable.trans (turnaround_forward_reachable sourceDeterministic trace) <|
    Reachable.trans
      (Reachable.single
        (turnaroundMachine_step_boundary sourceDeterministic terminal))
      (turnaround_reverse_reachable_bottom sourceDeterministic trace)

/-- A terminal source trace yields the same path in the closed compiler. -/
theorem return_bottom_reachable_of_terminal_trace
    {source : SourceMachine Q Γ} (sourceDeterministic : source.TableDeterministic)
    {start config : SourceConfig Q Γ} {rules : List (SourceRule Q Γ)}
    (trace : Trace source start rules config)
    (terminal : source.lookup config.state config.tape.head = none) :
    Reachable (returnMachine source).step
      (checkpoint start) (bottomTarget start) := by
  exact Reachable.trans (return_forward_reachable sourceDeterministic trace) <|
    Reachable.trans
      (Reachable.single
        (returnMachine_step_boundary sourceDeterministic terminal))
      (return_reverse_reachable_bottom sourceDeterministic trace)

/-- Source halting constructs the complete open path to the bottom target. -/
theorem turnaround_bottom_reachable_of_halts
    {source : SourceMachine Q Γ} (sourceDeterministic : source.TableDeterministic)
    {start : SourceConfig Q Γ} (halts : HaltsFrom source.step start) :
    Reachable (turnaroundMachine source).step
      (checkpoint start) (bottomTarget start) := by
  rw [haltsFrom_iff_exists_reachable_terminal] at halts
  obtain ⟨config, reachable, terminal⟩ := halts
  obtain ⟨rules, trace⟩ := exists_trace_of_reachable reachable
  exact turnaround_bottom_reachable_of_terminal_trace sourceDeterministic trace
    ((source.haltsAt_iff_lookup_eq_none config).mp terminal)

/-- Source halting constructs the same path in the closed compiler. -/
theorem return_bottom_reachable_of_halts
    {source : SourceMachine Q Γ} (sourceDeterministic : source.TableDeterministic)
    {start : SourceConfig Q Γ} (halts : HaltsFrom source.step start) :
    Reachable (returnMachine source).step
      (checkpoint start) (bottomTarget start) := by
  rw [haltsFrom_iff_exists_reachable_terminal] at halts
  obtain ⟨config, reachable, terminal⟩ := halts
  obtain ⟨rules, trace⟩ := exists_trace_of_reachable reachable
  exact return_bottom_reachable_of_terminal_trace sourceDeterministic trace
    ((source.haltsAt_iff_lookup_eq_none config).mp terminal)

omit [Fintype Q] [Fintype Γ] in
/-- The forward start and exposed reverse-bottom target are structurally
distinct control phases. -/
theorem checkpoint_ne_bottomTarget (config : SourceConfig Q Γ) :
    checkpoint config ≠ bottomTarget config := by
  intro configEq
  have stateEq := congrArg (fun target => target.state) configEq
  simp [checkpoint, bottomTarget] at stateEq

/-- The open compiler reaches its distinct restored bottom target exactly
when the source computation halts. -/
theorem turnaround_bottom_strictlyReachable_iff_source_halts
    {source : SourceMachine Q Γ} (sourceDeterministic : source.TableDeterministic)
    (start : SourceConfig Q Γ) :
    StrictlyReachable (turnaroundMachine source).step
        (checkpoint start) (bottomTarget start) ↔
      HaltsFrom source.step start := by
  constructor
  · intro reachable
    exact (turnaround_reachable_canonical sourceDeterministic
      reachable.toReachable).bottom_halts
  · intro halts
    exact (reachable_iff_strictlyReachable_of_ne
      (checkpoint_ne_bottomTarget start)).mp
        (turnaround_bottom_reachable_of_halts sourceDeterministic halts)

/-- The closed compiler has a nonempty return to its initial checkpoint
exactly when the source computation halts.  Reflection uses semantic backward
uniqueness to identify the last predecessor with the bottom target. -/
theorem return_positiveReturn_iff_source_halts
    {source : SourceMachine Q Γ} (sourceDeterministic : source.TableDeterministic)
    (start : SourceConfig Q Γ) :
    PositiveReturn (returnMachine source).step (checkpoint start) ↔
      HaltsFrom source.step start := by
  constructor
  · intro returned
    obtain ⟨predecessor, reachable, finalStep⟩ :=
      Relation.TransGen.tail'_iff.mp returned
    have predecessorEq : predecessor = bottomTarget start :=
      (returnMachine_reversible sourceDeterministic).2 finalStep
        (returnMachine_step_bottomTarget sourceDeterministic start)
    subst predecessor
    exact (return_reachable_canonical sourceDeterministic reachable).bottom_halts
  · intro halts
    have bottomReachable := return_bottom_reachable_of_halts sourceDeterministic halts
    have bottomPositive : StrictlyReachable (returnMachine source).step
        (checkpoint start) (bottomTarget start) :=
      (reachable_iff_strictlyReachable_of_ne
        (checkpoint_ne_bottomTarget start)).mp bottomReachable
    exact StrictlyReachable.trans bottomPositive <| StrictlyReachable.single <|
      returnMachine_step_bottomTarget sourceDeterministic start

/-- A genuine source trace is reproduced by the forward-only history
machine. -/
theorem history_forward_reachable
    {source : SourceMachine Q Γ} (sourceDeterministic : source.TableDeterministic)
    {start config : SourceConfig Q Γ} {rules : List (SourceRule Q Γ)}
    (trace : Trace source start rules config) :
    Reachable (historyMachine source).step (checkpoint start)
      (forwardConfiguration config rules) := by
  induction trace with
  | nil => exact Reachable.refl _ _
  | @push rules config rule trace selected reachable =>
      exact Reachable.trans reachable <| Reachable.single <|
        historyMachine_step_forward sourceDeterministic selected

/-- Every state reachable by the forward-only compiler is a logged source
trace endpoint. -/
theorem history_reachable_is_forward
    {source : SourceMachine Q Γ} (sourceDeterministic : source.TableDeterministic)
    {start : SourceConfig Q Γ} {target : TargetConfig Q Γ}
    (reachable : Reachable (historyMachine source).step (checkpoint start) target) :
    ∃ config rules, Trace source start rules config ∧
      target = forwardConfiguration config rules := by
  induction reachable with
  | refl => exact ⟨start, [], Trace.nil, rfl⟩
  | @tail middle target reachable executed ih =>
      obtain ⟨config, rules, trace, middleEq⟩ := ih
      subst middle
      cases selected : source.lookup config.state config.tape.head with
      | none =>
          rw [historyMachine_step_forward_of_lookup_none selected] at executed
          contradiction
      | some rule =>
          rw [historyMachine_step_forward sourceDeterministic selected] at executed
          cases Option.some.inj executed
          exact ⟨advance rule config, rule :: rules,
            Trace.push trace selected, rfl⟩

/-- Exact preservation and reflection of halting by the forward history
compiler. -/
theorem historyMachine_haltsFrom_iff_source
    {source : SourceMachine Q Γ} (sourceDeterministic : source.TableDeterministic)
    (start : SourceConfig Q Γ) :
    HaltsFrom (historyMachine source).step (checkpoint start) ↔
      HaltsFrom source.step start := by
  constructor
  · rw [haltsFrom_iff_exists_reachable_terminal]
    rintro ⟨target, reachable, terminal⟩
    obtain ⟨config, rules, trace, targetEq⟩ :=
      history_reachable_is_forward sourceDeterministic reachable
    subst target
    cases selected : source.lookup config.state config.tape.head with
    | none => exact source_halts_of_trace_of_lookup_none trace selected
    | some rule =>
        have executed := historyMachine_step_forward (rules := rules)
          sourceDeterministic selected
        rw [Terminal, executed] at terminal
        contradiction
  · rw [haltsFrom_iff_exists_reachable_terminal,
      haltsFrom_iff_exists_reachable_terminal]
    rintro ⟨config, reachable, terminal⟩
    obtain ⟨rules, trace⟩ := exists_trace_of_reachable reachable
    refine ⟨forwardConfiguration config rules,
      history_forward_reachable sourceDeterministic trace, ?_⟩
    exact historyMachine_step_forward_of_lookup_none
      ((source.haltsAt_iff_lookup_eq_none config).mp terminal)

end Lecerf.Machine.TwoTape.HistoryCompiler
