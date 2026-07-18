import Lecerf.Machine.TwoTape.HistoryCompiler.Basic

/-!
# Source traces and canonical history-compiler configurations

This proof-side leaf describes the configurations that the finite history
compiler is intended to visit.  A source trace stores the selected source
rules newest first, exactly as they appear on the history tape.  The four
configuration constructors expose the forward, reverse, inspection, and
restoration phases without yet proving any equations about the compiled
machine's executable step function.
-/

namespace Lecerf.Machine.TwoTape.HistoryCompiler

open Lecerf.Transition

universe u v

variable {Q : Type u} {Γ : Type v}

/-- A source-machine rule, named locally to keep trace signatures compact. -/
abbrev SourceRule (Q : Type u) (Γ : Type v) := Lecerf.Machine.Rule Q Γ

/-- A source-machine configuration. -/
abbrev SourceConfig (Q : Type u) (Γ : Type v) [Inhabited Γ] :=
  Lecerf.Machine.Config Q Γ

/-- A finite source machine. -/
abbrev SourceMachine (Q : Type u) (Γ : Type v) :=
  Lecerf.Machine.FiniteMachine Q Γ

/-- A configuration of the two-tape history compiler. -/
abbrev TargetConfig (Q : Type u) (Γ : Type v) [Inhabited Γ] :=
  TwoTape.Config (Control Q Γ) Γ (Mark Q Γ)

section HistoryTape

variable [DecidableEq Q] [DecidableEq Γ]

/-- The canonical history tape for a newest-first concrete rule log. -/
def historyTape : List (SourceRule Q Γ) → Tape (Mark Q Γ)
  | [] => initialHistory
  | rule :: rest => (historyTape rest).act (.token rule) .right

@[simp]
theorem historyTape_nil :
    historyTape ([] : List (SourceRule Q Γ)) = initialHistory :=
  rfl

@[simp]
theorem historyTape_cons (rule : SourceRule Q Γ)
    (rest : List (SourceRule Q Γ)) :
    historyTape (rule :: rest) =
      (historyTape rest).act (.token rule) .right :=
  rfl

/-- A normalized history log always scans a blank cell and has no cells to
the right of its head. -/
theorem historyTape_head_right (rules : List (SourceRule Q Γ)) :
    (historyTape rules).head = .blank ∧
      (historyTape rules).right = none := by
  induction rules with
  | nil => simp [historyTape, initialHistory]
  | cons rule rest ih =>
      rcases h : historyTape rest with ⟨head, left, right⟩
      simp only [h] at ih
      rcases ih with ⟨rfl, rfl⟩
      simp [historyTape, Tape.act, Tape.move, Tape.write, Side.head, Side.tail, h]

@[simp]
theorem historyTape_head (rules : List (SourceRule Q Γ)) :
    (historyTape rules).head = .blank :=
  (historyTape_head_right rules).1

@[simp]
theorem historyTape_right (rules : List (SourceRule Q Γ)) :
    (historyTape rules).right = none :=
  (historyTape_head_right rules).2

/-- The canonical history-tape view immediately after scanning left onto a
recorded rule token. -/
def tokenView (rule : SourceRule Q Γ) (rest : List (SourceRule Q Γ)) :
    Tape (Mark Q Γ) :=
  (historyTape rest).write (.token rule)

@[simp]
theorem tokenView_head (rule : SourceRule Q Γ)
    (rest : List (SourceRule Q Γ)) :
    (tokenView rule rest).head = .token rule :=
  rfl

/-- Scanning left from a nonempty normalized history exposes its newest
token. -/
theorem scan_historyTape_cons (rule : SourceRule Q Γ)
    (rest : List (SourceRule Q Γ)) :
    Tape.move .left (historyTape (rule :: rest)) = tokenView rule rest := by
  rcases h : historyTape rest with ⟨head, left, right⟩
  have head_eq := historyTape_head rest
  have right_eq := historyTape_right rest
  simp only [h] at head_eq right_eq
  subst head
  subst right
  simp [historyTape, tokenView, Tape.act, Tape.move, Tape.write, h]

/-- Erasing an exposed token without moving recovers the shorter normalized
history tape. -/
theorem erase_token_stay (rule : SourceRule Q Γ)
    (rest : List (SourceRule Q Γ)) :
    (tokenView rule rest).act (.blank) .stay = historyTape rest := by
  simp [tokenView, Tape.act,
    Tape.write_eq_self_of_head_eq (historyTape_head rest)]

@[simp]
theorem scan_historyTape_nil :
    Tape.move .left (historyTape ([] : List (SourceRule Q Γ))) =
      Tape.move .left (initialHistory : Tape (Mark Q Γ)) :=
  rfl

/-- Rewriting the exposed bottom marker and moving right closes the history
tape back to its initial normalized form. -/
theorem close_bottom :
    (Tape.move .left (initialHistory : Tape (Mark Q Γ))).act
        (.bottom) .right = initialHistory := by
  simp [initialHistory, Tape.act, Tape.move, Tape.write,
    Side.cons, Side.head, Side.tail]

end HistoryTape

section SourceTrace

variable [Inhabited Γ] [DecidableEq Q] [DecidableEq Γ]

/-- The source successor prescribed by a concrete source rule.  The trace
predicate below separately records that lookup really selected this rule. -/
def advance (rule : SourceRule Q Γ) (config : SourceConfig Q Γ) :
    SourceConfig Q Γ :=
  ⟨rule.target, config.tape.act rule.write rule.move⟩

@[simp]
omit [DecidableEq Q] in
theorem advance_state (rule : SourceRule Q Γ)
    (config : SourceConfig Q Γ) :
    (advance rule config).state = rule.target :=
  rfl

@[simp]
omit [DecidableEq Q] in
theorem advance_tape (rule : SourceRule Q Γ)
    (config : SourceConfig Q Γ) :
    (advance rule config).tape = config.tape.act rule.write rule.move :=
  rfl

/-- Exact generated source traces.  Rules are stored newest first so `push`
matches the concrete history-tape representation directly. -/
inductive Trace (machine : SourceMachine Q Γ) (start : SourceConfig Q Γ) :
    List (SourceRule Q Γ) → SourceConfig Q Γ → Prop
  | nil : Trace machine start [] start
  | push {rules : List (SourceRule Q Γ)} {config : SourceConfig Q Γ}
      {rule : SourceRule Q Γ} :
      Trace machine start rules config →
      machine.lookup config.state config.tape.head = some rule →
      Trace machine start (rule :: rules) (advance rule config)

namespace Trace

/-- The current endpoint of a concrete source trace is reachable from its
start under the executable source step. -/
theorem current_reachable {machine : SourceMachine Q Γ}
    {start config : SourceConfig Q Γ}
    {rules : List (SourceRule Q Γ)}
    (trace : Trace machine start rules config) :
    Reachable machine.step start config := by
  induction trace with
  | nil => exact Reachable.refl _ _
  | @push rules config rule trace selected reachable =>
      exact Reachable.trans reachable <| Reachable.single <|
        (Lecerf.Machine.FiniteMachine.step_eq_some_iff machine config
          (advance rule config)).mpr ⟨rule, selected, rfl⟩

/-- An empty concrete source trace can only end at its start. -/
theorem nil_eq_start {machine : SourceMachine Q Γ}
    {start config : SourceConfig Q Γ}
    (trace : Trace machine start [] config) : config = start := by
  cases trace
  rfl

end Trace

/-- Every executable source reachability witness admits a concrete trace of
the selected source rules. -/
theorem exists_trace_of_reachable {machine : SourceMachine Q Γ}
    {start config : SourceConfig Q Γ}
    (reachable : Reachable machine.step start config) :
    ∃ rules, Trace machine start rules config := by
  induction reachable with
  | refl => exact ⟨[], Trace.nil⟩
  | @tail middle target reachable executed ih =>
      obtain ⟨rules, trace⟩ := ih
      change machine.step middle = some target at executed
      obtain ⟨rule, selected, target_eq⟩ :=
        (Lecerf.Machine.FiniteMachine.step_eq_some_iff
          machine middle target).mp executed
      subst target
      exact ⟨rule :: rules, Trace.push trace selected⟩

/-- Canonical forward-phase configuration (`F`) carrying a concrete log. -/
def forwardConfiguration (config : SourceConfig Q Γ)
    (rules : List (SourceRule Q Γ)) : TargetConfig Q Γ :=
  ⟨.forward config.state, config.tape, historyTape rules⟩

/-- Canonical reverse-phase configuration (`R`) with the unconsumed log. -/
def reverseConfiguration (config : SourceConfig Q Γ)
    (rules : List (SourceRule Q Γ)) : TargetConfig Q Γ :=
  ⟨.reverse config.state, config.tape, historyTape rules⟩

/-- Canonical token-inspection configuration (`I`) for the newest source
rule. -/
def inspectionConfiguration (rule : SourceRule Q Γ)
    (previous : SourceConfig Q Γ) (rest : List (SourceRule Q Γ)) :
    TargetConfig Q Γ :=
  ⟨.inspect rule.target, (advance rule previous).tape, tokenView rule rest⟩

/-- Canonical restoration configuration (`S`) after moving the work head
back but before restoring the overwritten source symbol. -/
def restorationConfiguration (rule : SourceRule Q Γ)
    (previous : SourceConfig Q Γ) (rest : List (SourceRule Q Γ)) :
    TargetConfig Q Γ :=
  ⟨.restore rule, previous.tape.write rule.write, tokenView rule rest⟩

@[simp]
theorem forwardConfiguration_nil (config : SourceConfig Q Γ) :
    forwardConfiguration config [] = checkpoint config :=
  rfl

@[simp]
theorem reverseConfiguration_nil (config : SourceConfig Q Γ) :
    reverseConfiguration config [] = reverseCheckpoint config :=
  rfl

/-- Moving opposite the recorded source move from its successor tape exposes
the just-written cell. -/
omit [DecidableEq Q] in
theorem move_back_advance (rule : SourceRule Q Γ)
    (config : SourceConfig Q Γ) :
    Tape.move rule.move.reverse (advance rule config).tape =
      config.tape.write rule.write := by
  simp [advance, Tape.act]

/-- Lookup supplies the read-symbol equality needed to restore a source tape
after its recorded rule has been moved back. -/
theorem restore_work {machine : SourceMachine Q Γ}
    {rule : SourceRule Q Γ} {config : SourceConfig Q Γ}
    (selected : machine.lookup config.state config.tape.head = some rule) :
    (config.tape.write rule.write).act rule.read .stay = config.tape := by
  have key := Lecerf.Machine.FiniteMachine.lookup_eq_some_key selected
  simp [Tape.act, key.2, Tape.write_eq_self_of_head_eq]

end SourceTrace

end Lecerf.Machine.TwoTape.HistoryCompiler
