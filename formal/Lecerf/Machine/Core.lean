import Lecerf.Machine.Tape
import Lecerf.Transition.Core

/-!
# Finite read-write-move machines

Rules use the fixed convention: inspect the state and scanned symbol, write,
then move. A machine is a finite ordered rule table; execution selects the
first matching rule. Table determinism is nevertheless recorded separately
from the functionality already supplied by first-match execution.
-/

namespace Lecerf.Machine

open Lecerf.Transition

universe u v

/-- A control state together with a canonical tape. -/
structure Config (Q : Type u) (Γ : Type v) [Inhabited Γ] where
  state : Q
  tape : Tape Γ
  deriving DecidableEq

namespace Config

variable {Q : Type u} {Γ : Type v} [Inhabited Γ]

/-- The all-blank configuration in a supplied control state. -/
def blank (state : Q) : Config Q Γ := ⟨state, ⟨default, none, none⟩⟩

def equivRep : Config Q Γ ≃ Q × Tape Γ where
  toFun config := (config.state, config.tape)
  invFun data := ⟨data.1, data.2⟩
  left_inv := by intro config; cases config; rfl
  right_inv := by intro data; rcases data with ⟨state, tape⟩; rfl

instance [Primcodable Q] [Primcodable Γ] [DecidableEq Γ] :
    Primcodable (Config Q Γ) :=
  Primcodable.ofEquiv (Q × Tape Γ) equivRep

end Config

/-- One conventional instruction `(source, read, target, write, move)`. -/
structure Rule (Q : Type u) (Γ : Type v) where
  source : Q
  read : Γ
  target : Q
  write : Γ
  move : Tape.Move
  deriving DecidableEq

namespace Rule

variable {Q : Type u} {Γ : Type v} [Inhabited Γ]

/-- The input key used by deterministic lookup. -/
def key (rule : Rule Q Γ) : Q × Γ := (rule.source, rule.read)

/-- The output key visible after moving back during reverse execution. -/
def reverseKey (rule : Rule Q Γ) : Q × Γ := (rule.target, rule.write)

def equivRep : Rule Q Γ ≃ Q × Γ × Q × Γ × Tape.Move where
  toFun rule := (rule.source, rule.read, rule.target, rule.write, rule.move)
  invFun data := ⟨data.1, data.2.1, data.2.2.1, data.2.2.2.1, data.2.2.2.2⟩
  left_inv := by intro rule; cases rule; rfl
  right_inv := by
    intro data
    rcases data with ⟨source, read, target, write, move⟩
    rfl

instance [Primcodable Q] [Primcodable Γ] : Primcodable (Rule Q Γ) :=
  Primcodable.ofEquiv (Q × Γ × Q × Γ × Tape.Move) equivRep

/-- Apply one rule under read-write-then-move semantics. -/
def apply [DecidableEq Q] [DecidableEq Γ] (rule : Rule Q Γ) (config : Config Q Γ) :
    Option (Config Q Γ) :=
  if config.state = rule.source ∧ config.tape.head = rule.read then
    some ⟨rule.target, config.tape.act rule.write rule.move⟩
  else
    none

theorem apply_eq_some_iff [DecidableEq Q] [DecidableEq Γ]
    (rule : Rule Q Γ) (config next : Config Q Γ) :
    rule.apply config = some next ↔
      config.state = rule.source ∧ config.tape.head = rule.read ∧
        next = ⟨rule.target, config.tape.act rule.write rule.move⟩ := by
  unfold apply
  by_cases enabled : config.state = rule.source ∧ config.tape.head = rule.read
  · simp [enabled, eq_comm]
  · simp only [enabled, if_false, reduceCtorEq, false_iff]
    rintro ⟨state_eq, read_eq, _⟩
    exact enabled ⟨state_eq, read_eq⟩

end Rule

/-- A finite ordered table of conventional instructions. -/
structure FiniteMachine (Q : Type u) (Γ : Type v) where
  rules : List (Rule Q Γ)
  deriving DecidableEq

namespace FiniteMachine

variable {Q : Type u} {Γ : Type v} [Inhabited Γ]

def equivRep : FiniteMachine Q Γ ≃ List (Rule Q Γ) where
  toFun machine := machine.rules
  invFun rules := ⟨rules⟩
  left_inv := by intro machine; cases machine; rfl
  right_inv := by intro rules; rfl

instance [Primcodable Q] [Primcodable Γ] : Primcodable (FiniteMachine Q Γ) :=
  Primcodable.ofEquiv (List (Rule Q Γ)) equivRep

/-- First rule with the requested source/read key. -/
def lookupRules [DecidableEq Q] [DecidableEq Γ] :
    List (Rule Q Γ) → Q → Γ → Option (Rule Q Γ)
  | [], _, _ => none
  | rule :: rest, state, symbol =>
      if rule.source = state ∧ rule.read = symbol then
        some rule
      else
        lookupRules rest state symbol

/-- Deterministic first-match lookup. -/
def lookup [DecidableEq Q] [DecidableEq Γ] (machine : FiniteMachine Q Γ)
    (state : Q) (symbol : Γ) : Option (Rule Q Γ) :=
  lookupRules machine.rules state symbol

omit [Inhabited Γ] in
theorem lookupRules_eq_some_mem [DecidableEq Q] [DecidableEq Γ]
    {rules : List (Rule Q Γ)} {state : Q} {symbol : Γ} {rule : Rule Q Γ}
    (h : lookupRules rules state symbol = some rule) :
    rule ∈ rules := by
  induction rules with
  | nil => simp [lookupRules] at h
  | cons first rest ih =>
      simp only [lookupRules] at h
      split at h
      · exact List.mem_cons.mpr (Or.inl (Option.some.inj h).symm)
      · exact List.mem_cons.mpr (Or.inr (ih h))

omit [Inhabited Γ] in
theorem lookupRules_eq_some_key [DecidableEq Q] [DecidableEq Γ]
    {rules : List (Rule Q Γ)} {state : Q} {symbol : Γ} {rule : Rule Q Γ}
    (h : lookupRules rules state symbol = some rule) :
    rule.source = state ∧ rule.read = symbol := by
  induction rules with
  | nil => simp [lookupRules] at h
  | cons first rest ih =>
      simp only [lookupRules] at h
      split at h
      · rename_i enabled
        cases Option.some.inj h
        exact enabled
      · exact ih h

omit [Inhabited Γ] in
theorem lookup_eq_some_mem [DecidableEq Q] [DecidableEq Γ]
    {machine : FiniteMachine Q Γ} {state : Q} {symbol : Γ} {rule : Rule Q Γ}
    (h : machine.lookup state symbol = some rule) : rule ∈ machine.rules :=
  lookupRules_eq_some_mem h

omit [Inhabited Γ] in
theorem lookup_eq_some_key [DecidableEq Q] [DecidableEq Γ]
    {machine : FiniteMachine Q Γ} {state : Q} {symbol : Γ} {rule : Rule Q Γ}
    (h : machine.lookup state symbol = some rule) :
    rule.source = state ∧ rule.read = symbol :=
  lookupRules_eq_some_key h

/-- Execute the first matching instruction. -/
def applyRules [DecidableEq Q] [DecidableEq Γ] :
    List (Rule Q Γ) → Config Q Γ → Option (Config Q Γ)
  | [], _ => none
  | rule :: rest, config =>
      match rule.apply config with
      | some next => some next
      | none => applyRules rest config

/-- First-match rule application agrees with lookup followed by the fixed
read-write-move update. -/
theorem applyRules_eq_lookupRules_map [DecidableEq Q] [DecidableEq Γ]
    (rules : List (Rule Q Γ)) (config : Config Q Γ) :
    applyRules rules config =
      (lookupRules rules config.state config.tape.head).map fun rule =>
        ⟨rule.target, config.tape.act rule.write rule.move⟩ := by
  induction rules with
  | nil => rfl
  | cons rule rest ih =>
      by_cases enabled : config.state = rule.source ∧ config.tape.head = rule.read
      · simp [applyRules, lookupRules, Rule.apply, enabled]
      · simp [applyRules, lookupRules, Rule.apply, enabled, ih, eq_comm]

/-- Execute the first matching instruction. -/
def step [DecidableEq Q] [DecidableEq Γ]
    (machine : FiniteMachine Q Γ) : Step (Config Q Γ) :=
  applyRules machine.rules

theorem step_eq_some_iff [DecidableEq Q] [DecidableEq Γ]
    (machine : FiniteMachine Q Γ) (config next : Config Q Γ) :
    machine.step config = some next ↔
      ∃ rule, machine.lookup config.state config.tape.head = some rule ∧
        next = ⟨rule.target, config.tape.act rule.write rule.move⟩ := by
  rw [step, applyRules_eq_lookupRules_map]
  simp [lookup, eq_comm]

/-- Halting means that no table rule matches the current state and symbol. -/
def HaltsAt [DecidableEq Q] [DecidableEq Γ]
    (machine : FiniteMachine Q Γ) (config : Config Q Γ) : Prop :=
  Terminal machine.step config

theorem haltsAt_iff_lookup_eq_none [DecidableEq Q] [DecidableEq Γ]
    (machine : FiniteMachine Q Γ) (config : Config Q Γ) :
    machine.HaltsAt config ↔ machine.lookup config.state config.tape.head = none := by
  rw [HaltsAt, Terminal, step, applyRules_eq_lookupRules_map]
  simp [lookup]

/-- Entries with the same source/read key must be equal. Identical duplicate
values are semantically harmless; conflicting entries are forbidden. This
predicate is separate from the functionality of the executable first-match
step. -/
def TableDeterministic (machine : FiniteMachine Q Γ) : Prop :=
  ∀ ⦃first⦄, first ∈ machine.rules → ∀ ⦃second⦄, second ∈ machine.rules →
    first.source = second.source → first.read = second.read → first = second

/-- The structural well-formedness condition for a deterministic finite rule
table. -/
abbrev WellFormed (machine : FiniteMachine Q Γ) : Prop := machine.TableDeterministic

omit [Inhabited Γ] in
theorem TableDeterministic.rule_unique {machine : FiniteMachine Q Γ}
    (deterministic : machine.TableDeterministic)
    {first second : Rule Q Γ} (first_mem : first ∈ machine.rules)
    (second_mem : second ∈ machine.rules)
    (key_eq : first.key = second.key) : first = second :=
  deterministic first_mem second_mem (congrArg Prod.fst key_eq)
    (congrArg Prod.snd key_eq)

end FiniteMachine

end Lecerf.Machine
