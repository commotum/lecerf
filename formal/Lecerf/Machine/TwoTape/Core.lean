import Lecerf.Machine.Tape
import Lecerf.Transition.Core

/-!
# Conventional finite two-tape machines

Both tapes use the project's canonical finite-support `Tape`.  A rule reads
the two scanned symbols, writes both tapes, and then moves both heads.  The
finite rule table has ordered, first-match execution; table determinism is a
separate structural property.
-/

namespace Lecerf.Machine.TwoTape

open Lecerf.Transition

universe u v w

/-- A control state and two canonical tapes, possibly over different
alphabets. -/
structure Config (Q : Type u) (Γ₁ : Type v) (Γ₂ : Type w)
    [Inhabited Γ₁] [Inhabited Γ₂] where
  state : Q
  tape₁ : Tape Γ₁
  tape₂ : Tape Γ₂
  deriving DecidableEq

namespace Config

variable {Q : Type u} {Γ₁ : Type v} {Γ₂ : Type w}
  [Inhabited Γ₁] [Inhabited Γ₂]

/-- The configuration with both tapes blank. -/
def blank (state : Q) : Config Q Γ₁ Γ₂ :=
  ⟨state, ⟨default, none, none⟩, ⟨default, none, none⟩⟩

def equivRep : Config Q Γ₁ Γ₂ ≃ Q × Tape Γ₁ × Tape Γ₂ where
  toFun config := (config.state, config.tape₁, config.tape₂)
  invFun data := ⟨data.1, data.2.1, data.2.2⟩
  left_inv := by intro config; cases config; rfl
  right_inv := by intro data; rcases data with ⟨state, tape₁, tape₂⟩; rfl

instance [Primcodable Q] [Primcodable Γ₁] [Primcodable Γ₂]
    [DecidableEq Γ₁] [DecidableEq Γ₂] :
    Primcodable (Config Q Γ₁ Γ₂) :=
  Primcodable.ofEquiv (Q × Tape Γ₁ × Tape Γ₂) equivRep

end Config

/-- A simultaneous read-write-then-move instruction for two tapes. -/
structure Rule (Q : Type u) (Γ₁ : Type v) (Γ₂ : Type w) where
  source : Q
  read₁ : Γ₁
  read₂ : Γ₂
  target : Q
  write₁ : Γ₁
  move₁ : Tape.Move
  write₂ : Γ₂
  move₂ : Tape.Move
  deriving DecidableEq

namespace Rule

variable {Q : Type u} {Γ₁ : Type v} {Γ₂ : Type w}
  [Inhabited Γ₁] [Inhabited Γ₂]

/-- The forward lookup key. -/
def key (rule : Rule Q Γ₁ Γ₂) : Q × Γ₁ × Γ₂ :=
  (rule.source, rule.read₁, rule.read₂)

def equivRep : Rule Q Γ₁ Γ₂ ≃
    Q × Γ₁ × Γ₂ × Q × Γ₁ × Tape.Move × Γ₂ × Tape.Move where
  toFun rule :=
    (rule.source, rule.read₁, rule.read₂, rule.target,
      rule.write₁, rule.move₁, rule.write₂, rule.move₂)
  invFun data :=
    ⟨data.1, data.2.1, data.2.2.1, data.2.2.2.1,
      data.2.2.2.2.1, data.2.2.2.2.2.1,
      data.2.2.2.2.2.2.1, data.2.2.2.2.2.2.2⟩
  left_inv := by intro rule; cases rule; rfl
  right_inv := by
    intro data
    rcases data with
      ⟨source, read₁, read₂, target, write₁, move₁, write₂, move₂⟩
    rfl

instance [Primcodable Q] [Primcodable Γ₁] [Primcodable Γ₂] :
    Primcodable (Rule Q Γ₁ Γ₂) :=
  Primcodable.ofEquiv
    (Q × Γ₁ × Γ₂ × Q × Γ₁ × Tape.Move × Γ₂ × Tape.Move) equivRep

/-- Apply one rule using simultaneous read-write-then-move semantics. -/
def apply [DecidableEq Q] [DecidableEq Γ₁] [DecidableEq Γ₂]
    (rule : Rule Q Γ₁ Γ₂) (config : Config Q Γ₁ Γ₂) :
    Option (Config Q Γ₁ Γ₂) :=
  if config.state = rule.source ∧ config.tape₁.head = rule.read₁ ∧
      config.tape₂.head = rule.read₂ then
    some ⟨rule.target,
      config.tape₁.act rule.write₁ rule.move₁,
      config.tape₂.act rule.write₂ rule.move₂⟩
  else
    none

theorem apply_eq_some_iff [DecidableEq Q] [DecidableEq Γ₁] [DecidableEq Γ₂]
    (rule : Rule Q Γ₁ Γ₂) (config next : Config Q Γ₁ Γ₂) :
    rule.apply config = some next ↔
      config.state = rule.source ∧ config.tape₁.head = rule.read₁ ∧
        config.tape₂.head = rule.read₂ ∧
        next = ⟨rule.target,
          config.tape₁.act rule.write₁ rule.move₁,
          config.tape₂.act rule.write₂ rule.move₂⟩ := by
  unfold apply
  by_cases enabled : config.state = rule.source ∧
      config.tape₁.head = rule.read₁ ∧ config.tape₂.head = rule.read₂
  · simp [enabled, eq_comm]
  · simp only [enabled, if_false, reduceCtorEq, false_iff]
    rintro ⟨state_eq, read₁_eq, read₂_eq, _⟩
    exact enabled ⟨state_eq, read₁_eq, read₂_eq⟩

end Rule

/-- A finite ordered table of conventional two-tape rules. -/
structure FiniteMachine (Q : Type u) (Γ₁ : Type v) (Γ₂ : Type w) where
  rules : List (Rule Q Γ₁ Γ₂)
  deriving DecidableEq

namespace FiniteMachine

variable {Q : Type u} {Γ₁ : Type v} {Γ₂ : Type w}
  [Inhabited Γ₁] [Inhabited Γ₂]

def equivRep : FiniteMachine Q Γ₁ Γ₂ ≃ List (Rule Q Γ₁ Γ₂) where
  toFun machine := machine.rules
  invFun rules := ⟨rules⟩
  left_inv := by intro machine; cases machine; rfl
  right_inv := by intro rules; rfl

instance [Primcodable Q] [Primcodable Γ₁] [Primcodable Γ₂] :
    Primcodable (FiniteMachine Q Γ₁ Γ₂) :=
  Primcodable.ofEquiv (List (Rule Q Γ₁ Γ₂)) equivRep

/-- First rule matching a state and both scanned symbols. -/
def lookupRules [DecidableEq Q] [DecidableEq Γ₁] [DecidableEq Γ₂] :
    List (Rule Q Γ₁ Γ₂) → Q → Γ₁ → Γ₂ → Option (Rule Q Γ₁ Γ₂)
  | [], _, _, _ => none
  | rule :: rest, state, symbol₁, symbol₂ =>
      if rule.source = state ∧ rule.read₁ = symbol₁ ∧ rule.read₂ = symbol₂ then
        some rule
      else
        lookupRules rest state symbol₁ symbol₂

/-- Deterministic first-match lookup. -/
def lookup [DecidableEq Q] [DecidableEq Γ₁] [DecidableEq Γ₂]
    (machine : FiniteMachine Q Γ₁ Γ₂) (state : Q)
    (symbol₁ : Γ₁) (symbol₂ : Γ₂) : Option (Rule Q Γ₁ Γ₂) :=
  lookupRules machine.rules state symbol₁ symbol₂

omit [Inhabited Γ₁] [Inhabited Γ₂] in
theorem lookupRules_eq_some_mem [DecidableEq Q] [DecidableEq Γ₁] [DecidableEq Γ₂]
    {rules : List (Rule Q Γ₁ Γ₂)} {state : Q} {symbol₁ : Γ₁} {symbol₂ : Γ₂}
    {rule : Rule Q Γ₁ Γ₂}
    (h : lookupRules rules state symbol₁ symbol₂ = some rule) :
    rule ∈ rules := by
  induction rules with
  | nil => simp [lookupRules] at h
  | cons first rest ih =>
      simp only [lookupRules] at h
      split at h
      · exact List.mem_cons.mpr (Or.inl (Option.some.inj h).symm)
      · exact List.mem_cons.mpr (Or.inr (ih h))

omit [Inhabited Γ₁] [Inhabited Γ₂] in
theorem lookupRules_eq_some_key [DecidableEq Q] [DecidableEq Γ₁] [DecidableEq Γ₂]
    {rules : List (Rule Q Γ₁ Γ₂)} {state : Q} {symbol₁ : Γ₁} {symbol₂ : Γ₂}
    {rule : Rule Q Γ₁ Γ₂}
    (h : lookupRules rules state symbol₁ symbol₂ = some rule) :
    rule.source = state ∧ rule.read₁ = symbol₁ ∧ rule.read₂ = symbol₂ := by
  induction rules with
  | nil => simp [lookupRules] at h
  | cons first rest ih =>
      simp only [lookupRules] at h
      split at h
      · rename_i enabled
        cases Option.some.inj h
        exact enabled
      · exact ih h

omit [Inhabited Γ₁] [Inhabited Γ₂] in
theorem lookup_eq_some_mem [DecidableEq Q] [DecidableEq Γ₁] [DecidableEq Γ₂]
    {machine : FiniteMachine Q Γ₁ Γ₂} {state : Q}
    {symbol₁ : Γ₁} {symbol₂ : Γ₂} {rule : Rule Q Γ₁ Γ₂}
    (h : machine.lookup state symbol₁ symbol₂ = some rule) :
    rule ∈ machine.rules :=
  lookupRules_eq_some_mem h

omit [Inhabited Γ₁] [Inhabited Γ₂] in
theorem lookup_eq_some_key [DecidableEq Q] [DecidableEq Γ₁] [DecidableEq Γ₂]
    {machine : FiniteMachine Q Γ₁ Γ₂} {state : Q}
    {symbol₁ : Γ₁} {symbol₂ : Γ₂} {rule : Rule Q Γ₁ Γ₂}
    (h : machine.lookup state symbol₁ symbol₂ = some rule) :
    rule.source = state ∧ rule.read₁ = symbol₁ ∧ rule.read₂ = symbol₂ :=
  lookupRules_eq_some_key h

/-- Execute the first enabled rule. -/
def applyRules [DecidableEq Q] [DecidableEq Γ₁] [DecidableEq Γ₂] :
    List (Rule Q Γ₁ Γ₂) → Config Q Γ₁ Γ₂ → Option (Config Q Γ₁ Γ₂)
  | [], _ => none
  | rule :: rest, config =>
      match rule.apply config with
      | some next => some next
      | none => applyRules rest config

theorem applyRules_eq_lookupRules_map
    [DecidableEq Q] [DecidableEq Γ₁] [DecidableEq Γ₂]
    (rules : List (Rule Q Γ₁ Γ₂)) (config : Config Q Γ₁ Γ₂) :
    applyRules rules config =
      (lookupRules rules config.state config.tape₁.head config.tape₂.head).map
        fun rule => ⟨rule.target,
          config.tape₁.act rule.write₁ rule.move₁,
          config.tape₂.act rule.write₂ rule.move₂⟩ := by
  induction rules with
  | nil => rfl
  | cons rule rest ih =>
      by_cases enabled : config.state = rule.source ∧
          config.tape₁.head = rule.read₁ ∧ config.tape₂.head = rule.read₂
      · simp [applyRules, lookupRules, Rule.apply, enabled]
      · simp [applyRules, lookupRules, Rule.apply, enabled, ih, eq_comm]

/-- The deterministic first-match transition. -/
def step [DecidableEq Q] [DecidableEq Γ₁] [DecidableEq Γ₂]
    (machine : FiniteMachine Q Γ₁ Γ₂) : Step (Config Q Γ₁ Γ₂) :=
  applyRules machine.rules

theorem step_eq_some_iff [DecidableEq Q] [DecidableEq Γ₁] [DecidableEq Γ₂]
    (machine : FiniteMachine Q Γ₁ Γ₂) (config next : Config Q Γ₁ Γ₂) :
    machine.step config = some next ↔
      ∃ rule,
        machine.lookup config.state config.tape₁.head config.tape₂.head = some rule ∧
        next = ⟨rule.target,
          config.tape₁.act rule.write₁ rule.move₁,
          config.tape₂.act rule.write₂ rule.move₂⟩ := by
  rw [step, applyRules_eq_lookupRules_map]
  simp [lookup, eq_comm]

/-- Entries sharing the complete forward key must be equal. -/
def TableDeterministic (machine : FiniteMachine Q Γ₁ Γ₂) : Prop :=
  ∀ ⦃first⦄, first ∈ machine.rules → ∀ ⦃second⦄, second ∈ machine.rules →
    first.source = second.source → first.read₁ = second.read₁ →
      first.read₂ = second.read₂ → first = second

/-- Structural deterministic well-formedness. -/
abbrev WellFormed (machine : FiniteMachine Q Γ₁ Γ₂) : Prop :=
  machine.TableDeterministic

omit [Inhabited Γ₁] [Inhabited Γ₂] in
theorem TableDeterministic.rule_unique {machine : FiniteMachine Q Γ₁ Γ₂}
    (deterministic : machine.TableDeterministic)
    {first second : Rule Q Γ₁ Γ₂}
    (first_mem : first ∈ machine.rules) (second_mem : second ∈ machine.rules)
    (key_eq : first.key = second.key) : first = second :=
  deterministic first_mem second_mem
    (congrArg Prod.fst key_eq)
    (congrArg (fun key => key.2.1) key_eq)
    (congrArg (fun key => key.2.2) key_eq)

end FiniteMachine

end Lecerf.Machine.TwoTape
