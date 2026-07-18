import Lecerf.Machine.Core

/-!
# Expanding finite transition data into conventional rule tables

This module turns a transition function, together with explicit finite lists
of states and symbols, into the project's first-match `FiniteMachine` syntax.
The lists need not be duplicate-free: repeated entries emit only identical
rules and do not change the selected transition.

The construction is a generic table-expansion layer.  It does not assert that
an arbitrary computable transition has finite support; callers must supply and
maintain the state and alphabet membership hypotheses used by the exact-step
theorem.
-/

namespace Lecerf.Machine.Compiler.Table

universe u v

variable {Q : Type u} {Γ : Type v} [Inhabited Γ]

/-- A combined read/write/move transition before expansion into conventional
rules. -/
abbrev Delta (Q : Type u) (Γ : Type v) :=
  Q → Γ → Option (Q × Γ × Tape.Move)

/-- Expand one successful transition entry into a conventional rule. -/
def ruleFor (delta : Delta Q Γ) (state : Q) (symbol : Γ) : Option (Rule Q Γ) :=
  (delta state symbol).map fun output =>
    { source := state
      read := symbol
      target := output.1
      write := output.2.1
      move := output.2.2 }

/-- Expand one state's entries over an explicit symbol list. -/
def rulesForSymbols (delta : Delta Q Γ) (state : Q) : List Γ → List (Rule Q Γ)
  | [] => []
  | symbol :: rest =>
      (ruleFor delta state symbol).toList ++ rulesForSymbols delta state rest

/-- Expand explicit state and symbol supports into a finite first-match table. -/
def compile (delta : Delta Q Γ) (states : List Q) (symbols : List Γ) :
    FiniteMachine Q Γ :=
  ⟨states.flatMap fun state => rulesForSymbols delta state symbols⟩

omit [Inhabited Γ] in
/-- A rule occurs in one expanded state block exactly when it is the output
for one of the listed symbols.  This statement deliberately permits repeated
symbols. -/
theorem mem_rulesForSymbols_iff
    (delta : Delta Q Γ) (state : Q) (symbols : List Γ) (rule : Rule Q Γ) :
    rule ∈ rulesForSymbols delta state symbols ↔
      ∃ symbol ∈ symbols, ruleFor delta state symbol = some rule := by
  induction symbols with
  | nil => simp [rulesForSymbols]
  | cons symbol rest ih =>
      simp [rulesForSymbols, ih]

omit [Inhabited Γ] in
/-- Membership in an expanded table records a generating state and symbol.
Duplicate support entries merely give duplicate witnesses. -/
theorem mem_compile_iff
    (delta : Delta Q Γ) (states : List Q) (symbols : List Γ) (rule : Rule Q Γ) :
    rule ∈ (compile delta states symbols).rules ↔
      ∃ state ∈ states, ∃ symbol ∈ symbols,
        ruleFor delta state symbol = some rule := by
  simp [compile, mem_rulesForSymbols_iff]

omit [Inhabited Γ] in
/-- Expanding a transition function yields a deterministic conventional rule
table. Repetitions in either support list emit only identical rules. -/
theorem compile_tableDeterministic
    (delta : Delta Q Γ) (states : List Q) (symbols : List Γ) :
    (compile delta states symbols).TableDeterministic := by
  intro first firstMem second secondMem sourceEq readEq
  rw [mem_compile_iff] at firstMem secondMem
  rcases firstMem with ⟨firstState, _, firstSymbol, _, firstRule⟩
  rcases secondMem with ⟨secondState, _, secondSymbol, _, secondRule⟩
  have firstFields :
      first.source = firstState ∧ first.read = firstSymbol := by
    unfold ruleFor at firstRule
    cases h : delta firstState firstSymbol with
    | none => simp [h] at firstRule
    | some output =>
      rcases output with ⟨target, write, move⟩
      simp [h] at firstRule
      subst first
      exact ⟨rfl, rfl⟩
  have secondFields :
      second.source = secondState ∧ second.read = secondSymbol := by
    unfold ruleFor at secondRule
    cases h : delta secondState secondSymbol with
    | none => simp [h] at secondRule
    | some output =>
      rcases output with ⟨target, write, move⟩
      simp [h] at secondRule
      subst second
      exact ⟨rfl, rfl⟩
  have stateEq : firstState = secondState :=
    firstFields.1.symm.trans (sourceEq.trans secondFields.1)
  have symbolEq : firstSymbol = secondSymbol :=
    firstFields.2.symm.trans (readEq.trans secondFields.2)
  subst secondState
  subst secondSymbol
  exact Option.some.inj (firstRule.symm.trans secondRule)

omit [Inhabited Γ] in
theorem lookup_rulesForSymbols_eq
    [DecidableEq Q] [DecidableEq Γ]
    (delta : Delta Q Γ) (state : Q) (symbols : List Γ) (symbol : Γ) :
    FiniteMachine.lookupRules (rulesForSymbols delta state symbols) state symbol =
      if symbol ∈ symbols then ruleFor delta state symbol else none := by
  induction symbols with
  | nil => rfl
  | cons first rest ih =>
      simp only [rulesForSymbols, ruleFor]
      cases h : delta state first with
      | none =>
          by_cases equal : first = symbol
          · subst first
            simp [h, ih, ruleFor]
          · by_cases member : symbol ∈ rest <;>
              simp [Ne.symm equal, ih, member, ruleFor]
      | some output =>
          rcases output with ⟨target, write, move⟩
          by_cases equal : first = symbol
          · subst first
            simp [FiniteMachine.lookupRules, h]
          · by_cases member : symbol ∈ rest <;>
              simp [FiniteMachine.lookupRules, equal, Ne.symm equal, ih, member, ruleFor]

omit [Inhabited Γ] in
theorem lookupRules_append [DecidableEq Q] [DecidableEq Γ]
    (first second : List (Rule Q Γ)) (state : Q) (symbol : Γ) :
    FiniteMachine.lookupRules (first ++ second) state symbol =
      (FiniteMachine.lookupRules first state symbol <|>
        FiniteMachine.lookupRules second state symbol) := by
  induction first with
  | nil => rfl
  | cons rule rest ih =>
      simp only [List.cons_append, FiniteMachine.lookupRules]
      split
      · rfl
      · exact ih

omit [Inhabited Γ] in
theorem lookup_rulesForSymbols_ne
    [DecidableEq Q] [DecidableEq Γ]
    (delta : Delta Q Γ) {first second : Q} (notEqual : first ≠ second)
    (symbols : List Γ) (symbol : Γ) :
    FiniteMachine.lookupRules (rulesForSymbols delta first symbols) second symbol = none := by
  induction symbols with
  | nil => rfl
  | cons head rest ih =>
      simp only [rulesForSymbols, ruleFor]
      cases h : delta first head with
      | none => simpa using ih
      | some output =>
          rcases output with ⟨target, write, move⟩
          simp [FiniteMachine.lookupRules, notEqual, ih]

omit [Inhabited Γ] in
/-- Lookup in the expanded table is exactly the supplied transition entry on
the listed support, and is absent off that support. -/
theorem lookup_compile_eq
    [DecidableEq Q] [DecidableEq Γ]
    (delta : Delta Q Γ) (states : List Q) (symbols : List Γ)
    (state : Q) (symbol : Γ) :
    (compile delta states symbols).lookup state symbol =
      if state ∈ states ∧ symbol ∈ symbols then ruleFor delta state symbol else none := by
  induction states with
  | nil => rfl
  | cons first rest ih =>
      change FiniteMachine.lookupRules
        (rulesForSymbols delta first symbols ++
          List.flatMap (fun state => rulesForSymbols delta state symbols) rest)
          state symbol = _
      rw [lookupRules_append]
      by_cases equal : first = state
      · subst first
        rw [lookup_rulesForSymbols_eq]
        by_cases member : symbol ∈ symbols
        · simp only [member, List.mem_cons, true_or, true_and, if_true]
          rw [show FiniteMachine.lookupRules
              (List.flatMap (fun state => rulesForSymbols delta state symbols) rest)
                state symbol =
              (compile delta rest symbols).lookup state symbol by rfl]
          cases h : ruleFor delta state symbol with
          | none => rw [ih]; simp [member, h]
          | some rule => rfl
        · simp only [member, List.mem_cons, true_or, and_false, if_false]
          change (compile delta rest symbols).lookup state symbol = none
          rw [ih]
          simp [member]
      · rw [lookup_rulesForSymbols_ne delta equal symbols symbol]
        change (compile delta rest symbols).lookup state symbol = _
        rw [ih]
        simp [Ne.symm equal]

/-- On configurations whose state and scanned symbol belong to the supplied
supports, one compiled conventional step is exactly the original combined
transition. -/
theorem step_compile_eq
    [DecidableEq Q] [DecidableEq Γ]
    (delta : Delta Q Γ) (states : List Q) (symbols : List Γ)
    (config : Config Q Γ)
    (stateMember : config.state ∈ states)
    (symbolMember : config.tape.head ∈ symbols) :
    (compile delta states symbols).step config =
      (delta config.state config.tape.head).map fun output =>
        ⟨output.1, config.tape.act output.2.1 output.2.2⟩ := by
  rw [FiniteMachine.step, FiniteMachine.applyRules_eq_lookupRules_map]
  change Option.map _ ((compile delta states symbols).lookup
    config.state config.tape.head) = _
  rw [show (compile delta states symbols).lookup config.state config.tape.head =
      ruleFor delta config.state config.tape.head by
    rw [lookup_compile_eq]
    simp [stateMember, symbolMember]]
  simp only [ruleFor]
  cases delta config.state config.tape.head <;> rfl

end Lecerf.Machine.Compiler.Table
