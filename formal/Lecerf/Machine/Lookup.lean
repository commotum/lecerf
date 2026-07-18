import Lecerf.Machine.Core

/-!
# Lookup facts for conventional finite machines

These small lemmas complement the first-match runtime API.  Membership of a
rule guarantees that its key is defined, and a deterministic table returns
that very rule at its key even when identical duplicate entries occur.
-/

namespace Lecerf.Machine.FiniteMachine

universe u v

variable {Q : Type u} {Γ : Type v} [Inhabited Γ]

omit [Inhabited Γ] in
theorem lookupRules_ne_none_of_mem [DecidableEq Q] [DecidableEq Γ]
    {rules : List (Rule Q Γ)} {rule : Rule Q Γ}
    (member : rule ∈ rules) :
    lookupRules rules rule.source rule.read ≠ none := by
  induction rules with
  | nil => simp at member
  | cons first rest ih =>
      rcases List.mem_cons.mp member with equal | member
      · subst first
        simp [lookupRules]
      · by_cases enabled : first.source = rule.source ∧ first.read = rule.read
        · simp [lookupRules, enabled]
        · simp only [lookupRules, enabled, if_false]
          exact ih member

omit [Inhabited Γ] in
/-- A deterministic table returns any member at that member's own key. -/
theorem lookup_eq_some_of_mem [DecidableEq Q] [DecidableEq Γ]
    {machine : FiniteMachine Q Γ} (deterministic : machine.TableDeterministic)
    {rule : Rule Q Γ} (member : rule ∈ machine.rules) :
    machine.lookup rule.source rule.read = some rule := by
  have defined : machine.lookup rule.source rule.read ≠ none := by
    exact lookupRules_ne_none_of_mem member
  cases foundEq : machine.lookup rule.source rule.read with
  | none => exact False.elim (defined foundEq)
  | some found =>
      have foundMember := lookup_eq_some_mem foundEq
      have foundKey := lookup_eq_some_key foundEq
      have equal : rule = found := deterministic member foundMember
        foundKey.1.symm foundKey.2.symm
      exact congrArg some equal.symm

end Lecerf.Machine.FiniteMachine
