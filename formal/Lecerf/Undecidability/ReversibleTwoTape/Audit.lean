import Lecerf.Undecidability.ReversibleTwoTape.Reduction

/-!
# Diagnostics and axiom audit for reversible two-tape undecidability

This module is intentionally excluded from public APIs.  The small Boolean
tables exercise both outcomes of the finite validity checker, while the axiom
commands expose the dependencies of representative semantic and reduction
theorems.
-/

namespace Lecerf.Undecidability.ReversibleTwoTape.Audit

open Lecerf.Machine

/-- One individually invertible simultaneous two-tape rule. -/
def validRule : TwoTape.Rule Bool Bool Bool where
  source := false
  read₁ := false
  read₂ := false
  target := true
  write₁ := true
  move₁ := .right
  write₂ := true
  move₂ := .left

def validTable : TwoTape.FiniteMachine Bool Bool Bool :=
  ⟨[validRule]⟩

/-- The finite checker accepts a singleton reversible table. -/
example : validTable.SyntacticallyReversible := by
  decide

def conflictingRule : TwoTape.Rule Bool Bool Bool where
  source := false
  read₁ := false
  read₂ := false
  target := false
  write₁ := false
  move₁ := .stay
  write₂ := false
  move₂ := .stay

def conflictingTable : TwoTape.FiniteMachine Bool Bool Bool :=
  ⟨[validRule, conflictingRule]⟩

/-- Conflicting entries with the same complete forward key are rejected. -/
example : ¬conflictingTable.SyntacticallyReversible := by
  decide

#print axioms Lecerf.Machine.TwoTape.HistoryCompiler.return_positiveReturn_iff_source_halts
#print axioms Lecerf.Machine.Compiler.ReversibleUniversal.eval_dom_iff_history_halts
#print axioms Lecerf.Undecidability.ReversibleTwoTape.partrecHalts0_manyOne_haltingYes
#print axioms Lecerf.Undecidability.ReversibleTwoTape.haltingYes_not_computable
#print axioms Lecerf.Undecidability.ReversibleTwoTape.returnYes_not_computable
#print axioms Lecerf.Undecidability.ReversibleTwoTape.reachabilityYes_not_computable

end Lecerf.Undecidability.ReversibleTwoTape.Audit
