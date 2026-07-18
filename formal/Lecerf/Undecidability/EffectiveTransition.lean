import Lecerf.Machine.Coupling.Computable
import Mathlib.Computability.Reduce

/-!
# Undecidability for fixed effective reversible transitions

This is the reduction-theoretic checkpoint below the finite Turing-machine
compiler.  The three target predicates use fixed primitive-recursive
reversible transitions; only their start or target configurations vary.
They are intentionally not advertised as conventional finite-machine
decision problems.
-/

namespace Lecerf.Undecidability.EffectiveTransition

open Lecerf.Transition
open Lecerf.Machine

/-- The established source problem, specialized to input `0`. -/
def PartrecHalts0 (code : Nat.Partrec.Code) : Prop :=
  (Nat.Partrec.Code.eval code 0).Dom

/-- Configuration type of the fixed reversible history simulator. -/
abbrev HaltingConfig :=
  Machine.History.Config Machine.Source.EvalSearchConfig

/-- Configuration type of the fixed forward/reverse couplings. -/
abbrev CouplingConfig :=
  Machine.Coupling.Config HaltingConfig

/-- Halting for the fixed reversible full-history transition. -/
def ReversibleHaltingYes (config : HaltingConfig) : Prop :=
  HaltsFrom
    (Machine.History.reversible Machine.Source.universalEvalSearchStep).next
    config

/-- Positive return for the fixed closed history coupling. -/
def ReversibleReturnYes (config : CouplingConfig) : Prop :=
  PositiveReturn
    (Machine.Coupling.History.returnStep
      Machine.Source.universalEvalSearchStep).next
    config

/-- Strict reachability of a supplied, distinct target for the fixed open
history coupling. -/
def ReversibleReachabilityYes
    (input : CouplingConfig × CouplingConfig) : Prop :=
  input.1 ≠ input.2 ∧
    StrictlyReachable
      (Machine.Coupling.History.turnaroundStep
        Machine.Source.universalEvalSearchStep).next
      input.1 input.2

/-- Computable source map for reversible halting. -/
def compileHalting (code : Nat.Partrec.Code) : HaltingConfig :=
  Machine.History.universalHistoryStart code 0

/-- Computable source map for positive return. -/
def compileReturn (code : Nat.Partrec.Code) : CouplingConfig :=
  Machine.Coupling.History.universalStart code 0

/-- Computable source map for distinct-target reachability. -/
def compileReachability
    (code : Nat.Partrec.Code) : CouplingConfig × CouplingConfig :=
  (Machine.Coupling.History.universalStart code 0,
    Machine.Coupling.History.universalTarget code 0)

theorem compileHalting_primrec : Primrec compileHalting := by
  exact (Machine.History.universalHistoryStart_joint_primrec.comp
    (Primrec.id.pair (Primrec.const 0))).of_eq fun _ => rfl

theorem compileReturn_primrec : Primrec compileReturn := by
  exact (Machine.Coupling.History.universalStart_joint_primrec.comp
    (Primrec.id.pair (Primrec.const 0))).of_eq fun _ => rfl

theorem compileReachability_primrec : Primrec compileReachability := by
  exact (Machine.Coupling.History.universalStartTarget_joint_primrec.comp
    (Primrec.id.pair (Primrec.const 0))).of_eq fun _ => rfl

/-- Source halting is preserved and reflected by the fixed reversible history
transition. -/
theorem partrecHalts0_iff_reversibleHalting (code : Nat.Partrec.Code) :
    PartrecHalts0 code ↔ ReversibleHaltingYes (compileHalting code) := by
  simpa [PartrecHalts0, ReversibleHaltingYes, compileHalting] using
    (Machine.History.universalHistory_halts_iff_eval_dom code 0).symm

/-- Source halting is preserved and reflected by positive return of the fixed
closed coupling. -/
theorem partrecHalts0_iff_reversibleReturn (code : Nat.Partrec.Code) :
    PartrecHalts0 code ↔ ReversibleReturnYes (compileReturn code) := by
  simpa [PartrecHalts0, ReversibleReturnYes, compileReturn] using
    (Machine.Coupling.History.universalPositiveReturn_iff_eval_dom code 0).symm

/-- Source halting is preserved and reflected by strict reachability of the
computed, structurally distinct target. -/
theorem partrecHalts0_iff_reversibleReachability (code : Nat.Partrec.Code) :
    PartrecHalts0 code ↔
      ReversibleReachabilityYes (compileReachability code) := by
  constructor
  · intro halts
    exact ⟨Machine.Coupling.History.start_ne_target
        (Machine.Source.evalSearchStart code 0),
      (Machine.Coupling.History.universalTarget_strictlyReachable_iff_eval_dom
        code 0).mpr halts⟩
  · intro reaches
    exact (Machine.Coupling.History.universalTarget_strictlyReachable_iff_eval_dom
      code 0).mp reaches.2

theorem partrecHalts0_manyOne_reversibleHalting :
    PartrecHalts0 ≤₀ ReversibleHaltingYes :=
  ⟨compileHalting, compileHalting_primrec.to_comp,
    partrecHalts0_iff_reversibleHalting⟩

theorem partrecHalts0_manyOne_reversibleReturn :
    PartrecHalts0 ≤₀ ReversibleReturnYes :=
  ⟨compileReturn, compileReturn_primrec.to_comp,
    partrecHalts0_iff_reversibleReturn⟩

theorem partrecHalts0_manyOne_reversibleReachability :
    PartrecHalts0 ≤₀ ReversibleReachabilityYes :=
  ⟨compileReachability, compileReachability_primrec.to_comp,
    partrecHalts0_iff_reversibleReachability⟩

/-- Halting for this fixed primitive-recursive reversible transition is not a
computable predicate. -/
theorem reversibleHalting_not_computable :
    ¬ComputablePred ReversibleHaltingYes := by
  intro targetComputable
  exact ComputablePred.halting_problem 0
    (ComputablePred.computable_of_manyOneReducible
      partrecHalts0_manyOne_reversibleHalting targetComputable)

/-- Positive return for this fixed primitive-recursive reversible transition
is not a computable predicate. -/
theorem reversibleReturn_not_computable :
    ¬ComputablePred ReversibleReturnYes := by
  intro targetComputable
  exact ComputablePred.halting_problem 0
    (ComputablePred.computable_of_manyOneReducible
      partrecHalts0_manyOne_reversibleReturn targetComputable)

/-- Distinct-target strict reachability for this fixed primitive-recursive
reversible transition is not a computable predicate. -/
theorem reversibleReachability_not_computable :
    ¬ComputablePred ReversibleReachabilityYes := by
  intro targetComputable
  exact ComputablePred.halting_problem 0
    (ComputablePred.computable_of_manyOneReducible
      partrecHalts0_manyOne_reversibleReachability targetComputable)

end Lecerf.Undecidability.EffectiveTransition
