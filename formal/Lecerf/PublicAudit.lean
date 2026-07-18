import Lecerf

/-!
# Public-surface and headline trust audit

This diagnostic module imports only the stable public root before checking the
principal declarations.  It is intentionally not imported by `Lecerf`.
The axiom commands cover the main theorem chain from partial transitions
through reversible machines and simulations to both undecidability layers.
-/

/-! ## Public signatures -/

#check Lecerf.Transition.Step
#check Lecerf.Transition.BackwardUnique
#check Lecerf.Transition.ReversibleStep
#check Lecerf.Transition.PositiveReturn
#check Lecerf.Transition.ReversibleStep.next_eq_some_iff_prev_eq_some
#check Lecerf.Transition.ReversibleStep.strictlyReachable_iff_reverse_strictlyReachable

#check Lecerf.Machine.Tape
#check Lecerf.Machine.Rule
#check Lecerf.Machine.FiniteMachine
#check Lecerf.Machine.FiniteMachine.Reversible
#check Lecerf.Machine.Rule.apply_eq_some_iff_undo_eq_some
#check Lecerf.Machine.FiniteMachine.backwardCompatible_iff_backwardUnique

#check Lecerf.Machine.History.reversible
#check Lecerf.Machine.History.reachable_iff_valid
#check Lecerf.Machine.History.haltsFrom_forward_iff
#check Lecerf.Machine.History.finiteForward_uniform_primrec
#check Lecerf.Machine.Coupling.History.target_strictlyReachable_iff_halts
#check Lecerf.Machine.Coupling.History.positiveReturn_iff_halts

#check Lecerf.Machine.TwoTape.FiniteMachine
#check Lecerf.Machine.TwoTape.HistoryCompiler.historyMachine
#check Lecerf.Machine.TwoTape.HistoryCompiler.historyMachine_syntacticallyReversible
#check Lecerf.Machine.TwoTape.HistoryCompiler.historyMachine_haltsFrom_iff_source
#check Lecerf.Machine.TwoTape.HistoryCompiler.turnaround_bottom_strictlyReachable_iff_source_halts
#check Lecerf.Machine.TwoTape.HistoryCompiler.return_positiveReturn_iff_source_halts

#check Lecerf.Undecidability.ReversibleTwoTape.HaltingYes
#check Lecerf.Undecidability.ReversibleTwoTape.ReturnYes
#check Lecerf.Undecidability.ReversibleTwoTape.ReachabilityYes
#check Lecerf.Undecidability.ReversibleTwoTape.partrecHalts0_manyOne_haltingYes
#check Lecerf.Undecidability.ReversibleTwoTape.partrecHalts0_manyOne_returnYes
#check Lecerf.Undecidability.ReversibleTwoTape.partrecHalts0_manyOne_reachabilityYes

#check Lecerf.Word.IsIndexedCode
#check Lecerf.Word.isIndexedCode_iff_injective_and_uniquelyDecodable
#check Lecerf.Word.InjectiveMorphism
#check Lecerf.Word.CodeIso
#check Lecerf.Word.PaperCodeEpi
#check Lecerf.PEquiv.iterate
#check Lecerf.PEquiv.PositiveIterate

#check Lecerf.Encoding.ConfigCode.encodeConfig
#check Lecerf.Encoding.ConfigCode.decodeConfig
#check Lecerf.Encoding.StepCode.stepCodeIso
#check Lecerf.Encoding.StepCode.stepCodeIso_apply_eq_some_iff
#check Lecerf.Encoding.StepCode.stepCodeIso_positiveIterate_iff_strictlyReachable
#check Lecerf.Encoding.StepCode.Descriptor.checkedApply_uniform_primrec

#check Lecerf.Undecidability.CodeIterates.PositiveFixedOrbitYes
#check Lecerf.Undecidability.CodeIterates.DistinctOrbitYes
#check Lecerf.Undecidability.CodeIterates.PositiveIterateAtYes
#check Lecerf.Undecidability.CodeIterates.positiveIterateAtYes_computablePred
#check Lecerf.Undecidability.CodeIterates.positiveFixedOrbitYes_re
#check Lecerf.Undecidability.CodeIterates.distinctOrbitYes_re
#check Lecerf.Undecidability.CodeIterates.partrecHalts0_manyOne_positiveFixedOrbitYes
#check Lecerf.Undecidability.CodeIterates.partrecHalts0_manyOne_distinctOrbitYes

/-! ## Headline axiom audit -/

#print axioms Lecerf.Transition.haltsFrom_iff_exists_reachable_terminal
#print axioms Lecerf.Transition.ReversibleStep.next_eq_some_iff_prev_eq_some
#print axioms Lecerf.Transition.ReversibleStep.strictlyReachable_iff_reverse_strictlyReachable

#print axioms Lecerf.Machine.Rule.apply_eq_some_iff_undo_eq_some
#print axioms Lecerf.Machine.FiniteMachine.step_eq_some_iff_reverseStep_eq_some
#print axioms Lecerf.Machine.FiniteMachine.backwardCompatible_iff_backwardUnique

#print axioms Lecerf.Machine.History.forward_eq_some_iff_backward_eq_some
#print axioms Lecerf.Machine.History.reachable_iff_valid
#print axioms Lecerf.Machine.History.haltsFrom_forward_iff
#print axioms Lecerf.Machine.History.finiteForward_uniform_primrec
#print axioms Lecerf.Machine.History.finiteBackward_uniform_primrec

#print axioms Lecerf.Machine.TwoTape.HistoryCompiler.historyMachine_syntacticallyReversible
#print axioms Lecerf.Machine.TwoTape.HistoryCompiler.historyMachine_haltsFrom_iff_source
#print axioms Lecerf.Machine.TwoTape.HistoryCompiler.turnaround_bottom_strictlyReachable_iff_source_halts
#print axioms Lecerf.Machine.TwoTape.HistoryCompiler.return_positiveReturn_iff_source_halts

#print axioms Lecerf.Machine.Compiler.FiniteSource.halts_iff_eval_dom
#print axioms Lecerf.Machine.Compiler.FiniteSource.initial_joint_primrec
#print axioms Lecerf.Machine.Compiler.ReversibleUniversal.eval_dom_iff_history_halts
#print axioms Lecerf.Machine.Compiler.ReversibleUniversal.eval_dom_iff_turnaround_bottom_strictlyReachable
#print axioms Lecerf.Machine.Compiler.ReversibleUniversal.eval_dom_iff_return_positiveReturn

#print axioms Lecerf.Undecidability.ReversibleTwoTape.partrecHalts0_manyOne_haltingYes
#print axioms Lecerf.Undecidability.ReversibleTwoTape.partrecHalts0_manyOne_returnYes
#print axioms Lecerf.Undecidability.ReversibleTwoTape.partrecHalts0_manyOne_reachabilityYes
#print axioms Lecerf.Undecidability.ReversibleTwoTape.haltingYes_not_computable
#print axioms Lecerf.Undecidability.ReversibleTwoTape.returnYes_not_computable
#print axioms Lecerf.Undecidability.ReversibleTwoTape.reachabilityYes_not_computable

#print axioms Lecerf.Word.isIndexedCode_iff_injective_and_uniquelyDecodable
#print axioms Lecerf.Word.isIndexedCode_prependMarkerExtension
#print axioms Lecerf.Word.isIndexedCode_appendMarkerExtension
#print axioms Lecerf.Word.CodeIso.toPEquiv_generator
#print axioms Lecerf.PEquiv.iterate_symm

#print axioms Lecerf.Encoding.ConfigCode.decodeConfigs_eq_some_iff
#print axioms Lecerf.Encoding.ConfigCode.decodeConfigs_primrec
#print axioms Lecerf.Encoding.StepCode.targetWord_isIndexedCode_iff_backwardUnique
#print axioms Lecerf.Encoding.StepCode.stepCodeIso_apply_eq_some_iff_exists
#print axioms Lecerf.Encoding.StepCode.stepCodeIso_iterate_eq_some_iff
#print axioms Lecerf.Encoding.StepCode.stepCodeIso_positiveIterate_iff_strictlyReachable
#print axioms Lecerf.Encoding.StepCode.Descriptor.checkedApply_uniform_primrec

#print axioms Lecerf.Undecidability.CodeIterates.positiveIterateAtYes_computablePred
#print axioms Lecerf.Undecidability.CodeIterates.positiveFixedOrbitYes_re
#print axioms Lecerf.Undecidability.CodeIterates.distinctOrbitYes_re
#print axioms Lecerf.Undecidability.CodeIterates.partrecHalts0_manyOne_positiveFixedOrbitYes
#print axioms Lecerf.Undecidability.CodeIterates.partrecHalts0_manyOne_distinctOrbitYes
#print axioms Lecerf.Undecidability.CodeIterates.positiveFixedOrbitYes_not_computable
#print axioms Lecerf.Undecidability.CodeIterates.distinctOrbitYes_not_computable

