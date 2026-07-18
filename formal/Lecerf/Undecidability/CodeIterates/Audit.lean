import Lecerf.Undecidability.CodeIterates.Reduction

/-!
# Diagnostics and axiom audit for code-iterate undecidability

These non-public checks expose the three boundaries most easily obscured by
an informal iterate equation: exponent zero is not a witness, failure of a
partial iterate persists through every extension, and canonical reduction
words are not the empty free-monoid word.
-/

namespace Lecerf.Undecidability.CodeIterates.Audit

open Lecerf.Encoding
open Lecerf.Transition
open Lecerf.Word

/-- The supplied-exponent recognizer rejects exponent zero independently of
the descriptor and endpoint words. -/
example (descriptor : CodeDescriptor) (source target : Word Bool) :
    ¬PositiveIterateAtYes (descriptor, 0, source, target) := by
  intro yes
  exact yes.2.1 rfl

/-- Once exact partial iteration has failed, extending the requested length
cannot turn that failure into an identity or sink result. -/
example {σ : Type*} (next : Step σ) (m n : Nat) (state : σ)
    (failed : exactIterate next m state = none) :
    exactIterate next (m + n) state = none := by
  rw [exactIterate_add, failed]
  rfl

/-- The fixed-orbit word produced by the canonical return reduction is a
nonempty configuration frame. -/
example (input : ReversibleTwoTape.ReturnInput) :
    (encodeReturnInput input).2 ≠ (1 : Word Bool) := by
  change ConfigCode.encodeConfig input.2 ≠ 1
  exact ConfigCode.encodeConfig_ne_one input.2

#print axioms Lecerf.Undecidability.CodeIterates.positiveFixedOrbitYes_iff_stepCodeIso_positiveIterate
#print axioms Lecerf.Undecidability.CodeIterates.distinctOrbitYes_iff_stepCodeIso_positiveIterate
#print axioms Lecerf.Undecidability.CodeIterates.partrecHalts0_manyOne_positiveFixedOrbitYes
#print axioms Lecerf.Undecidability.CodeIterates.partrecHalts0_manyOne_distinctOrbitYes
#print axioms Lecerf.Undecidability.CodeIterates.positiveFixedOrbitYes_re
#print axioms Lecerf.Undecidability.CodeIterates.distinctOrbitYes_re
#print axioms Lecerf.Undecidability.CodeIterates.positiveIterateAtYes_computablePred
#print axioms Lecerf.Undecidability.CodeIterates.positiveFixedOrbitYes_not_computable
#print axioms Lecerf.Undecidability.CodeIterates.distinctOrbitYes_not_computable

end Lecerf.Undecidability.CodeIterates.Audit
