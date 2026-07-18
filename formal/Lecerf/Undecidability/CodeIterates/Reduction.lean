import Lecerf.Undecidability.CodeIterates.Correspondence
import Lecerf.Undecidability.CodeIterates.Effectivity
import Lecerf.Undecidability.ReversibleTwoTape.Reduction

/-!
# Reductions to positive code-iterate problems

The generic maps in this module canonically encode the configuration
endpoints of arbitrary raw reversible two-tape problem instances.  They leave
the finite descriptor untouched.  Consequently, an invalid descriptor stays
invalid on both sides of each exact iff theorem; the validity guard is neither
discarded nor repaired by the reduction.

The fixed-source halting reductions are obtained only after these generic
return and reachability reductions have been established.  Every map is
primitive recursive, and the final noncomputability results are transported
through explicit many-one reductions.
-/

namespace Lecerf.Undecidability.CodeIterates

open Lecerf.Encoding

noncomputable section

/-- Canonically encode the configuration of an arbitrary raw positive-return
instance, preserving its descriptor verbatim. -/
def encodeReturnInput
    (input : ReversibleTwoTape.ReturnInput) : FixedOrbitInput :=
  (input.1, ConfigCode.encodeConfig input.2)

/-- Canonically encode both endpoints of an arbitrary raw reachability
instance.  The runtime order remains descriptor, start, target. -/
def encodeReachabilityInput
    (input : ReversibleTwoTape.ReachabilityInput) : DistinctOrbitInput :=
  (input.1, ConfigCode.encodeConfig input.2.1,
    ConfigCode.encodeConfig input.2.2)

/-- The generic return-to-fixed-orbit map is primitive recursive. -/
theorem encodeReturnInput_primrec : Primrec encodeReturnInput := by
  exact Primrec.pair Primrec.fst
    (ConfigCode.encodeConfig_primrec.comp Primrec.snd)

/-- The generic return-to-fixed-orbit map is computable. -/
theorem encodeReturnInput_computable : Computable encodeReturnInput :=
  encodeReturnInput_primrec.to_comp

/-- The generic reachability-to-distinct-orbit map is primitive recursive. -/
theorem encodeReachabilityInput_primrec :
    Primrec encodeReachabilityInput := by
  exact Primrec.pair Primrec.fst
    (Primrec.pair
      (ConfigCode.encodeConfig_primrec.comp
        (Primrec.fst.comp Primrec.snd))
      (ConfigCode.encodeConfig_primrec.comp
        (Primrec.snd.comp Primrec.snd)))

/-- The generic reachability-to-distinct-orbit map is computable. -/
theorem encodeReachabilityInput_computable :
    Computable encodeReachabilityInput :=
  encodeReachabilityInput_primrec.to_comp

/-- Structural inequality of machine configurations is preserved by the
canonical indexed-code embedding. -/
theorem encodeReachabilityInput_start_ne_target
    (input : ReversibleTwoTape.ReachabilityInput)
    (distinct : input.2.1 ≠ input.2.2) :
    (encodeReachabilityInput input).2.1 ≠
      (encodeReachabilityInput input).2.2 := by
  change ConfigCode.encodeConfig input.2.1 ≠
    ConfigCode.encodeConfig input.2.2
  intro encodedEqual
  exact distinct
    (ConfigCode.encodeConfig_isIndexedCode.injective encodedEqual)

/-- For every raw descriptor, including an invalid one, certified positive
return is preserved and reflected exactly by canonical fixed-word orbit
encoding. -/
theorem returnYes_iff_positiveFixedOrbitYes
    (input : ReversibleTwoTape.ReturnInput) :
    ReversibleTwoTape.ReturnYes input ↔
      PositiveFixedOrbitYes (encodeReturnInput input) := by
  exact
    (positiveFixedOrbitYes_encodeConfig_iff_returnYes input.1 input.2).symm

/-- For every raw descriptor, including an invalid one, certified
distinct-target reachability is preserved and reflected exactly by canonical
word-orbit encoding. -/
theorem reachabilityYes_iff_distinctOrbitYes
    (input : ReversibleTwoTape.ReachabilityInput) :
    ReversibleTwoTape.ReachabilityYes input ↔
      DistinctOrbitYes (encodeReachabilityInput input) := by
  exact
    (distinctOrbitYes_encodeConfig_iff_reachabilityYes
      input.1 input.2.1 input.2.2).symm

/-- Generic many-one reduction from certified reversible-machine positive
return to positive fixed-word orbit. -/
theorem returnYes_manyOne_positiveFixedOrbitYes :
    ReversibleTwoTape.ReturnYes ≤₀ PositiveFixedOrbitYes :=
  ⟨encodeReturnInput, encodeReturnInput_computable,
    returnYes_iff_positiveFixedOrbitYes⟩

/-- Generic many-one reduction from certified reversible-machine
distinct-target reachability to distinct-word positive orbit. -/
theorem reachabilityYes_manyOne_distinctOrbitYes :
    ReversibleTwoTape.ReachabilityYes ≤₀ DistinctOrbitYes :=
  ⟨encodeReachabilityInput, encodeReachabilityInput_computable,
    reachabilityYes_iff_distinctOrbitYes⟩

/-- Direct fixed-source halting reduction to positive fixed-word orbit,
obtained by composing the Stage-6 return reduction with the generic canonical
encoding above. -/
theorem partrecHalts0_manyOne_positiveFixedOrbitYes :
    ReversibleTwoTape.PartrecHalts0 ≤₀ PositiveFixedOrbitYes :=
  ReversibleTwoTape.partrecHalts0_manyOne_returnYes.trans
    returnYes_manyOne_positiveFixedOrbitYes

/-- Direct fixed-source halting reduction to distinct-word positive orbit,
obtained by composing the Stage-6 reachability reduction with the generic
canonical encoding above. -/
theorem partrecHalts0_manyOne_distinctOrbitYes :
    ReversibleTwoTape.PartrecHalts0 ≤₀ DistinctOrbitYes :=
  ReversibleTwoTape.partrecHalts0_manyOne_reachabilityYes.trans
    reachabilityYes_manyOne_distinctOrbitYes

/-- Existence of a strictly positive fixed-word iterate is not computable for
finite raw code descriptors. -/
theorem positiveFixedOrbitYes_not_computable :
    ¬ComputablePred PositiveFixedOrbitYes := by
  intro targetComputable
  exact ComputablePred.halting_problem 0
    (ComputablePred.computable_of_manyOneReducible
      partrecHalts0_manyOne_positiveFixedOrbitYes targetComputable)

/-- Existence of a strictly positive iterate between specified distinct words
is not computable for finite raw code descriptors. -/
theorem distinctOrbitYes_not_computable :
    ¬ComputablePred DistinctOrbitYes := by
  intro targetComputable
  exact ComputablePred.halting_problem 0
    (ComputablePred.computable_of_manyOneReducible
      partrecHalts0_manyOne_distinctOrbitYes targetComputable)

end

end Lecerf.Undecidability.CodeIterates
