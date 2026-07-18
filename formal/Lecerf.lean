import Lecerf.Transition.API
import Lecerf.Machine.API
import Lecerf.Undecidability.API
import Lecerf.Word.API

/-!
# Lecerf

Public root for the formalization of reversible machines and code
isomorphisms. It currently exports the generic transition layer together with
canonical finite-support tapes, finite read-write-move machines, repaired
inverse semantics, effective finite-machine execution, the universal search
source, verified abstract and finite two-tape history simulations, exact
forward--reverse target and positive-return couplings, and validity-guarded
undecidability reductions for finite reversible two-tape machines. It also
exports the independent free-monoid layer for indexed codes, prefix/suffix
criteria, code map classes, generated-submonoid isomorphisms, ambient partial
actions, and positive partial iteration.
-/
