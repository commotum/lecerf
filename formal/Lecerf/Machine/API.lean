import Lecerf.Machine.Reversible
import Lecerf.Machine.SourceBridge
import Lecerf.Machine.History.API
import Lecerf.Machine.Coupling.API

/-!
# Public finite-machine API

Stable exports for canonical tapes, finite read-write-move machines, repaired
inverse execution, effective finite-machine interpretation, the universal
halting source, the abstract reversible history simulator, and exact
forward--reverse target and return couplings. Diagnostic counterexamples
remain in `Lecerf.Machine.Audit`, `Lecerf.Machine.History.Audit`, and
`Lecerf.Machine.Coupling.Audit`.
-/
