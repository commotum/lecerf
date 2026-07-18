import Lecerf.Machine.Reversible
import Lecerf.Machine.SourceBridge
import Lecerf.Machine.History.API

/-!
# Public finite-machine API

Stable exports for canonical tapes, finite read-write-move machines, repaired
inverse execution, effective finite-machine interpretation, the universal
halting source, and the abstract reversible history simulator. Diagnostic
counterexamples remain in `Lecerf.Machine.Audit` and
`Lecerf.Machine.History.Audit`.
-/
