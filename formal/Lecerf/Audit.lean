import Lecerf.PublicAudit
import Lecerf.Transition.Audit
import Lecerf.Machine.Audit
import Lecerf.Machine.History.Audit
import Lecerf.Machine.Coupling.Audit
import Lecerf.Undecidability.ReversibleTwoTape.Audit
import Lecerf.Word.Audit
import Lecerf.Encoding.StepCode.Audit
import Lecerf.Undecidability.CodeIterates.Audit

/-!
# Consolidated non-public audit target

`lake build Lecerf.Audit` checks the stable public signatures, headline axiom
dependencies, and all feature-specific diagnostic examples. Nothing in this
module is re-exported by `Lecerf`.
-/

