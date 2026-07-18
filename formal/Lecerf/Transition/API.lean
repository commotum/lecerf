import Lecerf.Transition.Reversible
import Lecerf.Transition.ExactCore
import Lecerf.Transition.ExactEffectivity

/-!
# Public transition API

Stable re-export of generic deterministic partial execution, exact-length
execution and reachability, its uniform primitive-recursive iterator, and
reversible partial-step semantics. Bridges to word-level partial-equivalence
powers remain in `Lecerf.Transition.Exact`. Diagnostic examples remain in
`Lecerf.Transition.Audit` and are intentionally not imported here.
-/
