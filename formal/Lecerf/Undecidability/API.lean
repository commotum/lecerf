import Lecerf.Undecidability.EffectiveTransition
import Lecerf.Undecidability.CodeIterates.API
import Lecerf.Undecidability.ReversibleTwoTape.API

/-!
# Public undecidability API

Exports the earlier abstract effective-transition checkpoint, the checked
finite reversible two-tape decision problems, and the finite-presentation
positive code-iterate problems reduced from them. The machine results are
deliberately not advertised as one-tape results, and the code inputs store raw
finite descriptors rather than semantic `CodeIso` proof objects.
-/
