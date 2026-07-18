import Lecerf.Encoding.StepCode.Effectivity
import Lecerf.Transition.Exact
import Lecerf.Undecidability.ReversibleTwoTape.Problems

/-!
# Raw decision problems for positive code iterates

The runtime presentation is a finite reversible two-tape rule table together
with Boolean words.  It contains no semantic `CodeIso`, partial equivalence,
function, validity proof, orbit witness, or choice-based decoder.

For a distinct-orbit input, the stored order is `(descriptor, start, target)`.
Thus the paper's equation `w₁ = θⁿ(w₂)` is represented with `w₂` as the
start word and `w₁` as the target word.  Every existential exponent below
is definitionally `k + 1`; exponent zero is not an admissible witness.
-/

namespace Lecerf.Undecidability.CodeIterates

open Lecerf.Encoding.StepCode
open Lecerf.Transition
open Lecerf.Word

/-- Finite raw presentation of the successful-edge code action.  The fixed
control and tape alphabets are those used by the reversible universal
compiler. -/
abbrev CodeDescriptor :=
  Descriptor ReversibleTwoTape.MachineState
    ReversibleTwoTape.WorkSymbol ReversibleTwoTape.HistorySymbol

/-- A raw descriptor and the word proposed to lie on a positive fixed orbit. -/
abbrev FixedOrbitInput := CodeDescriptor × Word Bool

/-- A raw descriptor, start word, and specified target word.  The start is
stored before the target even though the paper writes the target on the left
of its iterate equation. -/
abbrev DistinctOrbitInput :=
  CodeDescriptor × Word Bool × Word Bool

/-- A raw descriptor, supplied exponent, start word, and target word.  This is
kept separate from the existential orbit problems so that checking a supplied
positive exponent cannot be confused with deciding whether one exists. -/
abbrev SuppliedExponentInput :=
  CodeDescriptor × Nat × Word Bool × Word Bool

/-- A valid finite descriptor returns the supplied word to itself after some
strictly positive exact number of checked applications. -/
def PositiveFixedOrbitYes (input : FixedOrbitInput) : Prop :=
  input.1.Valid ∧
    ∃ k : Nat,
      ExactSteps input.1.checkedApply (k + 1) input.2 input.2

/-- A valid finite descriptor sends the supplied start word to the distinct
supplied target after some strictly positive exact number of checked
applications. -/
def DistinctOrbitYes (input : DistinctOrbitInput) : Prop :=
  input.1.Valid ∧ input.2.1 ≠ input.2.2 ∧
    ∃ k : Nat,
      ExactSteps input.1.checkedApply (k + 1) input.2.1 input.2.2

/-- Recognition problem for a supplied exponent.  In the right-associated
product, the projections are descriptor `input.1`, exponent `input.2.1`,
start `input.2.2.1`, and target `input.2.2.2`.  Positivity is an explicit
guard, and `ExactSteps` propagates any undefined intermediate application. -/
def PositiveIterateAtYes (input : SuppliedExponentInput) : Prop :=
  input.1.Valid ∧ input.2.1 ≠ 0 ∧
    ExactSteps input.1.checkedApply input.2.1
      input.2.2.1 input.2.2.2

end Lecerf.Undecidability.CodeIterates
