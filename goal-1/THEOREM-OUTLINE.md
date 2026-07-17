# Proposed Theorem and Reduction Outline

All names and signatures here are design sketches, not existing Lean
declarations. Quantifiers will be finalized during `1-SOURCE-AUDIT`.

## Layer 1: Partial Transition Systems

Candidate data:

```text
ReversibleSystem σ
  next : σ → Option σ
  prev : σ → Option σ
  prev b = some a ↔ next a = some b
```

This may be implemented directly by `PEquiv σ σ` plus named projections.
Candidate results:

- successful forward steps are right-unique by `Option` semantics;
- successful predecessors are unique by the inverse law;
- a forward path reverses to a backward path, with equal length;
- `Reaches₁ next s s` expresses positive return, while `Reaches next s s` is
  always true;
- terminality and reachability predicates behave predictably under encodings.

## Layer 2: Concrete Machines

Keep separate structures/predicates for:

- a syntactic rule and `Rule.inverse`;
- a finite deterministic rule table;
- an executable configuration step;
- a forward machine satisfying a backward-uniqueness condition;
- an explicitly constructed inverse machine;
- a proof that inverse execution undoes forward execution.

The central local theorem should have the shape:

```text
inverseStep_iff :
  forward.step c = some c' ↔ inverse.step (star c') = some (star c)
```

It must be proved from the selected read/write/move convention and explicit
well-formedness hypotheses.

## Layer 3: History Simulation

For a source transition `step : C → Option C`, define simulator checkpoints
containing at least `(current source configuration, history)`. A history item
records enough erased information to reconstruct the predecessor. If the
concrete machine requires microsteps, add a finite phase/control component.

Required result chain:

1. `encode_initial`: initial source input produces a valid empty-history
   checkpoint.
2. `checkpoint_step`: each source step produces a positive finite simulator
   path to the next checkpoint.
3. `history_spec`: decoded history is exactly the sequence of source steps or
   erased local data.
4. `checkpoint_reflect`: reaching a well-formed checkpoint reflects a source
   execution; no unrelated simulator state can masquerade as a checkpoint.
5. `halts_iff`: the simulator reaches/halts at a terminal checkpoint iff the
   source halts.
6. `reversible`: the whole simulator has an executable inverse step.

## Layer 4: Forward–Reverse Coupling

Construct a phase-tagged machine:

```text
forward source simulation
  -> switch only at a terminal checkpoint
  -> inverse simulation
  -> starred initial checkpoint
  -> optional return/target gadget
```

Required iff theorems:

- source halts iff coupled machine reaches the starred initial checkpoint;
- source halts iff coupled machine has a positive return to its designated
  start (after adding a final reversible edge/gadget);
- source halts iff coupled machine reaches a specified configuration proved
  distinct from its start.

## Layer 5: Machine Undecidability Reductions

Preferred source predicate for a fixed input `k`:

```text
fun code : Nat.Partrec.Code => (code.eval k).Dom
```

Mathlib proves this is not computable. Construct computable maps:

```text
compileHalt   : Code → ReversibleHaltingInstance
compileReturn : Code → ReversibleReturnInstance
compileReach  : Code → ReversibleReachabilityInstance
```

For each map prove a reduction specification `source code ↔ target (compile
code)`, package it as `ManyOneReducible`, then transfer noncomputability. The
compiler must include all well-formedness and reversibility evidence in a
computably representable way or make the target predicate check those
properties.

## Layer 6: Words and Codes

Tentative definitions:

- `Word α := FreeMonoid α` (possibly notation only).
- An indexed family `c : ι → Word α` induces
  `FreeMonoid.lift c : FreeMonoid ι →* FreeMonoid α`.
- `IsCode c := Function.Injective (FreeMonoid.lift c)`.
- A prefix-code predicate is pairwise non-prefix (and separately non-suffix),
  with orientation names checked against the French terminology.
- `CodeIso` is the multiplicative partial bijection between the ranges of two
  injective induced homomorphisms with common index alphabet.
- `PaperCodeEpi` is a separate reconstruction of §1e and must not be called a
  surjective homomorphism without proof.

The code isomorphism acts on ambient words only when they decode through its
source code. Its iterate should therefore be option-valued or carry a proof of
definedness.

## Layer 7: Machine-Step Encoding

Construct a finite ambient alphabet with tape symbols, state/head markers,
boundaries, history/control symbols, and fresh separators. Define:

```text
encodeConfig : Config → Word Alphabet
decodeConfig : Word Alphabet → Option Config
stepIso      : Word Alphabet ≃. Word Alphabet
```

or an equivalent `CodeIso`. Prove:

```text
step c = some c' ↔ stepIso (encodeConfig c) = some (encodeConfig c')
```

and the corresponding multi-step theorem. The source/target relation-word
families must be proved codes; this is where §1d's fresh-marker lemmas are
expected to be used.

## Layer 8: Iterate Problems

Candidate nontrivial predicates:

```text
PositiveFixedOrbit (θ, w) :=
  ∃ n : Nat, 0 < n ∧ iteratePartial θ n w = some w

DistinctOrbit (θ, w₁, w₂) :=
  w₁ ≠ w₂ ∧ ∃ n : Nat, iteratePartial θ n w₂ = some w₁
```

Whether `DistinctOrbit` should require `0 < n` is logically redundant when
zero iteration is identity and `w₁ ≠ w₂`, but including it may make the theorem
and reduction clearer.

Principal reduction chain:

```text
partial-recursive-code halting
  ≤₀ ordinary finite-machine halting
  ≤₀ reversible-machine halting
  ≤₀ reversible positive return / distinct reachability
  ≤₀ positive fixed orbit / distinct orbit of a code isomorphism
```

Every arrow denotes a computable instance translation plus an iff proof. It is
acceptable to factor or reuse arrows, but no arrow may be replaced by an
informal appeal to simulation.

## Recognition Versus Existence

For finite alphabets and an executable partial `θ`, evaluating a supplied
finite exponent and checking equality should be decidable. The anticipated
undecidability concerns existential orbit predicates over unbounded `n`.
The final library should state these separately so “unsolvable in `n`” is not
misread as inability to compute a given finite iterate.
