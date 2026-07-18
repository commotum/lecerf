# Lecerf: reversible machines and code isomorphisms in Lean 4

This repository formalizes the mathematical core of Yves Lecerf's 1963 note
on reversible Turing machines and isomorphisms of codes. The Lean library
develops reusable partial-transition, machine, history-simulation, free-monoid
code, machine-step encoding, and computability-reduction APIs.

The paper is treated as a mathematical source rather than a formal
specification. Material corrections and cleaner replacement constructions are
documented in [`goal-1/PAPER-MAP.md`](goal-1/PAPER-MAP.md) and
[`goal-1/AUDIT.md`](goal-1/AUDIT.md).

## Build

The project pins Lean `v4.31.0` and mathlib commit
`fabf563a7c95a166b8d7b6efca11c8b4dc9d911f`.

```sh
cd formal
lake build
```

The stable public import is:

```lean
import Lecerf
```

Feature-specific APIs are also available through:

- `Lecerf.Transition.API`
- `Lecerf.Machine.API`
- `Lecerf.Word.API`
- `Lecerf.Encoding.StepCode.API`
- `Lecerf.Undecidability.API`

Diagnostic examples and `#print axioms` commands live in non-public `Audit`
modules. Run the consolidated diagnostic surface with:

```sh
cd formal
lake build Lecerf.Audit
```

## Formalized results

The checked library includes:

- deterministic option-valued transitions, positive reachability, halting,
  backward uniqueness, and reversible `PEquiv` execution;
- canonical finite-support tapes and finite read-write-move machines with the
  correct move-back/check/restore inverse order;
- a generic reversible history simulation with exact reachable-history
  invariant and halting preservation/reflection;
- conventional finite reversible two-tape history, turnaround, and return
  machines;
- explicit computable many-one reductions proving noncomputability of guarded
  reversible-machine halting, positive return, and distinct-target
  reachability;
- free-monoid indexed codes, the exact bridge to mathlib's set-based uniquely
  decodable predicate, prefix/suffix marker results, injective morphisms,
  intrinsic code isomorphisms, and the paper's weaker “epimorphism of codes”;
- self-delimiting Boolean configuration codes and a successful-edge code
  isomorphism whose partial iterates correspond exactly to machine execution;
- primitive-recursive checking of a supplied positive exponent, recursive
  enumerability of positive orbit existence, and explicit many-one reductions
  proving noncomputability of the equations `w = θⁿ(w)` and
  `w₁ = θⁿ(w₂)` for the finite-machine-presented code-isomorphism subclass.

The iterate problems use strictly positive exponents. Code-isomorphism
iteration remains partial: an undefined intermediate application stays
undefined.

## Scope and historical fidelity

The first complete construction is intentionally cleaner than Lecerf's
sketch. It uses a conventional finite two-tape history machine and canonical
whole-configuration Boolean frames. The following remain explicit historical
follow-ups rather than hidden assumptions:

- lowering the reversible two-tape target tables to the project's one-tape
  model;
- identifying the clean history compiler with Lecerf's literal one-tape
  sweeping/marker construction; and
- reconstructing the paper's finite local `α`/`ω`/`β` relation list and
  `τ_min` argument.

The formal undecidability results do not depend on those identifications.
Detailed module dependencies and theorem statements are recorded in
[`goal-1/DEPENDENCIES.md`](goal-1/DEPENDENCIES.md) and
[`goal-1/THEOREM-OUTLINE.md`](goal-1/THEOREM-OUTLINE.md).
