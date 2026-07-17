# Dependency and Build Notes

## Pinned Project

- Lean toolchain: `leanprover/lean4:v4.31.0`
- mathlib revision: `fabf563a7c95a166b8d7b6efca11c8b4dc9d911f`
- That revision was locally verified as mathlib tag `v4.31.0`.
- Lake project root: `formal/`
- Library root/target: `Lecerf`

`lake-manifest.json` is part of the pin. Toolchain or manifest upgrades must be
their own maintenance stage with a full build and declaration-name audit.

## Checked Imports and API Decisions

The declarations in this section were checked against the pinned checkout and
compiled in a temporary `#check` probe during Stage 1. The probe was deleted;
it is not project code.

### Generic transition semantics

Import:

```lean
import Mathlib.Computability.StateTransition
```

Checked declarations and semantics:

- `StateTransition.eval` executes `σ → Option σ`; its `Part` is defined at the
  last configuration before `none` exactly when the run terminates.
- `StateTransition.Reaches` is reflexive-transitive and permits zero steps.
- `StateTransition.Reaches₁` is positive/transitive reachability.
- `StateTransition.mem_eval` characterizes evaluation by reachability plus
  terminality.
- `StateTransition.Respects` maps one source step to a positive target path and
  includes a terminal-state condition.
- `StateTransition.tr_reaches₁`, `tr_reaches`, `tr_eval`, `tr_eval_rev`, and
  `tr_eval_dom` provide the corresponding simulation consequences.
- `StateTransition.EvalsTo` records finite Kleisli iteration.

Decision: reuse these reachability and halting semantics. `Respects` is a
macro-step simulation tool, not reversibility and not sufficient by itself for
reflection of arbitrary checkpoint reachability.

### Partial equivalences

Import:

```lean
import Mathlib.Data.PEquiv
```

Checked declarations:

- `PEquiv α β` contains option-valued `toFun` and `invFun` with the exact law
  `invFun b = some a ↔ toFun a = some b`.
- `PEquiv.symm`, `PEquiv.trans`, `PEquiv.eq_some_iff`, and `PEquiv.inj` are
  available.

Decision: use `PEquiv σ σ` as the carrier of a generic reversible step, with
named `next`/`prev` wrappers if the API benefits. It does not represent finite
machine syntax, code multiplicativity, or a syntactic inverse instruction.
Mathlib has no checked `PEquiv` power API, so define partial iteration locally
and prove its forward map agrees with repeated `Option.bind`.

### Stage 2 realized transition boundary

The checked project modules are:

```text
Lecerf.Transition.Core
  imports Mathlib.Computability.StateTransition

Lecerf.Transition.Reversible
  imports Lecerf.Transition.Core
  imports Mathlib.Data.PEquiv

Lecerf.Transition.API
  imports Lecerf.Transition.Reversible
```

`Lecerf.Transition.Audit` imports the reversible leaf but is not re-exported.
The public root now imports only `Lecerf.Transition.API`; heavy computability,
Turing-machine, and word dependencies are absent from the compiled transition
layer.

Implementation confirmed three constraints for later stages:

- forward determinism is right uniqueness of the successful `Option` step
  relation and needs no extra machine predicate at the semantic-function
  level;
- `PEquiv` gives left uniqueness only for successful outputs, not
  `Function.Injective` of the entire option-valued function; and
- path reversal swaps endpoints, but forward and reverse terminality/halting
  are not pointwise equivalent without endpoint boundary hypotheses.

### Halting and reductions

Imports:

```lean
import Mathlib.Computability.Reduce
```

`Reduce` transitively supplies the relevant halting and recursive-enumerability
infrastructure. Checked declarations:

- `ComputablePred.halting_problem (n) :
  ¬ ComputablePred fun c : Nat.Partrec.Code => (c.eval n).Dom`;
- `ManyOneReducible`, notation `≤₀`, reflexivity, and transitivity;
- `ComputablePred.computable_of_manyOneReducible` for transferring
  computability backward along a reduction;
- `Nat.Partrec.Code.evaln`, `evaln_mono`, `evaln_sound`, the finite-stage
  completeness theorem for `eval`, and `primrec_evaln`.

Decision: the lowest-risk initial undecidability source is the explicit
computable search transition that increments a budget and calls `evaln` at
input zero. Its halting iff `(c.eval 0).Dom` follows from the checked
finite-stage completeness theorem. This supplies a generic partial transition
source; it is not yet a concrete Turing machine.

Keep `Mathlib.Computability.Reduce` out of low-level transition, machine, and
word cores. Reduction leaves should work over raw finite syntax types with
`Primcodable` instances and validity predicates, rather than semantic function
structures or proof-bearing subtypes.

### Reference Turing-machine models

Imports:

```lean
import Mathlib.Computability.TuringMachine.PostTuringMachine
import Mathlib.Computability.TuringMachine.StackTuringMachine
```

Use the following only in bridge/audit leaves when needed:

```lean
import Mathlib.Computability.TuringMachine.ToPartrec
```

Checked facts:

- `TM0.Stmt` performs either a move or a write, never both; `TM0.step` reads
  the old head and executes that single action.
- `Turing.Tape` is a head plus left/right `ListBlank` halves. `ListBlank`
  quotients trailing blank extensions. Tape movement has inverse lemmas;
  writing is not invertible without retained information.
- `TM1.step` and `TM2.step` compress statement-tree execution, so their step
  granularity is unsuitable as the primary syntactic reversible-machine API.
- `TM1to0.tr_respects`/`tr_eval` and
  `TM2to1.tr_respects`/`tr_eval_dom`/`tr_supports` are checked semantic
  simulation tools.
- `Turing.PartrecToTM2.tr_eval` and `tr_supports` exist for
  `Turing.ToPartrec.Code`.

Decision: define a finite project-local machine syntax with conventional
read-write-move source rules and repaired phase compilation. TM0 remains a
useful reference/possible bridge because its moves and writes are already
split.

Critical bridge mismatch: `ComputablePred.halting_problem` uses
`Nat.Partrec.Code`, while `Turing.PartrecToTM2.tr_eval` uses
`Turing.ToPartrec.Code`. `Turing.ToPartrec.exists_code` is existential rather
than an exposed computable syntax compiler, and the universal TM construction
uses function-bearing/infinite label types plus code-dependent finite support.
The existing semantic chain therefore does **not** yet provide the computable
map to a finite project machine required by `≤₀`.

Stage 3 must close this with one of three explicit routes:

1. compile the `evaln` search transition computably into the finite project
   machine and prove a halting iff;
2. implement a computable `Nat.Partrec.Code` syntax compiler with a semantic
   iff; or
3. establish an undecidable predicate directly over a suitably encodable
   finite `Turing.ToPartrec.Code` fragment.

No Church–Turing-equivalence shortcut is permitted.

### Words, generated submonoids, and codes

Imports:

```lean
import Mathlib.Algebra.FreeMonoid.Basic
import Mathlib.Algebra.Group.Submonoid.Membership
import Mathlib.Data.List.Infix
import Mathlib.InformationTheory.Coding.UniquelyDecodable
```

Checked declarations:

- `FreeMonoid α` is definitionally list-like; `FreeMonoid.of`, `toList`,
  `lift`, and homomorphism extensionality are available. Use `lift`, not `map`,
  when a generator is substituted by an arbitrary word.
- `FreeMonoid.mrange_lift` and `Submonoid.closure_eq_mrange` relate encoded
  factors to the generated submonoid.
- `List.IsPrefix`/`List.IsSuffix`, notations `<+:`/`<:+`, and decidable tests
  are available.
- `InformationTheory.UniquelyDecodable` is set-based and states uniqueness of
  flattened lists of codewords; its API includes exclusion of the empty word
  and injectivity consequences.

Decision: define the paper-facing indexed predicate

```text
IsIndexedCode (c : I → FreeMonoid A) :=
  Function.Injective (FreeMonoid.lift c)
```

and prove its relation to
`InformationTheory.UniquelyDecodable (Set.range fun i => (c i).toList)` plus
injectivity of `c`. The additional injectivity is essential because a set
forgets duplicate indices. Use `MulEquiv` between generated submonoids for the
intrinsic mathematical isomorphism and an explicitly law-carrying ambient
`PEquiv` for application. Avoid `Submonoid.equivMapOfInjective` in executable
reduction data because it is noncomputable.

### `Primcodable` constraints

Checked infrastructure includes instances/constructions for `Option`, sums,
products, `Fin`, lists, finite function spaces, denumerable types, and
primitive-recursive subtypes. No ready instances were found for semantic
`PEquiv`, `MonoidHom`, raw function-bearing TM machines, `Turing.Tape`, or
`ListBlank`; `deriving DecidableEq` is insufficient.

Decision: reduction codomains will be finite rule lists, alphabet codes, and
finite generator-image lists. Validity/reversibility/codehood are decidable
predicates on raw descriptions. Do not hide the target in a proof-bearing
subtype unless its membership predicate has the required primitive-recursive
encoding theorem.

For tapes, semantics are now fixed as a doubly infinite blank tape with finite
nonblank support. Stage 3 chooses between:

- `Turing.Tape` plus a proved executable canonical encoding and bridge; or
- a custom canonical finite-support representation plus a semantic bridge to
  the reference tape.

The exact Stage-3 test is whether the chosen type admits computable equality,
normalization, and a `Primcodable` encoding usable in reduction inputs.

## Tentative Module Layout

```text
formal/
  Lecerf.lean
  Lecerf/
    Transition/
      Core.lean
      Reversible.lean
      Audit.lean
      API.lean
    Machine/
      Core.lean
      Inverse.lean
      HistorySimulation.lean
      Coupling.lean
      API.lean
    Word/
      Code.lean
      Prefix.lean
      CodeMorphism.lean
      API.lean
    Encoding/
      MachineStep.lean
      Audit.lean
    Undecidability/
      ReversibleMachine.lean
      CodeIterates.lean
    Paper/
      Claims.lean
```

Create files only when their stage needs them. Audit probes remain leaves;
internal modules never import the public root.

## Build Policy

- New declaration skeleton: build the narrow leaf immediately.
- Import change: rebuild the leaf before writing a large proof.
- Shared transition/machine core change: build its named direct consumers.
- API, notation, instance, build configuration, or dependency change: run the
  full build.
- Keep diagnostics and exhaustive examples in `Audit` leaves.

Scaffold validation on 2026-07-17 generated `lake-manifest.json`; both
`lake build Lecerf` and `lake build` completed successfully with 831 jobs.
Stage-1 validation is recorded in `1-SOURCE-AUDIT.md`.
