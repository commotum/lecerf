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
Mathlib has no checked `PEquiv` power API. Stage 7 therefore defines
`Lecerf.PEquiv.iterate` locally and proves that successor application is
literal repeated `Option.bind`, together with addition, inverse, definedness,
and positive-exponent laws.

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

Decision: define a finite project-local one-tape source syntax with
conventional read-write-move rules, and a separate conventional finite
two-tape target syntax for the reversible history construction. TM0 remains
the checked bridge into the fixed one-tape source. A future theorem lowering
the simultaneous two-tape target rules back to the project's one-tape syntax
is a separate obligation.

Stages 3--5 exposed a critical bridge mismatch:
`ComputablePred.halting_problem` uses `Nat.Partrec.Code`, while
`Turing.PartrecToTM2.tr_eval` uses `Turing.ToPartrec.Code`.
`Turing.ToPartrec.Code.exists_code` is existential rather than an exposed
computable syntax compiler, and the universal TM construction uses
function-bearing/infinite label types plus code-dependent finite support.

Stage 3 checked this obstruction more precisely:

- `Turing.ToPartrec.Code.exists_code` has conclusion `∃ c : Code, ...`, not a
  compiler definition on `Nat.Partrec.Code`;
- `Turing.PartrecToTM2.tr_supports` proves a finite-support theorem for a
  selected `ToPartrec.Code`, but does not extract the project's finite rule
  list; and
- both `TM2to1.trSupp` and `TM1to0.trSupp` are explicitly `noncomputable` in
  the pinned source.

The first implemented replacement source was
`Lecerf.Machine.Source.universalEvalSearchStep`. It is one fixed transition
whose program/input are part of the configuration. Its step and joint
program/input start map are primitive recursive, and its halting predicate is
exactly `(Nat.Partrec.Code.eval code input).Dom`. Stage 6 then closed the
finite source bridge without a Church–Turing-equivalence shortcut:

- `Compiler.UniversalSource.universalCode` classically chooses one closed
  `Turing.ToPartrec.Code` computing the universal evaluator, while
  `encodedInput` places the varying `Nat.Partrec.Code` and input in its data;
- `Compiler.FiniteSource.machine` lowers that single program through the
  checked TM2-to-TM1-to-TM0 simulations, restricts control to the proved
  finite support, and compiles an actual fixed one-tape `FiniteMachine`;
- `Compiler.FiniteSource.halts_iff_eval_dom` proves exact halting preservation
  and reflection; and
- `Compiler.FiniteSource.initial_joint_primrec` and `initial_primrec` prove
  that the varying canonical input configuration is primitive recursive.

The use of choice and noncomputable support/enumeration operations is confined
to closed constants: the selected universal program, its finite state and
alphabet encodings, and the three resulting target tables. No source code
selects a different machine. Although the final `compileHalting`,
`compileReturn`, and `compileReachability` definitions require a
`noncomputable section` to mention those constants, each complete varying map
has an explicit `Primrec` theorem and hence an explicit `Computable` theorem.

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

Stage 7 implements the paper-facing indexed predicate

```text
IsIndexedCode (c : I → FreeMonoid A) :=
  Function.Injective (FreeMonoid.lift c)
```

with the exact checked bridge

```lean
isIndexedCode_iff_injective_and_uniquelyDecodable :
  IsIndexedCode c ↔
    Function.Injective c ∧
      InformationTheory.UniquelyDecodable
        (Set.range fun i ↦ (c i).toList)
```

The additional generator injectivity is essential because a set forgets
duplicate indices. `IsIndexedCode.injective`, `.ne_one`, and
`.uniquelyDecodable` expose the consequences separately;
`isIndexedCode_of_injective_of_uniquelyDecodable`,
`isIndexedCode_singleton_iff`, and `isIndexedCode_of` provide checked
constructors.

`Lecerf.Word.Prefix` implements `FreshFor`, `IsPrefixFree`, `IsSuffixFree`,
`IsPrefixCode`, and `IsSuffixCode`. Prefix/suffix codehood includes explicit
nonempty-generator hypotheses, so the pairwise predicates are not silently
treated as codes when the sole word is empty. The checked marker theorems are:

```text
isIndexedCode_prependMarkerExtension_of_freshFor_left
isIndexedCode_appendMarkerExtension_of_freshFor_left
isIndexedCode_prependMarkerExtension
isIndexedCode_appendMarkerExtension
```

The sharp variants require freshness only for the already-coded family `c`
and prefix- or suffix-freeness of the auxiliary family `k`. The final two
mirror the paper's stronger hypotheses by also accepting `FreshFor marker k`;
their proofs record that this extra freshness is redundant.

`Lecerf.Word.CodeMorphism` realizes the map boundaries rather than identifying
them:

- `generated c := Submonoid.closure (Set.range c)` and `generator c i`
  expose the intrinsic generated submonoid;
- `InjectiveMorphism M N` bundles a `MonoidHom` plus injectivity, but does not
  claim surjectivity;
- `CodeIso A I` stores source and target indexed codes, a `MulEquiv` between
  their generated submonoids, and the generator correspondence law;
- `PaperCodeEpi A I J` stores genuine source and target codes and an arbitrary
  selector `I → J`; repeated selected targets and omitted target generators
  are permitted; and
- `CodeIso.toPEquiv` exposes the same-alphabet ambient action exactly on
  `generated iso.source`, with its inverse exactly on `generated iso.target`.

`encodingEquiv`, `CodeIso.ofCodes`, `PaperCodeEpi.ofCodes`, and
`CodeIso.toPEquiv` are deliberately noncomputable semantic constructions:
arbitrary generated-submonoid membership and decoding from a bare code proof
need classical choice. Their domain, inverse-domain, generator, identity, and
multiplication laws are nevertheless proved. Stage 8 does not make this
arbitrary semantic constructor computable. Instead, it gives the particular
machine-edge schema an executable interpretation: the semantic `CodeIso` is
indexed by the generally infinite family of successful machine edges, while
the runtime `StepCode.Descriptor` is exactly the finite raw two-tape rule
table. Canonical configuration-frame decoding decides the relevant generated
language for this schema, and the validity-checked interpreter is proved
pointwise equal to the semantic ambient action. The semantic `CodeIso` and
its proof index are not stored as runtime reduction data.

The project-local iteration surface is `Lecerf.PEquiv`:

```text
iterate, iterate_zero, iterate_succ, iterate_succ_apply, iterate_succ_left
iterate_add, iterate_add_apply
iterate_symm, iterate_symm_eq_some_iff
DefinedAt, definedAt_iff_exists, definedAt_succ_iff
positiveIterate, PositiveDefinedAt, PositiveDefined, PositiveIterate
```

Here `positiveIterate θ k = iterate θ (k + 1)` is itself a `PEquiv`, while
`PositiveIterate θ source target` is the existential reachability predicate.
Undefined intermediates propagate through `Option.bind`; zero iteration is
total reflexivity and is not substituted for a positive witness.

### `Primcodable` constraints

Checked infrastructure includes instances/constructions for `Option`, sums,
products, `Fin`, lists, finite function spaces, denumerable types, and
primitive-recursive subtypes. No ready instances were found for semantic
`PEquiv`, `MonoidHom`, raw function-bearing TM machines, `Turing.Tape`, or
`ListBlank`; `deriving DecidableEq` is insufficient.

The pinned checkout also has no inferred `Primcodable (FreeMonoid A)` instance.
`Lecerf.Encoding.ConfigCodeEffectivity` therefore installs the representation
induced by the definitional list equivalence,
`Primcodable.ofEquiv (List A) FreeMonoid.toList`, and proves both word/list
conversions primitive recursive. This is a representation theorem for words,
not a computable representation of semantic `CodeIso` or `PEquiv` values.

Updated decision: the implemented Stage-8 runtime boundary and Stage-9 target
inputs use a finite two-tape rule list together with one or more `Word Bool`
values. Its validity guard is a decidable
primitive-recursive predicate on the raw table. The table uniformly describes
the generally infinite successful-edge code schema; no finite generator-image
list is currently claimed. Do not hide the target in a proof-bearing subtype
or store the semantic `CodeIso` unless the resulting representation has an
explicit primitive-recursive encoding theorem.

For tapes, semantics are fixed as a doubly infinite blank tape with finite
nonblank support. Stage 3 evaluated two routes:

- `Turing.Tape` plus a proved executable canonical encoding and bridge; or
- a custom canonical finite-support representation plus a semantic bridge to
  the reference tape.

Stage 3 selected the custom route. `Lecerf.Machine.Side` stores either the
all-blank half-tape or a nearest-first finite prefix with a subtype-certified
nonblank far cell. Trailing blanks therefore have one structural normal form.
`Lecerf.Machine.Tape` stores the scanned symbol and two sides; it has executable
read/write/move operations, decidable equality, inverse-move laws, and a
constructive `Primcodable` instance. The same is true of `Tape.Move`,
`Config`, `Rule`, and `FiniteMachine` when their parameters are primcodable.

The core deliberately does not import quotient-based `Turing.Tape`. Stage-3
source inspection and compiling prototypes verified that the chosen side is
equivalent to `Turing.ListBlank`, but promoting that quotient bridge is not
needed by the public executable layer and would inherit quotient/classical
dependencies. A checked project bridge may be added later in a narrow audit
leaf if a concrete TM translation consumes it.

A separate phase-control compiler probe generated ordinary `normal`/`move`
rule families and proved the forward compiled table deterministic from
`TableDeterministic` plus `ReverseTableCompatible`. It also exposed an
effectivity boundary: `Finset.univ.toList` is explicitly `noncomputable` in
the pinned mathlib source. A public compiler must therefore accept a checked
complete alphabet list or use a concrete `Fin n`; a bare `[Fintype Γ]` is not
sufficient reduction data. The probe did not prove the two-microstep semantic
correspondence and was not promoted into project code.

### Stage 4 realized history/effectivity boundary

`Lecerf.Machine.Effectivity` imports only `Lecerf.Machine.Core` and proves the
existing structural runtime primitive recursive without enumerating state or
alphabet types. Its checked chain is:

```text
Side.head/tail/cons
  -> Tape.head/write/move/act
  -> Rule.apply
  -> FiniteMachine.applyRules
  -> FiniteMachine.step_uniform_primrec
```

The subtype-certified nonblank branch is computed through canonical
`Encodable.decode₂`, not `Finset.univ`; the theorem assumptions need
`Primcodable`, decidable equality, and the alphabet blank, but no `Finite` or
`Fintype` instance.

The generic history dependency graph realized in Stage 4 is:

```text
Transition/API
  -> Machine/History/Core
  -> Machine/History/Correctness

Machine/Core
  -> Machine/Effectivity

History/Core + History/Correctness + Machine/Effectivity + SourceBridge
  -> Machine/History/Computable
  -> Machine/History/API
  -> Machine/API
```

`History/Core` stores complete predecessor configurations and constructs an
exact `PEquiv`; it does not import finite-machine syntax. `History.Correctness`
owns reachability/invariant and halting proofs. `History.Computable` owns
uniform interpreter theorems and source specializations. `History.Audit`
imports the computability leaf for executable diagnostics but is not on the
public path.

`finiteForward_uniform_primrec` and `finiteBackward_uniform_primrec` close the
effectivity question for interpreting a finite source description with an
abstract history state. They do **not** compile the unbounded `List` log into
a conventional one-tape `FiniteMachine`. That representation-level compiler,
and the earlier ordinary-rule phase compiler, remain separate later bridges.

### Stage 5 realized coupling boundary

The coupling layer is split so executable phase semantics remain below
history-specific correctness and computability:

```text
Transition/API + Primrec/List
  -> Machine/Coupling/Core

Machine/Coupling/Core + Machine/History/Correctness
  -> Machine/Coupling/Correctness

Coupling/Correctness + History/Computable + Machine/Effectivity + SourceBridge
  -> Machine/Coupling/Computable
  -> Machine/Coupling/API
  -> Machine/API
```

`Coupling/Core` defines constructive phase-tagged configurations, an open
turnaround `PEquiv`, and a uniformly closed return `PEquiv`; it imports no
history or machine syntax, and its runtime definitions inspect neither a
halting witness nor evaluation semantics. `Coupling/Correctness` owns generic
path lifting and the history-generated invariant. `Coupling/Computable`
owns the primitive-recursive generic interpreters and finite/universal source
specializations. `Coupling/Audit` is a non-public diagnostic and axiom-audit
leaf.

The finite coupling theorems consume an existing `FiniteMachine` description
and an abstract phase-tagged full-history state. They do **not** themselves
produce a finite rule table. Stage 6 closes that gap for a conventional finite
two-tape target in `Machine.TwoTape.HistoryCompiler`; it does not retroactively
turn the Stage-5 abstract gadget into a one-tape compiler.

### Stage 6 realized finite two-tape boundary

The previously grouped obligations now have different statuses:

- `A-018` is closed by the fixed universal one-tape source and its
  primitive-recursive varying start map.
- `A-024` is closed for the two-tape target by the decidable,
  primitive-recursive sufficient certificate
  `TwoTape.FiniteMachine.SyntacticallyReversible`; its theorem
  `SyntacticallyReversible.reversible` gives semantic whole-machine
  reversibility without asserting a converse.
- `A-025` is closed for the two-tape target by the finite history-token tape
  and microstate compiler, including generated-run reflection and exact
  halting, return, and reachability iff theorems.
- `A-023` is avoided, not silently solved: simultaneous read-write-move is an
  atomic rule of the new two-tape target. Lowering those rules to the existing
  one-tape `FiniteMachine` still requires a phase-control/tape encoding proof.

The realized dependency graph is:

```text
Mathlib ToPartrec
  -> Machine/Compiler/UniversalSource
  -> Machine/Compiler/FiniteSource
  -> Machine/Compiler/FiniteSourceComputable

Machine/Tape + Transition/Core
  -> Machine/TwoTape/Core
  -> Machine/TwoTape/Effectivity
  -> Machine/TwoTape/Validity

Machine/TwoTape/Core + Transition/Reversible
  -> Machine/TwoTape/Reversible
  -> Machine/TwoTape/Validity

Machine/Core + Machine/TwoTape/Reversible
  -> Machine/TwoTape/HistoryCompiler/Core
  -> HistoryCompiler/Basic
  -> HistoryCompiler/Trace

HistoryCompiler/Basic
  -> HistoryCompiler/Reversible

HistoryCompiler/Trace + HistoryCompiler/Reversible
  -> HistoryCompiler/Runtime
  -> HistoryCompiler/Correctness

HistoryCompiler/Core + Machine/TwoTape/Validity
  -> HistoryCompiler/Effectivity

FiniteSourceComputable + HistoryCompiler/Correctness +
HistoryCompiler/Effectivity
  -> Machine/Compiler/ReversibleUniversal

ReversibleUniversal + ReversibleTwoTape/Problems + Reduce
  -> ReversibleTwoTape/Reduction
  -> ReversibleTwoTape/API
  -> Undecidability/API
  -> Lecerf

ReversibleTwoTape/Reduction
  -> ReversibleTwoTape/Audit  (not publicly re-exported)
```

`ReversibleUniversal.historyTable`, `turnaroundTable`, and `returnTable` are
fixed finite tables. Only `sourceStart`, `startCheckpoint`, and `bottomTarget`
vary with the source code, and all three relevant endpoint maps are primitive
recursive. The historical correspondence to Lecerf's compact one-tape marker
scheme, including a two-to-one-tape lowering, remains future work and must not
be inferred from these two-tape declarations.

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
      Tape.lean
      Core.lean
      Lookup.lean
      Reversible.lean
      Validity.lean
      Effectivity.lean
      SourceBridge.lean
      Audit.lean
      Compiler/
        Table.lean
        TapeBridge.lean
        UniversalSource.lean
        FiniteSource.lean
        FiniteSourceComputable.lean
        ReversibleUniversal.lean
      TwoTape/
        Core.lean
        Reversible.lean
        Effectivity.lean
        Validity.lean
        HistoryCompiler/
          Core.lean
          Basic.lean
          Trace.lean
          Reversible.lean
          Runtime.lean
          Correctness.lean
          Effectivity.lean
      History/
        Core.lean
        Correctness.lean
        Computable.lean
        Audit.lean
        API.lean
      Coupling/
        Core.lean
        Correctness.lean
        Computable.lean
        Audit.lean
        API.lean
      API.lean
    Word/
      Code.lean
      Prefix.lean
      CodeMorphism.lean
      Audit.lean
      API.lean
    Encoding/
      MachineStep.lean
      Audit.lean
    Undecidability/
      EffectiveTransition.lean
      API.lean
      ReversibleTwoTape/
        Problems.lean
        Reduction.lean
        Audit.lean
        API.lean
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

Stage-3 realized dependency boundary:

```text
Machine/Tape          -> Mathlib.Computability.Primrec.List
Machine/Core          -> Machine/Tape, Transition/Core
Machine/Reversible    -> Machine/Core, Transition/Reversible
Machine/SourceBridge  -> Transition/Core, Mathlib.Computability.PartrecCode
Machine/API           -> Machine/Reversible, Machine/SourceBridge
Machine/Audit         -> Machine/Reversible   (not publicly re-exported)
```

Full `lake build` passed with 830 jobs after the public API import changed.

Stage-4 realized dependency additions:

```text
Machine/Effectivity          -> Machine/Core
Machine/History/Core         -> Transition/API, Primrec/List
Machine/History/Correctness  -> Machine/History/Core
Machine/History/Computable   -> History/Correctness, Machine/Effectivity,
                                Machine/SourceBridge
Machine/History/API          -> Machine/History/Computable
Machine/History/Audit        -> Machine/History/Computable (not re-exported)
Machine/API                  -> Machine/History/API
```

Full `lake build` passed with 835 jobs after the Stage-4 public API import
changed.

Stage-5 realized dependency additions:

```text
Machine/Coupling/Core        -> Transition/API, Primrec/List
Machine/Coupling/Correctness -> Coupling/Core, History/Correctness
Machine/Coupling/Computable  -> Coupling/Correctness, History/Computable,
                                Machine/Effectivity, Machine/SourceBridge
Machine/Coupling/API         -> Machine/Coupling/Computable
Machine/Coupling/Audit       -> Machine/Coupling/Computable (not re-exported)
Machine/API                  -> Machine/History/API, Machine/Coupling/API
```

Stage-5 focused builds passed through `Coupling.Audit` (834 jobs), and the
public `Machine.API`/root adjacent build passed after adding `Coupling.API`.
The final full `lake build` passed with 839 jobs; detailed validation and axiom
results are recorded in `5-COUPLING.md` and `AUDIT.md`.

Stage-6 realized dependency additions:

```text
Machine/Compiler/UniversalSource       -> Mathlib ToPartrec
Machine/Compiler/Table                 -> Machine/Core
Machine/Compiler/TapeBridge            -> Machine/Tape, mathlib Tape
Machine/Compiler/FiniteSource          -> compiler leaves, PostTuringMachine
Machine/Compiler/FiniteSourceComputable -> FiniteSource, Machine/Effectivity
Machine/TwoTape/Core                   -> Machine/Tape, Transition/Core
Machine/TwoTape/Reversible             -> TwoTape/Core, Transition/Reversible
Machine/TwoTape/Effectivity            -> Machine/Effectivity, TwoTape/Core
Machine/TwoTape/Validity               -> TwoTape/Effectivity, TwoTape/Reversible
Machine/TwoTape/HistoryCompiler/*      -> TwoTape layers, Machine/Core/Lookup
Machine/Compiler/ReversibleUniversal   -> FiniteSourceComputable,
                                           HistoryCompiler correctness/effectivity
Undecidability/ReversibleTwoTape/Problems -> FiniteSource,
                                             HistoryCompiler/Effectivity
Undecidability/ReversibleTwoTape/Reduction -> ReversibleUniversal, Problems,
                                              Mathlib Reduce
Undecidability/ReversibleTwoTape/API   -> Reduction
Undecidability/ReversibleTwoTape/Audit -> Reduction (not re-exported)
Undecidability/API                     -> EffectiveTransition,
                                          ReversibleTwoTape/API
```

On 2026-07-17, the focused
`lake build Lecerf.Undecidability.ReversibleTwoTape.Audit` passed with 877
jobs. Its representative axiom output contains only `propext`,
`Classical.choice`, and `Quot.sound`. A subsequent full `lake build` passed
with 893 jobs.

Stage-7 realized dependency additions:

```text
Word/Code              -> FreeMonoid/Basic, InformationTheory/UniquelyDecodable
Word/Prefix            -> Word/Code, Data/List/Infix
Word/CodeMorphism      -> Word/Code, Submonoid/Membership, Data/PEquiv
Word/API               -> Word/CodeMorphism, Word/Prefix
Word/Audit             -> Word/API  (not publicly re-exported)
Lecerf                  -> Word/API
```

The focused Stage-7 builds passed as follows: `Word.Code` with 522 jobs,
`Word.Prefix` with 526 jobs, `Word.CodeMorphism` with 693 jobs, and
`Word.API` plus `Word.Audit` with 696 jobs. The adjacent audit/root build
passed with 914 jobs, and the final full `lake build` passed with 913 jobs.

`Word.Audit` checks that duplicate indices and an empty generator are rejected,
constructs a `PaperCodeEpi` whose selector both repeats and omits targets,
checks that a `CodeIso` ambient application is `none` outside its generated
source, and distinguishes zero from positive iteration. Its `#print axioms`
output is:

- the indexed/set code bridge: `[propext, Quot.sound]`;
- both paper-shaped fresh-marker theorems and
  `CodeIso.toPEquiv_generator`:
  `[propext, Classical.choice, Quot.sound]`; and
- `Lecerf.PEquiv.iterate_symm`, `positiveIterate`, and
  `positiveIterate_symm`: `[propext, Quot.sound]`.

These are Lean/mathlib foundational dependencies, not project-specific
axioms.

Stage-8 realized dependency additions are:

```text
Encoding/ConfigCode
  -> Word/Prefix, Mathlib Computability/Primrec/Basic

Encoding/ConfigCodeEffectivity
  -> Encoding/ConfigCode, Mathlib Computability/Partrec

Transition/Exact
  -> Transition/Core, Word/CodeMorphism

Encoding/StepCode/Core
  -> Encoding/ConfigCode, Machine/TwoTape/Reversible,
     Word/CodeMorphism

Encoding/StepCode/Correctness
  -> Encoding/StepCode/Core, Transition/Exact

Encoding/StepCode/Interpreter
  -> Encoding/StepCode/Core

Encoding/StepCode/Effectivity
  -> Encoding/ConfigCodeEffectivity, Encoding/StepCode/Interpreter,
     Machine/TwoTape/Effectivity, Machine/TwoTape/Validity

Encoding/StepCode/API
  -> Encoding/StepCode/Correctness, Encoding/StepCode/Effectivity

Encoding/StepCode/Audit
  -> Encoding/StepCode/Correctness, Encoding/StepCode/Effectivity
     (not publicly re-exported)

Lecerf
  -> Encoding/StepCode/API
```

The codec uses the genuinely finite alphabet `Bool`. For every
`[Primcodable C]`, a value is the whole-configuration frame
`true^(Encodable.encode value) false`. `Encodable.decode₂` rejects natural
codes outside the canonical range. The exact single- and multiple-frame
results are:

```text
decodeUnaryFrame_eq_some_iff
decodeConfigBits_eq_some_iff
decodeConfig_eq_some_iff
decodeConfigListBits_eq_some_iff
decodeConfigs_eq_some_iff
encodeConfig_isPrefixCode
encodeConfig_isIndexedCode
encodeConfigs_eq_lift
```

Thus malformed, unterminated, trailing, and noncanonical frames cannot enter
the executable domain. `ConfigCodeEffectivity` proves `Primrec` and
`Computable` versions of unary framing, single-frame encoding/decoding,
concatenated-frame encoding/decoding, and their word-valued forms. In
particular, the stable joint results include
`encodeConfigs_primrec`, `decodeConfigListBits_primrec`, and
`decodeConfigs_primrec`.

`Transition.Exact` keeps option failure explicit through `exactIterate` and
`ExactSteps`, and connects exact exponents with reflexive and strict
reachability and with `Lecerf.PEquiv.iterate`. The successful-edge schema then
has the following checked layers:

- Stage-8 support lemmas `IsIndexedCode.comp`,
  `mem_generated_iff_exists_lift`, and `CodeIso.toPEquiv_lift` respectively
  preserve codehood under injective reindexing, expose generated-word
  factorization, and extend the generator equation to an arbitrary index word;
- `Edge machine` displays `machine.step source = some target`;
- `sourceWord_isIndexedCode` follows from deterministic option-valued
  execution, whereas `targetWord_isIndexedCode_iff_backwardUnique` makes
  successful-predecessor uniqueness an exact boundary;
- `stepCodeEpi` realizes the paper's weaker selector map for every table, and
  `stepCodeIso` is a genuine `CodeIso` under `BackwardUnique machine.step`;
- `stepCodeIso_apply_eq_some_iff_exists` reflects every successful ambient
  result from a canonical source to an encoded machine successor;
- `stepCodeIso_apply_eq_some_iff`,
  `stepCodeIso_iterate_eq_some_iff`, `stepCodeIso_definedAt_iff`, and
  `stepCodeIso_positiveIterate_iff_strictlyReachable` give exact one-step,
  supplied-iterate, definedness, and positive-reachability correspondence; and
- `liftPEquiv_machine_eq_stepCodeIso_toPEquiv` identifies the constructive
  framewise interpreter with the semantic ambient action on every Boolean
  word for a semantically reversible table.

The runtime boundary remains finite even though `Edge machine` is generally
infinite. `StepCode.Descriptor Q Γ₁ Γ₂` is an abbreviation for the raw
finite `TwoTape.FiniteMachine`; `Descriptor.Valid` is the existing
primitive-recursive `SyntacticallyReversible` guard. `Descriptor.applyWord`
executes the decoded table pointwise, and `Descriptor.checkedApply` returns
`none` before interpretation when validity fails. The checked effectivity
surface is:

```text
Descriptor.applyWord_uniform_primrec
Descriptor.applyWord_uniform_computable
Descriptor.valid_primrec
Descriptor.checkedApply_uniform_primrec
Descriptor.checkedApply_uniform_computable
Descriptor.applyWord_eq_stepCodeIso_toPEquiv
Descriptor.checkedApply_eq_stepCodeIso_toPEquiv
```

Only the forward interpreter is claimed primitive recursive; the semantic
inverse remains proof-side. This stage proves a cleaner whole-configuration
edge encoding, not Lecerf's finite local `alpha`/`omega`/`beta` relation list.
A literal historical local encoding and the two-to-one-tape lowering needed
to connect it to the project's two-tape undecidability source remain open.

Stage-9 realized dependency additions are:

```text
Transition/ExactEffectivity
  -> Transition/Exact, Mathlib Computability/Primrec/Basic

Undecidability/CodeIterates/Problems
  -> Encoding/StepCode/Effectivity, Transition/Exact,
     Undecidability/ReversibleTwoTape/Problems

Undecidability/CodeIterates/Effectivity
  -> Transition/ExactEffectivity, CodeIterates/Problems,
     Mathlib Computability/RE

Undecidability/CodeIterates/Correspondence
  -> Encoding/StepCode/Correctness, CodeIterates/Problems

Undecidability/CodeIterates/Reduction
  -> CodeIterates/Correspondence, CodeIterates/Effectivity,
     Undecidability/ReversibleTwoTape/Reduction

Undecidability/CodeIterates/API
  -> CodeIterates/Reduction

Undecidability/CodeIterates/Audit
  -> CodeIterates/Reduction (not publicly re-exported)

Undecidability/API
  -> EffectiveTransition, CodeIterates/API, ReversibleTwoTape/API
```

The finite runtime aliases are exact products, with no functions, semantic
partial equivalences, proofs, or witnesses stored in the input:

```lean
abbrev CodeDescriptor :=
  StepCode.Descriptor ReversibleTwoTape.MachineState
    ReversibleTwoTape.WorkSymbol ReversibleTwoTape.HistorySymbol

abbrev FixedOrbitInput := CodeDescriptor × Word Bool
abbrev DistinctOrbitInput := CodeDescriptor × Word Bool × Word Bool
abbrev SuppliedExponentInput :=
  CodeDescriptor × Nat × Word Bool × Word Bool
```

Products associate to the right. Thus the distinct input order is descriptor,
start, target, and the supplied-exponent order is descriptor, exponent, start,
target. This represents the paper's equation `w₁ = θⁿ(w₂)` with stored start
`w₂` before stored target `w₁`.

`PositiveFixedOrbitYes` and `DistinctOrbitYes` both require
`descriptor.Valid` and a predecessor witness `k` whose actual exponent is
`k + 1`. The distinct predicate additionally requires `start ≠ target`.
`PositiveIterateAtYes` takes the exponent as data, requires it to be nonzero,
and checks `ExactSteps descriptor.checkedApply exponent start target`.
`ExactSteps` is the bind-preserving partial semantics: an undefined
intermediate application makes the entire iterate undefined. In particular,
zero-step reflexivity cannot witness either existential target.

The reusable effectivity leaf proves:

```text
Transition.exactIterate_uniform_primrec
checkedExactIterate_uniform_primrec
positiveIterateAtYes_primrec
positiveIterateAtYes_computablePred
fixedOrbitWitnessYes_primrec
fixedOrbitWitnessYes_computablePred
distinctOrbitWitnessYes_primrec
distinctOrbitWitnessYes_computablePred
positiveFixedOrbitYes_iff_exists_witness
distinctOrbitYes_iff_exists_witness
positiveFixedOrbitYes_re
distinctOrbitYes_re
```

The first theorem uniformly iterates any primitive-recursive
`D → X → Option X` transition while retaining the `Option` state. The supplied
positive exponent is therefore a primitive-recursive predicate. The two
existential problems are only proved recursively enumerable, through the
primitive-recursive witness relations `FixedOrbitWitnessYes` and
`DistinctOrbitWitnessYes`; no total existence decider or total witness finder
is inferred.

The checked-runtime/semantic correspondence is exposed by:

```text
checkedExactIterate_eq_stepCodeIso_iterate
checkedExactSteps_iff_stepCodeIso_iterate_eq_some
checkedPositiveExactSteps_iff_stepCodeIso_positiveIterate
positiveFixedOrbitYes_iff_stepCodeIso_positiveIterate
distinctOrbitYes_iff_stepCodeIso_positiveIterate
positiveIterateAtYes_iff_stepCodeIso_iterate
encodedCheckedExactSteps_iff_exactSteps
encodedCheckedPositiveExactSteps_iff_strictlyReachable
positiveFixedOrbitYes_encodeConfig_iff_returnYes
distinctOrbitYes_encodeConfig_iff_reachabilityYes
```

These theorems first identify checked word iteration with the proof-side
`stepCodeIso` iterate for a valid descriptor, then specialize canonical
configuration words to exact machine steps and strict reachability. Both
directions are present, so successful checked iteration cannot introduce a
malformed or spurious endpoint.

The generic reduction maps preserve the raw descriptor verbatim and encode
only their configuration endpoints:

```text
encodeReturnInput
encodeReturnInput_primrec
encodeReturnInput_computable
encodeReachabilityInput
encodeReachabilityInput_primrec
encodeReachabilityInput_computable
encodeReachabilityInput_start_ne_target
returnYes_iff_positiveFixedOrbitYes
reachabilityYes_iff_distinctOrbitYes
returnYes_manyOne_positiveFixedOrbitYes
reachabilityYes_manyOne_distinctOrbitYes
```

Leaving the descriptor unchanged is important for malformed inputs. An
invalid table is invalid on both sides of each iff: the source machine
predicate and target orbit predicate both contain the same syntactic
reversibility guard, and `checkedApply` also rejects it. The reduction neither
repairs an invalid descriptor nor silently drops its guard.

Composing the generic arrows with the Stage-6 fixed-source reductions gives:

```text
partrecHalts0_manyOne_positiveFixedOrbitYes
partrecHalts0_manyOne_distinctOrbitYes
positiveFixedOrbitYes_not_computable
distinctOrbitYes_not_computable
```

The direct noncomputability results transfer
`ComputablePred.halting_problem 0` backward through the displayed many-one
reductions. `CodeIterates.Audit` remains a non-public leaf and checks the
positive-exponent, partial-failure, nonempty canonical-word, and axiom
boundaries.

This completes the finite-descriptor iterate reduction layer, but not the
paper's exact historical presentation. `Edge machine` is generally an
infinite successful-edge schema uniformly interpreted from a finite machine
table; there is still no finite generator-image list for that schema. A
literal finite local `alpha`/`omega`/`beta` encoding, a connection from it to
the present whole-configuration encoding, and the two-to-one-tape lowering
remain separate obligations. Stage 10 has not begun those historical
reconciliation tasks.
