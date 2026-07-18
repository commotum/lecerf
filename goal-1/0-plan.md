# Reversible Machines and Code Isomorphisms

Shorthand goal: **LECERF**

## Big-Picture Objective

Build a correct, reusable Lean 4 library that reconstructs the mathematical
content of Yves Lecerf's 1963 note on reversible Turing machines and
isomorphisms of codes. The end result must separate the generic mathematics
of reversible partial transition systems from concrete Turing-machine and
free-monoid encodings, and must expose checked computability reductions for
the paper's undecidability claims.

The paper is a source of mathematical ideas, not a formal specification.
Every convention, construction, and quantifier must be made explicit and
verified. A cleaner equivalent reversible simulation may be proved before a
faithful reconstruction of Lecerf's historical encoding.

This document is the authoritative strategy. Stage-specific evidence belongs
in `goal-1/[INDEX]-[SHORTHAND].md`, created only when that stage starts.

## Non-Negotiable Constraints

- Pin Lean and mathlib; keep the project buildable from the checked-in Lake
  manifest.
- Completed Lean modules contain no `sorry`, `admit`, `unsafe` proof bypass,
  or unexplained project-specific `axiom`.
- Never fabricate a theorem, paper claim, citation, or proof obligation.
- Preserve the distinction between:
  - an individually invertible rule and a deterministic reversible machine;
  - a syntactic inverse instruction and inverse execution on configurations;
  - simulation correctness and a computability reduction;
  - a monoid homomorphism, an injective morphism, a code isomorphism, and
    Lecerf's nonstandard “epimorphism of codes”;
  - decidability for a supplied exponent and decidability of existence of an
    exponent.
- State the machine convention before defining inverse transitions. Prove that
  the proposed inverse undoes the actual configuration step.
- A reversible simulation must expose encoding/decoding, a history invariant,
  forward simulation, reflection/no-spurious-acceptance, and halting
  preservation in both directions.
- Every undecidability result must be obtained from an explicit computable
  reduction with exact source and target predicates.
- Treat iteration of a code isomorphism as partial unless closure of outputs
  under further applications has been proved.
- Do not use `n = 0` to trivialize an iterate theorem. The final statement must
  resolve whether the paper intends a positive exponent, a supplied exponent,
  or another quantifier structure.
- Keep experimental encodings and diagnostics in leaf or audit modules; do not
  promote them into the public API until their invariants are proved.
- Follow `BUILD-PLAN.md`: narrow imports, low-fanout cores, one stage at a time,
  and the smallest builds that cover the changed dependency surface.

## Current Facts

- The repository contains English and French transcriptions, page images, and
  PDFs of the four-page 1963 note.
- The French source says a code admits **at most one** ordered factorization;
  the English translation omits “at most one.” English §1e also mistranslates
  `est bien un code` (“is indeed a code”) as “a complete code.”
- Section 4 gives only principles and one representative instruction family
  for the history-recording simulation; it does not give a complete machine or
  proof. Its displayed history formulas also make the initial history both
  empty and `b³`.
- The paper states undecidability of halting, return, and passage through a
  specified configuration for reversible machines, then states two iterate
  equation results for code isomorphisms.
- Under conventional read-write-then-move semantics, the paper's printed
  sign-reversed inverse quintuple is not a configuration-step inverse for a
  moving rule. Later machine syntax must repair it with phased operations.
- The paper does not define whether `N` contains zero. The fixed-orbit target
  must use a positive exponent, and ambient code-isomorphism iteration is
  partial because source and target generated submonoids can differ.
- Lean `v4.31.0` is installed locally. The scaffold pins mathlib's `v4.31.0`
  commit `fabf563a7c95a166b8d7b6efca11c8b4dc9d911f`.
- mathlib provides `StateTransition`, option-valued `PEquiv`, `FreeMonoid`,
  `InformationTheory.UniquelyDecodable`, Turing-machine models,
  `ComputablePred.halting_problem`, and computable many-one reductions.
- The existing halting theorem is over `Nat.Partrec.Code`, while the checked
  partial-recursive-to-TM construction uses `Turing.ToPartrec.Code`; mathlib
  does not expose the computable finite compiler needed to close that bridge.
- Stage 1 is complete. It changed documentation/specification only; no
  substantive Lean declaration or project configuration was added.
- Stage 2 is complete. `Lecerf.Transition.Core`, `Reversible`, `Audit`, and
  `API` compile, and the public root exports the API without importing the
  diagnostic leaf.
- Stage 3 is complete. `Lecerf.Machine.Tape`, `Core`, `Reversible`,
  `SourceBridge`, `Audit`, and `API` compile. The public API exposes canonical
  finite-support tapes, finite first-match rule tables, repaired phased inverse
  execution, whole-machine reversibility, and a fixed primitive-recursive
  `Nat.Partrec.Code.evaln` search source.
- Stage 4 is complete. `Lecerf.Machine.Effectivity` and
  `Lecerf.Machine.History.{Core,Correctness,Computable,Audit,API}` compile.
  The public construction stores complete predecessor configurations, is an
  exact `PEquiv` on all history states, proves generated history exactly
  equivalent to reachability, preserves and reflects halting, and is primitive
  recursive jointly in an existing finite-machine description.
- Stage 5 is complete. `Lecerf.Machine.Coupling.{Core,Correctness,Computable,
  Audit,API}` compile. The generic open turnaround and uniformly closed return
  gadget are exact `PEquiv`s; the history specialization proves source halting
  iff strict reachability of a structurally distinct reverse-initial target and
  iff positive return. Generic, finite-description, and universal interpreters
  and endpoint maps are primitive recursive.
- Stage 6 is complete. A fixed universal source is lowered through mathlib's
  checked TM2-to-TM1-to-TM0 simulations to a finite one-tape table. A separate
  finite two-tape history compiler supplies forward-only, open-turnaround, and
  closed-return tables with decidable primitive-recursive validity certificates
  implying semantic reversibility. The public undecidability API exposes three
  computable many-one reductions and noncomputability of guarded halting,
  positive return, and distinct-target strict reachability. These are explicitly
  two-tape results; a conventional one-tape lowering remains future work.
- Stage 7 is complete. The word layer defines indexed codehood by injectivity
  of `FreeMonoid.lift` and proves its exact equivalence with generator
  injectivity plus mathlib's set-based `UniquelyDecodable`. Tagged marker
  extensions, intrinsic generated-submonoid code isomorphisms, the weaker paper
  epimorphism, exact ambient partial domains, and bind-based positive iteration
  now form the public `Lecerf.Word` API.
- Stage 8 is complete. Canonical whole-configuration frames over the finite
  alphabet `Bool` have exact executable single/concatenated decoders and
  primitive-recursive effectivity proofs. Successful edges of a reversible
  two-tape machine index genuine source and target codes, with exact
  one-step/iterate reflection and an all-word executable interpreter. This is
  a uniformly finite-machine-described but generally infinite code schema,
  not the paper's finite local `alpha`/`omega`/`beta` relation list.

## Current Design Decisions

- Use `PEquiv σ σ` for generic reversible steps and reuse
  `StateTransition.Reaches`, `Reaches₁`, and `eval`. Positive return is
  `Reaches₁`; ordinary reachability remains reflexive.
- Forward determinism is automatic right uniqueness of a successful
  option-valued step. Reversibility adds `BackwardUnique`, i.e. left uniqueness
  only for successful outputs; it does not imply `Function.Injective` into
  `Option` because multiple states may map to `none`.
- Reversible path theorems exchange endpoints. Forward and reverse terminality
  are not pointwise equal; evaluation reversal records both required endpoint
  terminal hypotheses.
- Use `FiniteMachine` for finite lists of conventional read-write-move rules.
  Its canonical tape stores the alphabet's `default` blank and structurally
  excludes duplicate trailing-blank representations; tape, configuration,
  rule, and machine types have constructive `Primcodable` instances.
- A rule's tape action is the composition of a checked-write `PEquiv` and a
  total move equivalence. Its semantic inverse moves back before checking and
  restoring. A whole table additionally requires forward and backward
  compatibility; for deterministic tables, backward compatibility is exactly
  `BackwardUnique step`.
- The original one-tape `FiniteMachine` retains its atomic semantic phase
  decomposition and checked sufficient reversibility condition. Stage 6 does
  not claim a converse characterization for every semantically reversible
  table. Instead, `Machine.TwoTape` supplies a conventional finite local-rule
  model with a decidable primitive-recursive syntactic certificate that implies
  whole-machine reversibility and is satisfied by every compiled target.
- `Source.universalEvalSearchStep` remains the abstract computability source.
  For the concrete reductions, `Compiler.UniversalSource` selects one closed
  universal `Turing.ToPartrec.Code`; `Compiler.FiniteSource` lowers that fixed
  program through mathlib's checked TM simulations and finite support to an
  actual finite one-tape table. Only the encoded program/input tape varies, and
  `FiniteSourceComputable.initial_primrec` proves that map primitive recursive.
  The one-time universal-program and finite-encoding choices are isolated and
  visible in the axiom audit.
- The first complete reversible simulation uses an explicit history log. A
  faithful tape-level version of Lecerf's marker construction can be a later
  refinement.
- The implemented history log stores the entire previous source configuration
  on each successful step. `backward` recomputes and validates the popped edge,
  so `reversible` is a genuine `PEquiv` even on malformed ambient histories.
  `reachable_iff_valid` excludes malformed checkpoints from runs starting at
  an empty history, and `haltsFrom_forward_iff` proves halting in both
  directions.
- `FiniteMachine.step_uniform_primrec`,
  `History.finiteForward_uniform_primrec`, and
  `History.finiteBackward_uniform_primrec` establish effective interpretation
  jointly in a finite source description without enumerating its alphabet.
  That abstract simulator still contains an unbounded list and is not itself a
  finite local machine. Stage 6 therefore adds a separate finite two-tape
  compiler whose second tape stores rule tokens and whose checked microsteps
  implement logging, scanning, restoration, and bottom closure.
- `Coupling.turnaround` runs a `ReversibleStep` forward, switches phase exactly
  at a forward-terminal state, retraces through its checked inverse, and leaves
  an inverse-terminal state terminal. `Coupling.returnGadget` instead closes
  every inverse-terminal boundary back to the matching forward state. Closing
  every component uniformly preserves the exact ambient inverse law; the
  runtime never recognizes a privileged start or consults a halting witness.
- `Coupling.History.target_strictlyReachable_iff_halts` and
  `Coupling.History.positiveReturn_iff_halts` are semantic iff theorems. Their
  reflection uses a generated-state invariant, and positive return uses the
  exact predecessor of the forward start. `history_length_lt_of_strictlyReachable`
  separately certifies that the history-forward phase has no positive cycle.
- Stage-5 finite theorems remain abstract interpreters and are not relabelled as
  local-machine results. Stage 6 closes the concrete boundary independently:
  three fixed finite two-tape tables have checked syntactic and semantic
  reversibility, exact halting/return/reachability iff theorems, and
  primitive-recursive varying endpoints.
- Use `FreeMonoid α` for words and define indexed codehood by injectivity of
  `FreeMonoid.lift`. Relate this to mathlib's set-based uniquely-decodable API
  only together with generator injectivity; use the mathlib predicate directly
  and preserve paper unions as tagged `Sum`-indexed families.
- Define `generated c` as `Submonoid.closure (Set.range c)` and connect it to
  the lift image via `FreeMonoid.mrange_lift`. `CodeIso` is intrinsic to exactly
  the generated source and target submonoids; its ambient `PEquiv` has those
  exact domains. `InjectiveMorphism` and the arbitrary-selector `PaperCodeEpi`
  remain separate structures.
- The paper-shaped prefix/suffix marker theorems retain freshness hypotheses for
  both families. Sharper proved variants show that freshness for the already
  prefix/suffix-free family is redundant.
- Arbitrary semantic generated-submonoid decoding and ambient code action are
  explicitly `noncomputable`; no algorithm is inferred from them. Stage 8
  independently supplies exact executable frame decoding and a uniformly
  primitive-recursive finite-table word interpreter.
- Project-local `Lecerf.PEquiv.iterate` uses `Option.bind`, and
  `positiveIterate θ k` means exactly `k + 1` iterations, with checked inverse
  and definedness laws.
- For the first machine-step/code bridge, use canonical self-delimiting Boolean
  frames of complete `Primcodable` two-tape configurations. Source and target
  relation families are indexed by successful configuration edges; whole-step
  backward uniqueness, not local rule inversion, proves target codehood.
- Treat this whole-configuration construction as a cleaner uniform schema for
  a genuine code isomorphism. Its raw finite machine descriptor and checked
  executable interpreter are separated from the semantic infinite edge family
  and noncomputable `CodeIso` constructor. A comparison with Lecerf's finite
  local `alpha`/`omega`/`beta` relations remains an explicit later obligation.
- Interpret “recursively unsolvable in `n`” as a uniform existential problem
  over finite descriptions. Keep supplied-exponent evaluation,
  semidecidability of existence, and noncomputability of existence distinct.

## Success Metrics and Final Verification

The original goal is complete only when all of the following are checked:

1. Deterministic partial systems, reversibility, inverse execution, positive
   reachability, halting, return, and specified-target reachability have stable
   reusable APIs.
2. A concrete deterministic Turing-machine convention and its configuration
   semantics are formalized, with a proved characterization of reversibility.
3. Every ordinary source computation has an effectively constructed reversible
   simulation with a proved history invariant and halting equivalence.
4. Forward/reverse coupling yields explicit computable reductions from an
   established halting problem to reversible halting, return, and reachability.
5. Free monoids, uniquely decodable codes, prefix/suffix code lemmas, generated
   submonoids, code morphisms, and code isomorphisms are formalized without
   conflating total and partial maps.
6. Machine configurations and steps are encoded by code morphisms or code
   isomorphisms, with well-formedness, injectivity, and step-correspondence
   theorems.
7. Exact, nontrivial formulations of the two iterate problems are shown
   undecidable by computable many-one reductions.
8. `PAPER-MAP.md` maps each material paper claim to Lean declarations or an
   explicit correction/unresolved item.
9. `AUDIT.md` records material deviations, open issues, proof-hole scans, and
   `#print axioms` results for every main theorem.
10. Focused module builds and `lake build` succeed; scans find no unclassified
    `sorry`, `admit`, `axiom`, or forbidden shortcut; `git diff --check` passes.

## Proposed Lean Dependency Shape

```text
Transition/Core
  -> Transition/Reversible
  -> Machine/Core
  -> Machine/History/Core
  -> Machine/History/Correctness
  -> Machine/History/Computable
  -> Machine/Coupling
  -> Undecidability/ReversibleMachine

Word/Code
  -> Word/CodeMorphism
  -> Encoding/MachineStep
  -> Undecidability/CodeIterates

Audit/* and API leaves depend downward; core modules never import them.
```

The realized history hierarchy also depends sideways on
`Machine/Effectivity` and `Machine/SourceBridge`; exact import edges are
recorded in `DEPENDENCIES.md`. Later-layer module names remain provisional.

## Stage Index

| Index | Shorthand | Status | Main output |
|---:|---|---|---|
| 1 | `SOURCE-AUDIT` | Complete | Fixed conventions, claim inventory, corrected target statements |
| 2 | `TRANSITION` | Complete | Reversible partial-transition API |
| 3 | `MACHINE` | Complete | Concrete deterministic Turing-machine semantics |
| 4 | `HISTORY-SIM` | Complete | Constructive reversible history simulation |
| 5 | `COUPLING` | Complete | Forward/reverse coupling and return gadgets |
| 6 | `MACHINE-UNDEC` | Complete | Three finite reversible two-tape undecidability reductions |
| 7 | `WORD-CODES` | Complete | Free-monoid code and morphism API |
| 8 | `STEP-CODE` | Complete | Machine-step representation by code maps |
| 9 | `ITERATE-UNDEC` | In progress | Iterate-equation reductions |
| 10 | `PAPER-AUDIT` | Not started | Claim map, public API, corrections, axiom audit |

## 1-SOURCE-AUDIT

### Big Picture Objective

Turn the French source, English transcription, and relevant mathlib APIs into
an explicit formal specification without proving the substantive results.

### Detailed Implementation Plan

- Compare every mathematical statement in the English transcription against
  the French transcription and scans; assign stable claim identifiers.
- Fix the Turing-machine action order, tape boundary/blank convention, halting
  convention, configuration equality, and meaning of the paper's starred
  states.
- Resolve or branch the interpretations of `n ∈ ℕ`, “recursively unsolvable in
  n,” return, reachability, code, complete code, and epimorphism of codes.
- Inspect narrow mathlib modules and record reuse/bridge decisions.
- Draft exact Lean signatures and computability predicates without adding
  unproved declarations to public modules.
- Update `PAPER-MAP.md`, `AUDIT.md`, `DEPENDENCIES.md`, and
  `THEOREM-OUTLINE.md` with evidence.

### Completion Requirements

- Every paper section and theorem has a claim identifier and disposition.
- All critical conventions have either one justified choice or explicitly
  separated candidate formulations with a test that will decide between them.
- The `n = 0`, partial-iteration, inverse-transition, and code-definition issues
  have concrete resolutions or isolated proof obligations.
- Proposed imports and source undecidability theorem names are checked against
  the pinned mathlib source.
- Documentation scans and `git diff --check` pass; no substantive Lean theorem
  is claimed complete.

## 2-TRANSITION

### Big Picture Objective

Build the low-dependency API for deterministic partial execution,
reversibility, inverse steps, reachability, halting, and positive return.

### Detailed Implementation Plan

- Reuse or thinly wrap the checked `StateTransition.Reaches`, `Reaches₁`, and
  `eval` semantics.
- Use `PEquiv σ σ` as the reversible-step carrier and add named `next`/`prev`
  projections only where they improve theorem statements.
- Prove one-step and multi-step reversal, determinism, backward uniqueness,
  reachability reversal, and terminal-state facts.
- Define zero-step-free return and explicit-target reachability predicates.
- Add finite examples and negative tests in an audit leaf.

### Completion Requirements

- Focused builds cover all transition modules and examples.
- The API distinguishes right-unique execution from left-unique/reversible
  execution and distinguishes `Reaches` from `Reaches₁`.
- Inverse multi-step theorems are proved from local inverse laws with no
  project axioms or proof holes.
- Public API imports only stable transition leaves; scans and diff checks pass.

## 3-MACHINE

### Big Picture Objective

Define a finite deterministic Turing-machine model whose inverse semantics can
be stated and proved precisely, and relate it to the chosen computability
source.

### Detailed Implementation Plan

- Implement the fixed read-write-then-move convention and select a canonical
  computable representation of a doubly infinite finite-support blank tape.
- Define rules, deterministic lookup, configurations, step, halting, and
  well-formed finite machine encodings.
- Retain the paper's tuple inverse as audit syntax, compile moving rules through
  reversible write/move phases, and keep rule inversion separate from machine
  reversibility.
- Prove exact local conditions under which the global step has a partial
  inverse.
- Start from the checked `Nat.Partrec.Code.evaln` search transition and build an
  effective bridge to this machine representation. Reuse mathlib TM bridges
  only if they yield an explicit computable finite compiler and semantic iff.

### Completion Requirements

- The configuration-step equation is executable and covered by focused tests.
- A rule-level inverse theorem explicitly undoes execution under stated side
  conditions; movement order is not hidden in notation. The implemented
  atomic semantic phase decomposition is accepted as the cleaner equivalent
  result, while generation of an ordinary finite microstate table is recorded
  as an explicit later bridge.
- Determinism and reversibility are separate predicates with proved
  consequences.
- The source-machine translation is computable and semantics-preserving, or a
  checked obstruction and replacement source model is recorded.
- Focused and adjacent builds, proof-hole scans, and diff checks pass.

## 4-HISTORY-SIM

### Big Picture Objective

Construct a reversible simulator for an arbitrary deterministic source machine
by recording sufficient history, with full correctness and halting reflection.

### Detailed Implementation Plan

- Define simulator phases, encoded source configurations, and explicit history
  records containing the information erased by each source step.
- Define executable forward and inverse simulator steps.
- State and prove the history invariant and encode/decode round trips.
- Prove one source step corresponds to a finite positive simulator run and
  that checkpoint runs cannot arise spuriously.
- Prove source halting iff the simulator reaches its corresponding terminal
  checkpoint.
- Keep a cleaner abstract/tape-level construction distinct from any later
  faithful Lecerf marker encoding.

### Completion Requirements

- The simulator construction is computable on finite machine descriptions.
- Local reversibility and whole-machine determinism are proved.
- Forward simulation, reflection, checkpoint uniqueness, history growth, and
  halting equivalence are all checked.
- No theorem assumes the history invariant without proving initialization and
  preservation.
- Focused and adjacent builds, scans, and diff checks pass.

### Stage Results

- `ConfigCode` and `ConfigCodeEffectivity` provide exact self-delimiting
  Boolean codecs, indexed codehood, and primitive-recursive/computable single
  and concatenated encoders/decoders.
- `StepCode.Core` separates the always-available `PaperCodeEpi` from the
  genuine `CodeIso`; target codehood is equivalent to `BackwardUnique` for the
  whole executable step.
- `StepCode.Correctness` and `Transition.Exact` prove strong one-step, exact
  iterate, definedness, terminal-failure, and positive-reachability
  preservation and reflection.
- `StepCode.Interpreter` agrees with the semantic ambient code action on every
  Boolean word. `StepCode.Effectivity` stores only a raw finite table, uses the
  primitive-recursive syntactic validity guard, and proves its forward raw and
  checked word interpreters uniformly primitive recursive and computable.
- Audits cover all moves, blank extension, malformed/noncanonical frames,
  terminal failure, and the non-backward-unique target-code boundary. Focused,
  API/root, and full builds plus forbidden-construct and axiom scans passed.
- The construction remains a cleaner generally infinite edge schema. No
  theorem claims the historical finite local relation list or a two-to-one-tape
  lowering. Stage 9 has not started.

## 5-COUPLING

### Big Picture Objective

Formalize the forward-to-halt, reverse-to-start coupling and the gadgets needed
for nontrivial return and specified-target reachability.

### Detailed Implementation Plan

- Add a direction/phase bit and switching transition at simulated halting.
- Prove that reverse execution retraces exactly the recorded forward run.
- Construct a positive return to a designated initial configuration and a
  distinct target reachable only after the turnaround.
- State reachability facts using `Reaches₁` where zero steps would trivialize
  them.

### Completion Requirements

- Coupling is deterministic and reversible at phase boundaries.
- Positive return iff source halting and distinct-target reachability iff source
  halting are proved in both directions.
- Initial and target configurations are provably distinct where required.
- Focused builds, boundary scans, and diff checks pass.

## 6-MACHINE-UNDEC

### Big Picture Objective

Derive undecidability of finite reversible two-tape-machine halting, positive
return, and specified-target reachability through explicit computable
reductions.

### Detailed Implementation Plan

- Lower one fixed universal partial-recursive program through mathlib's checked
  TM simulations to a finite one-tape source, with a primitive-recursive
  varying input tape.
- Compile that source into fixed finite two-tape forward-history,
  open-turnaround, and closed-return tables with a checked syntactic validity
  certificate implying semantic reversibility.
- Package raw tables/configurations in `Primcodable` input types and define
  guarded halting, positive-return, and distinct-target strict-reachability
  predicates.
- Prove exact preservation/reflection, primitive recursiveness of each reduction
  map, three `ManyOneReducible` theorems, and their noncomputability corollaries.

### Completion Requirements

- Three explicit many-one reductions compile and their iff specifications are
  proved.
- Each target predicate restricts inputs to well-formed reversible machines
  without turning malformed inputs into a loophole.
- Noncomputability conclusions follow from the pinned mathlib halting theorem,
  not from an assumed project theorem.
- Focused/full relevant builds, scans, `#print axioms`, and diff checks pass.
- The result is scoped to the checked two-tape target model. A two-to-one-tape
  lowering and a literal reconstruction of Lecerf's marker syntax are recorded
  as follow-up work rather than silently assumed.

## 7-WORD-CODES

### Big Picture Objective

Create a precise reusable API for free-monoid words, uniquely decodable codes,
prefix/suffix codes, code-generated submonoids, and the paper's map classes.

### Implemented Direction

- Words use `FreeMonoid`; lists are accessed only through its checked API.
- Indexed codehood is injectivity of `FreeMonoid.lift`. Its exact bridge to
  `InformationTheory.UniquelyDecodable` includes generator injectivity, keeping
  completeness/generation separate from unique decipherability.
- Equation-explicit prefix/suffix predicates support tagged fresh-marker
  extension lemmas for paper §1d, including sharper minimal-hypothesis forms.
- `InjectiveMorphism`, intrinsic generated-submonoid `CodeIso`, and the paper's
  arbitrary-selector `PaperCodeEpi` are distinct. Ambient code-isomorphism
  application is an exactly scoped partial equivalence.
- Partial iteration exposes bind recurrence, inverse, domain/definedness,
  addition, and a separate positive-iterate wrapper.

### Completion Requirements

- Indexed code uniqueness is equivalent to injectivity of the
  generator-induced `FreeMonoid` homomorphism, and its relationship to the
  set-based mathlib predicate accounts for duplicate indices.
- Fresh-marker prefix/suffix extension lemmas are proved with all hypotheses.
- Total, partial, injective, bijective, and paper-specific maps have distinct
  types or predicates.
- Positive iteration exposes domain/definedness conditions.
- Focused and adjacent builds, scans, and diff checks pass.

## 8-STEP-CODE

### Big Picture Objective

Encode machine configurations and individual steps as applications of a code
morphism/isomorphism, closing the construction omitted by the note.

### Detailed Implementation Plan

- Encode complete canonical two-tape configurations as self-delimiting unary
  frames over `Bool`; define executable single/concatenated decoding and prove
  both round trips on the accepted language.
- Index relation words by all successful configuration edges of the finite
  machine. Prove the source family is a code from framing and forward
  functionality, and the target family is a code from whole-step backward
  uniqueness.
- Construct the intrinsic code isomorphism and prove strong one-step and exact
  iterate preservation/reflection, including undefined terminal applications
  and positive reachability.
- Supply a finite machine descriptor and executable interpreter boundary for
  Stage 9; do not store semantic choice or proof objects as runtime input.
- Cover every move and blank-extension case through the checked generic
  two-tape transition theorem. Record that the generally infinite edge schema
  is a cleaner equivalent bridge, not Lecerf's finite local
  `alpha`/`omega`/`beta` relation table.

### Completion Requirements

- Every constructor/rule family is covered; no ellipsis remains in executable
  definitions.
- Encode/decode, code well-formedness, induced-map class, and step iff theorems
  compile.
- The result says exactly when an iterate is defined and remains a valid
  encoded configuration.
- Focused and adjacent builds, scans, and diff checks pass.

## 9-ITERATE-UNDEC

### Big Picture Objective

Reduce reversible-machine return/reachability to the two nontrivial iterate
equation problems for code isomorphisms.

### Detailed Implementation Plan

- Finalize the input types and predicates for positive fixed-point orbit and
  distinct-word orbit reachability.
- Construct `(machine, start)` to `(θ, w)` and
  `(machine, start, target)` to `(θ, w₁, w₂)` computably.
- Prove iteration corresponds exactly to machine reachability, including
  definedness at every intermediate word.
- Derive undecidability with `ManyOneReducible` and explicitly state what is
  decidable when `n` itself is supplied.

### Completion Requirements

- Both target predicates quantify over `n > 0` or another source-justified
  nontrivial domain; `n = 0` cannot discharge the fixed-point problem.
- The distinct-word theorem includes and proves `w₁ ≠ w₂` for reduction
  outputs.
- Reduction functions are computable and both preservation and reflection are
  proved.
- The theorem names and quantifiers are recorded in `PAPER-MAP.md` and
  `AUDIT.md`; focused builds, scans, axiom audit, and diff checks pass.

## 10-PAPER-AUDIT

### Big Picture Objective

Finish the reusable public surface and reconcile every main result with the
paper, including documented corrections and trust assumptions.

### Detailed Implementation Plan

- Add thin API re-export modules without introducing new high-fanout proofs.
- Complete the paper-to-Lean declaration map and distinguish faithful,
  corrected, strengthened, weakened, and unresolved claims.
- Run proof-hole/shortcut scans and `#print axioms` on all headline theorems.
- Run focused consumer builds and the full build from a clean Lake state.
- Record any historical construction not yet connected as explicit follow-up
  work rather than silently treating it as complete.

### Completion Requirements

- Every success metric above has direct recorded evidence.
- `lake build` succeeds from the pinned manifest.
- No completed module contains an unclassified proof hole or project axiom.
- Headline theorem axiom output is recorded and explained.
- `PAPER-MAP.md`, `AUDIT.md`, dependency notes, module docs, and public API agree
  on names and semantics.
- `git diff --check` passes and the next maintenance/research tasks are explicit.

## Current Execution Status

Stages 1--8, including `8-STEP-CODE.md`, are complete. The public machine API
contains fixed finite
two-tape forward-history, open-turnaround, and closed-return tables; checked
syntactic certificates implying semantic reversibility; exact source-halting
iff target-halting/positive-return/distinct-target-strict-reachability theorems;
primitive-recursive reduction maps; three `ManyOneReducible` witnesses; and
three noncomputability results derived from mathlib's pinned halting theorem.
The abstract Stage-4/5 construction remains available but is not confused with
the concrete compiler. The selected universal program and finite encodings are
one-time classical choices; all varying maps are proved primitive recursive,
and representative headline results audit to only `propext`,
`Classical.choice`, and `Quot.sound`. The theorem is currently for a finite
two-tape target model. The independent Stage-7 word surface now includes the
exact indexed/set-code bridge, tagged prefix/suffix marker constructions,
distinct map classes, intrinsic generated-submonoid isomorphisms, exactly
scoped ambient partial action, and positive partial iteration. Stage 8 adds an
exact self-delimiting Boolean codec for complete two-tape configurations, a
successful-edge `PaperCodeEpi`/`CodeIso` with strong step and iterate
reflection, a constructive all-word interpreter, and a proof-free raw finite
table descriptor whose validity guard and forward interpreter are uniformly
primitive recursive. The semantic edge family remains generally infinite and
the semantic `CodeIso` constructor remains noncomputable; neither is stored as
runtime input. A one-tape lowering and the paper's finite local
`alpha`/`omega`/`beta` encoding remain explicit follow-up work. Stage 9 is in
progress with finite raw descriptor/word inputs, strictly positive partial
iteration, explicit validity guards, and a separate supplied-exponent
effectivity boundary fixed as its implementation contract.
