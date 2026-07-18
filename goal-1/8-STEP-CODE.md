# 8-STEP-CODE

## Current Facts

- Stages 1--7 are complete. Stage 6 supplies fixed finite reversible two-tape
  machines with checked halting, positive-return, and distinct-target
  reachability reductions; Stage 7 supplies genuine indexed codes, intrinsic
  generated-submonoid `CodeIso`s, exact ambient partial domains, and positive
  partial iteration.
- The paper's §3 construction is a finite local one-tape relation table using
  `alpha`/`omega`/`beta` head markers. It lists the three relations associated
  with each move direction, but leaves the configuration convention, boundary
  behavior, code proof, and step-reflection proof informal.
- The project's undecidability source is presently a conventional finite
  **two-tape** reversible machine. Directly linearizing two independently moving
  heads into the paper's one-tape local relations would require an additional
  multi-tape lowering or a new multi-phase local encoding; neither exists in
  the current tree.
- The objective expressly permits proving a cleaner equivalent theorem first
  and connecting it to Lecerf's historical encoding later. That permission
  does not allow the cleaner theorem to be mislabeled as the omitted local
  `alpha`/`omega`/`beta` construction.
- `TwoTape.Config` already has a constructive `Primcodable` instance whenever
  its state and tape alphabets do. Thus complete canonical configurations can
  be represented by self-delimiting words over the finite alphabet `Bool`.
- A family containing one self-delimiting word for every configuration is an
  indexed code when concatenations have a checked decoder. Restricting the
  family to successful source configurations preserves codehood; mapping each
  source to its successor preserves indexed injectivity exactly when successful
  predecessors are unique.
- `CodeIso.ofCodes` is semantic and noncomputable, but its generator equation
  is exact. Runtime reductions therefore need a separate executable finite
  descriptor and interpreter rather than treating the semantic constructor as
  an algorithm.

## Updated Assumptions

- Use a canonical unary frame over `Bool`: the natural `Primcodable` code of a
  configuration is represented by that many `true` letters followed by
  `false`. The decoder must reject noncanonical natural codes, accept
  concatenated frames, and be a two-sided inverse on its accepted language.
- Index the semantic relation family by successful configuration edges
  `source --machine.step--> target`. Its source word is the framed source
  configuration and its target word is the framed target configuration.
- Forward functionality makes the source projection on edges injective;
  `BackwardUnique machine.step` makes the target projection injective. These
  facts, rather than an appeal to individual rule inverses, justify the two
  indexed-code proofs.
- The resulting code family is generally infinite, but is uniformly generated
  by a finite machine table and an executable framing algorithm. This is a
  cleaner finite **schema** for a genuine code isomorphism, not yet the paper's
  finite local relation list. Preserve that distinction in every theorem and
  audit entry.
- Cover left, right, stationary, blank-extension, and every other rule case by
  proving correspondence with the already checked generic `machine.step`, not
  by restating only representative rules.
- Iteration is the Stage-7 partial `Lecerf.PEquiv.iterate`; a failed machine
  step must make the next code iterate undefined. Positive iteration remains
  distinct from exponent zero.
- Stage 9 inputs should store the raw finite machine table and use its
  primitive-recursive syntactic validity guard. They must not store a Lean
  function, a proof object, or the noncomputable semantic `CodeIso` as runtime
  data.

## Big Picture Objective

Construct an executable self-delimiting representation of conventional
two-tape configurations and a genuine code isomorphism whose action on one
encoded configuration is defined exactly for successful reversible-machine
steps. Prove preservation and reflection for one step and every supplied
iterate, while recording the remaining comparison with Lecerf's finite local
`alpha`/`omega`/`beta` relations.

## Detailed Implementation Plan

1. Add a low-dependency configuration-code leaf with canonical Boolean frames,
   single and concatenated decoders, round trips, injectivity, and indexed
   codehood.
2. Add an edge/code-isomorphism core. Prove source- and target-edge projection
   injectivity, both code-family theorems, and construct `stepCodeIso` without
   confusing semantic construction with executable interpretation.
3. Add correctness results giving a strong one-step equation (including that
   every successful output is an encoded configuration), exact supplied-step
   iteration, definedness, positive reachability, and terminal failure.
4. Add an executable interpreter over canonical frame sequences and the
   computability facts needed for the Stage-9 finite descriptor boundary. State
   precisely how far it agrees with the semantic ambient code action.
5. Add a non-public audit with left/right/stay and blank-extension examples,
   malformed/noncanonical word rejection, a nonreversible negative boundary,
   and representative `#print axioms` output. Add a thin public API only after
   focused builds pass.
6. Fold exact declarations, the infinite-schema versus finite-local correction,
   effectivity boundaries, builds, scans, and axiom evidence into all goal
   documents. Do not start Stage 9.

## Build Structure

- `formal/Lecerf/Encoding/ConfigCode.lean`: Boolean framing, decoding, and
  indexed codehood; imports only the two-tape configuration representation and
  `Word.Code` plus narrow computability/list support.
- `formal/Lecerf/Encoding/StepCode/Core.lean`: successful edges and semantic
  relation families/`CodeIso`; imports the codec and two-tape reversibility.
- `formal/Lecerf/Encoding/StepCode/Correctness.lean`: one-step and iterate
  preservation/reflection; imports the core and a narrow exact-step leaf.
- `formal/Lecerf/Encoding/StepCode/Effectivity.lean`: executable descriptor and
  interpreter theorems; imports primitive-recursive two-tape semantics only
  where required.
- `formal/Lecerf/Encoding/StepCode/API.lean`: thin stable re-export.
- `formal/Lecerf/Encoding/StepCode/Audit.lean`: diagnostic examples and axiom
  output; never publicly re-exported.
- Focused builds start with each new leaf. Because `Lecerf.lean` will gain a
  public API import, adjacent root and final full builds are required.

## No-Cheating Checks

- Do not encode a whole configuration as one alphabet letter; the ambient
  alphabet must remain genuinely finite (`Bool`).
- Do not use an arbitrary inverse function as an executable decoder. Decoding
  must be defined, reject noncanonical words, and prove both required round
  trips on the accepted language.
- Do not infer target-code injectivity from forward determinism. It must use
  successful-predecessor uniqueness supplied by whole-machine reversibility.
- Do not label the infinite configuration-edge family as Lecerf's finite local
  relation list or claim that a two-tape lowering has been proved.
- Do not replace the semantic `CodeIso` with an unrelated transition `PEquiv`.
  The code families, generator law, and agreement on encoded computations must
  all be checked.
- Do not prove only preservation. Successful ambient action starting from an
  encoded configuration must reflect a unique machine step and an encoded
  target; iterates need the same no-spurious-target property.
- Do not totalize terminal or malformed inputs, and do not use exponent zero
  for positive reachability.
- No `sorry`, `admit`, proof-bypassing `unsafe`, fabricated theorem, or project
  axiom.

## Boundary Checks

- Runtime declarations: Boolean frame encoder/decoder, finite machine
  descriptor, validator, and executable word interpreter.
- Public semantic declarations: successful edge family, source/target codes,
  `stepCodeIso`, and exact one-step/iterate correspondence.
- Proof-side declarations: codehood, generated-word factorization, target
  injectivity from `BackwardUnique`, and reachability bridges.
- Diagnostic declarations: concrete move/boundary cases, malformed words,
  negative nonreversible examples, and axiom output in `StepCode.Audit` only.
- The noncomputable `CodeIso.ofCodes` layer is permitted only as semantic
  evidence. Scan runtime/effectivity signatures to ensure it is absent from
  stored finite data and varying reduction functions.
- Inspect public signatures for an infinite `Edge` index and describe it as a
  uniform schema. Any theorem about a finite local relation list remains
  explicitly unproved.

## Completion Requirements

- The Boolean alphabet is finite, and `encodeConfig`/`decodeConfig` plus the
  concatenated-frame parser have checked round trips and malformed-word tests.
- The full configuration family, successful source family, and reversible
  target family are proved indexed codes. The target proof visibly depends on
  `BackwardUnique` or an equivalent whole-machine hypothesis.
- `stepCodeIso` is a genuine Stage-7 `CodeIso`; successful application to an
  encoded configuration is equivalent to `machine.step = some`, in both
  directions, with every output proved to be an encoded configuration.
- Exact supplied-step iteration preserves and reflects machine execution,
  including definedness of every intermediate application. Positive code
  iteration is equivalent to strict machine reachability.
- The executable descriptor/interpreter boundary is sufficient for Stage 9:
  no semantic choice is stored as input, and required encoding/interpreter
  maps have checked computability evidence or an explicitly isolated remaining
  obligation that prevents Stage 8 from being marked complete.
- Audits cover every move constructor, blank extension, malformed frames,
  terminal undefinedness, and the nonreversible target-injectivity boundary.
- Focused leaf/API/audit/root/full builds, proof-hole and boundary scans,
  representative axiom audits, whitespace checks, and `git diff --check` pass.
- Results are folded into `0-plan.md`, `DEPENDENCIES.md`,
  `THEOREM-OUTLINE.md`, `AUDIT.md`, and `PAPER-MAP.md`. Stage 9 is not started.

## Stage Results

- In progress.
