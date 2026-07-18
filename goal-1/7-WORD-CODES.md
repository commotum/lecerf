# 7-WORD-CODES

## Current Facts

- Stages 1--6 are complete. Stage 6 exposes validity-guarded finite reversible
  two-tape halting, positive-return, and distinct-target reachability problems
  with three explicit computable many-one reductions.
- The French §1b definition says a word has **at most one** ordered indexed
  factorization into codewords. The English transcription's existential
  wording is incorrect; codehood is unique decipherability, not completeness.
- `FreeMonoid A` is definitionally list-backed in the pinned mathlib version.
  `FreeMonoid.toList` is an equivalence, multiplication maps to append, and
  `FreeMonoid.lift c` is the generator-induced monoid homomorphism.
- Mathlib's `InformationTheory.UniquelyDecodable S` is set-based: it says two
  lists whose entries lie in `S` and whose flattenings agree are equal. Its
  API proves exclusion of the empty word and injectivity of flattening on
  lists of members.
- A set forgets duplicate generator indices. Therefore
  `UniquelyDecodable (Set.range fun i => (c i).toList)` alone is weaker than
  injectivity of `FreeMonoid.lift c`; the exact bridge must additionally require
  `Function.Injective c`.
- Mathlib has `Submonoid.mrange`, `FreeMonoid.mrange_lift`, and
  `Submonoid.closure_eq_mrange`. `Submonoid.equivMapOfInjective` is explicitly
  noncomputable, so executable later reduction descriptions must not be hidden
  inside that construction.
- `PEquiv.trans` uses `Option.bind`, and mathlib provides no checked natural
  power API for `PEquiv`. Stage 7 must define partial iteration locally and
  expose the bind recurrence rather than totalizing undefined applications.
- Paper §1d uses right/left prefix-code in an orientation opposite some modern
  naming conventions: `m_i = m_j y` is the right-extension/prefix-free case,
  while `m_i = y m_j` is the left-extension/suffix-free case. Public names must
  state their equations, not rely on the historical label alone.
- Paper §1e's “epimorphism of codes” only requires the source family to be a
  code and each assigned target word to belong to a target code. The selector
  may repeat target codewords and need not cover the target code; this is not
  categorical epimorphism, injectivity, or bijectivity.

## Updated Assumptions

- Use `Word A := FreeMonoid A` and define indexed codehood by injectivity of
  `FreeMonoid.lift`. Add a separately named set-code predicate only where the
  paper's union/fresh-marker lemma is naturally set-based.
- Generated submonoids are the `mrange` of the generator-induced lift. An
  intrinsic code isomorphism should retain its source and target generator
  families and an equivalence of exactly those generated submonoids.
- It is acceptable for the semantic ambient partial equivalence of arbitrary
  code families to use classical membership choice, provided this is explicit
  and no later finite computability claim is inferred from it. Stage 9 must use
  raw executable finite descriptions.
- Model the paper-specific epimorphism with a source code, a target code, and a
  selector into target indices. Do not add injectivity or surjectivity that the
  French definition does not state.
- Define zero-th partial iteration as identity for algebraic recursion, but
  expose a separate positive-iterate wrapper indexed by `k + 1` for the later
  nontrivial decision problems.

## Big Picture Objective

Create a precise reusable API for free-monoid words, indexed and set-based
codes, prefix/suffix code constructions, generated submonoids, code morphism
classes, intrinsic code isomorphisms, the paper's weaker epimorphism notion,
and partial positive iteration.

## Detailed Implementation Plan

1. Add `Word/Code.lean` with `Word`, `IsIndexedCode`, the exact bridge to
   `InformationTheory.UniquelyDecodable`, generated-submonoid definitions, and
   cheap consequences such as generator and nonempty-word injectivity.
2. Add `Word/Prefix.lean` with equation-explicit prefix/suffix-free predicates,
   freshness, marker-prefix/marker-suffix constructions, and both §1d code
   extension theorems with all hypotheses visible.
3. Add `Word/CodeMorphism.lean` distinguishing total monoid homomorphisms,
   injective morphisms, intrinsic code isomorphisms, ambient partial action,
   and `PaperCodeEpi`. Add partial iteration, positive iteration, bind,
   definedness, inverse, and addition lemmas needed by Stages 8--9.
4. Add a non-public `Word/Audit.lean` with positive and negative finite examples
   and `#print axioms` for the bridge, fresh-marker, ambient-action, and iterate
   results. Add a thin `Word/API.lean` and re-export it from `Lecerf.lean` only
   after focused builds pass.
5. Fold exact declarations, corrections, classical/noncomputable boundaries,
   and build/axiom evidence into the plan, theorem outline, dependency notes,
   audit, and paper map.

## Build Structure

- `formal/Lecerf/Word/Code.lean`: low-dependency word and code definitions plus
  the mathlib unique-decipherability bridge.
- `formal/Lecerf/Word/Prefix.lean`: fresh-marker and prefix/suffix proofs;
  imports only `Word.Code` plus narrow list/set support if needed.
- `formal/Lecerf/Word/CodeMorphism.lean`: generated-submonoid maps, semantic
  ambient `PEquiv`, paper-specific epimorphism, and partial iteration; imports
  `Word.Code` and narrow submonoid/`PEquiv` modules.
- `formal/Lecerf/Word/API.lean`: thin public re-export of stable Stage-7 leaves.
- `formal/Lecerf/Word/Audit.lean`: diagnostic examples and axiom output; never
  publicly re-exported.
- Focused builds:
  `lake build Lecerf.Word.Code`, `Lecerf.Word.Prefix`, and
  `Lecerf.Word.CodeMorphism`. Adjacent builds cover `Lecerf.Word.API` and
  `Lecerf`; the root import requires a final full `lake build`.

## No-Cheating Checks

- Do not define codehood as mere generator injectivity; the entire induced
  free-monoid homomorphism must be injective.
- Do not equate the set-based uniquely-decodable predicate with indexed
  codehood without the extra generator-injectivity condition.
- Do not call the paper's epimorphism a surjective monoid homomorphism or infer
  injectivity/bijectivity from membership of target words in a code.
- Do not represent an intrinsic generated-submonoid equivalence as a total
  ambient-word automorphism. Outside the source generated submonoid its action
  must be undefined.
- Do not totalize failed iteration as identity or an absorbing word. Successor
  iteration must be `Option.bind`, and later fixed-orbit statements must use a
  positive exponent.
- Do not silently admit the empty word into a nonempty code. Exercise this in a
  negative audit example.
- No `sorry`, `admit`, proof-bypassing `unsafe`, fabricated theorem, or project
  axiom.

## Boundary Checks

- Runtime/public definitions: word/code predicates, code-map structures,
  ambient partial action, and partial iteration.
- Proof-side declarations: equivalence with mathlib codehood, marker-extension
  correctness, generated-submonoid equivalence laws, and iteration algebra.
- Diagnostic declarations: concrete counterexamples and `#print axioms` only
  in `Word.Audit`.
- Any `noncomputable` declaration must be classified as a semantic arbitrary
  set/submonoid membership choice. No Stage-7 theorem may claim a computable
  finite code-description interpreter.
- Scan public signatures for accidental `Set.range` information loss,
  zero-step positive iteration, total ambient functions, and categorical
  `Epi` terminology.

## Completion Requirements

- `IsIndexedCode c` is implemented as injectivity of `FreeMonoid.lift c`, and
  its iff with generator injectivity plus mathlib `UniquelyDecodable` compiles.
- Prefix/suffix predicates and both fresh-marker code-extension theorems compile
  with explicit freshness and empty-word hypotheses where required.
- Monoid homomorphisms, injective morphisms, code isomorphisms, ambient partial
  actions, and `PaperCodeEpi` are distinct declarations with checked laws.
- Partial iteration has checked zero, successor-bind, addition, definedness,
  inverse, and positive-iterate statements sufficient for later machine-step
  iteration.
- Audit examples distinguish duplicate indices, empty codewords, non-surjective
  paper selectors, partial-domain failure, and positive versus zero iteration.
- Focused leaf builds, API/root/full builds, proof-hole and boundary scans,
  representative axiom audits, whitespace checks, and `git diff --check` pass.
- Results are folded into `0-plan.md`, `DEPENDENCIES.md`,
  `THEOREM-OUTLINE.md`, `AUDIT.md`, and `PAPER-MAP.md`. Stage 8 is not started.

## Stage Results

- In progress.
