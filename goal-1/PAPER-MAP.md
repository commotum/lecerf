# Paper Map

Source set:

- `lecerf-1963-fr/lecerf-1963-fr.pdf` and page images: primary historical text.
- `lecerf-1963-fr/lecerf-1963-fr.md`: searchable French transcription.
- `lecerf-1963-en/lecerf-1963-en.pdf` and Markdown: English translation and
  transcription, to be checked against the French.

Status labels used below: `unreviewed`, `proposed`, `corrected`, `formalized`,
`blocked`, and `out-of-scope-follow-up`.

## Claim Inventory

| ID | Location | Paper content | Proposed formal target | Status |
|---|---|---|---|---|
| `L1a-POST` | §1a | PCP/diagonalization is undecidable for arbitrary homomorphisms and with one monomorphism | Background dependency only unless needed as an alternate source reduction | unreviewed |
| `L1b-ISO` | §1b | `θ = ψ ∘ φ⁻¹` is a bijective multiplicative map between images of injective free-monoid morphisms | Code isomorphism between generated submonoids induced by two injective `FreeMonoid` homomorphisms | proposed |
| `L1b-CODE` | §1b | Images of generators form codes because decoding has at most one index sequence | Unique decipherability iff induced free-monoid homomorphism is injective | corrected |
| `L1c-REL` | §1c | Relation words define a code isomorphism when both indexed families are codes and correspondence is bijective | Construction from two injective generator maps sharing an index type | proposed |
| `L1d-PREFIX` | §1d | Fresh-marker union with a right/left prefix code remains a code | Two explicit uniquely-decodable-code extension lemmas | proposed |
| `L1e-EPI` | §1e | “Epimorphism of codes” has a code on the source and target relation words only constrained to lie in a code | Separate paper-specific structure; exact duplicate/surjectivity conditions unresolved | unreviewed |
| `L2-RULEINV` | §2 | Associate a sign-reversed inverse-image quintuple to each rule | Syntactic rule inversion under a fixed action-order convention | unreviewed |
| `L2-REV` | §2 | A machine is reversible when inverse-image quintuples constitute a machine; inverse runs traverse image configurations backward | Deterministic forward and inverse step functions satisfying partial inverse laws | unreviewed |
| `L2-COUPLE` | §2 | Union of machine, inverse image, and halt-switch rules runs forward then backward | Phase-tagged forward/reverse coupling theorem | proposed |
| `L3-RELATIONS` | §3 | Three relation elements per `+1`, `0`, or `-1` rule plus symbol identities define an epimorphism of codes | Exhaustive rule-family encoding with proved source-code property | unreviewed |
| `L3-CONFIG` | §3 | `α/ω/β` markers encode current read and previously written positions so `uᵢ₊₁ = τ(uᵢ)` | Encode/decode and one-step iff theorem for well-formed configurations | unreviewed |
| `L3-MIN` | §3 | Removing relation forms that never appear gives `τ_min`; if it is an isomorphism, the machine is reversible | Reachable-language restriction and a precisely directed implication/equivalence | unreviewed |
| `L4a-SIM1` | §4a(1) | One source step is simulated by finitely many reversible steps between checkpoints | Positive finite simulation theorem | proposed |
| `L4a-SIM2` | §4a(2) | Source steps use an epimorphism `τ`; simulator steps use code isomorphism `θ` | Layered step-encoding theorems, after machine simulation is complete | proposed |
| `L4a-SIM3` | §4a(3) | Checkpoint encodes source configuration and recoverable history between fresh delimiters | Encoding/decoding and checkpoint invariant | proposed |
| `L4a-SIM4` | §4a(4) | History word records exactly the invoked nonidentity rules | History trace equals source transition trace, with identity-step policy explicit | proposed |
| `L4a-SIM5` | §4a(5) | Reversible simulator halts exactly at source-halting checkpoints | Halting preservation and reflection | proposed |
| `L4a-SIM6` | §4a(6) | Coupled machine reaches the starred initial configuration iff source halts | Computable reduction to distinct-target reachability | proposed |
| `L4a-SIM7` | §4a(7) | Return or passage through a framed target can be made conditional on source halting | Positive-return and specified-target gadgets with iff theorems | proposed |
| `L4a-SKETCH` | §4a proof | Representative instruction scheme for one relation; other control and tape-management instructions omitted | Complete cleaner construction first; historical encoding connection later | unreviewed |
| `L4b-THM1H` | Theorem 1 | Halting is undecidable for general reversible Turing machines | Noncomputability of a well-formed finite reversible-machine halting predicate | proposed |
| `L4b-THM1R` | Theorem 1 | Return to initial configuration is undecidable | Noncomputability of **positive** return | corrected |
| `L4b-THM1T` | Theorem 1 | Passage through a specified noninitial configuration is undecidable | Noncomputability of reachability of a provably distinct target | proposed |
| `L4c-THM2F` | Theorem 2 | `w = θⁿ(w)` is recursively unsolvable in `n` for given `w, θ` | Existence of a **positive**, defined iterate returning to `w`; interpretation still requires source audit | corrected |
| `L4c-THM2O` | Theorem 2 | `w₁ = θⁿ(w₂)`, `w₁ ≠ w₂`, is recursively unsolvable in `n` | Existence of a defined iterate reaching a distinct word, with orientation checked | proposed |

## Planned Declaration Map

Exact names are provisional and are not yet Lean declarations.

| Claim family | Candidate declaration family | Planned stage |
|---|---|---:|
| Generic reversible execution | `ReversibleSystem`, `reaches_iff_reverse_reaches` | 2 |
| Concrete machine inverse | `Machine.IsReversible`, `inverse_step_iff` | 3 |
| History simulation | `historySim`, `historySim_checkpoint_iff`, `historySim_halts_iff` | 4 |
| Coupling | `coupled_reaches_star_iff`, `coupled_returns₁_iff` | 5 |
| Machine undecidability | `reversibleHalting_not_computable`, `reversibleReturn_not_computable`, `reversibleReachability_not_computable` | 6 |
| Codes | `IsCode`, `IsPrefixCode`, `CodeIso`, `PaperCodeEpi` | 7 |
| Step encoding | `encodeConfig`, `stepCodeIso`, `iterate_encode_iff_reaches` | 8 |
| Iterate undecidability | `positiveFixedOrbit_not_computable`, `distinctOrbit_not_computable` | 9 |

## Source-Audit Checklist

- Compare the meeting date in the bibliographic header and footnote.
- Verify every use of “au plus un”/“at most one” in the code definition.
- Determine whether `N` in the historical convention excludes zero; do not
  infer this from modern Lean `Nat`.
- Determine whether `θⁿ(w)` presupposes all intermediate words lie in the next
  source code.
- Reconstruct the exact read/write/move order required by the inverse
  quintuple.
- Determine whether repeated target relation words are allowed in the paper's
  “epimorphism,” and whether “complete code” means a whole indexed source code
  rather than completeness in modern coding theory.
- Check the orientation of `w₁ = θⁿ(w₂)` against the machine-to-word encoding.
- Separate statements proved in this note from announcements depending on the
  promised second note.
