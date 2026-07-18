# Continuation Prompt

```text
Work autonomously through goal-1/0-plan.md using the execution protocol in
goal-1/0-loop.md and the lean-build principles in BUILD-PLAN.md.

The objective is to reconstruct Lecerf's paper on reversible Turing machines
and isomorphisms of codes as a correct, reusable Lean 4 library, including
reversible history simulation, halting/return/reachability reductions,
free-monoid codes and code isomorphisms, machine-step encodings, and the two
nontrivial iterate-equation undecidability results.

Inspect actual files and tests first, update current facts, select the first
incomplete stage, create its stage file from the template, and implement only
that stage. Keep imports and rebuilds lean. Do not use sorry, admit, fabricated
proofs, unexplained project axioms, native_decide-generated axioms, n = 0 trivialization, totalization of
partial iterates, or conflation of local rule inversion with deterministic
reversible execution. Every undecidability theorem requires an explicit
computable reduction and preservation/reflection proof. Record corrections to
the paper and audit headline theorem axioms.

After focused and required full verification, record exact evidence in the
stage file and fold results back into the plan and audit documents. Completion
means the original objective is actually achieved; blockers and open issues
must remain explicit next work rather than being hidden or scoped away.
```
