# LECERF Execution Loop

Use this protocol for every work session on `goal-1`. Read `BUILD-PLAN.md` at
the start of any stage that changes Lean code.

## Repeatable Loop

1. Sync current state with actual files and tests.
2. Update `goal-1/0-plan.md` with current facts before starting the next stage.
3. Select the first incomplete stage.
4. Create or refresh `goal-1/[INDEX]-[SHORTHAND].md` from the stage template.
5. Implement only that stage.
6. Add verification and no-cheating checks.
7. Run focused tests, full verification, and whitespace/diff checks appropriate
   to the repository and the dependency surface changed.
8. Record exact commands and results in the stage file.
9. Fold results back into `goal-1/0-plan.md`, `PAPER-MAP.md`, `AUDIT.md`, and
   dependency/theorem notes when affected.
10. Continue toward the original objective. If stopping for the session, leave
    the goal resumable with current evidence, next experiments, unblock
    actions, and assumptions to challenge.

## Invariants

- Do not narrow the user's objective without saying so.
- Do not mark a stage complete without evidence.
- Do not use tests or green checks as evidence unless they cover the
  requirement.
- Prefer small, low-complexity stages that narrow uncertainty.
- Convert blockers into work items: decompose them, route around them, or turn
  them into proof and verification tasks.
- Preserve the distinction between implementation, verifier, diagnostic, and
  fallback paths.
- Treat the paper as evidence to audit, not as an authority that can discharge
  a Lean proof obligation.
- Do not silently conflate zero-step reachability with positive return, a
  partial iterate with a total function iterate, or local rule inversion with
  global machine reversibility.
- Do not add `sorry`, `admit`, proof-bypassing `unsafe`, or unexplained
  project-specific axioms to completed modules.
- Keep core imports narrow, heavy proofs and diagnostics in leaves, and API
  modules thin.
- A failed construction is evidence only when represented by a checked
  obstruction or a reproducible diagnostic.

## Initial State Sync

Before editing a stage:

- Read `goal-1/0-plan.md`, this file, the previous completed stage file, and the
  relevant parts of `BUILD-PLAN.md`.
- Run `git status --short` and inspect all relevant existing modules and docs.
- Recheck the pinned toolchain and manifest before relying on mathlib names.
- Record contradictions between actual files and the plan before
  implementation.
- Identify the lowest-dependency owner for each proposed declaration, the
  focused build command, and any adjacent consumer builds.

## Verification Ladder

Use only the levels required by the current changes, but cover every touched
module:

1. Build a new or touched leaf directly, for example:

   ```text
   cd formal && lake build Lecerf.Transition.Core
   ```

2. Build adjacent consumers if a shared definition or public surface changed.
3. Run the full project build when configuration, an API/umbrella import,
   global notation/instances, or a stage completion requirement changed:

   ```text
   cd formal && lake build
   ```

4. Scan Lean sources and goal evidence:

   ```text
   rg -n "sorry|admit|axiom|unsafe" formal goal-1 --glob '!formal/.lake/**'
   ```

   Documentation hits that describe guardrails are expected and must be
   classified. Lean hits require removal or an explicit audit disposition.

5. Run stage-specific shortcut scans, `git diff --check`, and inspect the
   actual diff.
6. For headline theorems, run `#print axioms` in a temporary or audit leaf and
   record the output in `goal-1/AUDIT.md`.

## Stage File Template

```markdown
# [INDEX]-[SHORTHAND]

## Current Facts

- Facts from current code, tests, docs, and previous stage results.

## Updated Assumptions

- Assumptions that still look valid.
- Assumptions that changed.
- Assumptions that need tests before being trusted.

## Big Picture Objective

- Restate the stage objective, adjusted for current facts.

## Detailed Implementation Plan

- Concrete code/doc/test changes for this stage.
- Files expected to change.
- New tests or commands required.

## Build Structure

- New or touched Lean modules and why each owns its declarations.
- High-fanout modules intentionally avoided.
- Focused build command.
- Adjacent consumer builds required.

## No-Cheating Checks

- Explicit checks proving the implementation does not route through forbidden
  fallback paths.
- Checks that distinguish zero/positive reachability, partial/total maps,
  local/global reversibility, and theorem/reduction layers as applicable.

## Boundary Checks

- Runtime, public API, proof-side, diagnostic, fallback, and temporary
  declarations introduced by the stage.
- Forbidden shortcuts and the exact scan or signature inspection used.

## Completion Requirements

- Requirement-by-requirement checks.
- Required test and build commands.
- Documentation updates required.

## Stage Results

- Fill in at the end of the stage.
- Include tests run and exact outcomes.
- Include what was learned.
- Include declarations and module paths added or changed.
- Include what should change in `0-plan.md` before the next stage.
```

## Fold-Back Before Stopping

- Update the stage results with exact evidence.
- Update stage status and current facts in `0-plan.md`.
- Update claim dispositions and correction entries affected by the work.
- Record exact theorem names, module paths, failed obligations, and next
  actions.
- Never leave a stage labeled complete when a completion requirement lacks
  evidence.
