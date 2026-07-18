import Lecerf.Machine.Lookup
import Lecerf.Machine.TwoTape.HistoryCompiler.Core

/-!
# Basic facts for the finite history compiler

This leaf exposes exact membership descriptions for the six generated rule
families.  Later validity and simulation proofs can therefore reason about a
generated rule by its source constructor rather than by unfolding nested
`Finset` enumerations repeatedly.
-/

namespace Lecerf.Machine.TwoTape.HistoryCompiler

open Lecerf.Machine

universe u v

variable {Q : Type u} {Γ : Type v}
  [Fintype Q] [Fintype Γ] [DecidableEq Q] [DecidableEq Γ]

omit [Fintype Q] [Fintype Γ] [DecidableEq Q] [DecidableEq Γ] in
theorem mem_forwardRules_iff
    {machine : Lecerf.Machine.FiniteMachine Q Γ}
    {entry : TwoTape.Rule (Control Q Γ) Γ (Mark Q Γ)} :
    entry ∈ forwardRules machine ↔
      ∃ rule ∈ machine.rules, forwardRule rule = entry := by
  simp [forwardRules]

theorem mem_boundaryRules_iff
    {machine : Lecerf.Machine.FiniteMachine Q Γ}
    {entry : TwoTape.Rule (Control Q Γ) Γ (Mark Q Γ)} :
    entry ∈ boundaryRules machine ↔
      ∃ state symbol, machine.lookup state symbol = none ∧
        boundaryRule state symbol = entry := by
  simp [boundaryRules]

omit [DecidableEq Q] [DecidableEq Γ] in
theorem mem_scanRules_iff
    {entry : TwoTape.Rule (Control Q Γ) Γ (Mark Q Γ)} :
    entry ∈ (scanRules :
      List (TwoTape.Rule (Control Q Γ) Γ (Mark Q Γ))) ↔
      ∃ state symbol, scanRule state symbol = entry := by
  simp [scanRules]

omit [Fintype Q] [DecidableEq Q] [DecidableEq Γ] in
theorem mem_inspectRules_iff
    {machine : Lecerf.Machine.FiniteMachine Q Γ}
    {entry : TwoTape.Rule (Control Q Γ) Γ (Mark Q Γ)} :
    entry ∈ inspectRules machine ↔
      ∃ rule ∈ machine.rules, ∃ symbol, inspectRule rule symbol = entry := by
  simp [inspectRules]

omit [Fintype Q] [Fintype Γ] [DecidableEq Q] [DecidableEq Γ] in
theorem mem_restoreRules_iff
    {machine : Lecerf.Machine.FiniteMachine Q Γ}
    {entry : TwoTape.Rule (Control Q Γ) Γ (Mark Q Γ)} :
    entry ∈ restoreRules machine ↔
      ∃ rule ∈ machine.rules, restoreRule rule = entry := by
  simp [restoreRules]

omit [DecidableEq Q] [DecidableEq Γ] in
theorem mem_bottomRules_iff
    {entry : TwoTape.Rule (Control Q Γ) Γ (Mark Q Γ)} :
    entry ∈ (bottomRules :
      List (TwoTape.Rule (Control Q Γ) Γ (Mark Q Γ))) ↔
      ∃ state symbol, bottomRule state symbol = entry := by
  simp [bottomRules]

theorem mem_turnaroundMachine_iff
    {machine : Lecerf.Machine.FiniteMachine Q Γ}
    {entry : TwoTape.Rule (Control Q Γ) Γ (Mark Q Γ)} :
    entry ∈ (turnaroundMachine machine).rules ↔
      entry ∈ forwardRules machine ∨ entry ∈ boundaryRules machine ∨
        entry ∈ scanRules ∨ entry ∈ inspectRules machine ∨
          entry ∈ restoreRules machine := by
  simp [turnaroundMachine]

theorem mem_returnMachine_iff
    {machine : Lecerf.Machine.FiniteMachine Q Γ}
    {entry : TwoTape.Rule (Control Q Γ) Γ (Mark Q Γ)} :
    entry ∈ (returnMachine machine).rules ↔
      entry ∈ (turnaroundMachine machine).rules ∨ entry ∈ bottomRules := by
  simp [returnMachine]

end Lecerf.Machine.TwoTape.HistoryCompiler
