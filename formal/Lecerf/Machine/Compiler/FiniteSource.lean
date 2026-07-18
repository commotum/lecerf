import Lecerf.Machine.Compiler.Table
import Lecerf.Machine.Compiler.TapeBridge
import Lecerf.Machine.Compiler.UniversalSource
import Mathlib.Computability.TuringMachine.PostTuringMachine

/-!
# A fixed finite one-tape source machine

This module lowers the fixed universal program from `UniversalSource` through
mathlib's checked TM2-to-TM1 and TM1-to-TM0 simulations.  The resulting TM0
program has a fixed finite support.  Restricting states to that support and
expanding every state/symbol entry produces an actual conventional
`FiniteMachine` table.

The program, its support, and the finite encodings are closed constants and
therefore deliberately noncomputable.  Source programs do not select or
compile a machine: only their initial tape data varies.  The computability of
that varying start map is proved separately below rather than inferred from
the closed choices.
-/

namespace Lecerf.Machine.Compiler.FiniteSource

open Encodable Denumerable
open Turing

namespace PartrecToTM2

/-- The four stack indices used by mathlib's fixed partial-recursive
interpreter form an explicitly finite type. -/
instance kFintype : Fintype Turing.PartrecToTM2.K' :=
  Fintype.ofList
    [Turing.PartrecToTM2.K'.main, Turing.PartrecToTM2.K'.rev,
      Turing.PartrecToTM2.K'.aux, Turing.PartrecToTM2.K'.stack]
    (by intro index; cases index <;> simp)

end PartrecToTM2

/-- For the fixed universal run, mathlib's TM2 support is rooted at the
selected program's entry label rather than at the inductive type's unrelated
canonical default. -/
noncomputable instance universalLabelInhabited :
    Inhabited Turing.PartrecToTM2.Λ' :=
  ⟨Turing.PartrecToTM2.trNormal UniversalSource.universalCode
    Turing.PartrecToTM2.Cont'.halt⟩

/-- The fixed TM1 tape alphabet used to multiplex the four TM2 stacks. -/
abbrev Symbol :=
  Turing.TM2to1.Γ' Turing.PartrecToTM2.K'
    (fun _ => Turing.PartrecToTM2.Γ')

/-- The fixed TM1 program obtained from mathlib's universal TM2 evaluator. -/
abbrev tm1Program :=
  Turing.TM2to1.tr Turing.PartrecToTM2.tr

/-- Labels of the fixed TM1 program. -/
abbrev TM1Label :=
  Turing.TM2to1.Λ' Turing.PartrecToTM2.K'
    (fun _ => Turing.PartrecToTM2.Γ')
    Turing.PartrecToTM2.Λ' (Option Turing.PartrecToTM2.Γ')

/-- States of the translated TM0 program before restriction to its finite
support. -/
abbrev AmbientState := Turing.TM1to0.Λ' tm1Program

/-- The fixed TM0 transition program. -/
noncomputable def ambientMachine : Turing.TM0.Machine Symbol AmbientState :=
  Turing.TM1to0.tr tm1Program

/-- Finite TM2 label support for the selected universal program. -/
noncomputable def tm2Support : Finset Turing.PartrecToTM2.Λ' :=
  Turing.PartrecToTM2.codeSupp UniversalSource.universalCode
    Turing.PartrecToTM2.Cont'.halt

/-- Finite support of the TM1 translation. -/
noncomputable def tm1Support : Finset TM1Label :=
  Turing.TM2to1.trSupp Turing.PartrecToTM2.tr tm2Support

/-- Finite support of the final TM0 translation. -/
noncomputable def ambientSupport : Finset AmbientState :=
  Turing.TM1to0.trStmts tm1Program tm1Support

/-- The fixed universal TM2 program is supported by `tm2Support`. -/
theorem tm2_supports :
    Turing.TM2.Supports Turing.PartrecToTM2.tr tm2Support := by
  exact Turing.PartrecToTM2.tr_supports UniversalSource.universalCode
    Turing.PartrecToTM2.Cont'.halt

/-- The translated TM1 program stays in its finite support. -/
theorem tm1_supports :
    Turing.TM1.Supports tm1Program tm1Support :=
  Turing.TM2to1.tr_supports Turing.PartrecToTM2.tr tm2_supports

/-- The translated TM0 program stays in its finite support. -/
theorem ambient_supports :
    Turing.TM0.Supports ambientMachine (ambientSupport : Set AmbientState) :=
  Turing.TM1to0.tr_supports tm1Program tm1_supports

/-- Control states of the actual finite source table. -/
abbrev State := { state : AmbientState // state ∈ ambientSupport }

noncomputable instance stateDecidableEq : DecidableEq State :=
  Classical.decEq State

noncomputable instance symbolDecidableEq : DecidableEq Symbol :=
  Classical.decEq Symbol

noncomputable instance statePrimcodable : Primcodable State :=
  Primcodable.ofEquiv (Fin (Fintype.card State)) (Fintype.equivFin State)

noncomputable instance symbolPrimcodable : Primcodable Symbol :=
  Primcodable.ofEquiv (Fin (Fintype.card Symbol)) (Fintype.equivFin Symbol)

/-- Translate mathlib's two primitive TM0 commands into the project's
write-then-move action data. -/
def action (scanned : Symbol) : Turing.TM0.Stmt Symbol → Symbol × Tape.Move
  | .move .left => (scanned, .left)
  | .move .right => (scanned, .right)
  | .write written => (written, .stay)

/-- Restrict one TM0 table entry to the proved finite state support. -/
noncomputable def delta : Table.Delta State Symbol := fun state scanned =>
  match h : ambientMachine state.1 scanned with
  | none => none
  | some (target, statement) =>
      some
        (⟨target, ambient_supports.2 h state.2⟩,
          (action scanned statement).1,
          (action scanned statement).2)

/-- The closed conventional table obtained by enumerating the fixed finite
state and alphabet types. -/
noncomputable def machine : FiniteMachine State Symbol :=
  Table.compile delta Finset.univ.toList Finset.univ.toList

/-- Forget the finite-support certificate and return to the mathlib TM0
configuration space. -/
def eraseConfig (config : Config State Symbol) : Turing.TM0.Cfg Symbol AmbientState :=
  ⟨config.state.1, TapeBridge.tapeToMathlib config.tape⟩

/-- Every compiled table step is exactly one fixed TM0 step after erasing the
support certificate and canonical tape representation. -/
theorem step_erases (config : Config State Symbol) :
    Option.map eraseConfig (machine.step config) =
      Turing.TM0.step ambientMachine (eraseConfig config) := by
  sorry

end Lecerf.Machine.Compiler.FiniteSource
