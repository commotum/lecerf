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
  rw [machine, Table.step_compile_eq delta Finset.univ.toList Finset.univ.toList
    config (by simp) (by simp)]
  unfold delta
  split
  next h =>
    simp [Turing.TM0.step, eraseConfig, h]
  next target statement h =>
    cases statement with
    | move direction =>
        cases direction <;>
          simp [Turing.TM0.step, eraseConfig, action, Tape.act, h]
    | write written =>
        simp [Turing.TM0.step, eraseConfig, action, Tape.act, h]

/-- Erasing the finite-support certificate and changing tape representation
loses no configuration information. -/
theorem eraseConfig_injective : Function.Injective eraseConfig := by
  intro first second equal
  rcases first with ⟨firstState, firstTape⟩
  rcases second with ⟨secondState, secondTape⟩
  have stateEqual : firstState = secondState :=
    Subtype.ext (congrArg Turing.TM0.Cfg.q equal)
  have tapeEqual : firstTape = secondTape :=
    TapeBridge.tapeEquiv.symm.injective
      (congrArg Turing.TM0.Cfg.Tape equal)
  cases stateEqual
  cases tapeEqual
  rfl

/-- Exact one-step correspondence packages as mathlib's refinement relation. -/
theorem machine_respects_ambient :
    StateTransition.Respects machine.step
      (Turing.TM0.step ambientMachine)
      (fun source target => eraseConfig source = target) := by
  rw [StateTransition.fun_respects]
  intro config
  cases localStep : machine.step config with
  | none =>
      have exactStep := step_erases config
      rw [localStep] at exactStep
      exact exactStep.symm
  | some next =>
      have exactStep := step_erases config
      rw [localStep] at exactStep
      exact Relation.TransGen.single exactStep.symm

/-- The finite source table is structurally deterministic. -/
theorem machine_tableDeterministic : machine.TableDeterministic := by
  exact Table.compile_tableDeterministic delta _ _

/-- Tape input supplied to the fixed TM1/TM0 translation. -/
def translatedInput (input : List Nat) : List Symbol :=
  Turing.TM2to1.trInit Turing.PartrecToTM2.K'.main
    (Turing.PartrecToTM2.trList input)

/-- The partial-recursive source configuration is exactly mathlib's generic
TM2 initial configuration under the fixed entry-label instance. -/
theorem source_init_eq_tm2_init (input : List Nat) :
    Turing.PartrecToTM2.init UniversalSource.universalCode input =
      (Turing.TM2.init Turing.PartrecToTM2.K'.main
        (Turing.PartrecToTM2.trList input) :
        Turing.TM2.Cfg
          (fun _ : Turing.PartrecToTM2.K' => Turing.PartrecToTM2.Γ')
          Turing.PartrecToTM2.Λ' (Option Turing.PartrecToTM2.Γ')) := by
  simp only [Turing.PartrecToTM2.init, Turing.TM2.init]
  congr
  funext index
  cases index <;> rfl

/-- The fixed TM1 simulation halts exactly when the selected source program
halts on the supplied list of naturals. -/
theorem tm1_eval_dom_iff_source (input : List Nat) :
    (Turing.TM1.eval tm1Program (translatedInput input)).Dom ↔
      (StateTransition.eval
        (Turing.TM2.step Turing.PartrecToTM2.tr)
        (Turing.PartrecToTM2.init UniversalSource.universalCode input)).Dom := by
  calc
    _ ↔ (Turing.TM2.eval Turing.PartrecToTM2.tr
          Turing.PartrecToTM2.K'.main
          (Turing.PartrecToTM2.trList input)).Dom :=
      Turing.TM2to1.tr_eval_dom Turing.PartrecToTM2.tr
        Turing.PartrecToTM2.K'.main (Turing.PartrecToTM2.trList input)
    _ ↔ (StateTransition.eval
          (Turing.TM2.step Turing.PartrecToTM2.tr)
          (Turing.TM2.init Turing.PartrecToTM2.K'.main
            (Turing.PartrecToTM2.trList input))).Dom := by
      simp [Turing.TM2.eval]
    _ ↔ _ := by rw [source_init_eq_tm2_init]

/-- The fixed supported TM0 program preserves and reflects halting of the
selected source program. -/
theorem ambient_eval_dom_iff_source (input : List Nat) :
    (Turing.TM0.eval ambientMachine (translatedInput input)).Dom ↔
      (StateTransition.eval
        (Turing.TM2.step Turing.PartrecToTM2.tr)
        (Turing.PartrecToTM2.init UniversalSource.universalCode input)).Dom := by
  change (Turing.TM0.eval (Turing.TM1to0.tr tm1Program)
    (translatedInput input)).Dom ↔ _
  rw [Turing.TM1to0.tr_eval]
  exact tm1_eval_dom_iff_source input

/-- The fixed TM0 program therefore halts exactly when an encoded
`Nat.Partrec.Code` halts. -/
theorem ambient_halts_iff_eval_dom (code : Nat.Partrec.Code) (input : Nat) :
    (Turing.TM0.eval ambientMachine
      (translatedInput (UniversalSource.encodedInput code input).1)).Dom ↔
        (Nat.Partrec.Code.eval code input).Dom := by
  rw [ambient_eval_dom_iff_source]
  exact UniversalSource.tm2_halts_iff_eval_dom code input

/-- The initial supported control state of the fixed conventional table. -/
noncomputable def initialState : State :=
  ⟨(Turing.TM0.init ([] : List Symbol)).q, ambient_supports.1⟩

/-- Canonical-table start configuration for a supplied natural-number list. -/
noncomputable def initial (input : List Nat) : Config State Symbol :=
  ⟨initialState,
    TapeBridge.tapeToLocal
      (Turing.Tape.mk₁ (translatedInput input))⟩

@[simp]
theorem erase_initial (input : List Nat) :
    eraseConfig (initial input) =
      (Turing.TM0.init (translatedInput input) :
        Turing.TM0.Cfg Symbol AmbientState) := by
  simp [initial, initialState, eraseConfig, Turing.TM0.init]

/-- Local conventional-table evaluation and the supported TM0 program have
the same definedness from translated inputs. -/
theorem local_eval_dom_iff_ambient (input : List Nat) :
    (StateTransition.eval machine.step (initial input)).Dom ↔
      (Turing.TM0.eval ambientMachine (translatedInput input)).Dom := by
  have refinement := StateTransition.tr_eval_dom machine_respects_ambient
    (erase_initial input)
  rw [Turing.TM0.eval]
  simpa using refinement.symm

/-- The actual fixed conventional finite table halts exactly when the source
partial-recursive code halts. -/
theorem halts_iff_eval_dom (code : Nat.Partrec.Code) (input : Nat) :
    (StateTransition.eval machine.step
      (initial (UniversalSource.encodedInput code input).1)).Dom ↔
        (Nat.Partrec.Code.eval code input).Dom := by
  rw [local_eval_dom_iff_ambient]
  exact ambient_halts_iff_eval_dom code input

end Lecerf.Machine.Compiler.FiniteSource
