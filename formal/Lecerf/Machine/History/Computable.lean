import Lecerf.Machine.History.Correctness
import Lecerf.Machine.Effectivity
import Lecerf.Machine.SourceBridge

/-!
# Effectivity of reversible history simulation

The history construction is uniform primitive recursive whenever the source
description has a jointly primitive-recursive interpreter.  The checked
universal `Nat.Partrec.Code.evaln` search source is instantiated explicitly.
-/

namespace Lecerf.Machine.History

open Lecerf.Transition

universe u v

namespace Config

/-- Decoding the structured history configuration to its product
representation is primitive recursive. -/
theorem decode_primrec {σ : Type u} [Primcodable σ] :
    Primrec (decode : Config σ → σ × List σ) :=
  Primrec.of_equiv

theorem current_primrec {σ : Type u} [Primcodable σ] :
    Primrec (fun config : Config σ => config.current) :=
  Primrec.fst.comp decode_primrec

theorem history_primrec {σ : Type u} [Primcodable σ] :
    Primrec (fun config : Config σ => config.history) :=
  Primrec.snd.comp decode_primrec

/-- Constructing a history configuration from its two explicit fields is
primitive recursive. -/
theorem encode_primrec {σ : Type u} [Primcodable σ] :
    Primrec₂ (encode : σ → List σ → Config σ) :=
  (show Primrec (equivRep.symm : σ × List σ → Config σ) from
    Primrec.of_equiv_symm).comp₂ Primrec₂.pair

theorem initial_primrec {σ : Type u} [Primcodable σ] :
    Primrec (initial : σ → Config σ) :=
  encode_primrec.comp Primrec.id (Primrec.const [])

end Config

/-- Execute the history simulator for a source description and a jointly
interpreted source step. -/
def forwardInterpreter {D : Type u} {σ : Type v}
    (source : D × σ → Option σ) : D × Config σ → Option (Config σ) :=
  fun data => forward (fun current => source (data.1, current)) data.2

/-- Execute the checked inverse simulator for a source description. -/
def backwardInterpreter {D : Type u} {σ : Type v} [DecidableEq σ]
    (source : D × σ → Option σ) : D × Config σ → Option (Config σ) :=
  fun data => backward (fun previous => source (data.1, previous)) data.2

/-- A uniform effective source interpreter yields a uniform effective forward
history interpreter. -/
theorem forwardInterpreter_primrec {D : Type u} {σ : Type v}
    [Primcodable D] [Primcodable σ]
    (source : D × σ → Option σ) (sourcePrimrec : Primrec source) :
    Primrec (forwardInterpreter source) := by
  let current : Primrec fun data : D × Config σ => data.2.current :=
    Config.current_primrec.comp Primrec.snd
  let history : Primrec fun data : D × Config σ => data.2.history :=
    Config.history_primrec.comp Primrec.snd
  let sourceAt : Primrec fun data : D × Config σ =>
      source (data.1, data.2.current) :=
    sourcePrimrec.comp (Primrec.fst.pair current)
  let pushed : Primrec fun data : D × Config σ =>
      data.2.current :: data.2.history :=
    Primrec.list_cons.comp current history
  let makeTarget : Primrec₂ fun (data : D × Config σ) (target : σ) =>
      Config.encode target (data.2.current :: data.2.history) :=
    Config.encode_primrec.comp₂ Primrec₂.right (pushed.comp₂ Primrec₂.left)
  exact (Primrec.option_map sourceAt makeTarget).of_eq fun data => by
    rcases data with ⟨description, config⟩
    rcases config with ⟨current, history⟩
    rfl

/-- The checked inverse history interpreter is uniformly primitive recursive
under the same source-interpreter hypothesis. -/
theorem backwardInterpreter_primrec {D : Type u} {σ : Type v}
    [Primcodable D] [Primcodable σ] [DecidableEq σ]
    (source : D × σ → Option σ) (sourcePrimrec : Primrec source) :
    Primrec (backwardInterpreter source) := by
  let current : Primrec fun data : D × Config σ => data.2.current :=
    Config.current_primrec.comp Primrec.snd
  let history : Primrec fun data : D × Config σ => data.2.history :=
    Config.history_primrec.comp Primrec.snd
  let nilCase : Primrec fun _ : D × Config σ => (none : Option (Config σ)) :=
    Primrec.const none
  let consCase : Primrec₂ fun (data : D × Config σ) (entry : σ × List σ) =>
      if source (data.1, entry.1) = some data.2.current then
        some (Config.encode entry.1 entry.2)
      else none := by
    let sourcePrevious : Primrec₂
        fun (data : D × Config σ) (entry : σ × List σ) =>
          source (data.1, entry.1) :=
      sourcePrimrec.comp₂ (Primrec₂.pair.comp₂
        (Primrec.fst.comp₂ Primrec₂.left)
        (Primrec.fst.comp₂ Primrec₂.right))
    let currentSome : Primrec₂
        fun (data : D × Config σ) (_ : σ × List σ) =>
          some data.2.current :=
      Primrec.option_some.comp₂ (current.comp₂ Primrec₂.left)
    let condition : PrimrecRel
        fun (data : D × Config σ) (entry : σ × List σ) =>
          source (data.1, entry.1) = some data.2.current :=
      Primrec.eq.comp₂ sourcePrevious currentSome
    let success : Primrec₂
        fun (_ : D × Config σ) (entry : σ × List σ) =>
          some (Config.encode entry.1 entry.2) :=
      Primrec.option_some.comp₂ (Config.encode_primrec.comp₂
        (Primrec.fst.comp₂ Primrec₂.right)
        (Primrec.snd.comp₂ Primrec₂.right))
    exact Primrec.ite condition success (Primrec.const none).to₂
  exact (Primrec.list_casesOn history nilCase consCase).of_eq fun data => by
    rcases data with ⟨description, config⟩
    rcases config with ⟨current, history⟩
    cases history <;> rfl

theorem forwardInterpreter_computable {D : Type u} {σ : Type v}
    [Primcodable D] [Primcodable σ]
    (source : D × σ → Option σ) (sourcePrimrec : Primrec source) :
    Computable (forwardInterpreter source) :=
  (forwardInterpreter_primrec source sourcePrimrec).to_comp

theorem backwardInterpreter_computable {D : Type u} {σ : Type v}
    [Primcodable D] [Primcodable σ] [DecidableEq σ]
    (source : D × σ → Option σ) (sourcePrimrec : Primrec source) :
    Computable (backwardInterpreter source) :=
  (backwardInterpreter_primrec source sourcePrimrec).to_comp

/-- The forward history step preserves primitive recursiveness for a fixed
source transition. -/
theorem forward_primrec {σ : Type u} [Primcodable σ]
    {next : Step σ} (nextPrimrec : Primrec next) : Primrec (forward next) := by
  let interpreted : Primrec (forwardInterpreter fun data : Unit × σ => next data.2) :=
    forwardInterpreter_primrec _ (nextPrimrec.comp Primrec.snd)
  exact (interpreted.comp ((Primrec.const ()).pair Primrec.id)).of_eq
    fun config => rfl

/-- The checked inverse history step preserves primitive recursiveness for a
fixed source transition. -/
theorem backward_primrec {σ : Type u} [Primcodable σ] [DecidableEq σ]
    {next : Step σ} (nextPrimrec : Primrec next) : Primrec (backward next) := by
  let interpreted : Primrec (backwardInterpreter fun data : Unit × σ => next data.2) :=
    backwardInterpreter_primrec _ (nextPrimrec.comp Primrec.snd)
  exact (interpreted.comp ((Primrec.const ()).pair Primrec.id)).of_eq
    fun config => rfl

theorem forward_computable {σ : Type u} [Primcodable σ]
    {next : Step σ} (nextPrimrec : Primrec next) : Computable (forward next) :=
  (forward_primrec nextPrimrec).to_comp

theorem backward_computable {σ : Type u} [Primcodable σ] [DecidableEq σ]
    {next : Step σ} (nextPrimrec : Primrec next) : Computable (backward next) :=
  (backward_primrec nextPrimrec).to_comp

/-- Effective source-start maps remain effective after adding an empty
history. -/
theorem initial_comp_primrec {D : Type u} {σ : Type v}
    [Primcodable D] [Primcodable σ] {start : D → σ}
    (startPrimrec : Primrec start) :
    Primrec fun description => Config.initial (start description) :=
  Config.initial_primrec.comp startPrimrec

/-- Retaining the finite description alongside its encoded start state is
also primitive recursive. -/
theorem described_initial_primrec {D : Type u} {σ : Type v}
    [Primcodable D] [Primcodable σ] {start : D → σ}
    (startPrimrec : Primrec start) :
    Primrec fun description => (description, Config.initial (start description)) :=
  Primrec.id.pair (initial_comp_primrec startPrimrec)

/-- Forward history execution is primitive recursive jointly in an existing
finite machine description and its abstract history configuration.  This is
an effective interpreter theorem, not a claim that the result is already a
generated conventional `FiniteMachine`. -/
theorem finiteForward_uniform_primrec
    {Q : Type u} {Γ : Type v} [Primcodable Q] [DecidableEq Q]
    [Inhabited Γ] [Primcodable Γ] [DecidableEq Γ] :
    Primrec fun data : FiniteMachine Q Γ ×
        Config (Lecerf.Machine.Config Q Γ) =>
      forward data.1.step data.2 := by
  exact (forwardInterpreter_primrec
    (fun data : FiniteMachine Q Γ × Lecerf.Machine.Config Q Γ =>
      data.1.step data.2)
    FiniteMachine.step_uniform_primrec).of_eq fun _ => rfl

/-- Checked inverse history execution is primitive recursive jointly in the
same finite machine description. -/
theorem finiteBackward_uniform_primrec
    {Q : Type u} {Γ : Type v} [Primcodable Q] [DecidableEq Q]
    [Inhabited Γ] [Primcodable Γ] [DecidableEq Γ] :
    Primrec fun data : FiniteMachine Q Γ ×
        Config (Lecerf.Machine.Config Q Γ) =>
      backward data.1.step data.2 := by
  exact (backwardInterpreter_primrec
    (fun data : FiniteMachine Q Γ × Lecerf.Machine.Config Q Γ =>
      data.1.step data.2)
    FiniteMachine.step_uniform_primrec).of_eq fun _ => rfl

/-- Package a finite machine description with an empty-history source
configuration, uniformly and constructively. -/
theorem finiteDescribedInitial_primrec
    {Q : Type u} {Γ : Type v} [Primcodable Q] [DecidableEq Q]
    [Inhabited Γ] [Primcodable Γ] [DecidableEq Γ] :
    Primrec fun data : FiniteMachine Q Γ × Lecerf.Machine.Config Q Γ =>
      (data.1, Config.initial data.2) :=
  Primrec.fst.pair (Config.initial_primrec.comp Primrec.snd)

/-- Effective initial history state for the fixed universal evaluator search. -/
def universalHistoryStart (code : Nat.Partrec.Code) (input : Nat) :
    Config Source.EvalSearchConfig :=
  Config.initial (Source.evalSearchStart code input)

theorem universalHistoryStart_joint_primrec :
    Primrec fun data : Nat.Partrec.Code × Nat =>
      universalHistoryStart data.1 data.2 :=
  (initial_comp_primrec Source.evalSearchStart_joint_primrec).of_eq fun _ => rfl

theorem universalForward_primrec :
    Primrec (forward Source.universalEvalSearchStep) :=
  forward_primrec Source.universalEvalSearchStep_primrec

theorem universalBackward_primrec :
    Primrec (backward Source.universalEvalSearchStep) :=
  backward_primrec Source.universalEvalSearchStep_primrec

/-- The effective reversible history simulator halts exactly when the source
partial-recursive program is defined. -/
theorem universalHistory_halts_iff_eval_dom
    (code : Nat.Partrec.Code) (input : Nat) :
    HaltsFrom (forward Source.universalEvalSearchStep)
        (universalHistoryStart code input) ↔
      (Nat.Partrec.Code.eval code input).Dom :=
  (haltsFrom_forward_iff Source.universalEvalSearchStep
    (Source.evalSearchStart code input)).trans
      (Source.universalEvalSearchStep_halts_iff_eval_dom code input)

end Lecerf.Machine.History
