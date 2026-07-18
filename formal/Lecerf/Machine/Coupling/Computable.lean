import Lecerf.Machine.Coupling.Correctness
import Lecerf.Machine.Effectivity
import Lecerf.Machine.SourceBridge

/-!
# Effectivity of forward--reverse coupling

The generic coupling interpreters are primitive recursive jointly in a finite
description whenever interpreters for both directions of the underlying
partial equivalence are primitive recursive.  Specializations use the checked
history inverse, existing finite source-machine descriptions, and the fixed
universal evaluator search.

These are interpreter theorems.  They do not construct a conventional finite
tape-machine rule table for the unbounded full-history state space.
-/

namespace Lecerf.Machine.Coupling

open Lecerf.Transition

universe u v

namespace Config

theorem decode_primrec {σ : Type u} [Primcodable σ] :
    Primrec (decode : Config σ → Direction × σ) :=
  Primrec.of_equiv

theorem direction_primrec {σ : Type u} [Primcodable σ] :
    Primrec (fun config : Config σ => config.direction) :=
  Primrec.fst.comp decode_primrec

theorem state_primrec {σ : Type u} [Primcodable σ] :
    Primrec (fun config : Config σ => config.state) :=
  Primrec.snd.comp decode_primrec

theorem encode_primrec {σ : Type u} [Primcodable σ] :
    Primrec₂ (encode : Direction → σ → Config σ) :=
  (show Primrec (equivRep.symm : Direction × σ → Config σ) from
    Primrec.of_equiv_symm).comp₂ Primrec₂.pair

theorem forward_primrec {σ : Type u} [Primcodable σ] :
    Primrec (forward : σ → Config σ) :=
  encode_primrec.comp (Primrec.const Direction.forward) Primrec.id

theorem reverse_primrec {σ : Type u} [Primcodable σ] :
    Primrec (reverse : σ → Config σ) :=
  encode_primrec.comp (Primrec.const Direction.reverse) Primrec.id

end Config

/-- Joint interpreter for the open coupling's forward transition. -/
def turnaroundNextInterpreter {D : Type u} {σ : Type v}
    (forwardSource reverseSource : D × σ → Option σ) :
    D × Config σ → Option (Config σ) :=
  fun data =>
    match data.2.direction with
    | .forward =>
        match forwardSource (data.1, data.2.state) with
        | some target => some (Config.forward target)
        | none => some (Config.reverse data.2.state)
    | .reverse =>
        (reverseSource (data.1, data.2.state)).map Config.reverse

/-- Joint interpreter for the open coupling's inverse transition. -/
def turnaroundPrevInterpreter {D : Type u} {σ : Type v}
    (forwardSource reverseSource : D × σ → Option σ) :
    D × Config σ → Option (Config σ) :=
  fun data =>
    match data.2.direction with
    | .forward =>
        (reverseSource (data.1, data.2.state)).map Config.forward
    | .reverse =>
        match forwardSource (data.1, data.2.state) with
        | some target => some (Config.reverse target)
        | none => some (Config.forward data.2.state)

/-- Joint interpreter for the closed coupling's forward transition. -/
def returnNextInterpreter {D : Type u} {σ : Type v}
    (forwardSource reverseSource : D × σ → Option σ) :
    D × Config σ → Option (Config σ) :=
  fun data =>
    match data.2.direction with
    | .forward =>
        match forwardSource (data.1, data.2.state) with
        | some target => some (Config.forward target)
        | none => some (Config.reverse data.2.state)
    | .reverse =>
        match reverseSource (data.1, data.2.state) with
        | some previous => some (Config.reverse previous)
        | none => some (Config.forward data.2.state)

/-- Joint interpreter for the closed coupling's inverse transition. -/
def returnPrevInterpreter {D : Type u} {σ : Type v}
    (forwardSource reverseSource : D × σ → Option σ) :
    D × Config σ → Option (Config σ) :=
  fun data =>
    match data.2.direction with
    | .forward =>
        match reverseSource (data.1, data.2.state) with
        | some previous => some (Config.forward previous)
        | none => some (Config.reverse data.2.state)
    | .reverse =>
        match forwardSource (data.1, data.2.state) with
        | some target => some (Config.reverse target)
        | none => some (Config.forward data.2.state)

theorem turnaroundNextInterpreter_primrec {D : Type u} {σ : Type v}
    [Primcodable D] [Primcodable σ]
    (forwardSource reverseSource : D × σ → Option σ)
    (forwardPrimrec : Primrec forwardSource)
    (reversePrimrec : Primrec reverseSource) :
    Primrec (turnaroundNextInterpreter forwardSource reverseSource) := by
  let direction : Primrec fun data : D × Config σ => data.2.direction :=
    Config.direction_primrec.comp Primrec.snd
  let state : Primrec fun data : D × Config σ => data.2.state :=
    Config.state_primrec.comp Primrec.snd
  let input : Primrec fun data : D × Config σ => (data.1, data.2.state) :=
    Primrec.fst.pair state
  let forwardAt := forwardPrimrec.comp input
  let reverseAt := reversePrimrec.comp input
  let makeForward : Primrec₂ fun (_ : D × Config σ) (target : σ) =>
      some (Config.forward target) :=
    Primrec.option_some.comp₂ (Config.forward_primrec.comp₂ Primrec₂.right)
  let makeReverse : Primrec₂ fun (_ : D × Config σ) (target : σ) =>
      Config.reverse target :=
    Config.reverse_primrec.comp₂ Primrec₂.right
  let currentReverse : Primrec fun data : D × Config σ =>
      some (Config.reverse data.2.state) :=
    Primrec.option_some.comp (Config.reverse_primrec.comp state)
  let forwardCase := Primrec.option_casesOn forwardAt currentReverse makeForward
  let reverseCase := Primrec.option_map reverseAt makeReverse
  let isForward : PrimrecPred fun data : D × Config σ =>
      data.2.direction = Direction.forward :=
    Primrec.eq.comp direction (Primrec.const Direction.forward)
  exact (Primrec.ite isForward forwardCase reverseCase).of_eq fun data => by
    rcases data with ⟨description, config⟩
    rcases config with ⟨direction, state⟩
    cases direction with
    | forward =>
        cases h : forwardSource (description, state) <;>
          simp [turnaroundNextInterpreter, h]
    | reverse =>
        cases h : reverseSource (description, state) <;>
          simp [turnaroundNextInterpreter, h]

theorem turnaroundPrevInterpreter_primrec {D : Type u} {σ : Type v}
    [Primcodable D] [Primcodable σ]
    (forwardSource reverseSource : D × σ → Option σ)
    (forwardPrimrec : Primrec forwardSource)
    (reversePrimrec : Primrec reverseSource) :
    Primrec (turnaroundPrevInterpreter forwardSource reverseSource) := by
  let direction : Primrec fun data : D × Config σ => data.2.direction :=
    Config.direction_primrec.comp Primrec.snd
  let state : Primrec fun data : D × Config σ => data.2.state :=
    Config.state_primrec.comp Primrec.snd
  let input : Primrec fun data : D × Config σ => (data.1, data.2.state) :=
    Primrec.fst.pair state
  let forwardAt := forwardPrimrec.comp input
  let reverseAt := reversePrimrec.comp input
  let makeForward : Primrec₂ fun (_ : D × Config σ) (target : σ) =>
      Config.forward target :=
    Config.forward_primrec.comp₂ Primrec₂.right
  let makeReverse : Primrec₂ fun (_ : D × Config σ) (target : σ) =>
      some (Config.reverse target) :=
    Primrec.option_some.comp₂ (Config.reverse_primrec.comp₂ Primrec₂.right)
  let currentForward : Primrec fun data : D × Config σ =>
      some (Config.forward data.2.state) :=
    Primrec.option_some.comp (Config.forward_primrec.comp state)
  let forwardCase := Primrec.option_map reverseAt makeForward
  let reverseCase := Primrec.option_casesOn forwardAt currentForward makeReverse
  let isForward : PrimrecPred fun data : D × Config σ =>
      data.2.direction = Direction.forward :=
    Primrec.eq.comp direction (Primrec.const Direction.forward)
  exact (Primrec.ite isForward forwardCase reverseCase).of_eq fun data => by
    rcases data with ⟨description, config⟩
    rcases config with ⟨direction, state⟩
    cases direction with
    | forward =>
        cases h : reverseSource (description, state) <;>
          simp [turnaroundPrevInterpreter, h]
    | reverse =>
        cases h : forwardSource (description, state) <;>
          simp [turnaroundPrevInterpreter, h]

theorem returnNextInterpreter_primrec {D : Type u} {σ : Type v}
    [Primcodable D] [Primcodable σ]
    (forwardSource reverseSource : D × σ → Option σ)
    (forwardPrimrec : Primrec forwardSource)
    (reversePrimrec : Primrec reverseSource) :
    Primrec (returnNextInterpreter forwardSource reverseSource) := by
  let direction : Primrec fun data : D × Config σ => data.2.direction :=
    Config.direction_primrec.comp Primrec.snd
  let state : Primrec fun data : D × Config σ => data.2.state :=
    Config.state_primrec.comp Primrec.snd
  let input : Primrec fun data : D × Config σ => (data.1, data.2.state) :=
    Primrec.fst.pair state
  let forwardAt := forwardPrimrec.comp input
  let reverseAt := reversePrimrec.comp input
  let makeForward : Primrec₂ fun (_ : D × Config σ) (target : σ) =>
      some (Config.forward target) :=
    Primrec.option_some.comp₂ (Config.forward_primrec.comp₂ Primrec₂.right)
  let makeReverse : Primrec₂ fun (_ : D × Config σ) (target : σ) =>
      some (Config.reverse target) :=
    Primrec.option_some.comp₂ (Config.reverse_primrec.comp₂ Primrec₂.right)
  let currentForward : Primrec fun data : D × Config σ =>
      some (Config.forward data.2.state) :=
    Primrec.option_some.comp (Config.forward_primrec.comp state)
  let currentReverse : Primrec fun data : D × Config σ =>
      some (Config.reverse data.2.state) :=
    Primrec.option_some.comp (Config.reverse_primrec.comp state)
  let forwardCase := Primrec.option_casesOn forwardAt currentReverse makeForward
  let reverseCase := Primrec.option_casesOn reverseAt currentForward makeReverse
  let isForward : PrimrecPred fun data : D × Config σ =>
      data.2.direction = Direction.forward :=
    Primrec.eq.comp direction (Primrec.const Direction.forward)
  exact (Primrec.ite isForward forwardCase reverseCase).of_eq fun data => by
    rcases data with ⟨description, config⟩
    rcases config with ⟨direction, state⟩
    cases direction with
    | forward =>
        cases h : forwardSource (description, state) <;>
          simp [returnNextInterpreter, h]
    | reverse =>
        cases h : reverseSource (description, state) <;>
          simp [returnNextInterpreter, h]

theorem returnPrevInterpreter_primrec {D : Type u} {σ : Type v}
    [Primcodable D] [Primcodable σ]
    (forwardSource reverseSource : D × σ → Option σ)
    (forwardPrimrec : Primrec forwardSource)
    (reversePrimrec : Primrec reverseSource) :
    Primrec (returnPrevInterpreter forwardSource reverseSource) := by
  let direction : Primrec fun data : D × Config σ => data.2.direction :=
    Config.direction_primrec.comp Primrec.snd
  let state : Primrec fun data : D × Config σ => data.2.state :=
    Config.state_primrec.comp Primrec.snd
  let input : Primrec fun data : D × Config σ => (data.1, data.2.state) :=
    Primrec.fst.pair state
  let forwardAt := forwardPrimrec.comp input
  let reverseAt := reversePrimrec.comp input
  let makeForward : Primrec₂ fun (_ : D × Config σ) (target : σ) =>
      some (Config.forward target) :=
    Primrec.option_some.comp₂ (Config.forward_primrec.comp₂ Primrec₂.right)
  let makeReverse : Primrec₂ fun (_ : D × Config σ) (target : σ) =>
      some (Config.reverse target) :=
    Primrec.option_some.comp₂ (Config.reverse_primrec.comp₂ Primrec₂.right)
  let currentForward : Primrec fun data : D × Config σ =>
      some (Config.forward data.2.state) :=
    Primrec.option_some.comp (Config.forward_primrec.comp state)
  let currentReverse : Primrec fun data : D × Config σ =>
      some (Config.reverse data.2.state) :=
    Primrec.option_some.comp (Config.reverse_primrec.comp state)
  let forwardCase := Primrec.option_casesOn reverseAt currentReverse makeForward
  let reverseCase := Primrec.option_casesOn forwardAt currentForward makeReverse
  let isForward : PrimrecPred fun data : D × Config σ =>
      data.2.direction = Direction.forward :=
    Primrec.eq.comp direction (Primrec.const Direction.forward)
  exact (Primrec.ite isForward forwardCase reverseCase).of_eq fun data => by
    rcases data with ⟨description, config⟩
    rcases config with ⟨direction, state⟩
    cases direction with
    | forward =>
        cases h : reverseSource (description, state) <;>
          simp [returnPrevInterpreter, h]
    | reverse =>
        cases h : forwardSource (description, state) <;>
          simp [returnPrevInterpreter, h]

theorem turnaroundNextInterpreter_computable {D : Type u} {σ : Type v}
    [Primcodable D] [Primcodable σ]
    (forwardSource reverseSource : D × σ → Option σ)
    (forwardPrimrec : Primrec forwardSource)
    (reversePrimrec : Primrec reverseSource) :
    Computable (turnaroundNextInterpreter forwardSource reverseSource) :=
  (turnaroundNextInterpreter_primrec forwardSource reverseSource
    forwardPrimrec reversePrimrec).to_comp

theorem returnNextInterpreter_computable {D : Type u} {σ : Type v}
    [Primcodable D] [Primcodable σ]
    (forwardSource reverseSource : D × σ → Option σ)
    (forwardPrimrec : Primrec forwardSource)
    (reversePrimrec : Primrec reverseSource) :
    Computable (returnNextInterpreter forwardSource reverseSource) :=
  (returnNextInterpreter_primrec forwardSource reverseSource
    forwardPrimrec reversePrimrec).to_comp

namespace History

variable {σ : Type v}

theorem start_primrec [Primcodable σ] :
    Primrec (start : σ → Config (Lecerf.Machine.History.Config σ)) :=
  Config.forward_primrec.comp Lecerf.Machine.History.Config.initial_primrec

theorem target_primrec [Primcodable σ] :
    Primrec (target : σ → Config (Lecerf.Machine.History.Config σ)) :=
  Config.reverse_primrec.comp Lecerf.Machine.History.Config.initial_primrec

theorem startTarget_primrec [Primcodable σ] :
    Primrec fun state : σ => (start state, target state) :=
  start_primrec.pair target_primrec

theorem describedStart_primrec {D : Type u} [Primcodable D] [Primcodable σ]
    {sourceStart : D → σ} (sourceStartPrimrec : Primrec sourceStart) :
    Primrec fun description => (description, start (sourceStart description)) :=
  Primrec.id.pair (start_primrec.comp sourceStartPrimrec)

theorem describedTarget_primrec {D : Type u} [Primcodable D] [Primcodable σ]
    {sourceStart : D → σ} (sourceStartPrimrec : Primrec sourceStart) :
    Primrec fun description => (description, target (sourceStart description)) :=
  Primrec.id.pair (target_primrec.comp sourceStartPrimrec)

def turnaroundNextInterpreter {D : Type u} [DecidableEq σ]
    (source : D × σ → Option σ) :
    D × Config (Lecerf.Machine.History.Config σ) →
      Option (Config (Lecerf.Machine.History.Config σ)) :=
  fun data => (turnaroundStep (fun state => source (data.1, state))).next data.2

def turnaroundPrevInterpreter {D : Type u} [DecidableEq σ]
    (source : D × σ → Option σ) :
    D × Config (Lecerf.Machine.History.Config σ) →
      Option (Config (Lecerf.Machine.History.Config σ)) :=
  fun data => (turnaroundStep (fun state => source (data.1, state))).prev data.2

def returnNextInterpreter {D : Type u} [DecidableEq σ]
    (source : D × σ → Option σ) :
    D × Config (Lecerf.Machine.History.Config σ) →
      Option (Config (Lecerf.Machine.History.Config σ)) :=
  fun data => (returnStep (fun state => source (data.1, state))).next data.2

def returnPrevInterpreter {D : Type u} [DecidableEq σ]
    (source : D × σ → Option σ) :
    D × Config (Lecerf.Machine.History.Config σ) →
      Option (Config (Lecerf.Machine.History.Config σ)) :=
  fun data => (returnStep (fun state => source (data.1, state))).prev data.2

theorem turnaroundNextInterpreter_primrec {D : Type u}
    [Primcodable D] [Primcodable σ] [DecidableEq σ]
    (source : D × σ → Option σ) (sourcePrimrec : Primrec source) :
    Primrec (History.turnaroundNextInterpreter source) := by
  have generic := Coupling.turnaroundNextInterpreter_primrec
    (Lecerf.Machine.History.forwardInterpreter source)
    (Lecerf.Machine.History.backwardInterpreter source)
    (Lecerf.Machine.History.forwardInterpreter_primrec source sourcePrimrec)
    (Lecerf.Machine.History.backwardInterpreter_primrec source sourcePrimrec)
  exact generic.of_eq fun data => by
    rcases data with ⟨description, config⟩
    rcases config with ⟨direction, history⟩
    cases direction <;> rfl

theorem turnaroundPrevInterpreter_primrec {D : Type u}
    [Primcodable D] [Primcodable σ] [DecidableEq σ]
    (source : D × σ → Option σ) (sourcePrimrec : Primrec source) :
    Primrec (History.turnaroundPrevInterpreter source) := by
  have generic := Coupling.turnaroundPrevInterpreter_primrec
    (Lecerf.Machine.History.forwardInterpreter source)
    (Lecerf.Machine.History.backwardInterpreter source)
    (Lecerf.Machine.History.forwardInterpreter_primrec source sourcePrimrec)
    (Lecerf.Machine.History.backwardInterpreter_primrec source sourcePrimrec)
  exact generic.of_eq fun data => by
    rcases data with ⟨description, config⟩
    rcases config with ⟨direction, history⟩
    cases direction <;> rfl

theorem returnNextInterpreter_primrec {D : Type u}
    [Primcodable D] [Primcodable σ] [DecidableEq σ]
    (source : D × σ → Option σ) (sourcePrimrec : Primrec source) :
    Primrec (History.returnNextInterpreter source) := by
  have generic := Coupling.returnNextInterpreter_primrec
    (Lecerf.Machine.History.forwardInterpreter source)
    (Lecerf.Machine.History.backwardInterpreter source)
    (Lecerf.Machine.History.forwardInterpreter_primrec source sourcePrimrec)
    (Lecerf.Machine.History.backwardInterpreter_primrec source sourcePrimrec)
  exact generic.of_eq fun data => by
    rcases data with ⟨description, config⟩
    rcases config with ⟨direction, history⟩
    cases direction <;> rfl

theorem returnPrevInterpreter_primrec {D : Type u}
    [Primcodable D] [Primcodable σ] [DecidableEq σ]
    (source : D × σ → Option σ) (sourcePrimrec : Primrec source) :
    Primrec (History.returnPrevInterpreter source) := by
  have generic := Coupling.returnPrevInterpreter_primrec
    (Lecerf.Machine.History.forwardInterpreter source)
    (Lecerf.Machine.History.backwardInterpreter source)
    (Lecerf.Machine.History.forwardInterpreter_primrec source sourcePrimrec)
    (Lecerf.Machine.History.backwardInterpreter_primrec source sourcePrimrec)
  exact generic.of_eq fun data => by
    rcases data with ⟨description, config⟩
    rcases config with ⟨direction, history⟩
    cases direction <;> rfl

theorem turnaroundStep_next_primrec [Primcodable σ] [DecidableEq σ]
    {source : Step σ} (sourcePrimrec : Primrec source) :
    Primrec (turnaroundStep source).next := by
  let interpreted : Primrec
      (History.turnaroundNextInterpreter fun data : Unit × σ => source data.2) :=
    History.turnaroundNextInterpreter_primrec _ (sourcePrimrec.comp Primrec.snd)
  exact (interpreted.comp ((Primrec.const ()).pair Primrec.id)).of_eq fun _ => rfl

theorem turnaroundStep_prev_primrec [Primcodable σ] [DecidableEq σ]
    {source : Step σ} (sourcePrimrec : Primrec source) :
    Primrec (turnaroundStep source).prev := by
  let interpreted : Primrec
      (History.turnaroundPrevInterpreter fun data : Unit × σ => source data.2) :=
    History.turnaroundPrevInterpreter_primrec _ (sourcePrimrec.comp Primrec.snd)
  exact (interpreted.comp ((Primrec.const ()).pair Primrec.id)).of_eq fun _ => rfl

theorem returnStep_next_primrec [Primcodable σ] [DecidableEq σ]
    {source : Step σ} (sourcePrimrec : Primrec source) :
    Primrec (returnStep source).next := by
  let interpreted : Primrec
      (History.returnNextInterpreter fun data : Unit × σ => source data.2) :=
    History.returnNextInterpreter_primrec _ (sourcePrimrec.comp Primrec.snd)
  exact (interpreted.comp ((Primrec.const ()).pair Primrec.id)).of_eq fun _ => rfl

theorem returnStep_prev_primrec [Primcodable σ] [DecidableEq σ]
    {source : Step σ} (sourcePrimrec : Primrec source) :
    Primrec (returnStep source).prev := by
  let interpreted : Primrec
      (History.returnPrevInterpreter fun data : Unit × σ => source data.2) :=
    History.returnPrevInterpreter_primrec _ (sourcePrimrec.comp Primrec.snd)
  exact (interpreted.comp ((Primrec.const ()).pair Primrec.id)).of_eq fun _ => rfl

theorem finiteTurnaroundNext_uniform_primrec
    {Q : Type u} {Γ : Type v} [Primcodable Q] [DecidableEq Q]
    [Inhabited Γ] [Primcodable Γ] [DecidableEq Γ] :
    Primrec fun data : FiniteMachine Q Γ ×
        Config (Lecerf.Machine.History.Config (Lecerf.Machine.Config Q Γ)) =>
      (turnaroundStep data.1.step).next data.2 := by
  exact (History.turnaroundNextInterpreter_primrec
    (fun data : FiniteMachine Q Γ × Lecerf.Machine.Config Q Γ =>
      data.1.step data.2)
    FiniteMachine.step_uniform_primrec).of_eq fun _ => rfl

theorem finiteTurnaroundPrev_uniform_primrec
    {Q : Type u} {Γ : Type v} [Primcodable Q] [DecidableEq Q]
    [Inhabited Γ] [Primcodable Γ] [DecidableEq Γ] :
    Primrec fun data : FiniteMachine Q Γ ×
        Config (Lecerf.Machine.History.Config (Lecerf.Machine.Config Q Γ)) =>
      (turnaroundStep data.1.step).prev data.2 := by
  exact (History.turnaroundPrevInterpreter_primrec
    (fun data : FiniteMachine Q Γ × Lecerf.Machine.Config Q Γ =>
      data.1.step data.2)
    FiniteMachine.step_uniform_primrec).of_eq fun _ => rfl

theorem finiteReturnNext_uniform_primrec
    {Q : Type u} {Γ : Type v} [Primcodable Q] [DecidableEq Q]
    [Inhabited Γ] [Primcodable Γ] [DecidableEq Γ] :
    Primrec fun data : FiniteMachine Q Γ ×
        Config (Lecerf.Machine.History.Config (Lecerf.Machine.Config Q Γ)) =>
      (returnStep data.1.step).next data.2 := by
  exact (History.returnNextInterpreter_primrec
    (fun data : FiniteMachine Q Γ × Lecerf.Machine.Config Q Γ =>
      data.1.step data.2)
    FiniteMachine.step_uniform_primrec).of_eq fun _ => rfl

theorem finiteReturnPrev_uniform_primrec
    {Q : Type u} {Γ : Type v} [Primcodable Q] [DecidableEq Q]
    [Inhabited Γ] [Primcodable Γ] [DecidableEq Γ] :
    Primrec fun data : FiniteMachine Q Γ ×
        Config (Lecerf.Machine.History.Config (Lecerf.Machine.Config Q Γ)) =>
      (returnStep data.1.step).prev data.2 := by
  exact (History.returnPrevInterpreter_primrec
    (fun data : FiniteMachine Q Γ × Lecerf.Machine.Config Q Γ =>
      data.1.step data.2)
    FiniteMachine.step_uniform_primrec).of_eq fun _ => rfl

def universalStart (code : Nat.Partrec.Code) (input : Nat) :
    Config (Lecerf.Machine.History.Config Source.EvalSearchConfig) :=
  start (Source.evalSearchStart code input)

def universalTarget (code : Nat.Partrec.Code) (input : Nat) :
    Config (Lecerf.Machine.History.Config Source.EvalSearchConfig) :=
  target (Source.evalSearchStart code input)

theorem universalStart_joint_primrec :
    Primrec fun data : Nat.Partrec.Code × Nat =>
      universalStart data.1 data.2 :=
  (start_primrec.comp Source.evalSearchStart_joint_primrec).of_eq fun _ => rfl

theorem universalTarget_joint_primrec :
    Primrec fun data : Nat.Partrec.Code × Nat =>
      universalTarget data.1 data.2 :=
  (target_primrec.comp Source.evalSearchStart_joint_primrec).of_eq fun _ => rfl

theorem universalStartTarget_joint_primrec :
    Primrec fun data : Nat.Partrec.Code × Nat =>
      (universalStart data.1 data.2, universalTarget data.1 data.2) :=
  universalStart_joint_primrec.pair universalTarget_joint_primrec

theorem universalTurnaroundNext_primrec :
    Primrec (turnaroundStep Source.universalEvalSearchStep).next :=
  turnaroundStep_next_primrec Source.universalEvalSearchStep_primrec

theorem universalTurnaroundPrev_primrec :
    Primrec (turnaroundStep Source.universalEvalSearchStep).prev :=
  turnaroundStep_prev_primrec Source.universalEvalSearchStep_primrec

theorem universalReturnNext_primrec :
    Primrec (returnStep Source.universalEvalSearchStep).next :=
  returnStep_next_primrec Source.universalEvalSearchStep_primrec

theorem universalReturnPrev_primrec :
    Primrec (returnStep Source.universalEvalSearchStep).prev :=
  returnStep_prev_primrec Source.universalEvalSearchStep_primrec

end History

end Lecerf.Machine.Coupling
