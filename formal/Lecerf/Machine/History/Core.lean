import Lecerf.Transition.API
import Mathlib.Computability.Primrec.List

/-!
# Reversible history simulation

An arbitrary deterministic partial transition becomes reversible when every
successful step stores its complete predecessor.  This is an abstract semantic
construction: it deliberately does not claim to be Lecerf's tape-marker
encoding or an ordinary finite Turing-machine compilation.
-/

namespace Lecerf.Machine.History

open Lecerf.Transition

universe u

/-- A source state together with the newest-first list of its predecessors. -/
structure Config (σ : Type u) where
  current : σ
  history : List σ
  deriving DecidableEq

namespace Config

variable {σ : Type u}

/-- The explicit product representation of history configurations. -/
def equivRep : Config σ ≃ σ × List σ where
  toFun config := (config.current, config.history)
  invFun data := ⟨data.1, data.2⟩
  left_inv := by intro config; cases config; rfl
  right_inv := by intro data; cases data; rfl

instance [Primcodable σ] : Primcodable (Config σ) :=
  Primcodable.ofEquiv (σ × List σ) equivRep

/-- Encode a current source state and its explicit predecessor log. -/
def encode (current : σ) (history : List σ) : Config σ :=
  ⟨current, history⟩

/-- Decode a history configuration without discarding its log. -/
def decode (config : Config σ) : σ × List σ :=
  (config.current, config.history)

@[simp]
theorem decode_encode (current : σ) (history : List σ) :
    decode (encode current history) = (current, history) :=
  rfl

@[simp]
theorem encode_decode (config : Config σ) :
    encode config.decode.1 config.decode.2 = config := by
  cases config
  rfl

theorem encode_injective :
    Function.Injective (fun data : σ × List σ => encode data.1 data.2) :=
  fun _ _ equal => by
    simpa using congrArg decode equal

/-- The simulator state corresponding to a fresh source computation. -/
def initial (state : σ) : Config σ :=
  encode state []

@[simp]
theorem initial_current (state : σ) : (initial state).current = state :=
  rfl

@[simp]
theorem initial_history (state : σ) : (initial state).history = [] :=
  rfl

end Config

/-- Execute one source step and push the complete predecessor if it succeeds. -/
def forward {σ : Type u} (next : Step σ) : Step (Config σ)
  | ⟨current, history⟩ =>
      (next current).map fun target => ⟨target, current :: history⟩

/-- Pop a predecessor only when recomputing it produces the recorded current
state.  The check makes this the inverse on the whole ambient configuration
space, including malformed histories. -/
def backward {σ : Type u} [DecidableEq σ] (next : Step σ) : Step (Config σ)
  | ⟨_, []⟩ => none
  | ⟨current, previous :: history⟩ =>
      if next previous = some current then
        some ⟨previous, history⟩
      else
        none

@[simp]
theorem forward_encode {σ : Type u} (next : Step σ) (current : σ)
    (history : List σ) :
    forward next (Config.encode current history) =
      (next current).map fun target => Config.encode target (current :: history) :=
  rfl

theorem forward_eq_some_iff {σ : Type u} (next : Step σ)
    (source target : Config σ) :
    forward next source = some target ↔
      next source.current = some target.current ∧
        target.history = source.current :: source.history := by
  rcases source with ⟨current, history⟩
  rcases target with ⟨target, targetHistory⟩
  constructor
  · intro step
    simp only [forward, Option.map_eq_some_iff] at step
    obtain ⟨nextState, sourceStep, configEq⟩ := step
    cases configEq
    exact ⟨sourceStep, rfl⟩
  · rintro ⟨sourceStep, rfl⟩
    simp [forward, sourceStep]

theorem forward_of_source_step {σ : Type u} {next : Step σ}
    {current target : σ} {history : List σ}
    (step : next current = some target) :
    forward next (Config.encode current history) =
      some (Config.encode target (current :: history)) := by
  exact (forward_eq_some_iff next _ _).mpr ⟨step, rfl⟩

theorem forward_eq_some_iff_backward_eq_some {σ : Type u} [DecidableEq σ]
    (next : Step σ) (source target : Config σ) :
    forward next source = some target ↔ backward next target = some source := by
  rcases source with ⟨current, history⟩
  rcases target with ⟨target, targetHistory⟩
  constructor
  · intro step
    obtain ⟨sourceStep, historyEq⟩ :=
      (forward_eq_some_iff next ⟨current, history⟩ ⟨target, targetHistory⟩).mp step
    simp only at historyEq
    subst targetHistory
    simp [backward, sourceStep]
  · intro inverse
    cases targetHistory with
    | nil =>
        change (none : Option (Config σ)) = some ⟨current, history⟩ at inverse
        contradiction
    | cons previous rest =>
        by_cases checked : next previous = some target
        · have rawEq : some (Config.encode previous rest) =
              some (Config.encode current history) := by
            change (if next previous = some target then
                some (Config.encode previous rest) else none) =
              some (Config.encode current history) at inverse
            rw [if_pos checked] at inverse
            exact inverse
          have configEq : Config.encode previous rest = Config.encode current history :=
            Option.some.inj rawEq
          cases configEq
          exact forward_of_source_step checked
        · change (if next previous = some target then
              some (Config.encode previous rest) else none) =
            some (Config.encode current history) at inverse
          rw [if_neg checked] at inverse
          contradiction

/-- The history construction as a reversible partial transition on all
history configurations. -/
def reversible {σ : Type u} [DecidableEq σ] (next : Step σ) :
    ReversibleStep (Config σ) where
  toFun := forward next
  invFun := backward next
  inv source target := (forward_eq_some_iff_backward_eq_some next source target).symm

@[simp]
theorem reversible_next {σ : Type u} [DecidableEq σ]
    (next : Step σ) : (reversible next).next = forward next :=
  rfl

@[simp]
theorem reversible_prev {σ : Type u} [DecidableEq σ]
    (next : Step σ) : (reversible next).prev = backward next :=
  rfl

/-- Histories generated from a chosen source start state.  Unlike a bare list
predicate, each constructor records the source transition that justifies the
new head of the log. -/
inductive Valid {σ : Type u} (next : Step σ) (start : σ) : Config σ → Prop
  | initial : Valid next start (Config.initial start)
  | push {current target : σ} {history : List σ} :
      Valid next start (Config.encode current history) →
      next current = some target →
      Valid next start (Config.encode target (current :: history))

theorem Valid.forward {σ : Type u} {next : Step σ} {start : σ}
    {source target : Config σ} (valid : Valid next start source)
    (step : forward next source = some target) : Valid next start target := by
  obtain ⟨sourceStep, historyEq⟩ := (forward_eq_some_iff next source target).mp step
  rcases source with ⟨current, history⟩
  rcases target with ⟨target, targetHistory⟩
  simp only at historyEq
  subst targetHistory
  exact Valid.push valid sourceStep

theorem Valid.initialized {σ : Type u} (next : Step σ) (start : σ) :
    Valid next start (Config.initial start) :=
  Valid.initial

end Lecerf.Machine.History
