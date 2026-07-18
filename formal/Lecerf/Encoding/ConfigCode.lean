import Lecerf.Word.Prefix
import Mathlib.Computability.Primrec.Basic

/-!
# Executable self-delimiting configuration codes

This file supplies a small executable boundary between `Primcodable`
configuration data and words over `Bool`.  A natural number `n` is framed as
`true` repeated `n` times followed by `false`; a configuration is represented
by the frame of its canonical `Encodable.encode` value.

The terminal `false` makes the family prefix-free.  Besides the exact
single-frame decoder, the file exposes a structurally recursive decoder for
concatenated frames.  No arbitrary code inverse or generated-submonoid
membership decision is used.
-/

namespace Lecerf.Encoding.ConfigCode

open Lecerf.Word

universe u

/-- The canonical self-delimiting unary frame `true^n false`. -/
def unaryFrame : Nat → List Bool
  | 0 => [false]
  | n + 1 => true :: unaryFrame n

@[simp]
theorem unaryFrame_zero : unaryFrame 0 = [false] :=
  rfl

@[simp]
theorem unaryFrame_succ (n : Nat) : unaryFrame (n + 1) = true :: unaryFrame n :=
  rfl

/-- Unary frames are never empty. -/
theorem unaryFrame_ne_nil (n : Nat) : unaryFrame n ≠ [] := by
  cases n <;> simp

/-- No unary frame is a proper prefix of another unary frame. -/
theorem unaryFrame_isPrefix_iff {m n : Nat} :
    unaryFrame m <+: unaryFrame n ↔ m = n := by
  induction m generalizing n with
  | zero =>
      cases n <;> simp [unaryFrame]
  | succ m ih =>
      cases n with
      | zero => simp [unaryFrame]
      | succ n => simpa [unaryFrame] using ih (n := n)

/-- Exact decoder for one unary frame.  Trailing data and unterminated runs
are rejected. -/
def decodeUnaryFrame : List Bool → Option Nat
  | [] => none
  | [false] => some 0
  | false :: _ :: _ => none
  | true :: rest => (decodeUnaryFrame rest).map Nat.succ

@[simp]
theorem decodeUnaryFrame_unaryFrame (n : Nat) :
    decodeUnaryFrame (unaryFrame n) = some n := by
  induction n with
  | zero => rfl
  | succ n ih => simp [unaryFrame, decodeUnaryFrame, ih]

variable {C : Type u} [Primcodable C]

/-- Bit-list representation of a configuration. -/
def encodeConfigBits (config : C) : List Bool :=
  unaryFrame (Encodable.encode config)

/-- Decode exactly one configuration frame. -/
def decodeConfigBits (bits : List Bool) : Option C :=
  (decodeUnaryFrame bits).bind (@Encodable.decode C _)

@[simp]
theorem decodeConfigBits_encodeConfigBits (config : C) :
    decodeConfigBits (encodeConfigBits config) = some config := by
  simp [decodeConfigBits, encodeConfigBits, Encodable.encodek]

/-- A configuration as a free-monoid word over `Bool`. -/
def encodeConfig (config : C) : Word Bool :=
  FreeMonoid.ofList (encodeConfigBits config)

/-- Exact decoder for configuration words. -/
def decodeConfig (word : Word Bool) : Option C :=
  decodeConfigBits word.toList

@[simp]
theorem encodeConfig_toList (config : C) :
    (encodeConfig config).toList = encodeConfigBits config :=
  rfl

@[simp]
theorem decodeConfig_encodeConfig (config : C) :
    decodeConfig (encodeConfig config) = some config := by
  simp [decodeConfig, encodeConfig]

/-- The configuration frame family is prefix-free. -/
theorem encodeConfig_isPrefixFree :
    IsPrefixFree (encodeConfig : C → Word Bool) := by
  intro left right hprefix
  apply Encodable.encode_injective
  apply unaryFrame_isPrefix_iff.mp
  simpa [encodeConfig, encodeConfigBits] using hprefix

/-- No encoded configuration is the empty word. -/
theorem encodeConfig_ne_one (config : C) : encodeConfig config ≠ 1 := by
  intro hempty
  have hbits : encodeConfigBits config = [] := by
    simpa [encodeConfig] using congrArg FreeMonoid.toList hempty
  exact unaryFrame_ne_nil (Encodable.encode config) hbits

/-- The configuration frames form an indexed prefix code. -/
theorem encodeConfig_isPrefixCode :
    IsPrefixCode (encodeConfig : C → Word Bool) :=
  ⟨encodeConfig_isPrefixFree, encodeConfig_ne_one⟩

/-- The configuration frames form an indexed code, so concatenations have a
unique factorization into configurations. -/
theorem encodeConfig_isIndexedCode :
    IsIndexedCode (encodeConfig : C → Word Bool) :=
  encodeConfig_isPrefixCode.isIndexedCode

/-! ## Executable decoding of concatenated frames -/

/-- Accumulator-based parser for a sequence of unary-framed configurations.
The accumulator is the number of `true` bits read in the current frame. -/
def decodeConfigListBitsAux : Nat → List Bool → Option (List C)
  | count, [] => if count = 0 then some [] else none
  | count, true :: rest => decodeConfigListBitsAux (count + 1) rest
  | count, false :: rest =>
      match @Encodable.decode C _ count with
      | none => none
      | some config =>
          (decodeConfigListBitsAux 0 rest).map (config :: ·)

/-- Encode a list as the concatenation of its configuration frames. -/
def encodeConfigListBits (configs : List C) : List Bool :=
  (configs.map encodeConfigBits).flatten

/-- Decode an entire concatenation of configuration frames. -/
def decodeConfigListBits (bits : List Bool) : Option (List C) :=
  decodeConfigListBitsAux 0 bits

private theorem decodeConfigListBitsAux_unaryFrame_append
    (count n : Nat) (rest : List Bool) :
    decodeConfigListBitsAux (C := C) count (unaryFrame n ++ rest) =
      match @Encodable.decode C _ (count + n) with
      | none => none
      | some config =>
          (decodeConfigListBitsAux 0 rest).map (config :: ·) := by
  induction n generalizing count with
  | zero => simp [unaryFrame, decodeConfigListBitsAux]
  | succ n ih =>
      simpa [unaryFrame, decodeConfigListBitsAux, Nat.add_assoc,
        Nat.add_comm, Nat.add_left_comm] using ih (count := count + 1)

private theorem decodeConfigListBitsAux_encode_append
    (config : C) (rest : List Bool) :
    decodeConfigListBitsAux 0 (encodeConfigBits config ++ rest) =
      (decodeConfigListBitsAux 0 rest).map (config :: ·) := by
  rw [encodeConfigBits, decodeConfigListBitsAux_unaryFrame_append]
  simp [Encodable.encodek]

@[simp]
theorem decodeConfigListBits_encodeConfigListBits (configs : List C) :
    decodeConfigListBits (encodeConfigListBits configs) = some configs := by
  induction configs with
  | nil => simp [decodeConfigListBits, encodeConfigListBits,
      decodeConfigListBitsAux]
  | cons config configs ih =>
      rw [encodeConfigListBits, List.map_cons, List.flatten_cons]
      rw [decodeConfigListBits]
      rw [decodeConfigListBitsAux_encode_append]
      change
        (decodeConfigListBitsAux 0 (encodeConfigListBits configs)).map
            (config :: ·) =
          some (config :: configs)
      simpa [decodeConfigListBits] using congrArg (Option.map (config :: ·)) ih

/-- Word-valued concatenation of configuration frames. -/
def encodeConfigs (configs : List C) : Word Bool :=
  FreeMonoid.ofList (encodeConfigListBits configs)

/-- Decode a word completely as a sequence of configuration frames. -/
def decodeConfigs (word : Word Bool) : Option (List C) :=
  decodeConfigListBits word.toList

@[simp]
theorem decodeConfigs_encodeConfigs (configs : List C) :
    decodeConfigs (encodeConfigs configs) = some configs := by
  simp [decodeConfigs, encodeConfigs]

/-- Concatenating the executable frames agrees with the homomorphic extension
of the indexed configuration code. -/
theorem encodeConfigs_eq_lift (configs : List C) :
    encodeConfigs configs =
      FreeMonoid.lift encodeConfig (FreeMonoid.ofList configs) := by
  apply FreeMonoid.toList.injective
  change encodeConfigListBits configs =
    (FreeMonoid.lift encodeConfig (FreeMonoid.ofList configs)).toList
  rw [Lecerf.Word.toList_lift_ofList]
  simp [encodeConfigListBits]

end Lecerf.Encoding.ConfigCode
