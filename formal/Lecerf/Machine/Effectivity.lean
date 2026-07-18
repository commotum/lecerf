import Lecerf.Machine.Core

/-!
# Effective finite-machine execution

This module proves that the executable operations of the concrete machine
model are primitive recursive uniformly in their finite descriptions.  The
proofs use the constructive `Primcodable` representations supplied by
`Machine.Tape` and `Machine.Core`; they do not enumerate the alphabet or the
control-state type.
-/

namespace Lecerf.Machine

universe u v

namespace Side

variable {Γ : Type v} [Inhabited Γ] [Primcodable Γ] [DecidableEq Γ]

/-- Recover a subtype-certified nonblank symbol through its canonical code,
without enumerating the alphabet. -/
private def certified? (symbol : Γ) : Option (Nonblank Γ) :=
  Encodable.decode₂ (Nonblank Γ) (Encodable.encode symbol)

private theorem certified_primrec : Primrec (certified? (Γ := Γ)) :=
  Primrec.decode₂.comp Primrec.encode

private theorem certified_eq (symbol : Γ) :
    certified? symbol =
      if h : symbol = default then none else some ⟨symbol, h⟩ := by
  by_cases h : symbol = default
  · rw [dif_pos h]
    apply Option.eq_none_iff_forall_not_mem.mpr
    intro candidate candidateMem
    have encoded : Encodable.encode candidate = Encodable.encode symbol :=
      Encodable.mem_decode₂.mp candidateMem
    have valueEq : candidate.1 = symbol := Encodable.encode_injective (by
      simpa [Encodable.Subtype.encode_eq] using encoded)
    exact candidate.2 (valueEq.trans h)
  · rw [dif_neg h]
    exact Encodable.decode₂_eq_some.mpr (by
      simp [Encodable.Subtype.encode_eq])

private def effectiveCons (data : Γ × Side Γ) : Side Γ :=
  match data.2 with
  | none => (certified? data.1).map fun far => (far, [])
  | some (far, near) => some (far, data.1 :: near)

private theorem effectiveCons_eq (data : Γ × Side Γ) :
    effectiveCons data = cons data.1 data.2 := by
  rcases data with ⟨symbol, _ | ⟨far, near⟩⟩
  · simp only [effectiveCons, certified_eq]
    split <;> simp [cons, *]
  · rfl

private theorem effectiveCons_primrec :
    Primrec (effectiveCons (Γ := Γ)) := by
  have noneCase : Primrec fun data : Γ × Side Γ =>
      (certified? data.1).map fun far => (far, []) :=
    Primrec.option_map (certified_primrec.comp Primrec.fst)
      ((Primrec.snd.pair (Primrec.const ([] : List Γ))).to₂)
  have someCase : Primrec₂ fun (data : Γ × Side Γ)
      (side : Nonblank Γ × List Γ) =>
        some (side.1, data.1 :: side.2) := by
    have pairSide : Primrec fun pair :
        (Γ × Side Γ) × (Nonblank Γ × List Γ) =>
          (pair.2.1, pair.1.1 :: pair.2.2) :=
      (Primrec.fst.comp Primrec.snd).pair
        (Primrec.list_cons.comp (Primrec.fst.comp Primrec.fst)
          (Primrec.snd.comp Primrec.snd))
    exact (Primrec.option_some.comp pairSide).to₂
  exact (Primrec.option_casesOn Primrec.snd noneCase someCase).of_eq fun data => by
    rcases data with ⟨symbol, _ | ⟨far, near⟩⟩ <;> rfl

/-- Reading the nearest cell of a canonical half-tape is primitive recursive. -/
theorem head_primrec : Primrec (head : Side Γ → Γ) := by
  have payload : Primrec fun side : Nonblank Γ × List Γ => head (some side) := by
    have empty : Primrec fun side : Nonblank Γ × List Γ => side.1.1 :=
      Primrec.subtype_val.comp Primrec.fst
    have nonempty : Primrec₂ fun (_side : Nonblank Γ × List Γ)
        (cellRest : Γ × List Γ) => cellRest.1 :=
      (Primrec.fst.comp Primrec.snd).to₂
    exact (Primrec.list_casesOn Primrec.snd empty nonempty).of_eq fun side => by
      rcases side with ⟨far, near⟩
      cases near <;> rfl
  exact (Primrec.option_casesOn Primrec.id (Primrec.const default)
    (payload.comp Primrec.snd).to₂).of_eq fun side => by
      rcases side with _ | side <;> rfl

/-- Removing the nearest cell of a canonical half-tape is primitive recursive. -/
theorem tail_primrec : Primrec (tail : Side Γ → Side Γ) := by
  have payload : Primrec fun side : Nonblank Γ × List Γ => tail (some side) := by
    have nonempty : Primrec₂ fun (side : Nonblank Γ × List Γ)
        (cellRest : Γ × List Γ) => some (side.1, cellRest.2) := by
      have pairResult : Primrec fun data :
          (Nonblank Γ × List Γ) × (Γ × List Γ) =>
            (data.1.1, data.2.2) :=
        (Primrec.fst.comp Primrec.fst).pair
          (Primrec.snd.comp Primrec.snd)
      exact (Primrec.option_some.comp pairResult).to₂
    exact (Primrec.list_casesOn Primrec.snd (Primrec.const none) nonempty).of_eq
      fun side => by
        rcases side with ⟨far, near⟩
        cases near <;> rfl
  exact (Primrec.option_casesOn Primrec.id (Primrec.const none)
    (payload.comp Primrec.snd).to₂).of_eq fun side => by
      rcases side with _ | side <;> rfl

/-- Adding and normalizing a nearest cell is primitive recursive jointly in
the symbol and canonical half-tape. -/
theorem cons_uniform_primrec :
    Primrec fun data : Γ × Side Γ => cons data.1 data.2 :=
  effectiveCons_primrec.of_eq effectiveCons_eq

end Side

namespace Tape

variable {Γ : Type v} [Inhabited Γ] [Primcodable Γ] [DecidableEq Γ]

/-- The canonical tape-to-product representation map is primitive recursive. -/
theorem equivRep_primrec :
    Primrec (equivRep : Tape Γ → Γ × (Side Γ × Side Γ)) :=
  Primrec.of_equiv

/-- Reconstruction from the canonical tape product is primitive recursive. -/
theorem equivRep_symm_primrec :
    Primrec (equivRep.symm : Γ × (Side Γ × Side Γ) → Tape Γ) :=
  Primrec.of_equiv_symm

/-- Reading a tape's scanned symbol is primitive recursive. -/
theorem head_primrec : Primrec (Tape.head : Tape Γ → Γ) :=
  Primrec.fst.comp equivRep_primrec

/-- Tape writing is primitive recursive jointly in the written symbol and
tape. -/
theorem write_uniform_primrec :
    Primrec fun data : Γ × Tape Γ => write data.1 data.2 := by
  have tapeRep : Primrec fun data : Γ × Tape Γ => equivRep data.2 :=
    equivRep_primrec.comp Primrec.snd
  have symbol : Primrec fun data : Γ × Tape Γ => data.1 := Primrec.fst
  have leftSide : Primrec fun data : Γ × Tape Γ => (equivRep data.2).2.1 :=
    Primrec.fst.comp (Primrec.snd.comp tapeRep)
  have rightSide : Primrec fun data : Γ × Tape Γ => (equivRep data.2).2.2 :=
    Primrec.snd.comp (Primrec.snd.comp tapeRep)
  have rep : Primrec fun data : Γ × Tape Γ =>
      (data.1, ((equivRep data.2).2.1, (equivRep data.2).2.2)) :=
    Primrec.pair symbol (Primrec.pair leftSide rightSide)
  exact (equivRep_symm_primrec.comp rep).of_eq fun data => by
    rcases data with ⟨symbol, ⟨head, left, right⟩⟩
    rfl

/-- Head movement is primitive recursive jointly in the direction and tape. -/
theorem move_uniform_primrec :
    Primrec fun data : Move × Tape Γ => move data.1 data.2 := by
  have tapeRep : Primrec fun data : Move × Tape Γ => equivRep data.2 :=
    equivRep_primrec.comp Primrec.snd
  have oldHead : Primrec fun data : Move × Tape Γ => (equivRep data.2).1 :=
    Primrec.fst.comp tapeRep
  have oldLeft : Primrec fun data : Move × Tape Γ => (equivRep data.2).2.1 :=
    Primrec.fst.comp (Primrec.snd.comp tapeRep)
  have oldRight : Primrec fun data : Move × Tape Γ => (equivRep data.2).2.2 :=
    Primrec.snd.comp (Primrec.snd.comp tapeRep)
  have leftRep : Primrec fun data : Move × Tape Γ =>
      (Side.head (equivRep data.2).2.1,
        (Side.tail (equivRep data.2).2.1,
          Side.cons (equivRep data.2).1 (equivRep data.2).2.2)) := by
    exact Primrec.pair
      (Side.head_primrec.comp oldLeft)
      (Primrec.pair
        (Side.tail_primrec.comp oldLeft)
        (Side.cons_uniform_primrec.comp (Primrec.pair oldHead oldRight)))
  have rightRep : Primrec fun data : Move × Tape Γ =>
      (Side.head (equivRep data.2).2.2,
        (Side.cons (equivRep data.2).1 (equivRep data.2).2.1,
          Side.tail (equivRep data.2).2.2)) := by
    exact Primrec.pair
      (Side.head_primrec.comp oldRight)
      (Primrec.pair
        (Side.cons_uniform_primrec.comp (Primrec.pair oldHead oldLeft))
        (Side.tail_primrec.comp oldRight))
  have direction : Primrec fun data : Move × Tape Γ => data.1 := Primrec.fst
  have selected : Primrec fun data : Move × Tape Γ =>
      if data.1 = .left then
        (Side.head (equivRep data.2).2.1,
          (Side.tail (equivRep data.2).2.1,
            Side.cons (equivRep data.2).1 (equivRep data.2).2.2))
      else if data.1 = .stay then equivRep data.2
      else
        (Side.head (equivRep data.2).2.2,
          (Side.cons (equivRep data.2).1 (equivRep data.2).2.1,
            Side.tail (equivRep data.2).2.2)) :=
    Primrec.ite (Primrec.eq.comp direction (Primrec.const Move.left)) leftRep
      (Primrec.ite (Primrec.eq.comp direction (Primrec.const Move.stay))
        tapeRep rightRep)
  exact (equivRep_symm_primrec.comp selected).of_eq fun data => by
    rcases data with ⟨direction, ⟨head, left, right⟩⟩
    cases direction <;> rfl

/-- The fixed write-then-move tape action is uniformly primitive recursive. -/
theorem act_uniform_primrec :
    Primrec fun data : (Γ × Move) × Tape Γ =>
      act data.1.1 data.1.2 data.2 := by
  have written : Primrec fun data : (Γ × Move) × Tape Γ =>
      write data.1.1 data.2 :=
    write_uniform_primrec.comp
      (Primrec.pair (Primrec.fst.comp Primrec.fst) Primrec.snd)
  exact (move_uniform_primrec.comp
    (Primrec.pair (Primrec.snd.comp Primrec.fst) written)).of_eq fun data => by
      simp [act]

end Tape

namespace Config

variable {Q : Type u} {Γ : Type v} [Inhabited Γ]
  [Primcodable Q] [Primcodable Γ] [DecidableEq Γ]

/-- The configuration-to-product representation map is primitive recursive. -/
theorem equivRep_primrec :
    Primrec (equivRep : Config Q Γ → Q × Tape Γ) :=
  Primrec.of_equiv

/-- Reconstruction from the configuration product is primitive recursive. -/
theorem equivRep_symm_primrec :
    Primrec (equivRep.symm : Q × Tape Γ → Config Q Γ) :=
  Primrec.of_equiv_symm

end Config

namespace Rule

variable {Q : Type u} {Γ : Type v} [Inhabited Γ]
  [Primcodable Q] [Primcodable Γ] [DecidableEq Q] [DecidableEq Γ]

omit [Inhabited Γ] [DecidableEq Q] [DecidableEq Γ] in
/-- The rule-to-product representation map is primitive recursive. -/
theorem equivRep_primrec :
    Primrec (equivRep : Rule Q Γ → Q × Γ × Q × Γ × Tape.Move) :=
  Primrec.of_equiv

/-- Applying one finite instruction is primitive recursive jointly in the
instruction and configuration. -/
theorem apply_uniform_primrec :
    Primrec fun data : Rule Q Γ × Config Q Γ => data.1.apply data.2 := by
  have ruleRep : Primrec fun data : Rule Q Γ × Config Q Γ => equivRep data.1 :=
    equivRep_primrec.comp Primrec.fst
  have configRep : Primrec fun data : Rule Q Γ × Config Q Γ =>
      Config.equivRep data.2 :=
    Config.equivRep_primrec.comp Primrec.snd
  have source : Primrec fun data : Rule Q Γ × Config Q Γ =>
      (equivRep data.1).1 :=
    Primrec.fst.comp ruleRep
  have read : Primrec fun data : Rule Q Γ × Config Q Γ =>
      (equivRep data.1).2.1 :=
    Primrec.fst.comp (Primrec.snd.comp ruleRep)
  have target : Primrec fun data : Rule Q Γ × Config Q Γ =>
      (equivRep data.1).2.2.1 :=
    Primrec.fst.comp (Primrec.snd.comp (Primrec.snd.comp ruleRep))
  have writeSymbol : Primrec fun data : Rule Q Γ × Config Q Γ =>
      (equivRep data.1).2.2.2.1 :=
    Primrec.fst.comp
      (Primrec.snd.comp (Primrec.snd.comp (Primrec.snd.comp ruleRep)))
  have direction : Primrec fun data : Rule Q Γ × Config Q Γ =>
      (equivRep data.1).2.2.2.2 :=
    Primrec.snd.comp
      (Primrec.snd.comp (Primrec.snd.comp (Primrec.snd.comp ruleRep)))
  have state : Primrec fun data : Rule Q Γ × Config Q Γ =>
      (Config.equivRep data.2).1 :=
    Primrec.fst.comp configRep
  have tape : Primrec fun data : Rule Q Γ × Config Q Γ =>
      (Config.equivRep data.2).2 :=
    Primrec.snd.comp configRep
  have tapeHead : Primrec fun data : Rule Q Γ × Config Q Γ =>
      data.2.tape.head :=
    Tape.head_primrec.comp tape
  have enabled : PrimrecPred fun data : Rule Q Γ × Config Q Γ =>
      data.2.state = data.1.source ∧ data.2.tape.head = data.1.read :=
    (Primrec.eq.comp state source).and (Primrec.eq.comp tapeHead read)
  have actedTape : Primrec fun data : Rule Q Γ × Config Q Γ =>
      data.2.tape.act data.1.write data.1.move :=
    (Tape.act_uniform_primrec.comp
      (Primrec.pair (Primrec.pair writeSymbol direction) tape)).of_eq
        fun _ => rfl
  have result : Primrec fun data : Rule Q Γ × Config Q Γ =>
      some (⟨data.1.target,
        data.2.tape.act data.1.write data.1.move⟩ : Config Q Γ) :=
    Primrec.option_some.comp
      (Config.equivRep_symm_primrec.comp (Primrec.pair target actedTape))
  exact (Primrec.ite enabled result (Primrec.const none)).of_eq fun data => by
    simp only [apply]

end Rule

namespace FiniteMachine

variable {Q : Type u} {Γ : Type v} [Inhabited Γ]
  [Primcodable Q] [Primcodable Γ] [DecidableEq Q] [DecidableEq Γ]

omit [Inhabited Γ] [DecidableEq Q] [DecidableEq Γ] in
/-- The finite-table list representation map is primitive recursive. -/
theorem equivRep_primrec :
    Primrec (equivRep : FiniteMachine Q Γ → List (Rule Q Γ)) :=
  Primrec.of_equiv

/-- First-success execution is primitive recursive jointly in a rule list and
configuration. -/
theorem applyRules_uniform_primrec :
    Primrec fun data : List (Rule Q Γ) × Config Q Γ =>
      applyRules data.1 data.2 := by
  have ruleStep : Primrec fun pair :
      (List (Rule Q Γ) × Config Q Γ) ×
        (Rule Q Γ × List (Rule Q Γ) × Option (Config Q Γ)) =>
      pair.2.1.apply pair.1.2 :=
    Rule.apply_uniform_primrec.comp
      (Primrec.pair (Primrec.fst.comp Primrec.snd)
        (Primrec.snd.comp Primrec.fst))
  have inherited : Primrec fun pair :
      (List (Rule Q Γ) × Config Q Γ) ×
        (Rule Q Γ × List (Rule Q Γ) × Option (Config Q Γ)) =>
      pair.2.2.2 :=
    Primrec.snd.comp (Primrec.snd.comp Primrec.snd)
  have body : Primrec₂ fun (data : List (Rule Q Γ) × Config Q Γ)
      (recData : Rule Q Γ × List (Rule Q Γ) × Option (Config Q Γ)) =>
        recData.1.apply data.2 <|> recData.2.2 :=
    (Primrec.option_orElse.comp ruleStep inherited).to₂
  exact (Primrec.list_rec Primrec.fst (Primrec.const none) body).of_eq
    fun data => by
      induction data.1 with
      | nil => rfl
      | cons rule rest ih =>
          simp only [applyRules]
          cases firstStep : rule.apply data.2 with
          | none => simpa using ih
          | some next => simp

/-- The transition selected by a finite machine is primitive recursive
uniformly in both the finite table and its input configuration. -/
theorem step_uniform_primrec :
    Primrec fun data : FiniteMachine Q Γ × Config Q Γ =>
      data.1.step data.2 := by
  exact (applyRules_uniform_primrec.comp
    (Primrec.pair (equivRep_primrec.comp Primrec.fst) Primrec.snd)).of_eq
      fun _ => rfl

end FiniteMachine

end Lecerf.Machine
