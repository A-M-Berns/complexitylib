/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/
import
  Complexitylib.TimeSpaceSimulation.Runtime.NeighborhoodMicrocode.PackedLocalHeadScan.Defs
import
  Complexitylib.TimeSpaceSimulation.Runtime.NeighborhoodMicrocode.PackedLocalConfiguration
import
  Complexitylib.TimeSpaceSimulation.Runtime.NeighborhoodMicrocode.PackedLocalRepresentation
import
  Complexitylib.TimeSpaceSimulation.Runtime.NeighborhoodMicrocode.CombineValue
import
  Complexitylib.TimeSpaceSimulation.Runtime.NeighborhoodMicrocode.ControlDecode
import Complexitylib.TimeSpaceSimulation.Runtime.NeighborhoodProgram

/-!
# Correctness internals for packed local-head scanning
-/

namespace Complexity
namespace TimeSpaceSimulation
namespace Runtime
namespace NeighborhoodMicrocode
namespace PackedLocalHeadScan
namespace Internal

open RAM Structured

variable {controller : SearchProgram.Registers}

private theorem basics_runs (ops : List Basic) (store : Store) :
    Runs (Cmd.basics ops) store (Basic.execList ops store) := by
  obtain ⟨cost, space, hexec⟩ :=
    RAM.Structured.Internal.exec_basics_exists ops store
  exact ⟨ops.length, cost, space, hexec⟩

private theorem runs_seq_seq_imm
    (first second : Cmd) (address value : ℕ)
    {initial final : Store}
    (hrun :
      Runs
        (.seq first
          (.seq second (.basic (.imm address value))))
        initial final) :
    final address = value := by
  rcases hrun with ⟨steps, cost, space, hexec⟩
  cases hexec with
  | seq hfirst hrest =>
      cases hrest with
      | seq hsecond hlast =>
          cases hlast
          simp [Basic.exec]

private theorem cmdWritesWithin_mono
    {small large : Finset ℕ} {cmd : Cmd}
    (hwrites : Footprint.CmdWritesWithin small cmd)
    (hsubset : small ⊆ large) :
    Footprint.CmdWritesWithin large cmd := by
  induction cmd with
  | skip =>
      trivial
  | basic op =>
      cases op <;>
        simp only [Footprint.CmdWritesWithin,
          Footprint.BasicWritesWithin] at hwrites ⊢
      all_goals
        exact hsubset hwrites
  | seq first second ihFirst ihSecond =>
      exact ⟨ihFirst hwrites.1, ihSecond hwrites.2⟩
  | ifZero test onZero onNonzero ihZero ihNonzero =>
      exact ⟨ihZero hwrites.1, ihNonzero hwrites.2⟩
  | whileNonzero test body ih =>
      exact ih hwrites

private theorem bank_mem_footprint
    (regs : NeighborhoodTrial.Registers controller)
    (slot : Fin 12) :
    (bankRegisters regs).index slot ∈ footprint regs :=
  Finset.mem_union_left _
    ((bankRegisters regs).index_mem_footprint slot)

private theorem countdown_mem_footprint
    (regs : NeighborhoodTrial.Registers controller) :
    countdown regs ∈ footprint regs :=
  Finset.mem_union_right _ (Finset.mem_singleton_self _)

private theorem division_writeFootprint_subset
    (regs : NeighborhoodTrial.Registers controller) :
    (cellDivision regs).writeFootprint ⊆ footprint regs := by
  intro address haddress
  simp only [ControlDecode.DivisionRegisters.writeFootprint,
    Finset.mem_insert, Finset.mem_singleton] at haddress
  rcases haddress with haddress | haddress | haddress |
      haddress
  all_goals
    subst address
  · exact bank_mem_footprint regs 10
  · exact bank_mem_footprint regs 1
  · exact bank_mem_footprint regs 5
  · exact bank_mem_footprint regs 6

private theorem prepareCellIndex_writesWithin
    (tape : TapeIndex workTapeCount)
    (regs : NeighborhoodTrial.Registers controller) :
    Footprint.CmdWritesWithin (footprint regs)
      (prepareCellIndex tape regs) := by
  simp [prepareCellIndex, Cmd.basics, Cmd.seqList,
    Footprint.CmdWritesWithin, Footprint.BasicWritesWithin,
    bank_mem_footprint]

theorem readCell_writesWithin_internal
    (tape : TapeIndex workTapeCount)
    (regs : NeighborhoodTrial.Registers controller) :
    Footprint.CmdWritesWithin (footprint regs)
      (readCell tape regs) := by
  exact
    ⟨prepareCellIndex_writesWithin tape regs,
      cmdWritesWithin_mono
        (NeighborhoodProgram.bankRead_sourceWritesWithin
          (bankRegisters regs))
        (Finset.subset_union_left :
          (bankRegisters regs).footprint ⊆ footprint regs)⟩

theorem decodeCell_writesWithin_internal
    (regs : NeighborhoodTrial.Registers controller) :
    Footprint.CmdWritesWithin (footprint regs)
      (decodeCell regs) := by
  exact
    ⟨bank_mem_footprint regs 2,
      cmdWritesWithin_mono
        (ControlDecode.divRem_writesWithin (cellDivision regs))
        (division_writeFootprint_subset regs)⟩

private theorem advance_writesWithin
    (tm : TM workTapeCount)
    (regs : NeighborhoodTrial.Registers controller) :
    Footprint.CmdWritesWithin (footprint regs)
      (advance tm regs) := by
  simp [advance, Cmd.basics, Cmd.seqList,
    Footprint.CmdWritesWithin, Footprint.BasicWritesWithin,
    bank_mem_footprint, countdown_mem_footprint]

private theorem step_writesWithin
    (tm : TM workTapeCount)
    (tape : TapeIndex workTapeCount)
    (regs : NeighborhoodTrial.Registers controller) :
    Footprint.CmdWritesWithin (footprint regs)
      (step tm tape regs) := by
  simp only [step, Cmd.seqList, Footprint.CmdWritesWithin]
  exact
    ⟨readCell_writesWithin_internal tape regs,
      decodeCell_writesWithin_internal regs,
      advance_writesWithin tm regs,
      countdown_mem_footprint regs⟩

private theorem initializeScan_writesWithin
    (tm : TM workTapeCount)
    (regs : NeighborhoodTrial.Registers controller) :
    Footprint.CmdWritesWithin (footprint regs)
      (initializeScan tm regs) := by
  simp [initializeScan, Cmd.basics, Cmd.seqList,
    Footprint.CmdWritesWithin, Footprint.BasicWritesWithin,
    bank_mem_footprint, countdown_mem_footprint]

theorem scan_writesWithin_internal
    (tm : TM workTapeCount)
    (tape : TapeIndex workTapeCount)
    (regs : NeighborhoodTrial.Registers controller) :
    Footprint.CmdWritesWithin (footprint regs)
      (scan tm tape regs) := by
  simp only [scan, Cmd.seqList, Footprint.CmdWritesWithin]
  exact
    ⟨initializeScan_writesWithin tm regs,
      step_writesWithin tm tape regs,
      bank_mem_footprint regs 9⟩

theorem scan_compiledWritesWithin_internal
    (tm : TM workTapeCount)
    (tape : TapeIndex workTapeCount)
    (regs : NeighborhoodTrial.Registers controller) :
    RAM.RegisterStore.DenseOverlay.FixedRegisters.Footprint.ProgramWritesWithin
      (scan tm tape regs).compile (footprint regs) :=
  Footprint.programWritesWithin_compile
    (scan_writesWithin_internal tm tape regs)

theorem footprint_subset_combineScratch_internal
    (regs : NeighborhoodTrial.Registers controller) :
    footprint regs ⊆ CombineValue.combineScratchFootprint regs := by
  intro address haddress
  simp only [footprint, Finset.mem_union,
    NeighborhoodProgram.BankRegisters.footprint,
    Finset.mem_image, Finset.mem_univ, true_and,
    Finset.mem_singleton] at haddress
  rcases haddress with ⟨slot, rfl⟩ | rfl
  · fin_cases slot
    all_goals
      simp [bankRegisters, bankMap,
        CombineValue.combineScratchFootprint,
        CombineValue.combineScratchMap]
    all_goals
      first
      | exact ⟨17, rfl⟩
      | exact ⟨0, rfl⟩
      | exact ⟨1, rfl⟩
      | exact ⟨2, rfl⟩
      | exact ⟨3, rfl⟩
      | exact ⟨4, rfl⟩
      | exact ⟨5, rfl⟩
      | exact ⟨7, rfl⟩
      | exact ⟨8, rfl⟩
      | exact ⟨9, rfl⟩
      | exact ⟨12, rfl⟩
      | exact ⟨14, rfl⟩
  · simp [CombineValue.combineScratchFootprint,
      CombineValue.combineScratchMap]
    exact ⟨15, rfl⟩

private theorem fixed_index_not_mem
    (regs : NeighborhoodTrial.Registers controller)
    (slot : Fin 34)
    (hslot : (∀ bankSlot, slot ≠ bankMap bankSlot) ∧
      slot ≠ (30 : Fin 34)) :
    regs.index slot ∉ footprint regs := by
  intro haddress
  simp only [footprint, Finset.mem_union,
    NeighborhoodProgram.BankRegisters.footprint,
    Finset.mem_image, Finset.mem_univ, true_and,
    Finset.mem_singleton] at haddress
  rcases haddress with ⟨bankSlot, heq⟩ | heq
  · exact hslot.1 bankSlot (regs.injective heq.symm)
  · exact hslot.2 (regs.injective heq)

theorem scan_preservesCombine_internal
    (tm : TM workTapeCount)
    (tape : TapeIndex workTapeCount)
    (regs : NeighborhoodTrial.Registers controller)
    {initial final : Store}
    (hone :
      initial (CombineValue.rangeRegisters regs).one = 1)
    (hrun : Runs (scan tm tape regs) initial final) :
    PreservesCombine regs initial final := by
  have fixed
      (slot : Fin 34)
      (hslot : (∀ bankSlot, slot ≠ bankMap bankSlot) ∧
        slot ≠ (30 : Fin 34)) :
      final (regs.index slot) = initial (regs.index slot) :=
    Footprint.runs_eq_outside
      (scan_writesWithin_internal tm tape regs) hrun
      (fixed_index_not_mem regs slot hslot)
  have hfinalOne :
      final (CombineValue.rangeRegisters regs).one = 1 := by
    apply runs_seq_seq_imm
      (initializeScan tm regs)
      (.whileNonzero (countdown regs) (step tm tape regs))
      (CombineValue.rangeRegisters regs).one 1
    simpa [scan, Cmd.seqList] using hrun
  refine
    { accumulator_eq := ?_
      assignment_eq := ?_
      term_eq := ?_
      count_eq := ?_
      one_eq := hfinalOne.trans hone.symm
      codecScratch_eq := ?_
      catalyticWord_eq := ?_
      abi := ?_ }
  · simpa [CombineValue.rangeRegisters] using
      fixed 18 (by
        constructor
        · intro slot
          fin_cases slot <;> decide
        · decide)
  · simpa [CombineValue.rangeRegisters] using
      fixed 21 (by
        constructor
        · intro slot
          fin_cases slot <;> decide
        · decide)
  · simpa [CombineValue.rangeRegisters] using
      fixed 19 (by
        constructor
        · intro slot
          fin_cases slot <;> decide
        · decide)
  · simpa [CombineValue.rangeRegisters] using
      fixed 10 (by
        constructor
        · intro slot
          fin_cases slot <;> decide
        · decide)
  · exact fixed 31 (by
      constructor
      · intro slot
        fin_cases slot <;> decide
      · decide)
  · exact fixed 33 (by
      constructor
      · intro slot
        fin_cases slot <;> decide
      · decide)
  · exact
      { fuel_eq := fixed 22 (by
          constructor
          · intro slot
            fin_cases slot <;> decide
          · decide)
        nodeCode_eq := fixed 23 (by
          constructor
          · intro slot
            fin_cases slot <;> decide
          · decide)
        scalar_eq := fixed 25 (by
          constructor
          · intro slot
            fin_cases slot <;> decide
          · decide)
        out_eq := fixed 26 (by
          constructor
          · intro slot
            fin_cases slot <;> decide
          · decide)
        phaseCode_eq := fixed 27 (by
          constructor
          · intro slot
            fin_cases slot <;> decide
          · decide)
        active_eq := fixed 28 (by
          constructor
          · intro slot
            fin_cases slot <;> decide
          · decide)
        blockLength_eq := fixed 2 (by
          constructor
          · intro slot
            fin_cases slot <;> decide
          · decide)
        horizon_eq := fixed 3 (by
          constructor
          · intro slot
            fin_cases slot <;> decide
          · decide)
        chunkCount_eq := fixed 7 (by
          constructor
          · intro slot
            fin_cases slot <;> decide
          · decide)
        chunkRadix_eq := fixed 8 (by
          constructor
          · intro slot
            fin_cases slot <;> decide
          · decide)
        frameRadix_eq := fixed 13 (by
          constructor
          · intro slot
            fin_cases slot <;> decide
          · decide)
        bankRadix_eq := fixed 14 (by
          constructor
          · intro slot
            fin_cases slot <;> decide
          · decide)
        bankDigitCount_eq := fixed 15 (by
          constructor
          · intro slot
            fin_cases slot <;> decide
          · decide)
        modulusPred_eq := fixed 16 (by
          constructor
          · intro slot
            fin_cases slot <;> decide
          · decide)
        modulus_eq := fixed 24 (by
          constructor
          · intro slot
            fin_cases slot <;> decide
          · decide) }

private theorem gammaCode_lt_four (symbol : Γ) :
    CompactValueCodeSemantics.gammaCode symbol < 4 := by
  cases symbol <;>
    simp [CompactValueCodeSemantics.gammaCode,
      NeighborhoodExecutableEvaluation.FiniteEncoding.gammaEquiv]

private theorem target_absolutePosition
    (blockLength center head : ℕ)
    (hlower :
      PackedLocalConfiguration.windowStart blockLength center ≤ head) :
    PackedLocalConfiguration.absolutePosition blockLength center
        (PackedLocalConfiguration.localHead blockLength center head) =
      head := by
  simp [PackedLocalConfiguration.absolutePosition,
    PackedLocalConfiguration.localHead]
  omega

private theorem represented_marker
    (tm : TM workTapeCount)
    (order :
      NeighborhoodExecutableEvaluation.FiniteEncoding.StateOrder tm)
    (blockLength : ℕ) (hpositive : 0 < blockLength)
    (centers : TapeIndex workTapeCount → ℕ)
    (cfg : Cfg workTapeCount tm.Q)
    (tape : TapeIndex workTapeCount)
    (suffix word localPosition : ℕ)
    (hrep :
      PackedLocalRepresentation.Represents
        tm order blockLength centers cfg suffix word)
    (hlocal :
      localPosition <
        PackedLocalConfiguration.tapeSpan blockLength)
    (hlower :
      PackedLocalConfiguration.windowStart
          blockLength (centers tape) ≤
        (tapeAt cfg tape).head) :
    PackedLocalConfiguration.markerPart
        (PackedDigits.digit
          (PackedLocalConfiguration.radix tm)
          word
          (PackedLocalConfiguration.cellIndex
            blockLength tape localPosition)) =
      if localPosition =
          PackedLocalConfiguration.localHead blockLength
            (centers tape) (tapeAt cfg tape).head then
        1
      else
        0 := by
  rw [PackedLocalRepresentation.represents_cell
    tm order blockLength hpositive centers cfg suffix word hrep
    tape localPosition hlocal]
  rw [PackedLocalConfiguration.markerPart_cellDigit]
  by_cases hposition :
      localPosition =
        PackedLocalConfiguration.localHead blockLength
          (centers tape) (tapeAt cfg tape).head
  · subst localPosition
    simp [target_absolutePosition blockLength (centers tape)
      (tapeAt cfg tape).head hlower]
  · have hhead :
        (tapeAt cfg tape).head ≠
          PackedLocalConfiguration.absolutePosition blockLength
            (centers tape) localPosition := by
      intro heq
      apply hposition
      rw [← target_absolutePosition blockLength (centers tape)
        (tapeAt cfg tape).head hlower] at heq
      simp only [PackedLocalConfiguration.absolutePosition] at heq
      omega
    simp [hposition, hhead]

private theorem represented_symbol
    (tm : TM workTapeCount)
    (order :
      NeighborhoodExecutableEvaluation.FiniteEncoding.StateOrder tm)
    (blockLength : ℕ) (hpositive : 0 < blockLength)
    (centers : TapeIndex workTapeCount → ℕ)
    (cfg : Cfg workTapeCount tm.Q)
    (tape : TapeIndex workTapeCount)
    (suffix word localPosition : ℕ)
    (hrep :
      PackedLocalRepresentation.Represents
        tm order blockLength centers cfg suffix word)
    (hlocal :
      localPosition <
        PackedLocalConfiguration.tapeSpan blockLength) :
    PackedLocalConfiguration.symbolPart
        (PackedDigits.digit
          (PackedLocalConfiguration.radix tm)
          word
          (PackedLocalConfiguration.cellIndex
            blockLength tape localPosition)) =
      CompactValueCodeSemantics.gammaCode
        ((tapeAt cfg tape).cells
          (PackedLocalConfiguration.absolutePosition blockLength
            (centers tape) localPosition)) := by
  rw [PackedLocalRepresentation.represents_cell
    tm order blockLength hpositive centers cfg suffix word hrep
    tape localPosition hlocal]
  exact PackedLocalConfiguration.symbolPart_cellDigit
    cfg blockLength centers tape localPosition

private theorem initializeScan_runs
    (tm : TM workTapeCount)
    (regs : NeighborhoodTrial.Registers controller)
    (store : Store) (blockLength word : ℕ)
    (hblock : store (Layout.blockLength regs) = blockLength)
    (hword : store (bankRegisters regs).word = word) :
    ∃ final,
      Runs (initializeScan tm regs) store final ∧
      final (bankRegisters regs).word = word ∧
      final (bankRegisters regs).base =
        PackedLocalConfiguration.radix tm ∧
      final (bankRegisters regs).basePred =
        PackedLocalConfiguration.radix tm - 1 ∧
      final (bankRegisters regs).one = 1 ∧
      final (headOffset regs) = 0 ∧
      final (countdown regs) =
        PackedLocalConfiguration.tapeSpan blockLength := by
  let ops : List Basic :=
    [.imm (bankRegisters regs).base
        (PackedLocalConfiguration.radix tm),
      .imm (bankRegisters regs).basePred
        (PackedLocalConfiguration.radix tm - 1),
      .imm (bankRegisters regs).one 1,
      .imm (bankRegisters regs).replacement 0,
      .imm (countdown regs) 0,
      .add (countdown regs) (Layout.blockLength regs)
        (countdown regs),
      .add (countdown regs) (Layout.blockLength regs)
        (countdown regs),
      .add (countdown regs) (Layout.blockLength regs)
        (countdown regs)]
  let final := Basic.execList ops store
  refine ⟨final, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simpa [initializeScan, ops] using basics_runs ops store
  · calc
      final (bankRegisters regs).word =
          store (bankRegisters regs).word := by
        simp [final, ops, Basic.execList, Basic.exec,
          bankRegisters, bankMap, regs.injective.eq_iff]
      _ = word := hword
  · simp [final, ops, Basic.execList, Basic.exec,
      bankRegisters, bankMap, regs.injective.eq_iff]
  · simp [final, ops, Basic.execList, Basic.exec,
      bankRegisters, bankMap, regs.injective.eq_iff]
  · simp [final, ops, Basic.execList, Basic.exec,
      bankRegisters, bankMap, regs.injective.eq_iff]
  · simp [final, ops, Basic.execList, Basic.exec,
      bankRegisters, bankMap, headOffset, countdown,
      regs.injective.eq_iff]
  · simp [final, ops, Basic.execList, Basic.exec,
      bankRegisters, bankMap, regs.injective.eq_iff,
      PackedLocalConfiguration.tapeSpan, hblock]
    omega

private theorem bank_index_not_mem
    (regs : NeighborhoodTrial.Registers controller)
    (slot : Fin 34)
    (hslot : ∀ bankSlot, slot ≠ bankMap bankSlot) :
    regs.index slot ∉ (bankRegisters regs).footprint := by
  intro haddress
  simp only [NeighborhoodProgram.BankRegisters.footprint,
    Finset.mem_image, Finset.mem_univ, true_and] at haddress
  obtain ⟨bankSlot, heq⟩ := haddress
  exact hslot bankSlot (regs.injective heq.symm)

private theorem countdown_not_mem_bank
    (regs : NeighborhoodTrial.Registers controller) :
    countdown regs ∉ (bankRegisters regs).footprint :=
  bank_index_not_mem regs 30 (by
    intro slot
    fin_cases slot <;> decide)

private theorem blockLength_not_mem_bank
    (regs : NeighborhoodTrial.Registers controller) :
    Layout.blockLength regs ∉ (bankRegisters regs).footprint :=
  bank_index_not_mem regs 2 (by
    intro slot
    fin_cases slot <;> decide)

private theorem bank_slot_not_mem_division
    (regs : NeighborhoodTrial.Registers controller)
    (slot : Fin 12)
    (hslot :
      slot ≠ 10 ∧ slot ≠ 1 ∧ slot ≠ 5 ∧ slot ≠ 6) :
    (bankRegisters regs).index slot ∉
      (cellDivision regs).writeFootprint := by
  simp only [ControlDecode.DivisionRegisters.writeFootprint,
    Finset.mem_insert, Finset.mem_singleton, not_or]
  exact
    ⟨(bankRegisters regs).index_ne hslot.1,
      (bankRegisters regs).index_ne hslot.2.1,
      (bankRegisters regs).index_ne hslot.2.2.1,
      (bankRegisters regs).index_ne hslot.2.2.2⟩

private theorem countdown_not_mem_division
    (regs : NeighborhoodTrial.Registers controller) :
    countdown regs ∉ (cellDivision regs).writeFootprint := by
  simp only [ControlDecode.DivisionRegisters.writeFootprint,
    Finset.mem_insert, Finset.mem_singleton, not_or]
  exact
    ⟨regs.injective.ne (by decide),
      regs.injective.ne (by decide),
      regs.injective.ne (by decide),
      regs.injective.ne (by decide)⟩

private theorem prepareCellIndex_runs
    (tm : TM workTapeCount)
    (tape : TapeIndex workTapeCount)
    (regs : NeighborhoodTrial.Registers controller)
    (store : Store)
    (blockLength word start remaining : ℕ)
    (hblock : store (Layout.blockLength regs) = blockLength)
    (hword : store (bankRegisters regs).word = word)
    (hstart : store (headOffset regs) = start)
    (hremaining : store (countdown regs) = remaining)
    (hone : store (bankRegisters regs).one = 1)
    (hbase :
      store (bankRegisters regs).base =
        PackedLocalConfiguration.radix tm)
    (hbasePred :
      store (bankRegisters regs).basePred =
        PackedLocalConfiguration.radix tm - 1) :
    ∃ final,
      Runs (prepareCellIndex tape regs) store final ∧
      final (bankRegisters regs).word = word ∧
      final (bankRegisters regs).indexCount =
        PackedLocalConfiguration.cellIndex
          blockLength tape start ∧
      final (headOffset regs) = start ∧
      final (countdown regs) = remaining ∧
      final (bankRegisters regs).one = 1 ∧
      final (bankRegisters regs).base =
        PackedLocalConfiguration.radix tm ∧
      final (bankRegisters regs).basePred =
        PackedLocalConfiguration.radix tm - 1 ∧
      final (Layout.blockLength regs) = blockLength := by
  let ops : List Basic :=
    [.imm (bankRegisters regs).indexCount 0,
      .add (bankRegisters regs).indexCount
        (Layout.blockLength regs) (bankRegisters regs).indexCount,
      .add (bankRegisters regs).indexCount
        (Layout.blockLength regs) (bankRegisters regs).indexCount,
      .add (bankRegisters regs).indexCount
        (Layout.blockLength regs) (bankRegisters regs).indexCount,
      .imm (bankRegisters regs).result tape.val,
      .mul (bankRegisters regs).indexCount
        (bankRegisters regs).result
        (bankRegisters regs).indexCount,
      .add (bankRegisters regs).indexCount
        (bankRegisters regs).replacement
        (bankRegisters regs).indexCount,
      .add (bankRegisters regs).indexCount
        (bankRegisters regs).one
        (bankRegisters regs).indexCount]
  let final := Basic.execList ops store
  refine ⟨final, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simpa [prepareCellIndex, ops] using basics_runs ops store
  · calc
      final (bankRegisters regs).word =
          store (bankRegisters regs).word := by
        simp [final, ops, Basic.execList, Basic.exec,
          bankRegisters, bankMap, regs.injective.eq_iff]
      _ = word := hword
  · simp [final, ops, Basic.execList, Basic.exec,
      bankRegisters, bankMap, regs.injective.eq_iff,
      PackedLocalConfiguration.cellIndex,
      PackedLocalConfiguration.tapeSpan]
    change
      store (bankRegisters regs).one +
          (store (bankRegisters regs).replacement +
            tape.val *
              (store (Layout.blockLength regs) +
                (store (Layout.blockLength regs) +
                  store (Layout.blockLength regs)))) =
        1 + tape.val * (3 * blockLength) + start
    rw [hstart, hone, hblock]
    have hthree :
        blockLength + (blockLength + blockLength) =
          3 * blockLength := by
      omega
    rw [hthree]
    omega
  · calc
      final (headOffset regs) = store (headOffset regs) := by
        simp [final, ops, Basic.execList, Basic.exec,
          bankRegisters, bankMap, headOffset,
          regs.injective.eq_iff]
      _ = start := hstart
  · simp [final, ops, Basic.execList, Basic.exec,
      bankRegisters, bankMap, countdown,
      regs.injective.eq_iff, hremaining]
  · calc
      final (bankRegisters regs).one =
          store (bankRegisters regs).one := by
        simp [final, ops, Basic.execList, Basic.exec,
          bankRegisters, bankMap, regs.injective.eq_iff]
      _ = 1 := hone
  · calc
      final (bankRegisters regs).base =
          store (bankRegisters regs).base := by
        simp [final, ops, Basic.execList, Basic.exec,
          bankRegisters, bankMap, regs.injective.eq_iff]
      _ = PackedLocalConfiguration.radix tm := hbase
  · calc
      final (bankRegisters regs).basePred =
          store (bankRegisters regs).basePred := by
        simp [final, ops, Basic.execList, Basic.exec,
          bankRegisters, bankMap, regs.injective.eq_iff]
      _ = PackedLocalConfiguration.radix tm - 1 := hbasePred
  · simp [final, ops, Basic.execList, Basic.exec,
      bankRegisters, bankMap, regs.injective.eq_iff, hblock]

theorem readCell_runs_internal
    (tm : TM workTapeCount)
    (tape : TapeIndex workTapeCount)
    (regs : NeighborhoodTrial.Registers controller)
    (store : Store)
    (blockLength word start remaining : ℕ)
    (hblock : store (Layout.blockLength regs) = blockLength)
    (hword : store (bankRegisters regs).word = word)
    (hstart : store (headOffset regs) = start)
    (hremaining : store (countdown regs) = remaining)
    (hone : store (bankRegisters regs).one = 1)
    (hbase :
      store (bankRegisters regs).base =
        PackedLocalConfiguration.radix tm)
    (hbasePred :
      store (bankRegisters regs).basePred =
        PackedLocalConfiguration.radix tm - 1) :
    ∃ final,
      Runs (readCell tape regs) store final ∧
      final (bankRegisters regs).word = word ∧
      final (symbolCode regs) =
        PackedDigits.digit (PackedLocalConfiguration.radix tm)
          word
          (PackedLocalConfiguration.cellIndex
            blockLength tape start) ∧
      final (headOffset regs) = start ∧
      final (countdown regs) = remaining ∧
      final (bankRegisters regs).one = 1 ∧
      final (bankRegisters regs).base =
        PackedLocalConfiguration.radix tm ∧
      final (bankRegisters regs).basePred =
        PackedLocalConfiguration.radix tm - 1 ∧
      final (Layout.blockLength regs) = blockLength := by
  obtain ⟨prepared, hprepareRun, hpreparedWord,
      hpreparedIndex, hpreparedStart, hpreparedRemaining,
      hpreparedOne, hpreparedBase, hpreparedBasePred,
      hpreparedBlock⟩ :=
    prepareCellIndex_runs tm tape regs store blockLength word
      start remaining hblock hword hstart hremaining hone hbase
      hbasePred
  obtain ⟨final, hreadRun, hfinalWord, hfinalBuffer,
      hfinalIndex, hfinalCompleted, hfinalResult, hfinalBase,
      hfinalBasePred, hfinalOne, hfinalReplacement⟩ :=
    NeighborhoodProgram.bankRead_runs (bankRegisters regs)
      prepared (PackedLocalConfiguration.radix tm) word
      (PackedLocalConfiguration.cellIndex blockLength tape start)
      (PackedLocalConfiguration.radix_pos tm) hpreparedWord
      hpreparedBase hpreparedBasePred hpreparedOne
      hpreparedIndex
  have hfinalCountdown :
      final (countdown regs) = remaining := by
    calc
      final (countdown regs) = prepared (countdown regs) :=
        Footprint.runs_eq_outside
          (NeighborhoodProgram.bankRead_sourceWritesWithin
            (bankRegisters regs))
          hreadRun (countdown_not_mem_bank regs)
      _ = remaining := hpreparedRemaining
  have hfinalBlock :
      final (Layout.blockLength regs) = blockLength := by
    calc
      final (Layout.blockLength regs) =
          prepared (Layout.blockLength regs) :=
        Footprint.runs_eq_outside
          (NeighborhoodProgram.bankRead_sourceWritesWithin
            (bankRegisters regs))
          hreadRun (blockLength_not_mem_bank regs)
      _ = blockLength := hpreparedBlock
  refine ⟨final, Runs.seq hprepareRun hreadRun,
    hfinalWord, hfinalResult, ?_, hfinalCountdown,
    hfinalOne, hfinalBase, hfinalBasePred, hfinalBlock⟩
  exact hfinalReplacement.trans hpreparedStart

theorem decodeCell_runs_internal
    (regs : NeighborhoodTrial.Registers controller)
    (store : Store)
    (digit word start remaining blockLength : ℕ)
    (hdigit : store (symbolCode regs) = digit)
    (hword : store (bankRegisters regs).word = word)
    (hstart : store (headOffset regs) = start)
    (hremaining : store (countdown regs) = remaining)
    (hblock : store (Layout.blockLength regs) = blockLength) :
    ∃ final,
      Runs (decodeCell regs) store final ∧
      final (bankRegisters regs).word = word ∧
      final (headOffset regs) = start ∧
      final (countdown regs) = remaining ∧
      final (symbolCode regs) = digit % 4 ∧
      final (cellDivision regs).quotient = digit / 4 ∧
      final (bankRegisters regs).one = 1 ∧
      final (Layout.blockLength regs) = blockLength := by
  let based :=
    (Basic.imm (bankRegisters regs).base 4).exec store
  have hdigit' :
      store (cellDivision regs).value = digit := by
    simpa [symbolCode, cellDivision] using hdigit
  have hbasedDigit :
      based (cellDivision regs).value = digit := by
    calc
      based (cellDivision regs).value =
          store (cellDivision regs).value := by
        simp [based, Basic.exec, cellDivision, bankRegisters,
          bankMap, regs.injective.eq_iff]
      _ = digit := hdigit'
  have hbasedDivisor :
      based (cellDivision regs).divisor = 4 := by
    change
      Function.update store (bankRegisters regs).base 4
        (bankRegisters regs).base = 4
    simp
  obtain ⟨final, hdivideRun, hpost⟩ :=
    ControlDecode.divRem_runs (cellDivision regs)
      based 4 digit (by omega) hbasedDigit hbasedDivisor
  have hrun : Runs (decodeCell regs) store final := by
    exact Runs.seq
      (Runs.basic
        (.imm (bankRegisters regs).base 4) store)
      hdivideRun
  refine ⟨final, hrun, ?_, ?_, ?_, hpost.value_eq,
    hpost.quotient_eq, hpost.one_eq, ?_⟩
  · calc
      final (bankRegisters regs).word =
          based (bankRegisters regs).word :=
        hpost.eq_outside _
          (bank_slot_not_mem_division regs 0
            ⟨by decide, by decide, by decide, by decide⟩)
      _ = store (bankRegisters regs).word := by
        simp [based, Basic.exec, bankRegisters, bankMap,
          regs.injective.eq_iff]
      _ = word := hword
  · calc
      final (headOffset regs) = based (headOffset regs) :=
        hpost.eq_outside _
          (bank_slot_not_mem_division regs 11
            ⟨by decide, by decide, by decide, by decide⟩)
      _ = store (headOffset regs) := by
        simp [based, Basic.exec, headOffset, bankRegisters,
          bankMap, regs.injective.eq_iff]
      _ = start := hstart
  · calc
      final (countdown regs) = based (countdown regs) :=
        hpost.eq_outside _ (countdown_not_mem_division regs)
      _ = store (countdown regs) := by
        simp [based, Basic.exec, countdown, bankRegisters,
          bankMap, regs.injective.eq_iff]
      _ = remaining := hremaining
  · calc
      final (Layout.blockLength regs) =
          based (Layout.blockLength regs) :=
        hpost.eq_outside _
          (by
            simp [ControlDecode.DivisionRegisters.writeFootprint,
              cellDivision, bankRegisters, bankMap,
              Layout.blockLength, regs.injective.eq_iff])
      _ = store (Layout.blockLength regs) := by
        simp [based, Basic.exec, Layout.blockLength,
          bankRegisters, bankMap, regs.injective.eq_iff]
      _ = blockLength := hblock

private theorem advance_runs
    (tm : TM workTapeCount)
    (regs : NeighborhoodTrial.Registers controller)
    (store : Store)
    (word start remaining blockLength : ℕ)
    (hword : store (bankRegisters regs).word = word)
    (hstart : store (headOffset regs) = start)
    (hremaining : store (countdown regs) = remaining)
    (hone : store (bankRegisters regs).one = 1)
    (hblock : store (Layout.blockLength regs) = blockLength) :
    ∃ final,
      Runs (advance tm regs) store final ∧
      final (bankRegisters regs).word = word ∧
      final (headOffset regs) = start + 1 ∧
      final (countdown regs) = remaining - 1 ∧
      final (bankRegisters regs).one = 1 ∧
      final (bankRegisters regs).base =
        PackedLocalConfiguration.radix tm ∧
      final (bankRegisters regs).basePred =
        PackedLocalConfiguration.radix tm - 1 ∧
      final (Layout.blockLength regs) = blockLength := by
  let ops : List Basic :=
    [.imm (regs.index 1)
        (PackedLocalConfiguration.radix tm),
      .imm (regs.index 4)
        (PackedLocalConfiguration.radix tm - 1),
      .add (regs.index 29) (regs.index 29)
        (regs.index 9),
      .sub (regs.index 30) (regs.index 30)
        (regs.index 9)]
  let final := Basic.execList ops store
  have hwordPhysical : store (regs.index 32) = word := by
    simpa [bankRegisters, bankMap] using hword
  have hstartPhysical : store (regs.index 29) = start := by
    simpa [headOffset, bankRegisters, bankMap] using hstart
  have hremainingPhysical :
      store (regs.index 30) = remaining := hremaining
  have honePhysical : store (regs.index 9) = 1 := by
    simpa [bankRegisters, bankMap] using hone
  have hblockPhysical :
      store (regs.index 2) = blockLength := hblock
  refine ⟨final, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simpa [advance, ops, bankRegisters, bankMap, countdown]
      using basics_runs ops store
  · change final (regs.index 32) = word
    simp [final, ops, Basic.execList, Basic.exec,
      regs.injective.eq_iff, hwordPhysical]
  · change final (regs.index 29) = start + 1
    simp [final, ops, Basic.execList, Basic.exec,
      regs.injective.eq_iff, hstartPhysical, honePhysical]
  · change final (regs.index 30) = remaining - 1
    simp [final, ops, Basic.execList, Basic.exec,
      regs.injective.eq_iff, hremainingPhysical, honePhysical]
  · change final (regs.index 9) = 1
    simp [final, ops, Basic.execList, Basic.exec,
      regs.injective.eq_iff, honePhysical]
  · change final (regs.index 1) =
      PackedLocalConfiguration.radix tm
    simp [final, ops, Basic.execList, Basic.exec,
      regs.injective.eq_iff]
  · change final (regs.index 4) =
      PackedLocalConfiguration.radix tm - 1
    simp [final, ops, Basic.execList, Basic.exec,
      regs.injective.eq_iff]
  · change final (regs.index 2) = blockLength
    simp [final, ops, Basic.execList, Basic.exec,
      regs.injective.eq_iff, hblockPhysical]

private theorem scanLoop_runs
    (tm : TM workTapeCount)
    (tape : TapeIndex workTapeCount)
    (regs : NeighborhoodTrial.Registers controller)
    (word blockLength target start distance remaining : ℕ)
    (store : Store)
    (hword : store (bankRegisters regs).word = word)
    (hblock : store (Layout.blockLength regs) = blockLength)
    (hbase :
      store (bankRegisters regs).base =
        PackedLocalConfiguration.radix tm)
    (hbasePred :
      store (bankRegisters regs).basePred =
        PackedLocalConfiguration.radix tm - 1)
    (hone : store (bankRegisters regs).one = 1)
    (hstart : store (headOffset regs) = start)
    (hremaining : store (countdown regs) = remaining)
    (htarget : target = start + distance)
    (hdistance : distance < remaining)
    (hspan :
      start + remaining =
        PackedLocalConfiguration.tapeSpan blockLength)
    (hmarker :
      ∀ localPosition,
        localPosition <
          PackedLocalConfiguration.tapeSpan blockLength →
        PackedLocalConfiguration.markerPart
            (PackedDigits.digit
              (PackedLocalConfiguration.radix tm) word
              (PackedLocalConfiguration.cellIndex
                blockLength tape localPosition)) =
          if localPosition = target then 1 else 0) :
    ∃ final,
      Runs
        (.whileNonzero (countdown regs)
          (step tm tape regs))
        store final ∧
      final (bankRegisters regs).word = word ∧
      final (headOffset regs) = target ∧
      final (symbolCode regs) =
        PackedLocalConfiguration.symbolPart
          (PackedDigits.digit
            (PackedLocalConfiguration.radix tm) word
            (PackedLocalConfiguration.cellIndex
              blockLength tape target)) ∧
      final (countdown regs) = 0 := by
  induction distance generalizing store start remaining with
  | zero =>
      have hremainingNonzero :
          store (countdown regs) ≠ 0 := by
        rw [hremaining]
        omega
      have htargetStart : target = start := by
        simpa using htarget
      have hstartSpan :
          start <
            PackedLocalConfiguration.tapeSpan blockLength := by
        omega
      let digit :=
        PackedDigits.digit
          (PackedLocalConfiguration.radix tm) word
          (PackedLocalConfiguration.cellIndex
            blockLength tape start)
      obtain ⟨read, hreadRun, hreadWord, hreadDigit,
          hreadStart, hreadRemaining, hreadOne, hreadBase,
          hreadBasePred, hreadBlock⟩ :=
        readCell_runs_internal tm tape regs store blockLength word start
          remaining hblock hword hstart hremaining hone hbase
          hbasePred
      obtain ⟨decoded, hdecodeRun, hdecodedWord,
          hdecodedStart, hdecodedRemaining, hdecodedSymbol,
          hdecodedQuotient, hdecodedOne, hdecodedBlock⟩ :=
        decodeCell_runs_internal regs read digit word start remaining
          blockLength hreadDigit hreadWord hreadStart
          hreadRemaining hreadBlock
      have hdigitMarker : digit / 4 = 1 := by
        have hmarkerStart := hmarker start hstartSpan
        simpa [digit, PackedLocalConfiguration.markerPart,
          htargetStart] using hmarkerStart
      have hdecodedMarkerNonzero :
          decoded (cellDivision regs).quotient ≠ 0 := by
        rw [hdecodedQuotient, hdigitMarker]
        omega
      let stopped :=
        (Basic.imm (countdown regs) 0).exec decoded
      have hstopRun :
          Runs
            (.basic (.imm (countdown regs) 0))
            decoded stopped := by
        exact Runs.basic _ _
      have hbranch :
          Runs
            (.ifZero (cellDivision regs).quotient
              (advance tm regs)
              (.basic (.imm (countdown regs) 0)))
            decoded stopped :=
        Runs.ifNonzero hdecodedMarkerNonzero hstopRun
      have hbody :
          Runs (step tm tape regs) store stopped := by
        simpa [step, Cmd.seqList] using
          Runs.seq hreadRun (Runs.seq hdecodeRun hbranch)
      have hstoppedWord :
          stopped (bankRegisters regs).word = word := by
        calc
          stopped (bankRegisters regs).word =
              decoded (bankRegisters regs).word := by
            simp [stopped, Basic.exec, bankRegisters, bankMap,
              countdown, regs.injective.eq_iff]
          _ = word := hdecodedWord
      have hstoppedHead :
          stopped (headOffset regs) = target := by
        calc
          stopped (headOffset regs) =
              decoded (headOffset regs) := by
            simp [stopped, Basic.exec, headOffset,
              bankRegisters, bankMap, countdown,
              regs.injective.eq_iff]
          _ = start := hdecodedStart
          _ = target := htargetStart.symm
      have hstoppedSymbol :
          stopped (symbolCode regs) =
            PackedLocalConfiguration.symbolPart
              (PackedDigits.digit
                (PackedLocalConfiguration.radix tm) word
                (PackedLocalConfiguration.cellIndex
                  blockLength tape target)) := by
        calc
          stopped (symbolCode regs) =
              decoded (symbolCode regs) := by
            simp [stopped, Basic.exec, symbolCode,
              bankRegisters, bankMap, countdown,
              regs.injective.eq_iff]
          _ = digit % 4 := hdecodedSymbol
          _ =
              PackedLocalConfiguration.symbolPart
                (PackedDigits.digit
                  (PackedLocalConfiguration.radix tm) word
                  (PackedLocalConfiguration.cellIndex
                    blockLength tape target)) := by
            simp [PackedLocalConfiguration.symbolPart, digit,
              htargetStart]
      have hstoppedCountdown :
          stopped (countdown regs) = 0 := by
        simp [stopped, Basic.exec]
      refine
        ⟨stopped,
          Runs.whileNonzero hremainingNonzero hbody
            (Runs.whileZero hstoppedCountdown),
          hstoppedWord, hstoppedHead, hstoppedSymbol,
          hstoppedCountdown⟩
  | succ distance ih =>
      have hremainingNonzero :
          store (countdown regs) ≠ 0 := by
        rw [hremaining]
        omega
      have hstartSpan :
          start <
            PackedLocalConfiguration.tapeSpan blockLength := by
        omega
      have hstartNeTarget : start ≠ target := by
        omega
      let digit :=
        PackedDigits.digit
          (PackedLocalConfiguration.radix tm) word
          (PackedLocalConfiguration.cellIndex
            blockLength tape start)
      obtain ⟨read, hreadRun, hreadWord, hreadDigit,
          hreadStart, hreadRemaining, hreadOne, hreadBase,
          hreadBasePred, hreadBlock⟩ :=
        readCell_runs_internal tm tape regs store blockLength word start
          remaining hblock hword hstart hremaining hone hbase
          hbasePred
      obtain ⟨decoded, hdecodeRun, hdecodedWord,
          hdecodedStart, hdecodedRemaining, hdecodedSymbol,
          hdecodedQuotient, hdecodedOne, hdecodedBlock⟩ :=
        decodeCell_runs_internal regs read digit word start remaining
          blockLength hreadDigit hreadWord hreadStart
          hreadRemaining hreadBlock
      have hdigitMarker : digit / 4 = 0 := by
        have hmarkerStart := hmarker start hstartSpan
        simpa [digit, PackedLocalConfiguration.markerPart,
          hstartNeTarget] using hmarkerStart
      have hdecodedMarkerZero :
          decoded (cellDivision regs).quotient = 0 := by
        rw [hdecodedQuotient, hdigitMarker]
      obtain ⟨advanced, hadvanceRun, hadvancedWord,
          hadvancedStart, hadvancedRemaining, hadvancedOne,
          hadvancedBase, hadvancedBasePred, hadvancedBlock⟩ :=
        advance_runs tm regs decoded word start remaining
          blockLength hdecodedWord hdecodedStart
          hdecodedRemaining hdecodedOne hdecodedBlock
      have hbranch :
          Runs
            (.ifZero (cellDivision regs).quotient
              (advance tm regs)
              (.basic (.imm (countdown regs) 0)))
            decoded advanced :=
        Runs.ifZero hdecodedMarkerZero hadvanceRun
      have hbody :
          Runs (step tm tape regs) store advanced := by
        simpa [step, Cmd.seqList] using
          Runs.seq hreadRun (Runs.seq hdecodeRun hbranch)
      have hnextTarget :
          target = start + 1 + distance := by
        omega
      have hnextDistance :
          distance < remaining - 1 := by
        omega
      have hnextSpan :
          start + 1 + (remaining - 1) =
            PackedLocalConfiguration.tapeSpan blockLength := by
        omega
      obtain ⟨final, hloopRun, hfinalWord, hfinalHead,
          hfinalSymbol, hfinalCountdown⟩ :=
        ih (store := advanced) (start := start + 1)
          (remaining := remaining - 1)
          hadvancedWord hadvancedBlock hadvancedBase
          hadvancedBasePred hadvancedOne hadvancedStart
          hadvancedRemaining hnextTarget hnextDistance hnextSpan
      exact
        ⟨final,
          Runs.whileNonzero hremainingNonzero hbody hloopRun,
          hfinalWord, hfinalHead, hfinalSymbol, hfinalCountdown⟩

theorem scan_runs_represents_internal
    (tm : TM workTapeCount)
    (order :
      NeighborhoodExecutableEvaluation.FiniteEncoding.StateOrder tm)
    (blockLength : ℕ) (hpositive : 0 < blockLength)
    (centers : TapeIndex workTapeCount → ℕ)
    (cfg : Cfg workTapeCount tm.Q)
    (tape : TapeIndex workTapeCount)
    (suffix word : ℕ)
    (regs : NeighborhoodTrial.Registers controller)
    (store : Store)
    (hblock : store (Layout.blockLength regs) = blockLength)
    (hword :
      store (bankRegisters regs).word = word)
    (hrep :
      PackedLocalRepresentation.Represents
        tm order blockLength centers cfg suffix word)
    (hrangeOne :
      store (CombineValue.rangeRegisters regs).one = 1)
    (hlower :
      PackedLocalConfiguration.windowStart
          blockLength (centers tape) ≤
        (tapeAt cfg tape).head)
    (hupper :
      (tapeAt cfg tape).head <
        PackedLocalConfiguration.windowStart
            blockLength (centers tape) +
          PackedLocalConfiguration.tapeSpan blockLength) :
    ∃ final,
      Runs (scan tm tape regs) store final ∧
      Post tm blockLength centers cfg tape
        word regs store final ∧
      PreservesCombine regs store final := by
  let target :=
    PackedLocalConfiguration.localHead blockLength
      (centers tape) (tapeAt cfg tape).head
  have htargetSpan :
      target <
        PackedLocalConfiguration.tapeSpan blockLength := by
    dsimp only [target]
    simp only [PackedLocalConfiguration.localHead]
    omega
  obtain ⟨initialized, hinitializeRun, hinitializedWord,
      hinitializedBase, hinitializedBasePred, hinitializedOne,
      hinitializedHead, hinitializedCountdown⟩ :=
    initializeScan_runs tm regs store blockLength word hblock
      hword
  have hinitializedBlock :
      initialized (Layout.blockLength regs) = blockLength := by
    calc
      initialized (Layout.blockLength regs) =
          store (Layout.blockLength regs) :=
        Footprint.runs_eq_outside
          (initializeScan_writesWithin tm regs)
          hinitializeRun
          (fixed_index_not_mem regs 2 (by
            constructor
            · intro slot
              fin_cases slot <;> decide
            · decide))
      _ = blockLength := hblock
  obtain ⟨looped, hloopRun, hloopedWord, hloopedHead,
      hloopedSymbol, hloopedCountdown⟩ :=
    scanLoop_runs tm tape regs word blockLength target 0 target
      (PackedLocalConfiguration.tapeSpan blockLength)
      initialized hinitializedWord hinitializedBlock
      hinitializedBase hinitializedBasePred hinitializedOne
      hinitializedHead hinitializedCountdown
      (by omega) htargetSpan (by omega)
      (by
        intro localPosition hlocal
        exact represented_marker tm order blockLength hpositive
          centers cfg tape suffix word localPosition hrep hlocal
          hlower)
  let final :=
    (Basic.imm (CombineValue.rangeRegisters regs).one 1).exec
      looped
  have hrestoreRun :
      Runs
        (.basic
          (.imm (CombineValue.rangeRegisters regs).one 1))
        looped final := by
    exact Runs.basic _ _
  have hrun : Runs (scan tm tape regs) store final := by
    simpa [scan, Cmd.seqList] using
      Runs.seq hinitializeRun (Runs.seq hloopRun hrestoreRun)
  have hfinalWord :
      final (bankRegisters regs).word = word := by
    calc
      final (bankRegisters regs).word =
          looped (bankRegisters regs).word := by
        simp [final, Basic.exec, CombineValue.rangeRegisters,
          bankRegisters, bankMap, regs.injective.eq_iff]
      _ = word := hloopedWord
  have hfinalHead :
      final (headOffset regs) = target := by
    calc
      final (headOffset regs) =
          looped (headOffset regs) := by
        simp [final, Basic.exec, CombineValue.rangeRegisters,
          headOffset, bankRegisters, bankMap,
          regs.injective.eq_iff]
      _ = target := hloopedHead
  have hfinalSymbol :
      final (symbolCode regs) =
        CompactValueCodeSemantics.gammaCode
          ((tapeAt cfg tape).cells (tapeAt cfg tape).head) := by
    calc
      final (symbolCode regs) =
          looped (symbolCode regs) := by
        simp [final, Basic.exec, CombineValue.rangeRegisters,
          symbolCode, bankRegisters, bankMap,
          regs.injective.eq_iff]
      _ =
          PackedLocalConfiguration.symbolPart
            (PackedDigits.digit
              (PackedLocalConfiguration.radix tm) word
              (PackedLocalConfiguration.cellIndex
                blockLength tape target)) :=
        hloopedSymbol
      _ =
          CompactValueCodeSemantics.gammaCode
            ((tapeAt cfg tape).cells
              (PackedLocalConfiguration.absolutePosition blockLength
                (centers tape) target)) := by
        exact represented_symbol tm order blockLength hpositive
          centers cfg tape suffix word target hrep htargetSpan
      _ =
          CompactValueCodeSemantics.gammaCode
            ((tapeAt cfg tape).cells (tapeAt cfg tape).head) := by
        rw [show
          PackedLocalConfiguration.absolutePosition blockLength
              (centers tape) target =
            (tapeAt cfg tape).head by
          exact target_absolutePosition blockLength (centers tape)
            (tapeAt cfg tape).head hlower]
  have hfinalCountdown :
      final (countdown regs) = 0 := by
    calc
      final (countdown regs) =
          looped (countdown regs) := by
        simp [final, Basic.exec, CombineValue.rangeRegisters,
          countdown, regs.injective.eq_iff]
      _ = 0 := hloopedCountdown
  have hfinalRangeOne :
      final (CombineValue.rangeRegisters regs).one =
        store (CombineValue.rangeRegisters regs).one := by
    simp [final, Basic.exec, hrangeOne]
  refine ⟨final, hrun, ?_, ?_⟩
  · exact
      { head_eq := by simpa [target] using hfinalHead
        symbol_eq := hfinalSymbol
        word_eq := hfinalWord
        countdown_eq := hfinalCountdown
        rangeOne_eq := hfinalRangeOne
        eq_outside := fun address haddress =>
          Footprint.runs_eq_outside
            (scan_writesWithin_internal tm tape regs)
            hrun haddress }
  · exact scan_preservesCombine_internal tm tape regs
      hrangeOne hrun

/-- Canonical-constructor specialization of the mutable-representation
execution theorem. -/
theorem scan_runs_internal
    (tm : TM workTapeCount)
    (order :
      NeighborhoodExecutableEvaluation.FiniteEncoding.StateOrder tm)
    (blockLength : ℕ) (hpositive : 0 < blockLength)
    (centers : TapeIndex workTapeCount → ℕ)
    (cfg : Cfg workTapeCount tm.Q)
    (tape : TapeIndex workTapeCount)
    (suffix : ℕ)
    (regs : NeighborhoodTrial.Registers controller)
    (store : Store)
    (hblock : store (Layout.blockLength regs) = blockLength)
    (hword :
      store (bankRegisters regs).word =
        PackedLocalConfiguration.encodeAbove
          tm order blockLength centers cfg suffix)
    (hrangeOne :
      store (CombineValue.rangeRegisters regs).one = 1)
    (hlower :
      PackedLocalConfiguration.windowStart
          blockLength (centers tape) ≤
        (tapeAt cfg tape).head)
    (hupper :
      (tapeAt cfg tape).head <
        PackedLocalConfiguration.windowStart
            blockLength (centers tape) +
          PackedLocalConfiguration.tapeSpan blockLength) :
    ∃ final,
      Runs (scan tm tape regs) store final ∧
      Post tm blockLength centers cfg tape
        (PackedLocalConfiguration.encodeAbove
          tm order blockLength centers cfg suffix)
        regs store final ∧
      PreservesCombine regs store final :=
  scan_runs_represents_internal tm order blockLength hpositive
    centers cfg tape suffix
    (PackedLocalConfiguration.encodeAbove
      tm order blockLength centers cfg suffix)
    regs store hblock hword
    (PackedLocalRepresentation.encodeAbove_represents
      tm order blockLength centers cfg suffix)
    hrangeOne hlower hupper

end Internal
end PackedLocalHeadScan
end NeighborhoodMicrocode
end Runtime
end TimeSpaceSimulation
end Complexity
