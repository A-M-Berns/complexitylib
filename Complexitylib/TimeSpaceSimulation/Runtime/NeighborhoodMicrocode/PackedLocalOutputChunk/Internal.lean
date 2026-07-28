/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/
import
  Complexitylib.TimeSpaceSimulation.Runtime.NeighborhoodMicrocode.PackedLocalOutputChunk.Defs
import
  Complexitylib.TimeSpaceSimulation.Runtime.NeighborhoodMicrocode.AssignmentPayloadBit
import
  Complexitylib.TimeSpaceSimulation.Runtime.NeighborhoodMicrocode.CombineSafeCenter
import
  Complexitylib.TimeSpaceSimulation.Runtime.NeighborhoodMicrocode.PackedLocalHeadScan
import
  Complexitylib.TimeSpaceSimulation.Runtime.NeighborhoodMicrocode.PackedLocalRepresentation
import
  Complexitylib.TimeSpaceSimulation.Runtime.NeighborhoodMicrocode.PackedLocalStep
import
  Complexitylib.TimeSpaceSimulation.Runtime.NeighborhoodMicrocode.PackedOutputChunkSemantics
import
  Complexitylib.TimeSpaceSimulation.Runtime.NeighborhoodMicrocode.FrameBounds
import
  Complexitylib.TimeSpaceSimulation.Runtime.NeighborhoodMicrocode.Representation

/-!
# Executable packed local output chunks -- proofs
-/

namespace Complexity
namespace TimeSpaceSimulation
namespace Runtime
namespace NeighborhoodMicrocode
namespace PackedLocalOutputChunk
namespace Internal

open RAM Structured
open NeighborhoodGraph

variable {controller : SearchProgram.Registers}

private theorem cmdWritesWithin_mono
    {small large : Finset ℕ} {command : Cmd}
    (hwrites : Footprint.CmdWritesWithin small command)
    (hsubset : small ⊆ large) :
    Footprint.CmdWritesWithin large command := by
  induction command with
  | skip =>
      trivial
  | basic operation =>
      cases operation <;>
        simp only [Footprint.CmdWritesWithin,
          Footprint.BasicWritesWithin] at hwrites ⊢
      all_goals exact hsubset hwrites
  | seq first second ihFirst ihSecond =>
      exact ⟨ihFirst hwrites.1, ihSecond hwrites.2⟩
  | ifZero test onZero onNonzero ihZero ihNonzero =>
      exact ⟨ihZero hwrites.1, ihNonzero hwrites.2⟩
  | whileNonzero test body ih =>
      exact ih hwrites

private theorem bank_footprint_subset_step
    (regs : NeighborhoodTrial.Registers controller) :
    (bankRegisters regs).footprint ⊆
      PackedLocalStep.footprint regs := by
  intro address haddress
  simp only [NeighborhoodProgram.BankRegisters.footprint,
    Finset.mem_image, Finset.mem_univ, true_and] at haddress
  obtain ⟨slot, rfl⟩ := haddress
  apply Finset.mem_image.mpr
  fin_cases slot <;>
    first
    | exact ⟨(0 : Fin 17), Finset.mem_univ _, rfl⟩
    | exact ⟨(1 : Fin 17), Finset.mem_univ _, rfl⟩
    | exact ⟨(2 : Fin 17), Finset.mem_univ _, rfl⟩
    | exact ⟨(3 : Fin 17), Finset.mem_univ _, rfl⟩
    | exact ⟨(4 : Fin 17), Finset.mem_univ _, rfl⟩
    | exact ⟨(5 : Fin 17), Finset.mem_univ _, rfl⟩
    | exact ⟨(7 : Fin 17), Finset.mem_univ _, rfl⟩
    | exact ⟨(8 : Fin 17), Finset.mem_univ _, rfl⟩
    | exact ⟨(9 : Fin 17), Finset.mem_univ _, rfl⟩
    | exact ⟨(12 : Fin 17), Finset.mem_univ _, rfl⟩
    | exact ⟨(13 : Fin 17), Finset.mem_univ _, rfl⟩
    | exact ⟨(16 : Fin 17), Finset.mem_univ _, rfl⟩

private theorem headScan_footprint_subset_step
    (regs : NeighborhoodTrial.Registers controller) :
    PackedLocalHeadScan.footprint regs ⊆
      PackedLocalStep.footprint regs := by
  intro address haddress
  simp only [PackedLocalHeadScan.footprint, Finset.mem_union,
    Finset.mem_singleton] at haddress
  rcases haddress with hbank | hcountdown
  · exact bank_footprint_subset_step regs hbank
  · rw [hcountdown]
    apply Finset.mem_image.mpr
    exact ⟨(14 : Fin 17), Finset.mem_univ _, rfl⟩

private theorem step_slot_mem
    (regs : NeighborhoodTrial.Registers controller)
    (slot : Fin 17) :
    regs.index (PackedLocalStep.writeMap slot) ∈
      PackedLocalStep.footprint regs :=
  Finset.mem_image.mpr ⟨slot, Finset.mem_univ _, rfl⟩

private theorem copy_writesWithin
    (regs : NeighborhoodTrial.Registers controller)
    (destination source : ℕ)
    (hdestination :
      destination ∈ PackedLocalStep.footprint regs) :
    Footprint.CmdWritesWithin (PackedLocalStep.footprint regs)
      (copy destination source) :=
  ⟨hdestination, hdestination⟩

private theorem seqList_writesWithin
    (commands : List Cmd) (footprint : Finset ℕ)
    (hcommands :
      ∀ command ∈ commands,
        Footprint.CmdWritesWithin footprint command) :
    Footprint.CmdWritesWithin footprint
      (Cmd.seqList commands) := by
  induction commands with
  | nil =>
      trivial
  | cons first rest ih =>
      cases rest with
      | nil =>
          exact hcommands first (by simp)
      | cons second rest =>
          exact
            ⟨hcommands first (by simp),
              ih (by
                intro command hcommand
                exact hcommands command (by simp [hcommand]))⟩

private theorem basics_runs (ops : List Basic) (store : Store) :
    Runs (Cmd.basics ops) store (Basic.execList ops store) := by
  obtain ⟨cost, space, hexec⟩ :=
    RAM.Structured.Internal.exec_basics_exists ops store
  exact ⟨ops.length, cost, space, hexec⟩

private theorem copy_runs
    (destination source : ℕ) (store : Store)
    (hne : destination ≠ source) :
    ∃ final,
      Runs (copy destination source) store final ∧
      final destination = store source ∧
      ∀ address, address ≠ destination →
        final address = store address := by
  let middle := (Basic.imm destination 0).exec store
  let final := (Basic.add destination source destination).exec middle
  refine ⟨final, ?_, ?_, ?_⟩
  · exact Runs.seq (Runs.basic _ _) (Runs.basic _ _)
  · simp [final, middle, Basic.exec, Ne.symm hne]
  · intro address haddress
    simp [final, middle, Basic.exec, Function.update_of_ne,
      haddress]

private theorem equalValues_runs
    (regs : NeighborhoodTrial.Registers controller)
    (left right output : ℕ) (store : Store)
    (leftValue rightValue : ℕ)
    (hleft : store left = leftValue)
    (hright : store right = rightValue)
    (htestLeft : (bankRegisters regs).test ≠ left)
    (htestRight : (bankRegisters regs).test ≠ right)
    (htestQuotient :
      (bankRegisters regs).test ≠
        (bankRegisters regs).quotient) :
    ∃ final,
      Runs (equalValues regs left right output) store final ∧
      final output =
        (if leftValue = rightValue then 1 else 0) ∧
      ∀ address,
        address ≠ (bankRegisters regs).test →
        address ≠ (bankRegisters regs).quotient →
        address ≠ output →
        final address = store address := by
  let afterLeft :=
    (Basic.sub (bankRegisters regs).test left right).exec store
  let afterRight :=
    (Basic.sub (bankRegisters regs).quotient right left).exec
      afterLeft
  let compared :=
    (Basic.add output (bankRegisters regs).test
      (bankRegisters regs).quotient).exec afterRight
  have hafterLeft :
      afterLeft (bankRegisters regs).test =
        leftValue - rightValue := by
    simp [afterLeft, Basic.exec, hleft, hright]
  have hafterRightTest :
      afterRight (bankRegisters regs).test =
        leftValue - rightValue := by
    simp [afterRight, Basic.exec, Function.update_of_ne,
      htestQuotient, hafterLeft]
  have hafterRightQuotient :
      afterRight (bankRegisters regs).quotient =
        rightValue - leftValue := by
    simp [afterRight, afterLeft, Basic.exec,
      Function.update_of_ne, htestLeft.symm,
      htestRight.symm, hleft, hright]
  have hcompared :
      compared output =
        (leftValue - rightValue) +
          (rightValue - leftValue) := by
    simp [compared, Basic.exec, hafterRightTest,
      hafterRightQuotient]
  by_cases heq : leftValue = rightValue
  · have hzero : compared output = 0 := by
      rw [hcompared, heq]
      simp
    let final := (Basic.imm output 1).exec compared
    have hbranch :
        Runs
          (.ifZero output
            (.basic (.imm output 1))
            (.basic (.imm output 0)))
          compared final :=
      Runs.ifZero hzero (Runs.basic _ _)
    refine ⟨final, ?_, ?_, ?_⟩
    · simpa [equalValues, Cmd.seqList] using
        Runs.seq
          (Runs.basic
            (.sub (bankRegisters regs).test left right) store)
          (Runs.seq
            (Runs.basic
              (.sub (bankRegisters regs).quotient right left)
              afterLeft)
            (Runs.seq
              (Runs.basic
                (.add output (bankRegisters regs).test
                  (bankRegisters regs).quotient)
                afterRight)
              hbranch))
    · simp [final, Basic.exec, heq]
    · intro address haddressTest haddressQuotient haddressOutput
      simp [final, compared, afterRight, afterLeft, Basic.exec,
        Function.update_of_ne, haddressTest, haddressQuotient,
        haddressOutput]
  · have hnonzero : compared output ≠ 0 := by
      rw [hcompared]
      omega
    let final := (Basic.imm output 0).exec compared
    have hbranch :
        Runs
          (.ifZero output
            (.basic (.imm output 1))
            (.basic (.imm output 0)))
          compared final :=
      Runs.ifNonzero hnonzero (Runs.basic _ _)
    refine ⟨final, ?_, ?_, ?_⟩
    · simpa [equalValues, Cmd.seqList] using
        Runs.seq
          (Runs.basic
            (.sub (bankRegisters regs).test left right) store)
          (Runs.seq
            (Runs.basic
              (.sub (bankRegisters regs).quotient right left)
              afterLeft)
            (Runs.seq
              (Runs.basic
                (.add output (bankRegisters regs).test
                  (bankRegisters regs).quotient)
                afterRight)
              hbranch))
    · simp [final, Basic.exec, heq]
    · intro address haddressTest haddressQuotient haddressOutput
      simp [final, compared, afterRight, afterLeft, Basic.exec,
        Function.update_of_ne, haddressTest, haddressQuotient,
        haddressOutput]

private theorem prepareCoordinate_runs
    (regs : NeighborhoodTrial.Registers controller)
    (store : Store) (cursor width bitsLeft : ℕ)
    (hcursor : store (Layout.active regs) = cursor)
    (hwidth : store (chunkBits regs) = width)
    (hremaining : store (remaining regs) = bitsLeft) :
    ∃ final,
      Runs (prepareCoordinate regs) store final ∧
      final (coordinate regs) =
        cursor * width + width - bitsLeft ∧
      ∀ address, address ≠ coordinate regs →
        final address = store address := by
  let ops : List Basic :=
    [.imm (coordinate regs) 0,
      .add (coordinate regs) (Layout.active regs)
        (coordinate regs),
      .mul (coordinate regs) (coordinate regs)
        (chunkBits regs),
      .add (coordinate regs) (coordinate regs)
        (chunkBits regs),
      .sub (coordinate regs) (coordinate regs)
        (remaining regs)]
  let final := Basic.execList ops store
  have hcoordinate_ne_active :
      coordinate regs ≠ Layout.active regs :=
    regs.injective.ne (by decide)
  have hcoordinate_ne_width :
      coordinate regs ≠ chunkBits regs :=
    regs.injective.ne (by decide)
  have hcoordinate_ne_remaining :
      coordinate regs ≠ remaining regs :=
    regs.injective.ne (by decide)
  have hactive_ne_coordinate :
      Layout.active regs ≠ coordinate regs :=
    hcoordinate_ne_active.symm
  have hwidth_ne_coordinate :
      chunkBits regs ≠ coordinate regs :=
    hcoordinate_ne_width.symm
  have hremaining_ne_coordinate :
      remaining regs ≠ coordinate regs :=
    hcoordinate_ne_remaining.symm
  refine ⟨final, ?_, ?_, ?_⟩
  · simpa [prepareCoordinate, Cmd.basics, ops] using
      basics_runs ops store
  · simp [final, ops, Basic.execList, Basic.exec,
      Function.update_of_ne, hactive_ne_coordinate,
      hwidth_ne_coordinate, hremaining_ne_coordinate,
      hcursor, hwidth, hremaining]
  · intro address haddress
    simp [final, ops, Basic.execList, Basic.exec,
      Function.update_of_ne, haddress]

private theorem initializeBank_runs
    (tm : TM workTapeCount)
    (regs : NeighborhoodTrial.Registers controller)
    (store : Store) :
    ∃ final,
      Runs (initializeBank tm regs) store final ∧
      final (bankRegisters regs).base =
        PackedLocalConfiguration.radix tm ∧
      final (bankRegisters regs).basePred =
        PackedLocalConfiguration.radix tm - 1 ∧
      final (bankRegisters regs).one = 1 ∧
      ∀ address,
        address ≠ (bankRegisters regs).base →
        address ≠ (bankRegisters regs).basePred →
        address ≠ (bankRegisters regs).one →
        final address = store address := by
  let ops : List Basic :=
    [.imm (bankRegisters regs).base
        (PackedLocalConfiguration.radix tm),
      .imm (bankRegisters regs).basePred
        (PackedLocalConfiguration.radix tm - 1),
      .imm (bankRegisters regs).one 1]
  let final := Basic.execList ops store
  refine ⟨final, ?_, ?_, ?_, ?_, ?_⟩
  · simpa [initializeBank, Cmd.basics, ops] using
      basics_runs ops store
  · simp [final, ops, Basic.execList, Basic.exec,
      (bankRegisters regs).index_ne (by decide : (2 : Fin 12) ≠ 3),
      (bankRegisters regs).index_ne (by decide : (2 : Fin 12) ≠ 6)]
  · simp [final, ops, Basic.execList, Basic.exec,
      (bankRegisters regs).index_ne (by decide : (3 : Fin 12) ≠ 6)]
  · simp [final, ops, Basic.execList, Basic.exec]
  · intro address hbase hbasePred hone
    simp [final, ops, Basic.execList, Basic.exec,
      Function.update_of_ne, hbase, hbasePred, hone]

private theorem readState_writesWithin
    (tm : TM workTapeCount)
    (regs : NeighborhoodTrial.Registers controller) :
    Footprint.CmdWritesWithin (bankRegisters regs).footprint
      (readState tm regs) := by
  have hinitialize :
      Footprint.CmdWritesWithin (bankRegisters regs).footprint
        (initializeBank tm regs) := by
    simp only [initializeBank, Cmd.basics]
    exact
      ⟨(bankRegisters regs).index_mem_footprint 2,
        (bankRegisters regs).index_mem_footprint 3,
        (bankRegisters regs).index_mem_footprint 6⟩
  simp only [readState, Cmd.seqList,
    Footprint.CmdWritesWithin, Footprint.BasicWritesWithin]
  exact
    ⟨hinitialize,
      (bankRegisters regs).index_mem_footprint 8,
      NeighborhoodProgram.bankRead_sourceWritesWithin
        (bankRegisters regs),
      (bankRegisters regs).index_mem_footprint 9⟩

private theorem readState_runs
    (tm : TM workTapeCount)
    (regs : NeighborhoodTrial.Registers controller)
    (store : Store) (word currentCoordinate : ℕ)
    (hword : store (bankRegisters regs).word = word)
    (hcoordinate :
      store (coordinate regs) = currentCoordinate) :
    ∃ final,
      Runs (readState tm regs) store final ∧
      final (bankRegisters regs).word = word ∧
      final (bitValue regs) =
        PackedDigits.digit
          (PackedLocalConfiguration.radix tm) word 0 ∧
      final (coordinate regs) = currentCoordinate ∧
      final (CombineValue.rangeRegisters regs).one = 1 ∧
      ∀ address, address ∉ (bankRegisters regs).footprint →
        final address = store address := by
  obtain ⟨initialized, hinitialize, hbase, hbasePred, hone,
      hinitializeOutside⟩ :=
    initializeBank_runs tm regs store
  let indexed :=
    (Basic.imm (bankRegisters regs).indexCount 0).exec initialized
  have hindexedWord :
      indexed (bankRegisters regs).word = word := by
    simp [indexed, Basic.exec,
      (bankRegisters regs).index_ne
        (by decide : (0 : Fin 12) ≠ 8),
      hinitializeOutside _ ((bankRegisters regs).index_ne
        (by decide : (0 : Fin 12) ≠ 2))
        ((bankRegisters regs).index_ne
          (by decide : (0 : Fin 12) ≠ 3))
        ((bankRegisters regs).index_ne
          (by decide : (0 : Fin 12) ≠ 6)),
      hword]
  have hindexedBase :
      indexed (bankRegisters regs).base =
        PackedLocalConfiguration.radix tm := by
    simp [indexed, Basic.exec,
      (bankRegisters regs).index_ne
        (by decide : (2 : Fin 12) ≠ 8), hbase]
  have hindexedBasePred :
      indexed (bankRegisters regs).basePred =
        PackedLocalConfiguration.radix tm - 1 := by
    simp [indexed, Basic.exec,
      (bankRegisters regs).index_ne
        (by decide : (3 : Fin 12) ≠ 8), hbasePred]
  have hindexedOne :
      indexed (bankRegisters regs).one = 1 := by
    simp [indexed, Basic.exec,
      (bankRegisters regs).index_ne
        (by decide : (6 : Fin 12) ≠ 8), hone]
  have hindexedIndex :
      indexed (bankRegisters regs).indexCount = 0 := by
    simp [indexed, Basic.exec]
  obtain ⟨read, hread, hreadWord, _, _, _, hreadResult,
      _, _, _, hreadCoordinate⟩ :=
    NeighborhoodProgram.bankRead_runs (bankRegisters regs)
      indexed (PackedLocalConfiguration.radix tm) word 0
      (PackedLocalConfiguration.radix_pos tm) hindexedWord
      hindexedBase hindexedBasePred hindexedOne hindexedIndex
  let final :=
    (Basic.imm (CombineValue.rangeRegisters regs).one 1).exec read
  have hrestore :
      Runs (restoreRangeOne regs) read final :=
    Runs.basic _ _
  have hrun : Runs (readState tm regs) store final := by
    simpa [readState, Cmd.seqList, indexed, final,
      restoreRangeOne] using
      Runs.seq hinitialize
        (Runs.seq (Runs.basic _ initialized)
          (Runs.seq hread hrestore))
  have hword_ne_one :
      (bankRegisters regs).word ≠
        (CombineValue.rangeRegisters regs).one :=
    regs.injective.ne (by decide)
  have hresult_ne_one :
      bitValue regs ≠ (CombineValue.rangeRegisters regs).one :=
    regs.injective.ne (by decide)
  have hcoordinate_ne_one :
      coordinate regs ≠ (CombineValue.rangeRegisters regs).one :=
    regs.injective.ne (by decide)
  refine ⟨final, hrun, ?_, ?_, ?_, ?_, ?_⟩
  · simp [final, Basic.exec, Function.update_of_ne,
      hword_ne_one, hreadWord]
  · simp [final, Basic.exec, Function.update_of_ne,
      hresult_ne_one, hreadResult]
  · rw [show final (coordinate regs) = read (coordinate regs) by
      simp [final, Basic.exec, Function.update_of_ne,
        hcoordinate_ne_one]]
    calc
      read (coordinate regs) = indexed (coordinate regs) :=
        hreadCoordinate
      _ = initialized (coordinate regs) := by
        simp [indexed, Basic.exec,
          (bankRegisters regs).index_ne
            (by decide : (11 : Fin 12) ≠ 8)]
      _ = store (coordinate regs) :=
        hinitializeOutside _
          ((bankRegisters regs).index_ne
            (by decide : (11 : Fin 12) ≠ 2))
          ((bankRegisters regs).index_ne
            (by decide : (11 : Fin 12) ≠ 3))
          ((bankRegisters regs).index_ne
            (by decide : (11 : Fin 12) ≠ 6))
      _ = currentCoordinate := hcoordinate
  · simp [final, Basic.exec]
  · intro address haddress
    exact Footprint.runs_eq_outside
      (readState_writesWithin tm regs) hrun haddress

private theorem stateBit_writesWithin
    (tm : TM workTapeCount)
    (regs : NeighborhoodTrial.Registers controller) :
    Footprint.CmdWritesWithin
      (PackedLocalHeadScan.footprint regs)
      (stateBit tm regs) := by
  have bankMem (slot : Fin 12) :
      (bankRegisters regs).index slot ∈
        PackedLocalHeadScan.footprint regs :=
    Finset.mem_union_left _
      ((bankRegisters regs).index_mem_footprint slot)
  simp only [stateBit, equalValues, Cmd.seqList,
    Footprint.CmdWritesWithin, Footprint.BasicWritesWithin]
  exact
    ⟨cmdWritesWithin_mono (readState_writesWithin tm regs)
        (by
          intro address haddress
          exact Finset.mem_union_left _ haddress),
      bankMem 5, bankMem 4, bankMem 10,
      ⟨bankMem 10, bankMem 10⟩⟩

private theorem stateBit_runs
    (tm : TM workTapeCount)
    (regs : NeighborhoodTrial.Registers controller)
    (store : Store) (word currentCoordinate : ℕ)
    (hword : store (bankRegisters regs).word = word)
    (hcoordinate :
      store (coordinate regs) = currentCoordinate) :
    ∃ final,
      Runs (stateBit tm regs) store final ∧
      final (bitValue regs) =
        (if currentCoordinate =
            PackedDigits.digit
              (PackedLocalConfiguration.radix tm) word 0 then
          1
        else
          0) ∧
      final (bankRegisters regs).word = word ∧
      final (coordinate regs) = currentCoordinate ∧
      final (CombineValue.rangeRegisters regs).one = 1 ∧
      ∀ address,
        address ∉ PackedLocalHeadScan.footprint regs →
          final address = store address := by
  obtain ⟨read, hread, hreadWord, hreadResult,
      hreadCoordinate, hreadOne, _⟩ :=
    readState_runs tm regs store word currentCoordinate
      hword hcoordinate
  obtain ⟨final, hequal, hfinalResult, hfinalOutside⟩ :=
    equalValues_runs regs (coordinate regs) (bitValue regs)
      (bitValue regs) read currentCoordinate
      (PackedDigits.digit
        (PackedLocalConfiguration.radix tm) word 0)
      hreadCoordinate hreadResult
      ((bankRegisters regs).index_ne
        (by decide : (5 : Fin 12) ≠ 11))
      ((bankRegisters regs).index_ne
        (by decide : (5 : Fin 12) ≠ 10))
      ((bankRegisters regs).index_ne
        (by decide : (5 : Fin 12) ≠ 4))
  have hrun : Runs (stateBit tm regs) store final := by
    exact Runs.seq hread hequal
  refine ⟨final, hrun, hfinalResult, ?_, ?_, ?_, ?_⟩
  · exact hfinalOutside _ ((bankRegisters regs).index_ne
      (by decide : (0 : Fin 12) ≠ 5))
      ((bankRegisters regs).index_ne
        (by decide : (0 : Fin 12) ≠ 4))
      ((bankRegisters regs).index_ne
        (by decide : (0 : Fin 12) ≠ 10))
      |>.trans hreadWord
  · exact hfinalOutside _ ((bankRegisters regs).index_ne
      (by decide : (11 : Fin 12) ≠ 5))
      ((bankRegisters regs).index_ne
        (by decide : (11 : Fin 12) ≠ 4))
      ((bankRegisters regs).index_ne
        (by decide : (11 : Fin 12) ≠ 10))
      |>.trans hreadCoordinate
  · exact hfinalOutside _ (regs.injective.ne (by decide))
      (regs.injective.ne (by decide))
      (regs.injective.ne (by decide))
      |>.trans hreadOne
  · intro address haddress
    exact Footprint.runs_eq_outside
      (stateBit_writesWithin tm regs) hrun haddress

private theorem division_writesWithin_bank
    (regs : NeighborhoodTrial.Registers controller) :
    Footprint.CmdWritesWithin (bankRegisters regs).footprint
      (ControlDecode.divRem
        (PackedLocalHeadScan.cellDivision regs)) := by
  apply cmdWritesWithin_mono
    (ControlDecode.divRem_writesWithin
      (PackedLocalHeadScan.cellDivision regs))
  intro address haddress
  simp only [ControlDecode.DivisionRegisters.writeFootprint,
    Finset.mem_insert, Finset.mem_singleton] at haddress
  rcases haddress with hvalue | hquotient | htest | hone
  · rw [hvalue]
    exact (bankRegisters regs).index_mem_footprint 10
  · rw [hquotient]
    exact (bankRegisters regs).index_mem_footprint 1
  · rw [htest]
    exact (bankRegisters regs).index_mem_footprint 5
  · rw [hone]
    exact (bankRegisters regs).index_mem_footprint 6

private theorem reduceHeadOffset_writesWithin
    (regs : NeighborhoodTrial.Registers controller) :
    Footprint.CmdWritesWithin (bankRegisters regs).footprint
      (reduceHeadOffset regs) := by
  simp only [reduceHeadOffset, Cmd.seqList,
    Footprint.CmdWritesWithin]
  exact
    ⟨⟨(bankRegisters regs).index_mem_footprint 10,
        (bankRegisters regs).index_mem_footprint 10⟩,
      ⟨(bankRegisters regs).index_mem_footprint 2,
        (bankRegisters regs).index_mem_footprint 2⟩,
      division_writesWithin_bank regs⟩

private theorem reduceHeadOffset_runs
    (regs : NeighborhoodTrial.Registers controller)
    (store : Store) (blockLength headOffset word : ℕ)
    (hpositive : 0 < blockLength)
    (hblock :
      store (Layout.blockLength regs) = blockLength)
    (hhead :
      store (PackedLocalHeadScan.headOffset regs) = headOffset)
    (hword : store (bankRegisters regs).word = word) :
    ∃ final,
      Runs (reduceHeadOffset regs) store final ∧
      final (bitValue regs) = headOffset % blockLength ∧
      final (bankRegisters regs).word = word ∧
      ∀ address, address ∉ (bankRegisters regs).footprint →
        final address = store address := by
  obtain ⟨copied, hcopyHead, hcopiedHead,
      hcopyHeadOutside⟩ :=
    copy_runs (bitValue regs)
      (PackedLocalHeadScan.headOffset regs) store
      ((bankRegisters regs).index_ne
        (by decide : (10 : Fin 12) ≠ 11))
  obtain ⟨based, hcopyBase, hbasedBase, hbasedOutside⟩ :=
    copy_runs (bankRegisters regs).base
      (Layout.blockLength regs) copied
      (regs.injective.ne (by decide))
  have hcopiedBlock :
      copied (Layout.blockLength regs) = blockLength := by
    exact
      (hcopyHeadOutside _ (regs.injective.ne (by decide))).trans
        hblock
  have hbasedValue :
      based (PackedLocalHeadScan.cellDivision regs).value =
        headOffset := by
    change based (bitValue regs) = headOffset
    exact
      (hbasedOutside _ ((bankRegisters regs).index_ne
        (by decide : (10 : Fin 12) ≠ 2))).trans
        (hcopiedHead.trans hhead)
  have hbasedDivisor :
      based (PackedLocalHeadScan.cellDivision regs).divisor =
        blockLength := by
    change based (bankRegisters regs).base = blockLength
    exact hbasedBase.trans hcopiedBlock
  obtain ⟨final, hdivide, hpost⟩ :=
    ControlDecode.divRem_runs
      (PackedLocalHeadScan.cellDivision regs)
      based blockLength headOffset hpositive
      hbasedValue hbasedDivisor
  have hcopiedWord :
      copied (bankRegisters regs).word = word :=
    (hcopyHeadOutside _ ((bankRegisters regs).index_ne
      (by decide : (0 : Fin 12) ≠ 10))).trans hword
  have hbasedWord :
      based (bankRegisters regs).word = word :=
    (hbasedOutside _ ((bankRegisters regs).index_ne
      (by decide : (0 : Fin 12) ≠ 2))).trans hcopiedWord
  have hwordNotDivision :
      (bankRegisters regs).word ∉
        (PackedLocalHeadScan.cellDivision regs).writeFootprint := by
    intro hmember
    simp only [ControlDecode.DivisionRegisters.writeFootprint,
      Finset.mem_insert, Finset.mem_singleton] at hmember
    rcases hmember with hvalue | hquotient | htest | hone
    · exact (bankRegisters regs).index_ne
        (by decide : (0 : Fin 12) ≠ 10) hvalue
    · exact (bankRegisters regs).index_ne
        (by decide : (0 : Fin 12) ≠ 1) hquotient
    · exact (bankRegisters regs).index_ne
        (by decide : (0 : Fin 12) ≠ 5) htest
    · exact (bankRegisters regs).index_ne
        (by decide : (0 : Fin 12) ≠ 6) hone
  have hfinalWord :
      final (bankRegisters regs).word = word :=
    (hpost.eq_outside _ hwordNotDivision).trans hbasedWord
  have hrun :
      Runs (reduceHeadOffset regs) store final := by
    simpa [reduceHeadOffset, Cmd.seqList] using
      Runs.seq hcopyHead (Runs.seq hcopyBase hdivide)
  refine ⟨final, hrun, hpost.value_eq, hfinalWord, ?_⟩
  intro address haddress
  exact Footprint.runs_eq_outside
    (reduceHeadOffset_writesWithin regs) hrun haddress

private theorem compareHeadCoordinate_writesWithin
    (tm : TM workTapeCount)
    (regs : NeighborhoodTrial.Registers controller) :
    Footprint.CmdWritesWithin (bankRegisters regs).footprint
      (compareHeadCoordinate tm regs) := by
  have bankMem (slot : Fin 12) :
      (bankRegisters regs).index slot ∈
        (bankRegisters regs).footprint :=
    (bankRegisters regs).index_mem_footprint slot
  have hprepare :
      Footprint.CmdWritesWithin (bankRegisters regs).footprint
        (prepareCoordinate regs) := by
    simp only [prepareCoordinate, Cmd.seqList,
      Footprint.CmdWritesWithin, Footprint.BasicWritesWithin]
    exact ⟨bankMem 11, bankMem 11, bankMem 11,
      bankMem 11, bankMem 11⟩
  have hequal :
      Footprint.CmdWritesWithin (bankRegisters regs).footprint
        (equalValues regs (coordinate regs)
          (bankRegisters regs).result
          (bankRegisters regs).result) := by
    simp only [equalValues, Cmd.seqList,
      Footprint.CmdWritesWithin, Footprint.BasicWritesWithin]
    exact
      ⟨bankMem 5, bankMem 4, bankMem 10,
        ⟨bankMem 10, bankMem 10⟩⟩
  simp only [compareHeadCoordinate, Cmd.seqList,
    Footprint.CmdWritesWithin, Footprint.BasicWritesWithin]
  exact
    ⟨hprepare, bankMem 7, bankMem 11, hequal, bankMem 9⟩

private theorem compareHeadCoordinate_runs
    (tm : TM workTapeCount)
    (regs : NeighborhoodTrial.Registers controller)
    (store : Store)
    (cursor width bitsLeft headRemainder word : ℕ)
    (hcursor : store (Layout.active regs) = cursor)
    (hwidth : store (chunkBits regs) = width)
    (hremaining : store (remaining regs) = bitsLeft)
    (hhead : store (bitValue regs) = headRemainder)
    (hword : store (bankRegisters regs).word = word) :
    ∃ final,
      Runs (compareHeadCoordinate tm regs) store final ∧
      final (bitValue regs) =
        (if cursor * width + width - bitsLeft -
              Fintype.card tm.Q =
            headRemainder then
          1
        else
          0) ∧
      final (bankRegisters regs).word = word ∧
      final (CombineValue.rangeRegisters regs).one = 1 ∧
      ∀ address, address ∉ (bankRegisters regs).footprint →
        final address = store address := by
  let current := cursor * width + width - bitsLeft
  obtain ⟨prepared, hprepare, hpreparedCoordinate,
      hprepareOutside⟩ :=
    prepareCoordinate_runs regs store cursor width bitsLeft
      hcursor hwidth hremaining
  let withState :=
    (Basic.imm (bankRegisters regs).value
      (Fintype.card tm.Q)).exec prepared
  let offset :=
    (Basic.sub (coordinate regs) (coordinate regs)
      (bankRegisters regs).value).exec withState
  have hpreparedHead :
      prepared (bitValue regs) = headRemainder :=
    (hprepareOutside _ ((bankRegisters regs).index_ne
      (by decide : (10 : Fin 12) ≠ 11))).trans hhead
  have hwithStateHead :
      withState (bitValue regs) = headRemainder := by
    simp [withState, Basic.exec,
      (bankRegisters regs).index_ne
        (by decide : (10 : Fin 12) ≠ 7),
      hpreparedHead]
  have hoffsetHead :
      offset (bitValue regs) = headRemainder := by
    simp [offset, Basic.exec,
      (bankRegisters regs).index_ne
        (by decide : (10 : Fin 12) ≠ 11),
      hwithStateHead]
  have hoffsetCoordinate :
      offset (coordinate regs) =
        current - Fintype.card tm.Q := by
    simp [offset, withState, Basic.exec,
      (bankRegisters regs).index_ne
        (by decide : (11 : Fin 12) ≠ 7),
      hpreparedCoordinate, current]
  have hpreparedWord :
      prepared (bankRegisters regs).word = word :=
    (hprepareOutside _ ((bankRegisters regs).index_ne
      (by decide : (0 : Fin 12) ≠ 11))).trans hword
  have hwithStateWord :
      withState (bankRegisters regs).word = word := by
    simp [withState, Basic.exec,
      (bankRegisters regs).index_ne
        (by decide : (0 : Fin 12) ≠ 7),
      hpreparedWord]
  have hoffsetWord :
      offset (bankRegisters regs).word = word := by
    simp [offset, Basic.exec,
      (bankRegisters regs).index_ne
        (by decide : (0 : Fin 12) ≠ 11),
      hwithStateWord]
  obtain ⟨compared, hequal, hcomparedBit,
      hcompareOutside⟩ :=
    equalValues_runs regs (coordinate regs) (bitValue regs)
      (bitValue regs) offset
      (current - Fintype.card tm.Q) headRemainder
      hoffsetCoordinate hoffsetHead
      ((bankRegisters regs).index_ne
        (by decide : (5 : Fin 12) ≠ 11))
      ((bankRegisters regs).index_ne
        (by decide : (5 : Fin 12) ≠ 10))
      ((bankRegisters regs).index_ne
        (by decide : (5 : Fin 12) ≠ 4))
  let final :=
    (Basic.imm (CombineValue.rangeRegisters regs).one 1).exec
      compared
  have hrestore :
      Runs (restoreRangeOne regs) compared final :=
    Runs.basic _ _
  have hrun :
      Runs (compareHeadCoordinate tm regs) store final := by
    simpa [compareHeadCoordinate, Cmd.seqList, withState,
      offset, final, restoreRangeOne] using
      Runs.seq hprepare
        (Runs.seq (Runs.basic _ prepared)
          (Runs.seq (Runs.basic _ withState)
            (Runs.seq hequal hrestore)))
  have hbit_ne_one :
      bitValue regs ≠ (CombineValue.rangeRegisters regs).one :=
    regs.injective.ne (by decide)
  have hcomparedWord :
      compared (bankRegisters regs).word = word :=
    (hcompareOutside _
      ((bankRegisters regs).index_ne
        (by decide : (0 : Fin 12) ≠ 5))
      ((bankRegisters regs).index_ne
        (by decide : (0 : Fin 12) ≠ 4))
      ((bankRegisters regs).index_ne
        (by decide : (0 : Fin 12) ≠ 10))).trans hoffsetWord
  have hword_ne_one :
      (bankRegisters regs).word ≠
        (CombineValue.rangeRegisters regs).one :=
    regs.injective.ne (by decide)
  refine
    ⟨final, hrun, ?_, ?_,
      by simp [final, Basic.exec], ?_⟩
  · simp [final, Basic.exec, Function.update_of_ne,
      hbit_ne_one, hcomparedBit, current]
  · simp [final, Basic.exec, Function.update_of_ne,
      hword_ne_one, hcomparedWord]
  · intro address haddress
    exact Footprint.runs_eq_outside
      (compareHeadCoordinate_writesWithin tm regs)
      hrun haddress

private theorem fixed_index_not_mem_bank
    (regs : NeighborhoodTrial.Registers controller)
    (slot : Fin 34)
    (hslot :
      ∀ bankSlot,
        slot ≠ PackedLocalHeadScan.bankMap bankSlot) :
    regs.index slot ∉ (bankRegisters regs).footprint := by
  intro hmember
  simp only [NeighborhoodProgram.BankRegisters.footprint,
    Finset.mem_image, Finset.mem_univ, true_and] at hmember
  obtain ⟨bankSlot, hbankSlot⟩ := hmember
  exact hslot bankSlot (regs.injective hbankSlot.symm)

private theorem headBit_writesWithin
    (tm : TM workTapeCount)
    (tape : TapeIndex workTapeCount)
    (regs : NeighborhoodTrial.Registers controller) :
    Footprint.CmdWritesWithin
      (PackedLocalHeadScan.footprint regs)
      (headBit tm tape regs) := by
  simp only [headBit, Cmd.seqList, Footprint.CmdWritesWithin]
  exact
    ⟨PackedLocalHeadScan.scan_writesWithin tm tape regs,
      cmdWritesWithin_mono
        (reduceHeadOffset_writesWithin regs)
        (by
          intro address haddress
          exact Finset.mem_union_left _ haddress),
      cmdWritesWithin_mono
        (compareHeadCoordinate_writesWithin tm regs)
        (by
          intro address haddress
          exact Finset.mem_union_left _ haddress)⟩

private theorem headBit_runs
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
    (cursor width bitsLeft : ℕ)
    (hblock : store (Layout.blockLength regs) = blockLength)
    (hword : store (bankRegisters regs).word = word)
    (hrep :
      PackedLocalRepresentation.Represents tm order blockLength
        centers cfg suffix word)
    (hone :
      store (CombineValue.rangeRegisters regs).one = 1)
    (hcursor : store (Layout.active regs) = cursor)
    (hwidth : store (chunkBits regs) = width)
    (hremaining : store (remaining regs) = bitsLeft)
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
      Runs (headBit tm tape regs) store final ∧
      final (bitValue regs) =
        (if cursor * width + width - bitsLeft -
              Fintype.card tm.Q =
            PackedLocalConfiguration.findHeadOffset
              tm blockLength tape word % blockLength then
          1
        else
          0) ∧
      final (bankRegisters regs).word = word ∧
      final (CombineValue.rangeRegisters regs).one = 1 ∧
      ∀ address,
        address ∉ PackedLocalHeadScan.footprint regs →
          final address = store address := by
  obtain ⟨scanned, hscan, hscanPost, hscanPreserves⟩ :=
    PackedLocalHeadScan.scan_runs_represents
      tm order blockLength hpositive centers cfg tape suffix word
      regs store hblock hword hrep hone hlower hupper
  let localHead :=
    PackedLocalConfiguration.localHead blockLength
      (centers tape) (tapeAt cfg tape).head
  obtain ⟨reduced, hreduce, hreduceValue,
      hreduceWord, hreduceOutside⟩ :=
    reduceHeadOffset_runs regs scanned blockLength localHead word
      hpositive
      (hscanPreserves.abi.blockLength_eq.trans hblock)
      hscanPost.head_eq hscanPost.word_eq
  have hreducedCursor :
      reduced (Layout.active regs) = cursor := by
    calc
      reduced (Layout.active regs) =
          scanned (Layout.active regs) :=
        hreduceOutside _
          (fixed_index_not_mem_bank regs 28 (by
            intro bankSlot
            fin_cases bankSlot <;> decide))
      _ = store (Layout.active regs) :=
        hscanPreserves.abi.active_eq
      _ = cursor := hcursor
  have hreducedWidth :
      reduced (chunkBits regs) = width := by
    calc
      reduced (chunkBits regs) = scanned (chunkBits regs) :=
        hreduceOutside _
          (fixed_index_not_mem_bank regs 19 (by
            intro bankSlot
            fin_cases bankSlot <;> decide))
      _ = store (chunkBits regs) :=
        hscanPreserves.term_eq
      _ = width := hwidth
  have hreducedRemaining :
      reduced (remaining regs) = bitsLeft := by
    calc
      reduced (remaining regs) = scanned (remaining regs) :=
        hreduceOutside _
          (fixed_index_not_mem_bank regs 10 (by
            intro bankSlot
            fin_cases bankSlot <;> decide))
      _ = store (remaining regs) :=
        hscanPreserves.count_eq
      _ = bitsLeft := hremaining
  obtain ⟨final, hcompare, hcompareValue, hcompareWord,
      hcompareOne, _⟩ :=
    compareHeadCoordinate_runs tm regs reduced cursor width
      bitsLeft (localHead % blockLength) word
      hreducedCursor hreducedWidth hreducedRemaining
      hreduceValue hreduceWord
  have hrun : Runs (headBit tm tape regs) store final := by
    simpa [headBit, Cmd.seqList] using
      Runs.seq hscan (Runs.seq hreduce hcompare)
  have hfind :
      PackedLocalConfiguration.findHeadOffset
          tm blockLength tape word =
        localHead := by
    exact
      PackedLocalRepresentation.findHeadOffset_represents
        tm order blockLength hpositive centers cfg suffix word hrep
        tape hlower hupper
  refine ⟨final, hrun, ?_, hcompareWord, hcompareOne, ?_⟩
  · simpa [hfind] using hcompareValue
  · intro address haddress
    exact Footprint.runs_eq_outside
      (headBit_writesWithin tm tape regs) hrun haddress

private theorem decodeCellCoordinate_writesWithin
    (tm : TM workTapeCount)
    (regs : NeighborhoodTrial.Registers controller) :
    Footprint.CmdWritesWithin (bankRegisters regs).footprint
      (decodeCellCoordinate tm regs) := by
  have bankMem (slot : Fin 12) :
      (bankRegisters regs).index slot ∈
        (bankRegisters regs).footprint :=
    (bankRegisters regs).index_mem_footprint slot
  simp only [decodeCellCoordinate, Cmd.seqList,
    Footprint.CmdWritesWithin, Footprint.BasicWritesWithin]
  exact
    ⟨bankMem 7, bankMem 7, bankMem 11,
      ⟨bankMem 10, bankMem 10⟩,
      bankMem 2, division_writesWithin_bank regs⟩

private theorem decodeCellCoordinate_runs
    (tm : TM workTapeCount)
    (regs : NeighborhoodTrial.Registers controller)
    (store : Store)
    (blockLength currentCoordinate word : ℕ)
    (hblock :
      store (Layout.blockLength regs) = blockLength)
    (hcoordinate :
      store (coordinate regs) = currentCoordinate)
    (hword : store (bankRegisters regs).word = word) :
    ∃ final,
      Runs (decodeCellCoordinate tm regs) store final ∧
      final (bitValue regs) =
        (currentCoordinate -
            (Fintype.card tm.Q + blockLength)) % 4 ∧
      final (bankRegisters regs).buffer =
        (currentCoordinate -
            (Fintype.card tm.Q + blockLength)) / 4 ∧
      final (coordinate regs) =
        currentCoordinate -
          (Fintype.card tm.Q + blockLength) ∧
      final (bankRegisters regs).indexCount =
        store (bankRegisters regs).indexCount ∧
      final (bankRegisters regs).word = word ∧
      final (Layout.blockLength regs) = blockLength ∧
      ∀ address, address ∉ (bankRegisters regs).footprint →
        final address = store address := by
  let withState :=
    (Basic.imm (bankRegisters regs).value
      (Fintype.card tm.Q)).exec store
  let withUpper :=
    (Basic.add (bankRegisters regs).value
      (bankRegisters regs).value
      (Layout.blockLength regs)).exec withState
  let shifted :=
    (Basic.sub (coordinate regs) (coordinate regs)
      (bankRegisters regs).value).exec withUpper
  have hblock_ne_value :
      Layout.blockLength regs ≠ (bankRegisters regs).value :=
    regs.injective.ne (by decide)
  have hblock_ne_coordinate :
      Layout.blockLength regs ≠ coordinate regs :=
    regs.injective.ne (by decide)
  have hblock_ne_base :
      Layout.blockLength regs ≠ (bankRegisters regs).base :=
    regs.injective.ne (by decide)
  have hcoordinate_ne_value :
      coordinate regs ≠ (bankRegisters regs).value :=
    (bankRegisters regs).index_ne
      (by decide : (11 : Fin 12) ≠ 7)
  have hwithStateBlock :
      withState (Layout.blockLength regs) = blockLength := by
    simpa [withState, Basic.exec, Function.update_of_ne,
      hblock_ne_value] using hblock
  have hwithUpperValue :
      withUpper (bankRegisters regs).value =
        Fintype.card tm.Q + blockLength := by
    have hwithStateValue :
        withState (bankRegisters regs).value =
          Fintype.card tm.Q := by
      simp [withState, Basic.exec]
    simp [withUpper, Basic.exec, hwithStateValue,
      hwithStateBlock]
  have hwithStateCoordinate :
      withState (coordinate regs) = currentCoordinate := by
    simpa [withState, Basic.exec, Function.update_of_ne,
      hcoordinate_ne_value] using hcoordinate
  have hwithUpperCoordinate :
      withUpper (coordinate regs) = currentCoordinate := by
    simpa [withUpper, Basic.exec, Function.update_of_ne,
      hcoordinate_ne_value] using hwithStateCoordinate
  have hshiftedCoordinate :
      shifted (coordinate regs) =
        currentCoordinate -
          (Fintype.card tm.Q + blockLength) := by
    simp [shifted, Basic.exec, hwithUpperCoordinate,
      hwithUpperValue]
  obtain ⟨copied, hcopy, hcopiedValue, hcopyOutside⟩ :=
    copy_runs (bitValue regs) (coordinate regs) shifted
      ((bankRegisters regs).index_ne
        (by decide : (10 : Fin 12) ≠ 11))
  let based :=
    (Basic.imm (bankRegisters regs).base 4).exec copied
  have hcopiedInput :
      copied (bitValue regs) =
        currentCoordinate -
          (Fintype.card tm.Q + blockLength) :=
    hcopiedValue.trans hshiftedCoordinate
  have hbasedInput :
      based (PackedLocalHeadScan.cellDivision regs).value =
        currentCoordinate -
          (Fintype.card tm.Q + blockLength) := by
    change based (bitValue regs) = _
    simp [based, Basic.exec,
      (bankRegisters regs).index_ne
        (by decide : (10 : Fin 12) ≠ 2),
      hcopiedInput]
  have hbasedDivisor :
      based (PackedLocalHeadScan.cellDivision regs).divisor = 4 := by
    change based (bankRegisters regs).base = 4
    simp [based, Basic.exec]
  obtain ⟨final, hdivide, hpost⟩ :=
    ControlDecode.divRem_runs
      (PackedLocalHeadScan.cellDivision regs) based 4
      (currentCoordinate -
        (Fintype.card tm.Q + blockLength))
      (by omega) hbasedInput hbasedDivisor
  have hrun :
      Runs (decodeCellCoordinate tm regs) store final := by
    simpa [decodeCellCoordinate, Cmd.seqList, withState,
      withUpper, shifted, based] using
      Runs.seq (Runs.basic _ store)
        (Runs.seq (Runs.basic _ withState)
          (Runs.seq (Runs.basic _ withUpper)
            (Runs.seq hcopy
              (Runs.seq (Runs.basic _ copied) hdivide))))
  have hshiftedWord :
      shifted (bankRegisters regs).word = word := by
    simp [shifted, withUpper, withState, Basic.exec,
      (bankRegisters regs).index_ne
        (by decide : (0 : Fin 12) ≠ 11),
      (bankRegisters regs).index_ne
        (by decide : (0 : Fin 12) ≠ 7),
      hword]
  have hcopiedWord :
      copied (bankRegisters regs).word = word :=
    (hcopyOutside _ ((bankRegisters regs).index_ne
      (by decide : (0 : Fin 12) ≠ 10))).trans hshiftedWord
  have hbasedWord :
      based (bankRegisters regs).word = word := by
    simp [based, Basic.exec,
      (bankRegisters regs).index_ne
        (by decide : (0 : Fin 12) ≠ 2),
      hcopiedWord]
  have hwordNotDivision :
      (bankRegisters regs).word ∉
        (PackedLocalHeadScan.cellDivision regs).writeFootprint := by
    intro hmember
    simp only [ControlDecode.DivisionRegisters.writeFootprint,
      Finset.mem_insert, Finset.mem_singleton] at hmember
    rcases hmember with hvalue | hquotient | htest | hone
    · exact (bankRegisters regs).index_ne
        (by decide : (0 : Fin 12) ≠ 10) hvalue
    · exact (bankRegisters regs).index_ne
        (by decide : (0 : Fin 12) ≠ 1) hquotient
    · exact (bankRegisters regs).index_ne
        (by decide : (0 : Fin 12) ≠ 5) htest
    · exact (bankRegisters regs).index_ne
        (by decide : (0 : Fin 12) ≠ 6) hone
  have hfinalWord :
      final (bankRegisters regs).word = word :=
    (hpost.eq_outside _ hwordNotDivision).trans hbasedWord
  have hshiftedBlock :
      shifted (Layout.blockLength regs) = blockLength := by
    have hwithUpperBlock :
        withUpper (Layout.blockLength regs) = blockLength := by
      simpa [withUpper, Basic.exec, Function.update_of_ne,
        hblock_ne_value] using hwithStateBlock
    simpa [shifted, Basic.exec, Function.update_of_ne,
      hblock_ne_coordinate] using hwithUpperBlock
  have hcopiedBlock :
      copied (Layout.blockLength regs) = blockLength :=
    (hcopyOutside _ (regs.injective.ne (by decide))).trans
      hshiftedBlock
  have hbasedBlock :
      based (Layout.blockLength regs) = blockLength := by
    simpa [based, Basic.exec, Function.update_of_ne,
      hblock_ne_base] using hcopiedBlock
  have hblock_ne_divValue :
      Layout.blockLength regs ≠
        (PackedLocalHeadScan.cellDivision regs).value :=
    regs.injective.ne (by decide)
  have hblock_ne_divQuotient :
      Layout.blockLength regs ≠
        (PackedLocalHeadScan.cellDivision regs).quotient :=
    regs.injective.ne (by decide)
  have hblock_ne_divTest :
      Layout.blockLength regs ≠
        (PackedLocalHeadScan.cellDivision regs).test :=
    regs.injective.ne (by decide)
  have hblock_ne_divOne :
      Layout.blockLength regs ≠
        (PackedLocalHeadScan.cellDivision regs).one :=
    regs.injective.ne (by decide)
  have hblockNotDivision :
      Layout.blockLength regs ∉
        (PackedLocalHeadScan.cellDivision regs).writeFootprint := by
    intro hmember
    simp only [ControlDecode.DivisionRegisters.writeFootprint,
      Finset.mem_insert, Finset.mem_singleton] at hmember
    rcases hmember with hvalue | hquotient | htest | hone
    · exact hblock_ne_divValue hvalue
    · exact hblock_ne_divQuotient hquotient
    · exact hblock_ne_divTest htest
    · exact hblock_ne_divOne hone
  have hfinalBlock :
      final (Layout.blockLength regs) = blockLength :=
    (hpost.eq_outside _ hblockNotDivision).trans hbasedBlock
  have hshiftedValue :
      shifted (coordinate regs) =
        currentCoordinate -
          (Fintype.card tm.Q + blockLength) :=
    hshiftedCoordinate
  have hcopiedCoordinate :
      copied (coordinate regs) =
        currentCoordinate -
          (Fintype.card tm.Q + blockLength) :=
    (hcopyOutside _ ((bankRegisters regs).index_ne
      (by decide : (11 : Fin 12) ≠ 10))).trans hshiftedValue
  have hbasedCoordinate :
      based (coordinate regs) =
        currentCoordinate -
          (Fintype.card tm.Q + blockLength) := by
    simp [based, Basic.exec,
      (bankRegisters regs).index_ne
        (by decide : (11 : Fin 12) ≠ 2),
      hcopiedCoordinate]
  have hcoordinateNotDivision :
      coordinate regs ∉
        (PackedLocalHeadScan.cellDivision regs).writeFootprint := by
    intro hmember
    simp only [ControlDecode.DivisionRegisters.writeFootprint,
      Finset.mem_insert, Finset.mem_singleton] at hmember
    rcases hmember with hvalue | hquotient | htest | hone
    · exact (bankRegisters regs).index_ne
        (by decide : (11 : Fin 12) ≠ 10) hvalue
    · exact (bankRegisters regs).index_ne
        (by decide : (11 : Fin 12) ≠ 1) hquotient
    · exact (bankRegisters regs).index_ne
        (by decide : (11 : Fin 12) ≠ 5) htest
    · exact (bankRegisters regs).index_ne
        (by decide : (11 : Fin 12) ≠ 6) hone
  have hfinalCoordinate :
      final (coordinate regs) =
        currentCoordinate -
          (Fintype.card tm.Q + blockLength) :=
    (hpost.eq_outside _ hcoordinateNotDivision).trans
      hbasedCoordinate
  have hshiftedIndex :
      shifted (bankRegisters regs).indexCount =
        store (bankRegisters regs).indexCount := by
    simp [shifted, withUpper, withState, Basic.exec,
      (bankRegisters regs).index_ne
        (by decide : (8 : Fin 12) ≠ 11),
      (bankRegisters regs).index_ne
        (by decide : (8 : Fin 12) ≠ 7)]
  have hcopiedIndex :
      copied (bankRegisters regs).indexCount =
        store (bankRegisters regs).indexCount :=
    (hcopyOutside _ ((bankRegisters regs).index_ne
      (by decide : (8 : Fin 12) ≠ 10))).trans hshiftedIndex
  have hbasedIndex :
      based (bankRegisters regs).indexCount =
        store (bankRegisters regs).indexCount := by
    simp [based, Basic.exec,
      (bankRegisters regs).index_ne
        (by decide : (8 : Fin 12) ≠ 2),
      hcopiedIndex]
  have hindexNotDivision :
      (bankRegisters regs).indexCount ∉
        (PackedLocalHeadScan.cellDivision regs).writeFootprint := by
    intro hmember
    simp only [ControlDecode.DivisionRegisters.writeFootprint,
      Finset.mem_insert, Finset.mem_singleton] at hmember
    rcases hmember with hvalue | hquotient | htest | hone
    · exact (bankRegisters regs).index_ne
        (by decide : (8 : Fin 12) ≠ 10) hvalue
    · exact (bankRegisters regs).index_ne
        (by decide : (8 : Fin 12) ≠ 1) hquotient
    · exact (bankRegisters regs).index_ne
        (by decide : (8 : Fin 12) ≠ 5) htest
    · exact (bankRegisters regs).index_ne
        (by decide : (8 : Fin 12) ≠ 6) hone
  have hfinalIndex :
      final (bankRegisters regs).indexCount =
        store (bankRegisters regs).indexCount :=
    (hpost.eq_outside _ hindexNotDivision).trans hbasedIndex
  refine
    ⟨final, hrun, hpost.value_eq, hpost.quotient_eq,
      hfinalCoordinate, hfinalIndex, hfinalWord, hfinalBlock, ?_⟩
  intro address haddress
  exact Footprint.runs_eq_outside
    (decodeCellCoordinate_writesWithin tm regs)
    hrun haddress

private theorem readSelectedCell_writesWithin
    (tm : TM workTapeCount)
    (tape : TapeIndex workTapeCount)
    (localBlock : ℕ)
    (regs : NeighborhoodTrial.Registers controller) :
    Footprint.CmdWritesWithin
      (PackedLocalHeadScan.footprint regs)
      (readSelectedCell tm tape localBlock regs) := by
  have bankMem (slot : Fin 12) :
      (bankRegisters regs).index slot ∈
        PackedLocalHeadScan.footprint regs :=
    Finset.mem_union_left _
      ((bankRegisters regs).index_mem_footprint slot)
  have hinitialize :
      Footprint.CmdWritesWithin
        (PackedLocalHeadScan.footprint regs)
        (initializeBank tm regs) := by
    simp only [initializeBank, Cmd.basics]
    exact ⟨bankMem 2, bankMem 3, bankMem 6⟩
  simp only [readSelectedCell, Cmd.seqList,
    Footprint.CmdWritesWithin, Footprint.BasicWritesWithin]
  exact
    ⟨bankMem 11, bankMem 11, bankMem 11,
      hinitialize,
      PackedLocalHeadScan.Internal.readCell_writesWithin_internal
        tape regs,
      PackedLocalHeadScan.Internal.decodeCell_writesWithin_internal
        regs,
      ⟨bankMem 8, bankMem 8⟩⟩

private theorem readSelectedCell_runs
    (tm : TM workTapeCount)
    (tape : TapeIndex workTapeCount)
    (localBlock : ℕ)
    (regs : NeighborhoodTrial.Registers controller)
    (store : Store)
    (blockLength offset word : ℕ)
    (hblock :
      store (Layout.blockLength regs) = blockLength)
    (hoffset :
      store (bankRegisters regs).buffer = offset)
    (hword : store (bankRegisters regs).word = word) :
    ∃ final,
      Runs (readSelectedCell tm tape localBlock regs)
        store final ∧
      final (bankRegisters regs).indexCount =
        PackedDigits.digit
          (PackedLocalConfiguration.radix tm) word
          (PackedLocalConfiguration.cellIndex blockLength tape
            (localBlock * blockLength + offset)) % 4 ∧
      final (bankRegisters regs).word = word ∧
      final (Layout.blockLength regs) = blockLength ∧
      ∀ address,
        address ∉ PackedLocalHeadScan.footprint regs →
          final address = store address := by
  let withBlock :=
    (Basic.imm (coordinate regs) localBlock).exec store
  let scaled :=
    (Basic.mul (coordinate regs) (coordinate regs)
      (Layout.blockLength regs)).exec withBlock
  let positioned :=
    (Basic.add (coordinate regs) (bankRegisters regs).buffer
      (coordinate regs)).exec scaled
  have hcoordinate_ne_block :
      coordinate regs ≠ Layout.blockLength regs :=
    regs.injective.ne (by decide)
  have hcoordinate_ne_buffer :
      coordinate regs ≠ (bankRegisters regs).buffer :=
    (bankRegisters regs).index_ne
      (by decide : (11 : Fin 12) ≠ 1)
  have hwithBlockLength :
      withBlock (Layout.blockLength regs) = blockLength := by
    simpa [withBlock, Basic.exec, Function.update_of_ne,
      hcoordinate_ne_block.symm] using hblock
  have hscaledCoordinate :
      scaled (coordinate regs) = localBlock * blockLength := by
    have hwithBlockCoordinate :
        withBlock (coordinate regs) = localBlock := by
      simp [withBlock, Basic.exec]
    simp [scaled, Basic.exec, hwithBlockCoordinate,
      hwithBlockLength]
  have hwithBlockOffset :
      withBlock (bankRegisters regs).buffer = offset := by
    simpa [withBlock, Basic.exec, Function.update_of_ne,
      hcoordinate_ne_buffer.symm] using hoffset
  have hscaledOffset :
      scaled (bankRegisters regs).buffer = offset := by
    simpa [scaled, Basic.exec, Function.update_of_ne,
      hcoordinate_ne_buffer.symm] using hwithBlockOffset
  have hpositionedCoordinate :
      positioned (coordinate regs) =
        localBlock * blockLength + offset := by
    simp [positioned, Basic.exec, hscaledCoordinate,
      hscaledOffset, Nat.add_comm]
  have hpositionedBlock :
      positioned (Layout.blockLength regs) = blockLength := by
    have hscaledBlock :
        scaled (Layout.blockLength regs) = blockLength := by
      simpa [scaled, Basic.exec, Function.update_of_ne,
        hcoordinate_ne_block.symm] using hwithBlockLength
    simpa [positioned, Basic.exec, Function.update_of_ne,
      hcoordinate_ne_block.symm] using hscaledBlock
  have hpositionedWord :
      positioned (bankRegisters regs).word = word := by
    have hword_ne_coordinate :
        (bankRegisters regs).word ≠ coordinate regs :=
      (bankRegisters regs).index_ne
        (by decide : (0 : Fin 12) ≠ 11)
    simpa [positioned, scaled, withBlock, Basic.exec,
      Function.update_of_ne, hword_ne_coordinate] using hword
  obtain ⟨initialized, hinitialize, hbase, hbasePred, hone,
      hinitializeOutside⟩ :=
    initializeBank_runs tm regs positioned
  have hinitializedPosition :
      initialized (coordinate regs) =
        localBlock * blockLength + offset :=
    (hinitializeOutside _
      ((bankRegisters regs).index_ne
        (by decide : (11 : Fin 12) ≠ 2))
      ((bankRegisters regs).index_ne
        (by decide : (11 : Fin 12) ≠ 3))
      ((bankRegisters regs).index_ne
        (by decide : (11 : Fin 12) ≠ 6))).trans
      hpositionedCoordinate
  have hinitializedBlock :
      initialized (Layout.blockLength regs) = blockLength :=
    (hinitializeOutside _ (regs.injective.ne (by decide))
      (regs.injective.ne (by decide))
      (regs.injective.ne (by decide))).trans hpositionedBlock
  have hinitializedWord :
      initialized (bankRegisters regs).word = word :=
    (hinitializeOutside _
      ((bankRegisters regs).index_ne
        (by decide : (0 : Fin 12) ≠ 2))
      ((bankRegisters regs).index_ne
        (by decide : (0 : Fin 12) ≠ 3))
      ((bankRegisters regs).index_ne
        (by decide : (0 : Fin 12) ≠ 6))).trans
      hpositionedWord
  let countdownValue :=
    initialized (PackedLocalHeadScan.countdown regs)
  obtain ⟨read, hread, hreadWord, hreadDigit,
      hreadPosition, hreadCountdown, _, _, _, hreadBlock⟩ :=
    PackedLocalHeadScan.Internal.readCell_runs_internal
      tm tape regs initialized blockLength word
      (localBlock * blockLength + offset) countdownValue
      hinitializedBlock hinitializedWord hinitializedPosition rfl
      hone hbase hbasePred
  let digit :=
    PackedDigits.digit
      (PackedLocalConfiguration.radix tm) word
      (PackedLocalConfiguration.cellIndex blockLength tape
        (localBlock * blockLength + offset))
  obtain ⟨decoded, hdecode, hdecodeWord, _, _,
      hdecodeDigit, _, _, hdecodeBlock⟩ :=
    PackedLocalHeadScan.Internal.decodeCell_runs_internal
      regs read digit word
      (localBlock * blockLength + offset) countdownValue
      blockLength hreadDigit hreadWord hreadPosition
      hreadCountdown
      hreadBlock
  obtain ⟨final, hcopy, hfinalIndex, hcopyOutside⟩ :=
    copy_runs (bankRegisters regs).indexCount
      (bankRegisters regs).result decoded
      ((bankRegisters regs).index_ne
        (by decide : (8 : Fin 12) ≠ 10))
  have hrun :
      Runs (readSelectedCell tm tape localBlock regs)
        store final := by
    simpa [readSelectedCell, Cmd.seqList, withBlock,
      scaled, positioned] using
      Runs.seq (Runs.basic _ store)
        (Runs.seq (Runs.basic _ withBlock)
          (Runs.seq (Runs.basic _ scaled)
            (Runs.seq hinitialize
              (Runs.seq hread (Runs.seq hdecode hcopy)))))
  have hfinalWord :
      final (bankRegisters regs).word = word :=
    (hcopyOutside _ ((bankRegisters regs).index_ne
      (by decide : (0 : Fin 12) ≠ 8))).trans hdecodeWord
  have hfinalBlock :
      final (Layout.blockLength regs) = blockLength :=
    (hcopyOutside _ (regs.injective.ne (by decide))).trans
      hdecodeBlock
  refine
    ⟨final, hrun, hfinalIndex.trans hdecodeDigit,
      hfinalWord, hfinalBlock, ?_⟩
  intro address haddress
  exact Footprint.runs_eq_outside
    (readSelectedCell_writesWithin tm tape localBlock regs)
    hrun haddress

private theorem compareCellCoordinate_writesWithin
    (tm : TM workTapeCount)
    (regs : NeighborhoodTrial.Registers controller) :
    Footprint.CmdWritesWithin (bankRegisters regs).footprint
      (compareCellCoordinate tm regs) := by
  have bankMem (slot : Fin 12) :
      (bankRegisters regs).index slot ∈
        (bankRegisters regs).footprint :=
    (bankRegisters regs).index_mem_footprint slot
  have hprepare :
      Footprint.CmdWritesWithin (bankRegisters regs).footprint
        (prepareCoordinate regs) := by
    simp only [prepareCoordinate, Cmd.seqList,
      Footprint.CmdWritesWithin, Footprint.BasicWritesWithin]
    exact ⟨bankMem 11, bankMem 11, bankMem 11,
      bankMem 11, bankMem 11⟩
  have hequal :
      Footprint.CmdWritesWithin (bankRegisters regs).footprint
        (equalValues regs (bankRegisters regs).result
          (bankRegisters regs).indexCount
          (bankRegisters regs).result) := by
    simp only [equalValues, Cmd.seqList,
      Footprint.CmdWritesWithin, Footprint.BasicWritesWithin]
    exact
      ⟨bankMem 5, bankMem 4, bankMem 10,
        ⟨bankMem 10, bankMem 10⟩⟩
  simp only [compareCellCoordinate, Cmd.seqList,
    Footprint.CmdWritesWithin]
  exact
    ⟨hprepare, decodeCellCoordinate_writesWithin tm regs,
      hequal, bankMem 9⟩

private theorem compareCellCoordinate_runs
    (tm : TM workTapeCount)
    (regs : NeighborhoodTrial.Registers controller)
    (store : Store)
    (blockLength cursor width bitsLeft actualSymbol word : ℕ)
    (hblock :
      store (Layout.blockLength regs) = blockLength)
    (hcursor : store (Layout.active regs) = cursor)
    (hwidth : store (chunkBits regs) = width)
    (hremaining : store (remaining regs) = bitsLeft)
    (hactual :
      store (bankRegisters regs).indexCount = actualSymbol)
    (hword : store (bankRegisters regs).word = word) :
    ∃ final,
      Runs (compareCellCoordinate tm regs) store final ∧
      final (bitValue regs) =
        (if (cursor * width + width - bitsLeft -
                (Fintype.card tm.Q + blockLength)) % 4 =
              actualSymbol then
          1
        else
          0) ∧
      final (bankRegisters regs).word = word ∧
      final (CombineValue.rangeRegisters regs).one = 1 ∧
      ∀ address, address ∉ (bankRegisters regs).footprint →
        final address = store address := by
  let current := cursor * width + width - bitsLeft
  obtain ⟨prepared, hprepare, hpreparedCoordinate,
      hprepareOutside⟩ :=
    prepareCoordinate_runs regs store cursor width bitsLeft
      hcursor hwidth hremaining
  have hpreparedBlock :
      prepared (Layout.blockLength regs) = blockLength :=
    (hprepareOutside _ (regs.injective.ne (by decide))).trans
      hblock
  have hpreparedActual :
      prepared (bankRegisters regs).indexCount = actualSymbol :=
    (hprepareOutside _ ((bankRegisters regs).index_ne
      (by decide : (8 : Fin 12) ≠ 11))).trans hactual
  have hpreparedWord :
      prepared (bankRegisters regs).word = word :=
    (hprepareOutside _ ((bankRegisters regs).index_ne
      (by decide : (0 : Fin 12) ≠ 11))).trans hword
  obtain ⟨decoded, hdecode, hdecodedCandidate, _,
      _, hdecodedActual, hdecodedWord, _, _⟩ :=
    decodeCellCoordinate_runs tm regs prepared blockLength
      current word hpreparedBlock hpreparedCoordinate hpreparedWord
  obtain ⟨compared, hequal, hcomparedBit,
      hcompareOutside⟩ :=
    equalValues_runs regs (bankRegisters regs).result
      (bankRegisters regs).indexCount
      (bankRegisters regs).result decoded
      ((current - (Fintype.card tm.Q + blockLength)) % 4)
      actualSymbol hdecodedCandidate
      (hdecodedActual.trans hpreparedActual)
      ((bankRegisters regs).index_ne
        (by decide : (5 : Fin 12) ≠ 10))
      ((bankRegisters regs).index_ne
        (by decide : (5 : Fin 12) ≠ 8))
      ((bankRegisters regs).index_ne
        (by decide : (5 : Fin 12) ≠ 4))
  let final :=
    (Basic.imm (CombineValue.rangeRegisters regs).one 1).exec
      compared
  have hrestore :
      Runs (restoreRangeOne regs) compared final :=
    Runs.basic _ _
  have hrun :
      Runs (compareCellCoordinate tm regs) store final := by
    simpa [compareCellCoordinate, Cmd.seqList, final,
      restoreRangeOne] using
      Runs.seq hprepare
        (Runs.seq hdecode (Runs.seq hequal hrestore))
  have hbit_ne_one :
      bitValue regs ≠ (CombineValue.rangeRegisters regs).one :=
    regs.injective.ne (by decide)
  have hcomparedWord :
      compared (bankRegisters regs).word = word :=
    (hcompareOutside _
      ((bankRegisters regs).index_ne
        (by decide : (0 : Fin 12) ≠ 5))
      ((bankRegisters regs).index_ne
        (by decide : (0 : Fin 12) ≠ 4))
      ((bankRegisters regs).index_ne
        (by decide : (0 : Fin 12) ≠ 10))).trans hdecodedWord
  have hword_ne_one :
      (bankRegisters regs).word ≠
        (CombineValue.rangeRegisters regs).one :=
    regs.injective.ne (by decide)
  refine
    ⟨final, hrun, ?_, ?_,
      by simp [final, Basic.exec], ?_⟩
  · simp [final, Basic.exec, Function.update_of_ne,
      hbit_ne_one, hcomparedBit, current]
  · simp [final, Basic.exec, Function.update_of_ne,
      hword_ne_one, hcomparedWord]
  · intro address haddress
    exact Footprint.runs_eq_outside
      (compareCellCoordinate_writesWithin tm regs)
      hrun haddress

private theorem fixed_index_not_mem_headScan
    (regs : NeighborhoodTrial.Registers controller)
    (slot : Fin 34)
    (hbank :
      ∀ bankSlot,
        slot ≠ PackedLocalHeadScan.bankMap bankSlot)
    (hcountdown : slot ≠ 30) :
    regs.index slot ∉ PackedLocalHeadScan.footprint regs := by
  simp only [PackedLocalHeadScan.footprint, Finset.mem_union,
    Finset.mem_singleton, not_or]
  exact
    ⟨fixed_index_not_mem_bank regs slot hbank,
      regs.injective.ne hcountdown⟩

private theorem cellBit_writesWithin
    (tm : TM workTapeCount)
    (tape : TapeIndex workTapeCount)
    (localBlock : ℕ)
    (regs : NeighborhoodTrial.Registers controller) :
    Footprint.CmdWritesWithin
      (PackedLocalHeadScan.footprint regs)
      (cellBit tm tape localBlock regs) := by
  simp only [cellBit, Cmd.seqList, Footprint.CmdWritesWithin]
  exact
    ⟨cmdWritesWithin_mono
        (decodeCellCoordinate_writesWithin tm regs)
        (by
          intro address haddress
          exact Finset.mem_union_left _ haddress),
      readSelectedCell_writesWithin tm tape localBlock regs,
      cmdWritesWithin_mono
        (compareCellCoordinate_writesWithin tm regs)
        (by
          intro address haddress
          exact Finset.mem_union_left _ haddress)⟩

private theorem cellBit_runs
    (tm : TM workTapeCount)
    (blockLength : ℕ)
    (center : ℕ)
    (tape : TapeIndex workTapeCount)
    (slot : Slot)
    (localBlock : ℕ)
    (regs : NeighborhoodTrial.Registers controller)
    (store : Store)
    (word cursor width bitsLeft : ℕ)
    (hblock : store (Layout.blockLength regs) = blockLength)
    (hword : store (bankRegisters regs).word = word)
    (hcursor : store (Layout.active regs) = cursor)
    (hwidth : store (chunkBits regs) = width)
    (hremaining : store (remaining regs) = bitsLeft)
    (hcoordinate :
      store (coordinate regs) =
        cursor * width + width - bitsLeft)
    (hlower :
      Fintype.card tm.Q + blockLength ≤
        cursor * width + width - bitsLeft)
    (hupper :
      cursor * width + width - bitsLeft <
        Fintype.card tm.Q + blockLength + blockLength * 4)
    (hlocal :
      ∀ offset, offset < blockLength →
        localBlock * blockLength + offset =
          PackedLocalConfiguration.requestedLocalPosition
            blockLength center slot offset) :
    ∃ final,
      Runs (cellBit tm tape localBlock regs) store final ∧
      final (bitValue regs) =
        (if
          (cursor * width + width - bitsLeft -
              (Fintype.card tm.Q + blockLength)) % 4 =
            PackedLocalConfiguration.symbolPart
              (PackedDigits.digit
                (PackedLocalConfiguration.radix tm) word
                (PackedLocalConfiguration.cellIndex blockLength tape
                  (PackedLocalConfiguration.requestedLocalPosition
                    blockLength center slot
                    ((cursor * width + width - bitsLeft -
                      (Fintype.card tm.Q + blockLength)) / 4)))) then
          1
        else
          0) ∧
      final (bankRegisters regs).word = word ∧
      final (CombineValue.rangeRegisters regs).one = 1 ∧
      ∀ address,
        address ∉ PackedLocalHeadScan.footprint regs →
          final address = store address := by
  let current := cursor * width + width - bitsLeft
  let cellCode :=
    current - (Fintype.card tm.Q + blockLength)
  let offset := cellCode / 4
  have hcellCode : cellCode < blockLength * 4 := by
    dsimp only [cellCode, current]
    omega
  have hoffset : offset < blockLength := by
    dsimp only [offset]
    omega
  obtain ⟨decoded, hdecode, hdecodedCandidate,
      hdecodedOffset, _, _, hdecodedWord, hdecodedBlock,
      hdecodeOutside⟩ :=
    decodeCellCoordinate_runs tm regs store blockLength current word
      hblock hcoordinate hword
  obtain ⟨read, hread, hreadActual, hreadWord,
      hreadBlock, hreadOutside⟩ :=
    readSelectedCell_runs tm tape localBlock regs decoded
      blockLength offset word hdecodedBlock hdecodedOffset
      hdecodedWord
  have hreadCursor :
      read (Layout.active regs) = cursor := by
    calc
      read (Layout.active regs) = decoded (Layout.active regs) :=
        hreadOutside _
          (fixed_index_not_mem_headScan regs 28
            (by
              intro bankSlot
              fin_cases bankSlot <;> decide)
            (by decide))
      _ = store (Layout.active regs) :=
        hdecodeOutside _
          (fixed_index_not_mem_bank regs 28 (by
            intro bankSlot
            fin_cases bankSlot <;> decide))
      _ = cursor := hcursor
  have hreadWidth :
      read (chunkBits regs) = width := by
    calc
      read (chunkBits regs) = decoded (chunkBits regs) :=
        hreadOutside _
          (fixed_index_not_mem_headScan regs 19
            (by
              intro bankSlot
              fin_cases bankSlot <;> decide)
            (by decide))
      _ = store (chunkBits regs) :=
        hdecodeOutside _
          (fixed_index_not_mem_bank regs 19 (by
            intro bankSlot
            fin_cases bankSlot <;> decide))
      _ = width := hwidth
  have hreadRemaining :
      read (remaining regs) = bitsLeft := by
    calc
      read (remaining regs) = decoded (remaining regs) :=
        hreadOutside _
          (fixed_index_not_mem_headScan regs 10
            (by
              intro bankSlot
              fin_cases bankSlot <;> decide)
            (by decide))
      _ = store (remaining regs) :=
        hdecodeOutside _
          (fixed_index_not_mem_bank regs 10 (by
            intro bankSlot
            fin_cases bankSlot <;> decide))
      _ = bitsLeft := hremaining
  obtain ⟨final, hcompare, hcompareBit, hcompareWord,
      hcompareOne, _⟩ :=
    compareCellCoordinate_runs tm regs read blockLength cursor
      width bitsLeft
      (PackedDigits.digit
        (PackedLocalConfiguration.radix tm) word
        (PackedLocalConfiguration.cellIndex blockLength tape
          (localBlock * blockLength + offset)) % 4)
      word hreadBlock hreadCursor hreadWidth hreadRemaining
      hreadActual hreadWord
  have hrun :
      Runs (cellBit tm tape localBlock regs) store final := by
    simpa [cellBit, Cmd.seqList] using
      Runs.seq hdecode (Runs.seq hread hcompare)
  have hlocalPosition :
      localBlock * blockLength + offset =
        PackedLocalConfiguration.requestedLocalPosition
          blockLength center slot offset :=
    hlocal offset hoffset
  refine ⟨final, hrun, ?_, hcompareWord, hcompareOne, ?_⟩
  · simpa [current, cellCode, offset,
      PackedLocalConfiguration.symbolPart, hlocalPosition] using
      hcompareBit
  · intro address haddress
    exact Footprint.runs_eq_outside
      (cellBit_writesWithin tm tape localBlock regs)
      hrun haddress

private theorem boundaryLocalBlock_requested
    (blockLength offset : ℕ) (slot : Slot)
    :
    boundaryLocalBlock slot * blockLength + offset =
      PackedLocalConfiguration.requestedLocalPosition
        blockLength 0 slot offset := by
  cases slot <;>
    simp [boundaryLocalBlock,
      PackedLocalConfiguration.requestedLocalPosition,
      neighborBlock, PackedLocalConfiguration.windowStart]

private theorem regularLocalBlock_requested
    (blockLength center offset : ℕ) (slot : Slot)
    (hcenter : 0 < center)
    (hoffset : offset < blockLength) :
    regularLocalBlock slot * blockLength + offset =
      PackedLocalConfiguration.requestedLocalPosition
        blockLength center slot offset := by
  cases center with
  | zero =>
      omega
  | succ center =>
      cases slot <;>
        simp [regularLocalBlock,
          PackedLocalConfiguration.requestedLocalPosition,
          neighborBlock, PackedLocalConfiguration.windowStart,
          Nat.add_mul]
      all_goals omega

private theorem payloadBit_writesWithin
    (tm : TM workTapeCount)
    (tape : TapeIndex workTapeCount)
    (localBlock : ℕ)
    (regs : NeighborhoodTrial.Registers controller) :
    Footprint.CmdWritesWithin
      (PackedLocalHeadScan.footprint regs)
      (payloadBit tm tape localBlock regs) := by
  have bankMem (bankSlot : Fin 12) :
      (bankRegisters regs).index bankSlot ∈
        PackedLocalHeadScan.footprint regs :=
    Finset.mem_union_left _
      ((bankRegisters regs).index_mem_footprint bankSlot)
  simp only [payloadBit, Cmd.basics,
    Footprint.CmdWritesWithin, Footprint.BasicWritesWithin]
  exact
    ⟨⟨bankMem 7, bankMem 1, bankMem 7, bankMem 1,
        bankMem 5⟩,
      bankMem 10, cellBit_writesWithin tm tape localBlock regs⟩

private theorem payloadBit_runs
    (tm : TM workTapeCount)
    (blockLength center : ℕ)
    (tape : TapeIndex workTapeCount)
    (slot : Slot)
    (localBlock : ℕ)
    (regs : NeighborhoodTrial.Registers controller)
    (store : Store)
    (word cursor width bitsLeft : ℕ)
    (hblock : store (Layout.blockLength regs) = blockLength)
    (hword : store (bankRegisters regs).word = word)
    (hone :
      store (CombineValue.rangeRegisters regs).one = 1)
    (hcursor : store (Layout.active regs) = cursor)
    (hwidth : store (chunkBits regs) = width)
    (hremaining : store (remaining regs) = bitsLeft)
    (hcoordinate :
      store (coordinate regs) =
        cursor * width + width - bitsLeft)
    (hlower :
      Fintype.card tm.Q + blockLength ≤
        cursor * width + width - bitsLeft)
    (hlocal :
      ∀ offset, offset < blockLength →
        localBlock * blockLength + offset =
          PackedLocalConfiguration.requestedLocalPosition
            blockLength center slot offset) :
    ∃ final,
      Runs (payloadBit tm tape localBlock regs) store final ∧
      final (bitValue regs) =
        (if
          cursor * width + width - bitsLeft <
              Fintype.card tm.Q + blockLength +
                blockLength * 4 then
          if
            (cursor * width + width - bitsLeft -
                (Fintype.card tm.Q + blockLength)) % 4 =
              PackedLocalConfiguration.symbolPart
                (PackedDigits.digit
                  (PackedLocalConfiguration.radix tm) word
                  (PackedLocalConfiguration.cellIndex blockLength tape
                    (PackedLocalConfiguration.requestedLocalPosition
                      blockLength center slot
                      ((cursor * width + width - bitsLeft -
                        (Fintype.card tm.Q + blockLength)) / 4)))) then
            1
          else
            0
        else
          0) ∧
      final (bankRegisters regs).word = word ∧
      final (CombineValue.rangeRegisters regs).one = 1 ∧
      ∀ address,
        address ∉ PackedLocalHeadScan.footprint regs →
          final address = store address := by
  let ops : List Basic :=
    [.imm (bankRegisters regs).value 5,
      .mul (bankRegisters regs).buffer
        (bankRegisters regs).value (Layout.blockLength regs),
      .imm (bankRegisters regs).value (Fintype.card tm.Q),
      .add (bankRegisters regs).buffer
        (bankRegisters regs).value (bankRegisters regs).buffer,
      .sub (bankRegisters regs).test
        (bankRegisters regs).buffer (coordinate regs)]
  let tested := Basic.execList ops store
  have hsetup : Runs (Cmd.basics ops) store tested :=
    basics_runs ops store
  have htestedOutside :
      ∀ address,
        address ≠ (bankRegisters regs).value →
        address ≠ (bankRegisters regs).buffer →
        address ≠ (bankRegisters regs).test →
        tested address = store address := by
    intro address hvalue hbuffer htest
    simp [tested, ops, Basic.execList, Basic.exec,
      Function.update_of_ne, hvalue, hbuffer, htest]
  have htestedTest :
      tested (bankRegisters regs).test =
        Fintype.card tm.Q + blockLength + blockLength * 4 -
          (cursor * width + width - bitsLeft) := by
    have hraw :
        tested (bankRegisters regs).test =
          Fintype.card tm.Q + 5 * blockLength -
            store (coordinate regs) := by
      have hblock_ne_value :
          Layout.blockLength regs ≠
            (bankRegisters regs).value :=
        regs.injective.ne (by decide)
      simp [tested, ops, Basic.execList, Basic.exec,
        Function.update_of_ne, hblock, hblock_ne_value,
        (bankRegisters regs).index_ne
          (by decide : (1 : Fin 12) ≠ 7),
        (bankRegisters regs).index_ne
          (by decide : (11 : Fin 12) ≠ 7),
        (bankRegisters regs).index_ne
          (by decide : (11 : Fin 12) ≠ 1)]
    rw [hraw, hcoordinate]
    omega
  have htestedBlock :
      tested (Layout.blockLength regs) = blockLength :=
    (htestedOutside _ (regs.injective.ne (by decide))
      (regs.injective.ne (by decide))
      (regs.injective.ne (by decide))).trans hblock
  have htestedWord :
      tested (bankRegisters regs).word = word :=
    (htestedOutside _
      ((bankRegisters regs).index_ne
        (by decide : (0 : Fin 12) ≠ 7))
      ((bankRegisters regs).index_ne
        (by decide : (0 : Fin 12) ≠ 1))
      ((bankRegisters regs).index_ne
        (by decide : (0 : Fin 12) ≠ 5))).trans hword
  have htestedOne :
      tested (CombineValue.rangeRegisters regs).one = 1 :=
    (htestedOutside _ (regs.injective.ne (by decide))
      (regs.injective.ne (by decide))
      (regs.injective.ne (by decide))).trans hone
  have htestedCursor :
      tested (Layout.active regs) = cursor :=
    (htestedOutside _ (regs.injective.ne (by decide))
      (regs.injective.ne (by decide))
      (regs.injective.ne (by decide))).trans hcursor
  have htestedWidth :
      tested (chunkBits regs) = width :=
    (htestedOutside _ (regs.injective.ne (by decide))
      (regs.injective.ne (by decide))
      (regs.injective.ne (by decide))).trans hwidth
  have htestedRemaining :
      tested (remaining regs) = bitsLeft :=
    (htestedOutside _ (regs.injective.ne (by decide))
      (regs.injective.ne (by decide))
      (regs.injective.ne (by decide))).trans hremaining
  have htestedCoordinate :
      tested (coordinate regs) =
        cursor * width + width - bitsLeft :=
    (htestedOutside _
      ((bankRegisters regs).index_ne
        (by decide : (11 : Fin 12) ≠ 7))
      ((bankRegisters regs).index_ne
        (by decide : (11 : Fin 12) ≠ 1))
      ((bankRegisters regs).index_ne
        (by decide : (11 : Fin 12) ≠ 5))).trans hcoordinate
  by_cases hupper :
      cursor * width + width - bitsLeft <
        Fintype.card tm.Q + blockLength + blockLength * 4
  · have htest :
        tested (bankRegisters regs).test ≠ 0 := by
      rw [htestedTest]
      omega
    obtain ⟨final, hcell, hcellBit, hcellWord, hcellOne, _⟩ :=
      cellBit_runs tm blockLength center tape slot localBlock regs
        tested word cursor width bitsLeft htestedBlock htestedWord
        htestedCursor htestedWidth htestedRemaining
        htestedCoordinate hlower hupper hlocal
    have hbranch :
        Runs
          (.ifZero (bankRegisters regs).test
            (.basic (.imm (bitValue regs) 0))
            (cellBit tm tape localBlock regs))
          tested final :=
      Runs.ifNonzero htest hcell
    have hrun :
        Runs (payloadBit tm tape localBlock regs) store final := by
      simpa [payloadBit, ops] using Runs.seq hsetup hbranch
    refine ⟨final, hrun, ?_, hcellWord, hcellOne, ?_⟩
    · simpa [hupper] using hcellBit
    · intro address haddress
      exact Footprint.runs_eq_outside
        (payloadBit_writesWithin tm tape localBlock regs)
        hrun haddress
  · have htest :
        tested (bankRegisters regs).test = 0 := by
      rw [htestedTest]
      omega
    let final := (Basic.imm (bitValue regs) 0).exec tested
    have hbranch :
        Runs
          (.ifZero (bankRegisters regs).test
            (.basic (.imm (bitValue regs) 0))
            (cellBit tm tape localBlock regs))
          tested final :=
      Runs.ifZero htest (Runs.basic _ _)
    have hrun :
        Runs (payloadBit tm tape localBlock regs) store final := by
      simpa [payloadBit, ops] using Runs.seq hsetup hbranch
    have hword_ne_bit :
        (bankRegisters regs).word ≠ bitValue regs :=
      (bankRegisters regs).index_ne (by decide)
    have hone_ne_bit :
        (CombineValue.rangeRegisters regs).one ≠ bitValue regs :=
      regs.injective.ne (by decide)
    refine ⟨final, hrun, ?_, ?_, ?_, ?_⟩
    · simp [final, Basic.exec, hupper]
    · simp [final, Basic.exec, Function.update_of_ne,
        hword_ne_bit, htestedWord]
    · simp [final, Basic.exec, Function.update_of_ne,
        hone_ne_bit, htestedOne]
    · intro address haddress
      exact Footprint.runs_eq_outside
        (payloadBit_writesWithin tm tape localBlock regs)
        hrun haddress

private theorem nonStateBit_writesWithin
    (tm : TM workTapeCount)
    (tape : TapeIndex workTapeCount)
    (localBlock : ℕ)
    (regs : NeighborhoodTrial.Registers controller) :
    Footprint.CmdWritesWithin
      (PackedLocalHeadScan.footprint regs)
      (nonStateBit tm tape localBlock regs) := by
  have bankMem (bankSlot : Fin 12) :
      (bankRegisters regs).index bankSlot ∈
        PackedLocalHeadScan.footprint regs :=
    Finset.mem_union_left _
      ((bankRegisters regs).index_mem_footprint bankSlot)
  simp only [nonStateBit, Cmd.basics,
    Footprint.CmdWritesWithin]
  exact
    ⟨⟨bankMem 7, bankMem 7, bankMem 5⟩,
      payloadBit_writesWithin tm tape localBlock regs,
      headBit_writesWithin tm tape regs⟩

private theorem nonStateBit_runs
    (tm : TM workTapeCount)
    (order :
      NeighborhoodExecutableEvaluation.FiniteEncoding.StateOrder tm)
    (blockLength : ℕ) (hpositive : 0 < blockLength)
    (centers : TapeIndex workTapeCount → ℕ)
    (cfg : Cfg workTapeCount tm.Q)
    (center : ℕ)
    (tape : TapeIndex workTapeCount)
    (slot : Slot)
    (localBlock : ℕ)
    (suffix word : ℕ)
    (regs : NeighborhoodTrial.Registers controller)
    (store : Store)
    (cursor width bitsLeft : ℕ)
    (hblock : store (Layout.blockLength regs) = blockLength)
    (hword : store (bankRegisters regs).word = word)
    (hrep :
      PackedLocalRepresentation.Represents tm order blockLength
        centers cfg suffix word)
    (hone :
      store (CombineValue.rangeRegisters regs).one = 1)
    (hcursor : store (Layout.active regs) = cursor)
    (hwidth : store (chunkBits regs) = width)
    (hremaining : store (remaining regs) = bitsLeft)
    (hcoordinate :
      store (coordinate regs) =
        cursor * width + width - bitsLeft)
    (hstateLower :
      Fintype.card tm.Q ≤
        cursor * width + width - bitsLeft)
    (hheadLower :
      PackedLocalConfiguration.windowStart
          blockLength (centers tape) ≤
        (tapeAt cfg tape).head)
    (hheadUpper :
      (tapeAt cfg tape).head <
        PackedLocalConfiguration.windowStart
            blockLength (centers tape) +
          PackedLocalConfiguration.tapeSpan blockLength)
    (hlocal :
      ∀ offset, offset < blockLength →
        localBlock * blockLength + offset =
          PackedLocalConfiguration.requestedLocalPosition
            blockLength center slot offset) :
    ∃ final,
      Runs (nonStateBit tm tape localBlock regs) store final ∧
      final (bitValue regs) =
        (if
          PackedLocalConfiguration.outputBitFromWord
            tm blockLength
              (cursor * width + width - bitsLeft)
              center tape slot word then
          1
        else
          0) ∧
      final (bankRegisters regs).word = word ∧
      final (CombineValue.rangeRegisters regs).one = 1 ∧
      ∀ address,
        address ∉ PackedLocalHeadScan.footprint regs →
          final address = store address := by
  let current := cursor * width + width - bitsLeft
  let ops : List Basic :=
    [.imm (bankRegisters regs).value (Fintype.card tm.Q),
      .add (bankRegisters regs).value
        (bankRegisters regs).value (Layout.blockLength regs),
      .sub (bankRegisters regs).test
        (bankRegisters regs).value (coordinate regs)]
  let tested := Basic.execList ops store
  have hsetup : Runs (Cmd.basics ops) store tested :=
    basics_runs ops store
  have htestedOutside :
      ∀ address,
        address ≠ (bankRegisters regs).value →
        address ≠ (bankRegisters regs).test →
        tested address = store address := by
    intro address hvalue htest
    simp [tested, ops, Basic.execList, Basic.exec,
      Function.update_of_ne, hvalue, htest]
  have htestedTest :
      tested (bankRegisters regs).test =
        Fintype.card tm.Q + blockLength - current := by
    have hblock_ne_value :
        Layout.blockLength regs ≠
          (bankRegisters regs).value :=
      regs.injective.ne (by decide)
    have hraw :
        tested (bankRegisters regs).test =
          Fintype.card tm.Q + blockLength -
            store (coordinate regs) := by
      simp [tested, ops, Basic.execList, Basic.exec,
        Function.update_of_ne, hblock, hblock_ne_value,
        (bankRegisters regs).index_ne
          (by decide : (11 : Fin 12) ≠ 7)]
    rw [hraw, hcoordinate]
  have htestedBlock :
      tested (Layout.blockLength regs) = blockLength :=
    (htestedOutside _ (regs.injective.ne (by decide))
      (regs.injective.ne (by decide))).trans hblock
  have htestedWord :
      tested (bankRegisters regs).word = word :=
    (htestedOutside _
      ((bankRegisters regs).index_ne
        (by decide : (0 : Fin 12) ≠ 7))
      ((bankRegisters regs).index_ne
        (by decide : (0 : Fin 12) ≠ 5))).trans hword
  have htestedOne :
      tested (CombineValue.rangeRegisters regs).one = 1 :=
    (htestedOutside _ (regs.injective.ne (by decide))
      (regs.injective.ne (by decide))).trans hone
  have htestedCursor :
      tested (Layout.active regs) = cursor :=
    (htestedOutside _ (regs.injective.ne (by decide))
      (regs.injective.ne (by decide))).trans hcursor
  have htestedWidth :
      tested (chunkBits regs) = width :=
    (htestedOutside _ (regs.injective.ne (by decide))
      (regs.injective.ne (by decide))).trans hwidth
  have htestedRemaining :
      tested (remaining regs) = bitsLeft :=
    (htestedOutside _ (regs.injective.ne (by decide))
      (regs.injective.ne (by decide))).trans hremaining
  have htestedCoordinate :
      tested (coordinate regs) = current :=
    (htestedOutside _
      ((bankRegisters regs).index_ne
        (by decide : (11 : Fin 12) ≠ 7))
      ((bankRegisters regs).index_ne
        (by decide : (11 : Fin 12) ≠ 5))).trans hcoordinate
  by_cases hhead :
      current < Fintype.card tm.Q + blockLength
  · have htest :
        tested (bankRegisters regs).test ≠ 0 := by
      rw [htestedTest]
      omega
    obtain ⟨final, hheadRun, hheadBit, hheadWord,
        hheadOne, _⟩ :=
      headBit_runs tm order blockLength hpositive centers cfg tape
        suffix word regs tested cursor width bitsLeft htestedBlock
        htestedWord hrep htestedOne htestedCursor htestedWidth
        htestedRemaining hheadLower hheadUpper
    have hbranch :
        Runs
          (.ifZero (bankRegisters regs).test
            (payloadBit tm tape localBlock regs)
            (headBit tm tape regs))
          tested final :=
      Runs.ifNonzero htest hheadRun
    have hrun :
        Runs (nonStateBit tm tape localBlock regs) store final := by
      simpa [nonStateBit, ops] using Runs.seq hsetup hbranch
    refine ⟨final, hrun, ?_, hheadWord, hheadOne, ?_⟩
    · rw [hheadBit]
      simp [PackedLocalConfiguration.outputBitFromWord,
        current, Nat.not_lt.mpr hstateLower, hhead]
    · intro address haddress
      exact Footprint.runs_eq_outside
        (nonStateBit_writesWithin tm tape localBlock regs)
        hrun haddress
  · have htest :
        tested (bankRegisters regs).test = 0 := by
      rw [htestedTest]
      omega
    have hlower :
        Fintype.card tm.Q + blockLength ≤ current :=
      Nat.le_of_not_gt hhead
    obtain ⟨final, hpayload, hpayloadBit, hpayloadWord,
        hpayloadOne, _⟩ :=
      payloadBit_runs tm blockLength center tape slot localBlock regs
        tested word cursor width bitsLeft htestedBlock htestedWord
        htestedOne htestedCursor htestedWidth htestedRemaining
        htestedCoordinate hlower hlocal
    have hbranch :
        Runs
          (.ifZero (bankRegisters regs).test
            (payloadBit tm tape localBlock regs)
            (headBit tm tape regs))
          tested final :=
      Runs.ifZero htest hpayload
    have hrun :
        Runs (nonStateBit tm tape localBlock regs) store final := by
      simpa [nonStateBit, ops] using Runs.seq hsetup hbranch
    refine ⟨final, hrun, ?_, hpayloadWord, hpayloadOne, ?_⟩
    · rw [hpayloadBit]
      simp [PackedLocalConfiguration.outputBitFromWord,
        current, Nat.not_lt.mpr hstateLower, hhead, hlower]
      split_ifs <;> simp_all
    · intro address haddress
      exact Footprint.runs_eq_outside
        (nonStateBit_writesWithin tm tape localBlock regs)
        hrun haddress

private theorem prepareCoordinate_writesWithin
    (regs : NeighborhoodTrial.Registers controller) :
    Footprint.CmdWritesWithin
      (bankRegisters regs).footprint
      (prepareCoordinate regs) := by
  simp only [prepareCoordinate, Cmd.seqList,
    Footprint.CmdWritesWithin, Footprint.BasicWritesWithin]
  exact
    ⟨(bankRegisters regs).index_mem_footprint 11,
      (bankRegisters regs).index_mem_footprint 11,
      (bankRegisters regs).index_mem_footprint 11,
      (bankRegisters regs).index_mem_footprint 11,
      (bankRegisters regs).index_mem_footprint 11⟩

private theorem outputBit_writesWithin
    (tm : TM workTapeCount)
    (tape : TapeIndex workTapeCount)
    (localBlock : ℕ)
    (regs : NeighborhoodTrial.Registers controller) :
    Footprint.CmdWritesWithin
      (PackedLocalHeadScan.footprint regs)
      (outputBit tm tape localBlock regs) := by
  have bankMem (bankSlot : Fin 12) :
      (bankRegisters regs).index bankSlot ∈
        PackedLocalHeadScan.footprint regs :=
    Finset.mem_union_left _
      ((bankRegisters regs).index_mem_footprint bankSlot)
  simp only [outputBit, Cmd.basics,
    Footprint.CmdWritesWithin]
  exact
    ⟨cmdWritesWithin_mono
        (prepareCoordinate_writesWithin regs)
        (by
          intro address haddress
          exact Finset.mem_union_left _ haddress),
      ⟨bankMem 7, bankMem 5⟩,
      nonStateBit_writesWithin tm tape localBlock regs,
      stateBit_writesWithin tm regs⟩

private theorem outputBit_runs
    (tm : TM workTapeCount)
    (order :
      NeighborhoodExecutableEvaluation.FiniteEncoding.StateOrder tm)
    (blockLength : ℕ) (hpositive : 0 < blockLength)
    (centers : TapeIndex workTapeCount → ℕ)
    (cfg : Cfg workTapeCount tm.Q)
    (center : ℕ)
    (tape : TapeIndex workTapeCount)
    (slot : Slot)
    (localBlock : ℕ)
    (suffix word : ℕ)
    (regs : NeighborhoodTrial.Registers controller)
    (store : Store)
    (cursor width bitsLeft : ℕ)
    (hblock : store (Layout.blockLength regs) = blockLength)
    (hword : store (bankRegisters regs).word = word)
    (hrep :
      PackedLocalRepresentation.Represents tm order blockLength
        centers cfg suffix word)
    (hone :
      store (CombineValue.rangeRegisters regs).one = 1)
    (hcursor : store (Layout.active regs) = cursor)
    (hwidth : store (chunkBits regs) = width)
    (hremaining : store (remaining regs) = bitsLeft)
    (hheadLower :
      PackedLocalConfiguration.windowStart
          blockLength (centers tape) ≤
        (tapeAt cfg tape).head)
    (hheadUpper :
      (tapeAt cfg tape).head <
        PackedLocalConfiguration.windowStart
            blockLength (centers tape) +
          PackedLocalConfiguration.tapeSpan blockLength)
    (hlocal :
      ∀ offset, offset < blockLength →
        localBlock * blockLength + offset =
          PackedLocalConfiguration.requestedLocalPosition
            blockLength center slot offset) :
    ∃ final,
      Runs (outputBit tm tape localBlock regs) store final ∧
      final (bitValue regs) =
        (if
          PackedLocalConfiguration.outputBitFromWord
            tm blockLength
              (cursor * width + width - bitsLeft)
              center tape slot word then
          1
        else
          0) ∧
      final (bankRegisters regs).word = word ∧
      final (CombineValue.rangeRegisters regs).one = 1 ∧
      ∀ address,
        address ∉ PackedLocalHeadScan.footprint regs →
          final address = store address := by
  let current := cursor * width + width - bitsLeft
  obtain ⟨prepared, hprepare, hpreparedCoordinate,
      hprepareOutside⟩ :=
    prepareCoordinate_runs regs store cursor width bitsLeft
      hcursor hwidth hremaining
  have hpreparedBlock :
      prepared (Layout.blockLength regs) = blockLength :=
    (hprepareOutside _ (regs.injective.ne (by decide))).trans
      hblock
  have hpreparedWord :
      prepared (bankRegisters regs).word = word :=
    (hprepareOutside _
      ((bankRegisters regs).index_ne
        (by decide : (0 : Fin 12) ≠ 11))).trans hword
  have hpreparedOne :
      prepared (CombineValue.rangeRegisters regs).one = 1 :=
    (hprepareOutside _ (regs.injective.ne (by decide))).trans
      hone
  have hpreparedCursor :
      prepared (Layout.active regs) = cursor :=
    (hprepareOutside _ (regs.injective.ne (by decide))).trans
      hcursor
  have hpreparedWidth :
      prepared (chunkBits regs) = width :=
    (hprepareOutside _ (regs.injective.ne (by decide))).trans
      hwidth
  have hpreparedRemaining :
      prepared (remaining regs) = bitsLeft :=
    (hprepareOutside _ (regs.injective.ne (by decide))).trans
      hremaining
  let ops : List Basic :=
    [.imm (bankRegisters regs).value (Fintype.card tm.Q),
      .sub (bankRegisters regs).test
        (bankRegisters regs).value (coordinate regs)]
  let tested := Basic.execList ops prepared
  have hsetup : Runs (Cmd.basics ops) prepared tested :=
    basics_runs ops prepared
  have htestedOutside :
      ∀ address,
        address ≠ (bankRegisters regs).value →
        address ≠ (bankRegisters regs).test →
        tested address = prepared address := by
    intro address hvalue htest
    simp [tested, ops, Basic.execList, Basic.exec,
      Function.update_of_ne, hvalue, htest]
  have htestedTest :
      tested (bankRegisters regs).test =
        Fintype.card tm.Q - current := by
    have hraw :
        tested (bankRegisters regs).test =
          Fintype.card tm.Q -
            prepared (coordinate regs) := by
      simp [tested, ops, Basic.execList, Basic.exec,
        Function.update_of_ne,
        (bankRegisters regs).index_ne
          (by decide : (11 : Fin 12) ≠ 7)]
    rw [hraw, hpreparedCoordinate]
  have htestedBlock :
      tested (Layout.blockLength regs) = blockLength :=
    (htestedOutside _ (regs.injective.ne (by decide))
      (regs.injective.ne (by decide))).trans hpreparedBlock
  have htestedWord :
      tested (bankRegisters regs).word = word :=
    (htestedOutside _
      ((bankRegisters regs).index_ne
        (by decide : (0 : Fin 12) ≠ 7))
      ((bankRegisters regs).index_ne
        (by decide : (0 : Fin 12) ≠ 5))).trans hpreparedWord
  have htestedOne :
      tested (CombineValue.rangeRegisters regs).one = 1 :=
    (htestedOutside _ (regs.injective.ne (by decide))
      (regs.injective.ne (by decide))).trans hpreparedOne
  have htestedCursor :
      tested (Layout.active regs) = cursor :=
    (htestedOutside _ (regs.injective.ne (by decide))
      (regs.injective.ne (by decide))).trans hpreparedCursor
  have htestedWidth :
      tested (chunkBits regs) = width :=
    (htestedOutside _ (regs.injective.ne (by decide))
      (regs.injective.ne (by decide))).trans hpreparedWidth
  have htestedRemaining :
      tested (remaining regs) = bitsLeft :=
    (htestedOutside _ (regs.injective.ne (by decide))
      (regs.injective.ne (by decide))).trans hpreparedRemaining
  have htestedCoordinate :
      tested (coordinate regs) = current :=
    (htestedOutside _
      ((bankRegisters regs).index_ne
        (by decide : (11 : Fin 12) ≠ 7))
      ((bankRegisters regs).index_ne
        (by decide : (11 : Fin 12) ≠ 5))).trans
      hpreparedCoordinate
  by_cases hstate : current < Fintype.card tm.Q
  · have htest :
        tested (bankRegisters regs).test ≠ 0 := by
      rw [htestedTest]
      omega
    obtain ⟨final, hstateRun, hstateBit, hstateWord, _,
        hstateOne, _⟩ :=
      stateBit_runs tm regs tested word current
        htestedWord htestedCoordinate
    have hbranch :
        Runs
          (.ifZero (bankRegisters regs).test
            (nonStateBit tm tape localBlock regs)
            (stateBit tm regs))
          tested final :=
      Runs.ifNonzero htest hstateRun
    have hrun :
        Runs (outputBit tm tape localBlock regs) store final := by
      simpa [outputBit, ops] using
        Runs.seq hprepare (Runs.seq hsetup hbranch)
    refine ⟨final, hrun, ?_, hstateWord, hstateOne, ?_⟩
    · rw [hstateBit]
      simp [PackedLocalConfiguration.outputBitFromWord,
        current, hstate]
    · intro address haddress
      exact Footprint.runs_eq_outside
        (outputBit_writesWithin tm tape localBlock regs)
        hrun haddress
  · have htest :
        tested (bankRegisters regs).test = 0 := by
      rw [htestedTest]
      omega
    have hstateLower : Fintype.card tm.Q ≤ current :=
      Nat.le_of_not_gt hstate
    obtain ⟨final, hnonState, hnonStateBit,
        hnonStateWord, hnonStateOne, _⟩ :=
      nonStateBit_runs tm order blockLength hpositive centers cfg
        center tape slot localBlock suffix word regs tested cursor
        width bitsLeft htestedBlock htestedWord hrep htestedOne
        htestedCursor htestedWidth htestedRemaining
        htestedCoordinate hstateLower hheadLower hheadUpper hlocal
    have hbranch :
        Runs
          (.ifZero (bankRegisters regs).test
            (nonStateBit tm tape localBlock regs)
            (stateBit tm regs))
          tested final :=
      Runs.ifZero htest hnonState
    have hrun :
        Runs (outputBit tm tape localBlock regs) store final := by
      simpa [outputBit, ops] using
        Runs.seq hprepare (Runs.seq hsetup hbranch)
    refine
      ⟨final, hrun, hnonStateBit, hnonStateWord,
        hnonStateOne, ?_⟩
    intro address haddress
    exact Footprint.runs_eq_outside
      (outputBit_writesWithin tm tape localBlock regs)
      hrun haddress

private theorem outputBitValue_eq_bounded
    (tm : TM workTapeCount)
    (blockLength center : ℕ)
    (tape : TapeIndex workTapeCount)
    (slot : Slot)
    (word coordinate : ℕ) :
    (if
      PackedLocalConfiguration.outputBitFromWord
        tm blockLength coordinate center tape slot word then
      1
    else
      0) =
      PackedOutputChunkSemantics.boundedOutputBitValue
        tm blockLength center tape slot word coordinate := by
  unfold PackedOutputChunkSemantics.boundedOutputBitValue
  by_cases hcoordinate :
      coordinate <
        NeighborhoodExecutableEvaluation.payloadWidth
          tm blockLength
  · rw [PackedOutputChunkSemantics.boundedOutputBitFromWord_eq
      tm blockLength center tape slot word coordinate hcoordinate]
  · have hwidth :
        NeighborhoodExecutableEvaluation.payloadWidth
            tm blockLength =
          Fintype.card tm.Q + 5 * blockLength := by
      exact ComputationGraph.CompactEncoding.width_eq
        blockLength tm.Q
    have hge :
        Fintype.card tm.Q + 5 * blockLength ≤ coordinate := by
      rw [← hwidth]
      exact Nat.le_of_not_gt hcoordinate
    have hstate :
        ¬coordinate < Fintype.card tm.Q := by
      omega
    have hhead :
        ¬coordinate <
          Fintype.card tm.Q + blockLength := by
      omega
    have hcell :
        ¬(Fintype.card tm.Q + blockLength ≤ coordinate ∧
          coordinate <
            Fintype.card tm.Q + blockLength +
              blockLength * 4) := by
      omega
    have hwordBit :
        PackedLocalConfiguration.outputBitFromWord
            tm blockLength coordinate center tape slot word =
          false := by
      simp [PackedLocalConfiguration.outputBitFromWord,
        hstate, hhead, hcell]
    rw [PackedOutputChunkSemantics.boundedOutputBitFromWord_eq_false
      tm blockLength center tape slot word coordinate
      (Nat.le_of_not_gt hcoordinate)]
    simp [hwordBit]

private theorem chunkBody_writesWithin
    (tm : TM workTapeCount)
    (tape : TapeIndex workTapeCount)
    (localBlock : ℕ)
    (regs : NeighborhoodTrial.Registers controller) :
    Footprint.CmdWritesWithin
      (PackedLocalStep.footprint regs)
      (chunkBody tm tape localBlock regs) := by
  simp only [chunkBody, Cmd.basics,
    Footprint.CmdWritesWithin]
  exact
    ⟨cmdWritesWithin_mono
        (outputBit_writesWithin tm tape localBlock regs)
        (headScan_footprint_subset_step regs),
      step_slot_mem regs 1,
      step_slot_mem regs 15,
      step_slot_mem regs 15,
      step_slot_mem regs 5,
      step_slot_mem regs 6⟩

private theorem chunkBody_runs
    (tm : TM workTapeCount)
    (order :
      NeighborhoodExecutableEvaluation.FiniteEncoding.StateOrder tm)
    (blockLength : ℕ) (hpositive : 0 < blockLength)
    (centers : TapeIndex workTapeCount → ℕ)
    (cfg : Cfg workTapeCount tm.Q)
    (center : ℕ)
    (tape : TapeIndex workTapeCount)
    (slot : Slot)
    (localBlock : ℕ)
    (suffix word : ℕ)
    (regs : NeighborhoodTrial.Registers controller)
    (store : Store)
    (cursor width bitsLeft accumulatorValue : ℕ)
    (hblock : store (Layout.blockLength regs) = blockLength)
    (hword : store (bankRegisters regs).word = word)
    (hrep :
      PackedLocalRepresentation.Represents tm order blockLength
        centers cfg suffix word)
    (hone :
      store (CombineValue.rangeRegisters regs).one = 1)
    (hcursor : store (Layout.active regs) = cursor)
    (hwidth : store (chunkBits regs) = width)
    (hremaining :
      store (remaining regs) = bitsLeft + 1)
    (haccumulator :
      store (accumulator regs) = accumulatorValue)
    (hheadLower :
      PackedLocalConfiguration.windowStart
          blockLength (centers tape) ≤
        (tapeAt cfg tape).head)
    (hheadUpper :
      (tapeAt cfg tape).head <
        PackedLocalConfiguration.windowStart
            blockLength (centers tape) +
          PackedLocalConfiguration.tapeSpan blockLength)
    (hlocal :
      ∀ offset, offset < blockLength →
        localBlock * blockLength + offset =
          PackedLocalConfiguration.requestedLocalPosition
            blockLength center slot offset) :
    ∃ final,
      Runs (chunkBody tm tape localBlock regs) store final ∧
      final (accumulator regs) =
        2 * accumulatorValue +
          PackedOutputChunkSemantics.boundedOutputBitValue
            tm blockLength center tape slot word
              (cursor * width + width - (bitsLeft + 1)) ∧
      final (remaining regs) = bitsLeft ∧
      final (Layout.blockLength regs) = blockLength ∧
      final (bankRegisters regs).word = word ∧
      final (CombineValue.rangeRegisters regs).one = 1 ∧
      final (Layout.active regs) = cursor ∧
      final (chunkBits regs) = width ∧
      final (CombineValue.rangeRegisters regs).accumulator =
        store (CombineValue.rangeRegisters regs).accumulator ∧
      ∀ address,
        address ∉ PackedLocalStep.footprint regs →
          final address = store address := by
  obtain ⟨output, houtput, houtputBit, houtputWord,
      houtputOne, houtputOutside⟩ :=
    outputBit_runs tm order blockLength hpositive centers cfg center
      tape slot localBlock suffix word regs store cursor width
      (bitsLeft + 1) hblock hword hrep hone hcursor hwidth
      hremaining hheadLower hheadUpper hlocal
  rw [outputBitValue_eq_bounded tm blockLength center tape slot
    word (cursor * width + width - (bitsLeft + 1))] at houtputBit
  have houtputAccumulator :
      output (accumulator regs) = accumulatorValue := by
    calc
      output (accumulator regs) = store (accumulator regs) :=
        houtputOutside _
          (fixed_index_not_mem_headScan regs 31
            (by
              intro bankSlot
              fin_cases bankSlot <;> decide)
            (by decide))
      _ = accumulatorValue := haccumulator
  have houtputRemaining :
      output (remaining regs) = bitsLeft + 1 := by
    calc
      output (remaining regs) = store (remaining regs) :=
        houtputOutside _
          (fixed_index_not_mem_headScan regs 10
            (by
              intro bankSlot
              fin_cases bankSlot <;> decide)
            (by decide))
      _ = bitsLeft + 1 := hremaining
  have houtputBlock :
      output (Layout.blockLength regs) = blockLength := by
    calc
      output (Layout.blockLength regs) =
          store (Layout.blockLength regs) :=
        houtputOutside _
          (fixed_index_not_mem_headScan regs 2
            (by
              intro bankSlot
              fin_cases bankSlot <;> decide)
            (by decide))
      _ = blockLength := hblock
  have houtputCursor :
      output (Layout.active regs) = cursor := by
    calc
      output (Layout.active regs) = store (Layout.active regs) :=
        houtputOutside _
          (fixed_index_not_mem_headScan regs 28
            (by
              intro bankSlot
              fin_cases bankSlot <;> decide)
            (by decide))
      _ = cursor := hcursor
  have houtputWidth :
      output (chunkBits regs) = width := by
    calc
      output (chunkBits regs) = store (chunkBits regs) :=
        houtputOutside _
          (fixed_index_not_mem_headScan regs 19
            (by
              intro bankSlot
              fin_cases bankSlot <;> decide)
            (by decide))
      _ = width := hwidth
  let afterBase :=
    (Basic.imm (bankRegisters regs).base 2).exec output
  let afterScale :=
    (Basic.mul (accumulator regs) (accumulator regs)
      (bankRegisters regs).base).exec afterBase
  let afterAccumulate :=
    (Basic.add (accumulator regs) (bitValue regs)
      (accumulator regs)).exec afterScale
  let afterOne :=
    (Basic.imm (bankRegisters regs).one 1).exec afterAccumulate
  let final :=
    (Basic.sub (remaining regs) (remaining regs)
      (bankRegisters regs).one).exec afterOne
  have htail :
      Runs
        (Cmd.basics
          [.imm (bankRegisters regs).base 2,
            .mul (accumulator regs) (accumulator regs)
              (bankRegisters regs).base,
            .add (accumulator regs) (bitValue regs)
              (accumulator regs),
            .imm (bankRegisters regs).one 1,
            .sub (remaining regs) (remaining regs)
              (bankRegisters regs).one])
        output final := by
    simpa [Cmd.basics, Cmd.seqList, afterBase, afterScale,
      afterAccumulate, afterOne, final] using
      Runs.seq
        (Runs.basic
          (.imm (bankRegisters regs).base 2) output)
        (Runs.seq
          (Runs.basic
            (.mul (accumulator regs) (accumulator regs)
              (bankRegisters regs).base)
            afterBase)
          (Runs.seq
            (Runs.basic
              (.add (accumulator regs) (bitValue regs)
                (accumulator regs))
              afterScale)
            (Runs.seq
              (Runs.basic
                (.imm (bankRegisters regs).one 1)
                afterAccumulate)
              (Runs.basic
                (.sub (remaining regs) (remaining regs)
                  (bankRegisters regs).one)
                afterOne))))
  have hrun :
      Runs (chunkBody tm tape localBlock regs) store final := by
    exact Runs.seq houtput htail
  have hfinishOutside :
      ∀ address,
        address ≠ (bankRegisters regs).base →
        address ≠ accumulator regs →
        address ≠ (bankRegisters regs).one →
        address ≠ remaining regs →
        final address = output address := by
    intro address hbase hacc hone' hremaining'
    simp [final, afterOne, afterAccumulate, afterScale,
      afterBase, Basic.exec, Function.update_of_ne,
      hbase, hacc, hone', hremaining']
  have haccBase :
      accumulator regs ≠ (bankRegisters regs).base :=
    regs.injective.ne (by decide)
  have haccBit :
      accumulator regs ≠ bitValue regs :=
    regs.injective.ne (by decide)
  have haccOne :
      accumulator regs ≠ (bankRegisters regs).one :=
    regs.injective.ne (by decide)
  have haccRemaining :
      accumulator regs ≠ remaining regs :=
    regs.injective.ne (by decide)
  have hbitBase :
      bitValue regs ≠ (bankRegisters regs).base :=
    (bankRegisters regs).index_ne (by decide)
  have hremainingBase :
      remaining regs ≠ (bankRegisters regs).base :=
    regs.injective.ne (by decide)
  have hremainingAccumulator :
      remaining regs ≠ accumulator regs :=
    regs.injective.ne (by decide)
  have hremainingOne :
      remaining regs ≠ (bankRegisters regs).one :=
    regs.injective.ne (by decide)
  have hfinalAccumulator :
      final (accumulator regs) =
        2 * accumulatorValue +
          PackedOutputChunkSemantics.boundedOutputBitValue
            tm blockLength center tape slot word
              (cursor * width + width - (bitsLeft + 1)) := by
    simp [final, afterOne, afterAccumulate, afterScale,
      afterBase, Basic.exec, Function.update_of_ne,
      haccRemaining, haccOne, haccBit.symm, haccBase, hbitBase,
      houtputAccumulator, houtputBit]
    omega
  have hfinalRemaining :
      final (remaining regs) = bitsLeft := by
    simp [final, afterOne, afterAccumulate, afterScale,
      afterBase, Basic.exec, Function.update_of_ne,
      hremainingBase, hremainingAccumulator, hremainingOne,
      houtputRemaining]
  refine
    ⟨final, hrun, hfinalAccumulator, hfinalRemaining,
      ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact
      (hfinishOutside _ (regs.injective.ne (by decide))
        (regs.injective.ne (by decide))
        (regs.injective.ne (by decide))
        (regs.injective.ne (by decide))).trans houtputBlock
  · exact
      (hfinishOutside _
        ((bankRegisters regs).index_ne
          (by decide : (0 : Fin 12) ≠ 2))
        (regs.injective.ne (by decide))
        ((bankRegisters regs).index_ne
          (by decide : (0 : Fin 12) ≠ 6))
        (regs.injective.ne (by decide))).trans houtputWord
  · exact
      (hfinishOutside _ (regs.injective.ne (by decide))
        (regs.injective.ne (by decide))
        (regs.injective.ne (by decide))
        (regs.injective.ne (by decide))).trans houtputOne
  · exact
      (hfinishOutside _ (regs.injective.ne (by decide))
        (regs.injective.ne (by decide))
        (regs.injective.ne (by decide))
        (regs.injective.ne (by decide))).trans houtputCursor
  · exact
      (hfinishOutside _ (regs.injective.ne (by decide))
        (regs.injective.ne (by decide))
        (regs.injective.ne (by decide))
        (regs.injective.ne (by decide))).trans houtputWidth
  · calc
      final (CombineValue.rangeRegisters regs).accumulator =
          output (CombineValue.rangeRegisters regs).accumulator :=
        hfinishOutside _ (regs.injective.ne (by decide))
          (regs.injective.ne (by decide))
          (regs.injective.ne (by decide))
          (regs.injective.ne (by decide))
      _ = store (CombineValue.rangeRegisters regs).accumulator :=
        houtputOutside _
          (fixed_index_not_mem_headScan regs 18
            (by
              intro bankSlot
              fin_cases bankSlot <;> decide)
            (by decide))
  · intro address haddress
    exact Footprint.runs_eq_outside
      (chunkBody_writesWithin tm tape localBlock regs)
      hrun haddress

private theorem chunkLoop_runs
    (tm : TM workTapeCount)
    (order :
      NeighborhoodExecutableEvaluation.FiniteEncoding.StateOrder tm)
    (blockLength : ℕ) (hpositive : 0 < blockLength)
    (centers : TapeIndex workTapeCount → ℕ)
    (cfg : Cfg workTapeCount tm.Q)
    (center : ℕ)
    (tape : TapeIndex workTapeCount)
    (slot : Slot)
    (localBlock : ℕ)
    (suffix word : ℕ)
    (regs : NeighborhoodTrial.Registers controller)
    (store : Store)
    (cursor width remainingBits accumulatorValue : ℕ)
    (hbits : remainingBits ≤ width)
    (hblock : store (Layout.blockLength regs) = blockLength)
    (hword : store (bankRegisters regs).word = word)
    (hrep :
      PackedLocalRepresentation.Represents tm order blockLength
        centers cfg suffix word)
    (hone :
      store (CombineValue.rangeRegisters regs).one = 1)
    (hcursor : store (Layout.active regs) = cursor)
    (hwidth : store (chunkBits regs) = width)
    (hremaining :
      store (remaining regs) = remainingBits)
    (haccumulator :
      store (accumulator regs) = accumulatorValue)
    (hheadLower :
      PackedLocalConfiguration.windowStart
          blockLength (centers tape) ≤
        (tapeAt cfg tape).head)
    (hheadUpper :
      (tapeAt cfg tape).head <
        PackedLocalConfiguration.windowStart
            blockLength (centers tape) +
          PackedLocalConfiguration.tapeSpan blockLength)
    (hlocal :
      ∀ offset, offset < blockLength →
        localBlock * blockLength + offset =
          PackedLocalConfiguration.requestedLocalPosition
            blockLength center slot offset) :
    ∃ final,
      Runs
        (.whileNonzero (remaining regs)
          (chunkBody tm tape localBlock regs))
        store final ∧
      final (accumulator regs) =
        PackedOutputChunkSemantics.forwardBits
          (PackedOutputChunkSemantics.boundedOutputBitValue
            tm blockLength center tape slot word)
          (cursor * width + width - remainingBits)
          remainingBits accumulatorValue ∧
      final (remaining regs) = 0 ∧
      final (Layout.blockLength regs) = blockLength ∧
      final (bankRegisters regs).word = word ∧
      final (CombineValue.rangeRegisters regs).one = 1 ∧
      final (Layout.active regs) = cursor ∧
      final (chunkBits regs) = width ∧
      final (CombineValue.rangeRegisters regs).accumulator =
        store (CombineValue.rangeRegisters regs).accumulator ∧
      ∀ address,
        address ∉ PackedLocalStep.footprint regs →
          final address = store address := by
  induction remainingBits generalizing store accumulatorValue with
  | zero =>
      refine
        ⟨store, Runs.whileZero hremaining, ?_, hremaining,
          hblock, hword, hone, hcursor, hwidth, rfl, ?_⟩
      · simpa [PackedOutputChunkSemantics.forwardBits] using
          haccumulator
      · intro address _
        rfl
  | succ remainingBits ih =>
      have hnonzero :
          store (remaining regs) ≠ 0 := by
        rw [hremaining]
        omega
      let coordinate :=
        cursor * width + width - (remainingBits + 1)
      let nextAccumulator :=
        2 * accumulatorValue +
          PackedOutputChunkSemantics.boundedOutputBitValue
            tm blockLength center tape slot word coordinate
      obtain ⟨afterBody, hbodyRun, hbodyAccumulator,
          hbodyRemaining, hbodyBlock, hbodyWord, hbodyOne,
          hbodyCursor, hbodyWidth, hbodyOuter, hbodyOutside⟩ :=
        chunkBody_runs tm order blockLength hpositive centers cfg
          center tape slot localBlock suffix word regs store cursor
          width remainingBits accumulatorValue hblock hword hrep
          hone hcursor hwidth hremaining haccumulator hheadLower
          hheadUpper hlocal
      have hbodyAccumulator' :
          afterBody (accumulator regs) = nextAccumulator := by
        simpa [nextAccumulator, coordinate] using hbodyAccumulator
      obtain ⟨final, hloopRun, hloopAccumulator,
          hloopRemaining, hloopBlock, hloopWord, hloopOne,
          hloopCursor, hloopWidth, hloopOuter, hloopOutside⟩ :=
        ih (store := afterBody)
          (accumulatorValue := nextAccumulator)
          (by omega) hbodyBlock hbodyWord hbodyOne
          hbodyCursor hbodyWidth hbodyRemaining hbodyAccumulator'
      have hrun :
          Runs
            (.whileNonzero (remaining regs)
              (chunkBody tm tape localBlock regs))
            store final :=
        Runs.whileNonzero hnonzero hbodyRun hloopRun
      refine
        ⟨final, hrun, ?_, hloopRemaining, hloopBlock,
          hloopWord, hloopOne, hloopCursor, hloopWidth,
          hloopOuter.trans hbodyOuter, ?_⟩
      · rw [hloopAccumulator]
        have hnextCoordinate :
            cursor * width + width - remainingBits =
              coordinate + 1 := by
          dsimp [coordinate]
          omega
        simp only [PackedOutputChunkSemantics.forwardBits]
        rw [hnextCoordinate]
      · intro address haddress
        calc
          final address = afterBody address :=
            hloopOutside address haddress
          _ = store address :=
            hbodyOutside address haddress

private theorem recovery_footprint_subset_step
    (regs : NeighborhoodTrial.Registers controller) :
    AssignmentPayloadBit.recoveryFootprint regs ⊆
      PackedLocalStep.footprint regs := by
  intro address haddress
  simp only [AssignmentPayloadBit.recoveryFootprint,
    Finset.mem_union, Finset.mem_singleton] at haddress
  rcases haddress with hstack | hrecovered
  · simp only [
      NeighborhoodProgram.StackRegisters.footprint,
      Finset.mem_image, Finset.mem_univ, true_and] at hstack
    obtain ⟨stackSlot, rfl⟩ := hstack
    apply Finset.mem_image.mpr
    fin_cases stackSlot <;>
      first
      | exact ⟨(0 : Fin 17), Finset.mem_univ _, rfl⟩
      | exact ⟨(1 : Fin 17), Finset.mem_univ _, rfl⟩
      | exact ⟨(2 : Fin 17), Finset.mem_univ _, rfl⟩
      | exact ⟨(3 : Fin 17), Finset.mem_univ _, rfl⟩
      | exact ⟨(5 : Fin 17), Finset.mem_univ _, rfl⟩
      | exact ⟨(7 : Fin 17), Finset.mem_univ _, rfl⟩
      | exact ⟨(8 : Fin 17), Finset.mem_univ _, rfl⟩
  · rw [hrecovered]
    apply Finset.mem_image.mpr
    exact ⟨(12 : Fin 17), Finset.mem_univ _, rfl⟩

private theorem fixed_index_not_mem_recovery
    (regs : NeighborhoodTrial.Registers controller)
    (slot : Fin 34)
    (hstack :
      ∀ stackSlot,
        slot ≠ AssignmentPayloadBit.exponentStackMap stackSlot)
    (hrecovered : slot ≠ 20) :
    regs.index slot ∉
      AssignmentPayloadBit.recoveryFootprint regs := by
  simp [AssignmentPayloadBit.recoveryFootprint,
    AssignmentPayloadBit.exponentStackRegisters,
    NeighborhoodProgram.StackRegisters.footprint,
    AssignmentPayloadBit.recoveredChunkBits,
    regs.injective.eq_iff]
  refine ⟨hrecovered, ?_⟩
  intro stackSlot heq
  exact hstack stackSlot heq.symm

private theorem computeSelected_writesWithin
    (tm : TM workTapeCount)
    (tape : TapeIndex workTapeCount)
    (localBlock : ℕ)
    (regs : NeighborhoodTrial.Registers controller) :
    Footprint.CmdWritesWithin
      (PackedLocalStep.footprint regs)
      (computeSelected tm tape localBlock regs) := by
  simp only [computeSelected, Cmd.seqList,
    Footprint.CmdWritesWithin, Footprint.BasicWritesWithin]
  exact
    ⟨cmdWritesWithin_mono
        (AssignmentPayloadBit.recoverChunkBits_writesWithin regs)
        (recovery_footprint_subset_step regs),
      copy_writesWithin regs _ _ (step_slot_mem regs 11),
      copy_writesWithin regs _ _ (step_slot_mem regs 6),
      step_slot_mem regs 15,
      chunkBody_writesWithin tm tape localBlock regs,
      copy_writesWithin regs _ _ (step_slot_mem regs 4),
      step_slot_mem regs 9⟩

private theorem computeSelected_runs
    (tm : TM workTapeCount)
    (order :
      NeighborhoodExecutableEvaluation.FiniteEncoding.StateOrder tm)
    (blockLength : ℕ) (hpositive : 0 < blockLength)
    (centers : TapeIndex workTapeCount → ℕ)
    (cfg : Cfg workTapeCount tm.Q)
    (center : ℕ)
    (tape : TapeIndex workTapeCount)
    (slot : Slot)
    (localBlock : ℕ)
    (suffix word : ℕ)
    (regs : NeighborhoodTrial.Registers controller)
    (store : Store)
    (cursor width : ℕ)
    (hradix : store (Layout.chunkRadix regs) = 2 ^ width)
    (hblock : store (Layout.blockLength regs) = blockLength)
    (hword : store (bankRegisters regs).word = word)
    (hrep :
      PackedLocalRepresentation.Represents tm order blockLength
        centers cfg suffix word)
    (hone :
      store (CombineValue.rangeRegisters regs).one = 1)
    (hcursor : store (Layout.active regs) = cursor)
    (hheadLower :
      PackedLocalConfiguration.windowStart
          blockLength (centers tape) ≤
        (tapeAt cfg tape).head)
    (hheadUpper :
      (tapeAt cfg tape).head <
        PackedLocalConfiguration.windowStart
            blockLength (centers tape) +
          PackedLocalConfiguration.tapeSpan blockLength)
    (hlocal :
      ∀ offset, offset < blockLength →
        localBlock * blockLength + offset =
          PackedLocalConfiguration.requestedLocalPosition
            blockLength center slot offset) :
    ∃ final,
      Runs (computeSelected tm tape localBlock regs) store final ∧
      final (CombineTerm.packedValue regs) =
        PackedOutputChunkSemantics.packedOutputChunk
          tm blockLength center tape slot word cursor width ∧
      final (bankRegisters regs).word = word ∧
      final (remaining regs) = 0 ∧
      final (CombineValue.rangeRegisters regs).accumulator =
        store (CombineValue.rangeRegisters regs).accumulator ∧
      final (CombineValue.rangeRegisters regs).one = 1 ∧
      final (Layout.blockLength regs) = blockLength ∧
      final (Layout.active regs) = cursor ∧
      ∀ address,
        address ∉ PackedLocalStep.footprint regs →
          final address = store address := by
  obtain ⟨recovered, hrecover, hrecoveredWidth, _, _, _, _, _,
      hrecoverOutside⟩ :=
    AssignmentPayloadBit.recoverChunkBits_runs
      regs store width hradix
  obtain ⟨afterWidth, hcopyWidth, hafterWidthValue,
      hcopyWidthOutside⟩ :=
    copy_runs (chunkBits regs)
      (AssignmentPayloadBit.recoveredChunkBits regs) recovered
      (regs.injective.ne (by decide))
  have hafterWidthRecovered :
      afterWidth
          (AssignmentPayloadBit.recoveredChunkBits regs) =
        width := by
    exact
      (hcopyWidthOutside _
        (regs.injective.ne (by decide))).trans hrecoveredWidth
  obtain ⟨afterRemaining, hcopyRemaining,
      hafterRemainingValue, hcopyRemainingOutside⟩ :=
    copy_runs (remaining regs)
      (AssignmentPayloadBit.recoveredChunkBits regs) afterWidth
      (regs.injective.ne (by decide))
  let initialized :=
    (Basic.imm (accumulator regs) 0).exec afterRemaining
  have hinitialize :
      Runs (.basic (.imm (accumulator regs) 0))
        afterRemaining initialized :=
    Runs.basic _ _
  have hinitializedFixed
      (fixedSlot : Fin 34)
      (hstack :
        ∀ stackSlot,
          fixedSlot ≠
            AssignmentPayloadBit.exponentStackMap stackSlot)
      (hrecovered : fixedSlot ≠ 20)
      (hwidthSlot : fixedSlot ≠ 19)
      (hremainingSlot : fixedSlot ≠ 10)
      (haccumulatorSlot : fixedSlot ≠ 31) :
      initialized (regs.index fixedSlot) =
        store (regs.index fixedSlot) := by
    calc
      initialized (regs.index fixedSlot) =
          afterRemaining (regs.index fixedSlot) := by
        simp [initialized, Basic.exec, Function.update_of_ne,
          regs.injective.ne haccumulatorSlot]
      _ = afterWidth (regs.index fixedSlot) :=
        hcopyRemainingOutside _
          (regs.injective.ne hremainingSlot)
      _ = recovered (regs.index fixedSlot) :=
        hcopyWidthOutside _ (regs.injective.ne hwidthSlot)
      _ = store (regs.index fixedSlot) :=
        hrecoverOutside _
          (fixed_index_not_mem_recovery regs fixedSlot
            hstack hrecovered)
  have hinitializedBlock :
      initialized (Layout.blockLength regs) = blockLength :=
    (hinitializedFixed 2
      (by
        intro stackSlot
        fin_cases stackSlot <;> decide)
      (by decide) (by decide) (by decide) (by decide)).trans
      hblock
  have hinitializedWord :
      initialized (bankRegisters regs).word = word :=
    (hinitializedFixed 32
      (by
        intro stackSlot
        fin_cases stackSlot <;> decide)
      (by decide) (by decide) (by decide) (by decide)).trans
      hword
  have hinitializedOne :
      initialized (CombineValue.rangeRegisters regs).one = 1 :=
    (hinitializedFixed 17
      (by
        intro stackSlot
        fin_cases stackSlot <;> decide)
      (by decide) (by decide) (by decide) (by decide)).trans
      hone
  have hinitializedCursor :
      initialized (Layout.active regs) = cursor :=
    (hinitializedFixed 28
      (by
        intro stackSlot
        fin_cases stackSlot <;> decide)
      (by decide) (by decide) (by decide) (by decide)).trans
      hcursor
  have hinitializedOuter :
      initialized (CombineValue.rangeRegisters regs).accumulator =
        store (CombineValue.rangeRegisters regs).accumulator :=
    hinitializedFixed 18
      (by
        intro stackSlot
        fin_cases stackSlot <;> decide)
      (by decide) (by decide) (by decide) (by decide)
  have hinitializedWidth :
      initialized (chunkBits regs) = width := by
    have hremaining_ne_width :
        chunkBits regs ≠ remaining regs :=
      regs.injective.ne (by decide)
    have haccumulator_ne_width :
        chunkBits regs ≠ accumulator regs :=
      regs.injective.ne (by decide)
    simp [initialized, Basic.exec, Function.update_of_ne,
      haccumulator_ne_width]
    exact
      (hcopyRemainingOutside _ hremaining_ne_width).trans
        (hafterWidthValue.trans hrecoveredWidth)
  have hinitializedRemaining :
      initialized (remaining regs) = width := by
    have haccumulator_ne_remaining :
        remaining regs ≠ accumulator regs :=
      regs.injective.ne (by decide)
    simp [initialized, Basic.exec, Function.update_of_ne,
      haccumulator_ne_remaining, hafterRemainingValue,
      hafterWidthRecovered]
  have hinitializedAccumulator :
      initialized (accumulator regs) = 0 := by
    simp [initialized, Basic.exec]
  obtain ⟨looped, hloop, hloopAccumulator, hloopRemaining,
      hloopBlock, hloopWord, hloopOne, hloopCursor, _,
      hloopOuter, _⟩ :=
    chunkLoop_runs tm order blockLength hpositive centers cfg center
      tape slot localBlock suffix word regs initialized cursor width
      width 0 (by rfl) hinitializedBlock hinitializedWord hrep
      hinitializedOne hinitializedCursor hinitializedWidth
      hinitializedRemaining hinitializedAccumulator hheadLower
      hheadUpper hlocal
  have hloopPacked :
      looped (accumulator regs) =
        PackedOutputChunkSemantics.packedOutputChunk
          tm blockLength center tape slot word cursor width := by
    rw [hloopAccumulator]
    simp [PackedOutputChunkSemantics.packedOutputChunk,
      PackedOutputChunkSemantics.chunkStart]
  obtain ⟨packed, hcopyPacked, hpackedValue,
      hcopyPackedOutside⟩ :=
    copy_runs (CombineTerm.packedValue regs)
      (accumulator regs) looped
      (regs.injective.ne (by decide))
  let final :=
    (Basic.imm (CombineValue.rangeRegisters regs).one 1).exec
      packed
  have hrestore :
      Runs (restoreRangeOne regs) packed final :=
    Runs.basic _ _
  have hrun :
      Runs (computeSelected tm tape localBlock regs) store final := by
    simpa [computeSelected, Cmd.seqList, initialized, final,
      restoreRangeOne] using
      Runs.seq hrecover
        (Runs.seq hcopyWidth
          (Runs.seq hcopyRemaining
            (Runs.seq hinitialize
              (Runs.seq hloop
                (Runs.seq hcopyPacked hrestore)))))
  have hpacked_ne_one :
      CombineTerm.packedValue regs ≠
        (CombineValue.rangeRegisters regs).one :=
    regs.injective.ne (by decide)
  have hword_ne_packed :
      (bankRegisters regs).word ≠
        CombineTerm.packedValue regs :=
    regs.injective.ne (by decide)
  have hword_ne_one :
      (bankRegisters regs).word ≠
        (CombineValue.rangeRegisters regs).one :=
    regs.injective.ne (by decide)
  have hremaining_ne_packed :
      remaining regs ≠ CombineTerm.packedValue regs :=
    regs.injective.ne (by decide)
  have hremaining_ne_one :
      remaining regs ≠
        (CombineValue.rangeRegisters regs).one :=
    regs.injective.ne (by decide)
  have houter_ne_packed :
      (CombineValue.rangeRegisters regs).accumulator ≠
        CombineTerm.packedValue regs :=
    regs.injective.ne (by decide)
  have houter_ne_one :
      (CombineValue.rangeRegisters regs).accumulator ≠
        (CombineValue.rangeRegisters regs).one :=
    regs.injective.ne (by decide)
  refine
    ⟨final, hrun, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simp [final, Basic.exec, Function.update_of_ne,
      hpacked_ne_one, hpackedValue, hloopPacked]
  · simp [final, Basic.exec, Function.update_of_ne,
      hword_ne_one, hcopyPackedOutside _ hword_ne_packed,
      hloopWord]
  · simp [final, Basic.exec, Function.update_of_ne,
      hremaining_ne_one,
      hcopyPackedOutside _ hremaining_ne_packed,
      hloopRemaining]
  · simp [final, Basic.exec, Function.update_of_ne,
      houter_ne_one, hcopyPackedOutside _ houter_ne_packed,
      hloopOuter, hinitializedOuter]
  · simp [final, Basic.exec]
  · have hblock_ne_packed :
        Layout.blockLength regs ≠
          CombineTerm.packedValue regs :=
      regs.injective.ne (by decide)
    have hblock_ne_one :
        Layout.blockLength regs ≠
          (CombineValue.rangeRegisters regs).one :=
      regs.injective.ne (by decide)
    simp [final, Basic.exec, Function.update_of_ne,
      hblock_ne_one, hcopyPackedOutside _ hblock_ne_packed,
      hloopBlock]
  · have hcursor_ne_packed :
        Layout.active regs ≠ CombineTerm.packedValue regs :=
      regs.injective.ne (by decide)
    have hcursor_ne_one :
        Layout.active regs ≠
          (CombineValue.rangeRegisters regs).one :=
      regs.injective.ne (by decide)
    simp [final, Basic.exec, Function.update_of_ne,
      hcursor_ne_one, hcopyPackedOutside _ hcursor_ne_packed,
      hloopCursor]
  · intro address haddress
    exact Footprint.runs_eq_outside
      (computeSelected_writesWithin tm tape localBlock regs)
      hrun haddress

private theorem center_footprint_subset_step
    (regs : NeighborhoodTrial.Registers controller) :
    CombineSafeCenter.footprint regs ⊆
      PackedLocalStep.footprint regs := by
  intro address haddress
  simp only [CombineSafeCenter.footprint, Finset.mem_image,
    Finset.mem_univ, true_and] at haddress
  obtain ⟨centerSlot, rfl⟩ := haddress
  apply Finset.mem_image.mpr
  fin_cases centerSlot <;>
    first
    | exact ⟨(0 : Fin 17), Finset.mem_univ _, rfl⟩
    | exact ⟨(2 : Fin 17), Finset.mem_univ _, rfl⟩
    | exact ⟨(3 : Fin 17), Finset.mem_univ _, rfl⟩
    | exact ⟨(5 : Fin 17), Finset.mem_univ _, rfl⟩
    | exact ⟨(7 : Fin 17), Finset.mem_univ _, rfl⟩
    | exact ⟨(14 : Fin 17), Finset.mem_univ _, rfl⟩
    | exact ⟨(4 : Fin 17), Finset.mem_univ _, rfl⟩
    | exact ⟨(1 : Fin 17), Finset.mem_univ _, rfl⟩
    | exact ⟨(8 : Fin 17), Finset.mem_univ _, rfl⟩
    | exact ⟨(12 : Fin 17), Finset.mem_univ _, rfl⟩
    | exact ⟨(13 : Fin 17), Finset.mem_univ _, rfl⟩

private theorem fixed_index_not_mem_center
    (regs : NeighborhoodTrial.Registers controller)
    (slot : Fin 34)
    (hslot :
      ∀ centerSlot,
        slot ≠ CombineSafeCenter.scratchMap centerSlot) :
    regs.index slot ∉ CombineSafeCenter.footprint regs := by
  simp [CombineSafeCenter.footprint, regs.injective.eq_iff]
  intro centerSlot heq
  exact hslot centerSlot heq.symm

private theorem computeTapeSlot_writesWithin
    (tm : TM workTapeCount)
    (controller : SearchProgram.Registers)
    (tape : TapeIndex workTapeCount)
    (slot : Slot)
    (regs : NeighborhoodTrial.Registers controller) :
    Footprint.CmdWritesWithin
      (PackedLocalStep.footprint regs)
      (computeTapeSlot tm controller tape slot regs) := by
  simp only [computeTapeSlot, Footprint.CmdWritesWithin]
  exact
    ⟨cmdWritesWithin_mono
        (CombineSafeCenter.deriveCenter_writesWithin
          workTapeCount controller regs)
        (center_footprint_subset_step regs),
      computeSelected_writesWithin tm tape
        (boundaryLocalBlock slot) regs,
      computeSelected_writesWithin tm tape
        (regularLocalBlock slot) regs⟩

private theorem computeTapeSlot_runs
    (tm : TM workTapeCount)
    (order :
      NeighborhoodExecutableEvaluation.FiniteEncoding.StateOrder tm)
    (blockLength : ℕ) (hpositive : 0 < blockLength)
    (centers : TapeIndex workTapeCount → ℕ)
    (cfg : Cfg workTapeCount tm.Q)
    (tape : TapeIndex workTapeCount)
    (slot : Slot)
    (suffix word : ℕ)
    (controller : SearchProgram.Registers)
    (regs : NeighborhoodTrial.Registers controller)
    (store : Store)
    (guessWord interval cursor width : ℕ)
    (hguess : store controller.guess = guessWord)
    (htape :
      store (ControlDecode.nodeTape regs) = tape.val)
    (hinterval :
      store (ControlDecode.nodePayload1 regs) = interval)
    (hcenter :
      ChildNode.centerOutputValue
          (ChildNode.derivedCenterValue
            workTapeCount guessWord tape.val interval) =
        centers tape)
    (hradix : store (Layout.chunkRadix regs) = 2 ^ width)
    (hblock : store (Layout.blockLength regs) = blockLength)
    (hword : store (bankRegisters regs).word = word)
    (hrep :
      PackedLocalRepresentation.Represents tm order blockLength
        centers cfg suffix word)
    (hone :
      store (CombineValue.rangeRegisters regs).one = 1)
    (hcursor : store (Layout.active regs) = cursor)
    (hheadLower :
      PackedLocalConfiguration.windowStart
          blockLength (centers tape) ≤
        (tapeAt cfg tape).head)
    (hheadUpper :
      (tapeAt cfg tape).head <
        PackedLocalConfiguration.windowStart
            blockLength (centers tape) +
          PackedLocalConfiguration.tapeSpan blockLength) :
    ∃ final,
      Runs (computeTapeSlot tm controller tape slot regs)
        store final ∧
      final (CombineTerm.packedValue regs) =
        PackedOutputChunkSemantics.packedOutputChunk
          tm blockLength (centers tape) tape slot word cursor width ∧
      final (bankRegisters regs).word = word ∧
      final (remaining regs) = 0 ∧
      final (CombineValue.rangeRegisters regs).accumulator =
        store (CombineValue.rangeRegisters regs).accumulator ∧
      final (CombineValue.rangeRegisters regs).one = 1 ∧
      final (Layout.blockLength regs) = blockLength ∧
      final (Layout.active regs) = cursor ∧
      ∀ address,
        address ∉ PackedLocalStep.footprint regs →
          final address = store address := by
  obtain ⟨derived, hderive, hderivePost⟩ :=
    CombineSafeCenter.deriveCenter_runs workTapeCount controller regs
      store guessWord tape.val interval hguess htape hinterval
  have hderivePreserves :=
    CombineSafeCenter.deriveCenter_preservesCombine
      workTapeCount controller regs hderive
  have hderivedCenter :
      derived (CombineSafeCenter.centerValue regs) =
        centers tape :=
    hderivePost.center_eq.trans hcenter
  have hderivedRadix :
      derived (Layout.chunkRadix regs) = 2 ^ width :=
    hderivePreserves.abi.chunkRadix_eq.trans hradix
  have hderivedBlock :
      derived (Layout.blockLength regs) = blockLength :=
    hderivePreserves.abi.blockLength_eq.trans hblock
  have hderivedWord :
      derived (bankRegisters regs).word = word := by
    calc
      derived (bankRegisters regs).word =
          store (bankRegisters regs).word :=
        hderivePost.eq_outside _
          (fixed_index_not_mem_center regs 32
            (by
              intro centerSlot
              fin_cases centerSlot <;> decide))
      _ = word := hword
  have hderivedOne :
      derived (CombineValue.rangeRegisters regs).one = 1 :=
    hderivePreserves.one_eq.trans hone
  have hderivedCursor :
      derived (Layout.active regs) = cursor :=
    hderivePreserves.abi.active_eq.trans hcursor
  by_cases hzero : centers tape = 0
  · obtain ⟨final, hselected, hselectedPacked,
        hselectedWord, hselectedRemaining, hselectedOuter,
        hselectedOne, hselectedBlock, hselectedCursor, _⟩ :=
      computeSelected_runs tm order blockLength hpositive centers cfg
        (centers tape) tape slot (boundaryLocalBlock slot) suffix
        word regs derived cursor width hderivedRadix hderivedBlock
        hderivedWord hrep hderivedOne hderivedCursor hheadLower
        hheadUpper (by
          intro offset hoffset
          rw [hzero]
          exact boundaryLocalBlock_requested blockLength offset slot)
    have hbranch :
        Runs
          (.ifZero (CombineSafeCenter.centerValue regs)
            (computeSelected tm tape (boundaryLocalBlock slot) regs)
            (computeSelected tm tape (regularLocalBlock slot) regs))
          derived final := by
      apply Runs.ifZero
      · exact hderivedCenter.trans hzero
      · exact hselected
    have hrun :
        Runs (computeTapeSlot tm controller tape slot regs)
          store final :=
      Runs.seq hderive hbranch
    refine
      ⟨final, hrun, hselectedPacked, hselectedWord,
        hselectedRemaining,
        hselectedOuter.trans hderivePreserves.accumulator_eq,
        hselectedOne, hselectedBlock, hselectedCursor, ?_⟩
    intro address haddress
    exact Footprint.runs_eq_outside
      (computeTapeSlot_writesWithin tm controller tape slot regs)
      hrun haddress
  · have hpositiveCenter : 0 < centers tape := by
      omega
    obtain ⟨final, hselected, hselectedPacked,
        hselectedWord, hselectedRemaining, hselectedOuter,
        hselectedOne, hselectedBlock, hselectedCursor, _⟩ :=
      computeSelected_runs tm order blockLength hpositive centers cfg
        (centers tape) tape slot (regularLocalBlock slot) suffix
        word regs derived cursor width hderivedRadix hderivedBlock
        hderivedWord hrep hderivedOne hderivedCursor hheadLower
        hheadUpper (by
          intro offset hoffset
          exact regularLocalBlock_requested blockLength
            (centers tape) offset slot hpositiveCenter hoffset)
    have hbranch :
        Runs
          (.ifZero (CombineSafeCenter.centerValue regs)
            (computeSelected tm tape (boundaryLocalBlock slot) regs)
            (computeSelected tm tape (regularLocalBlock slot) regs))
          derived final := by
      apply Runs.ifNonzero
      · rw [hderivedCenter]
        exact hzero
      · exact hselected
    have hrun :
        Runs (computeTapeSlot tm controller tape slot regs)
          store final :=
      Runs.seq hderive hbranch
    refine
      ⟨final, hrun, hselectedPacked, hselectedWord,
        hselectedRemaining,
        hselectedOuter.trans hderivePreserves.accumulator_eq,
        hselectedOne, hselectedBlock, hselectedCursor, ?_⟩
    intro address haddress
    exact Footprint.runs_eq_outside
      (computeTapeSlot_writesWithin tm controller tape slot regs)
      hrun haddress

private theorem compareImmediate_runs
    (regs : NeighborhoodTrial.Registers controller)
    (value output : ℕ) (constant : ℕ)
    (store : Store) (valueAt : ℕ)
    (hvalue : store value = valueAt)
    (hvalueZero : value ≠ regs.index 0)
    (hvalueFour : value ≠ regs.index 4) :
    ∃ final,
      Runs (compareImmediate regs value output constant)
        store final ∧
      final output =
        (valueAt - constant) + (constant - valueAt) ∧
      ∀ address,
        address ≠ regs.index 0 →
        address ≠ regs.index 4 →
        address ≠ regs.index 5 →
        address ≠ output →
        final address = store address := by
  let afterConstant :=
    (Basic.imm (regs.index 0) constant).exec store
  let afterForward :=
    (Basic.sub (regs.index 4) value (regs.index 0)).exec
      afterConstant
  let afterBackward :=
    (Basic.sub (regs.index 5) (regs.index 0) value).exec
      afterForward
  let final :=
    (Basic.add output (regs.index 4) (regs.index 5)).exec
      afterBackward
  have hrun :
      Runs (compareImmediate regs value output constant)
        store final := by
    simpa [compareImmediate, Cmd.seqList, afterConstant,
      afterForward, afterBackward, final] using
      Runs.seq
        (Runs.basic (.imm (regs.index 0) constant) store)
        (Runs.seq
          (Runs.basic
            (.sub (regs.index 4) value (regs.index 0))
            afterConstant)
          (Runs.seq
            (Runs.basic
              (.sub (regs.index 5) (regs.index 0) value)
              afterForward)
            (Runs.basic
              (.add output (regs.index 4) (regs.index 5))
              afterBackward)))
  refine ⟨final, hrun, ?_, ?_⟩
  · simp [final, afterBackward, afterForward, afterConstant,
      Basic.exec, Function.update_of_ne, hvalueZero,
      hvalueFour, regs.injective.eq_iff, hvalue]
  · intro address hzero hfour hfive houtput
    simp [final, afterBackward, afterForward, afterConstant,
      Basic.exec, Function.update_of_ne, hzero, hfour, hfive,
      houtput]

private theorem compareImmediatePacked_writesWithin
    (regs : NeighborhoodTrial.Registers controller)
    (value constant : ℕ) :
    Footprint.CmdWritesWithin
      (PackedLocalStep.footprint regs)
      (compareImmediate regs value
        (CombineTerm.packedValue regs) constant) := by
  simp only [compareImmediate, Cmd.seqList,
    Footprint.CmdWritesWithin, Footprint.BasicWritesWithin]
  exact
    ⟨step_slot_mem regs 0, step_slot_mem regs 2,
      step_slot_mem regs 3, step_slot_mem regs 4⟩

private theorem dispatchSlots_writesWithin
    (tm : TM workTapeCount)
    (controller : SearchProgram.Registers)
    (tape : TapeIndex workTapeCount)
    (regs : NeighborhoodTrial.Registers controller)
    (slots : List Slot) :
    Footprint.CmdWritesWithin
      (PackedLocalStep.footprint regs)
      (dispatchSlots tm controller tape regs slots) := by
  induction slots with
  | nil =>
      trivial
  | cons slot slots ih =>
      simp only [dispatchSlots, Footprint.CmdWritesWithin]
      exact
        ⟨compareImmediatePacked_writesWithin regs
            (ControlDecode.nodePayload0 regs) slot.toFin.val,
          computeTapeSlot_writesWithin tm controller tape slot regs,
          ih⟩

private theorem dispatchSlots_runs
    (tm : TM workTapeCount)
    (order :
      NeighborhoodExecutableEvaluation.FiniteEncoding.StateOrder tm)
    (blockLength : ℕ) (hpositive : 0 < blockLength)
    (centers : TapeIndex workTapeCount → ℕ)
    (cfg : Cfg workTapeCount tm.Q)
    (tape : TapeIndex workTapeCount)
    (targetSlot : Slot)
    (slots : List Slot)
    (hmember : targetSlot ∈ slots)
    (suffix word : ℕ)
    (controller : SearchProgram.Registers)
    (regs : NeighborhoodTrial.Registers controller)
    (store : Store)
    (guessWord interval cursor width : ℕ)
    (hguess : store controller.guess = guessWord)
    (htape :
      store (ControlDecode.nodeTape regs) = tape.val)
    (hslot :
      store (ControlDecode.nodePayload0 regs) =
        targetSlot.toFin.val)
    (hinterval :
      store (ControlDecode.nodePayload1 regs) = interval)
    (hcenter :
      ChildNode.centerOutputValue
          (ChildNode.derivedCenterValue
            workTapeCount guessWord tape.val interval) =
        centers tape)
    (hradix : store (Layout.chunkRadix regs) = 2 ^ width)
    (hblock : store (Layout.blockLength regs) = blockLength)
    (hword : store (bankRegisters regs).word = word)
    (hrep :
      PackedLocalRepresentation.Represents tm order blockLength
        centers cfg suffix word)
    (hone :
      store (CombineValue.rangeRegisters regs).one = 1)
    (hcursor : store (Layout.active regs) = cursor)
    (hheadLower :
      PackedLocalConfiguration.windowStart
          blockLength (centers tape) ≤
        (tapeAt cfg tape).head)
    (hheadUpper :
      (tapeAt cfg tape).head <
        PackedLocalConfiguration.windowStart
            blockLength (centers tape) +
          PackedLocalConfiguration.tapeSpan blockLength) :
    ∃ final,
      Runs (dispatchSlots tm controller tape regs slots)
        store final ∧
      final (CombineTerm.packedValue regs) =
        PackedOutputChunkSemantics.packedOutputChunk
          tm blockLength (centers tape) tape targetSlot
            word cursor width ∧
      final (bankRegisters regs).word = word ∧
      final (remaining regs) = 0 ∧
      final (CombineValue.rangeRegisters regs).accumulator =
        store (CombineValue.rangeRegisters regs).accumulator ∧
      final (CombineValue.rangeRegisters regs).one = 1 ∧
      final (Layout.blockLength regs) = blockLength ∧
      final (Layout.active regs) = cursor ∧
      ∀ address,
        address ∉ PackedLocalStep.footprint regs →
          final address = store address := by
  induction slots generalizing store with
  | nil =>
      simp at hmember
  | cons candidate slots ih =>
      obtain ⟨compared, hcompare, hcompareValue,
          hcompareOutside⟩ :=
        compareImmediate_runs regs
          (ControlDecode.nodePayload0 regs)
          (CombineTerm.packedValue regs)
          candidate.toFin.val store targetSlot.toFin.val hslot
          (regs.injective.ne (by decide))
          (regs.injective.ne (by decide))
      have hcomparedFixed
          (fixedSlot : Fin 34)
          (hzero : fixedSlot ≠ 0)
          (hfour : fixedSlot ≠ 4)
          (hfive : fixedSlot ≠ 5)
          (hsix : fixedSlot ≠ 6) :
          compared (regs.index fixedSlot) =
            store (regs.index fixedSlot) :=
        hcompareOutside _ (regs.injective.ne hzero)
          (regs.injective.ne hfour)
          (regs.injective.ne hfive)
          (regs.injective.ne hsix)
      have hcomparedGuess :
          compared controller.guess = guessWord := by
        calc
          compared controller.guess = store controller.guess :=
            hcompareOutside _
              ((regs.index_ne_controller 0 2).symm)
              ((regs.index_ne_controller 4 2).symm)
              ((regs.index_ne_controller 5 2).symm)
              ((regs.index_ne_controller 6 2).symm)
          _ = guessWord := hguess
      have hcomparedTape :
          compared (ControlDecode.nodeTape regs) = tape.val :=
        (hcomparedFixed 9 (by decide) (by decide)
          (by decide) (by decide)).trans htape
      have hcomparedSlot :
          compared (ControlDecode.nodePayload0 regs) =
            targetSlot.toFin.val :=
        (hcomparedFixed 10 (by decide) (by decide)
          (by decide) (by decide)).trans hslot
      have hcomparedInterval :
          compared (ControlDecode.nodePayload1 regs) = interval :=
        (hcomparedFixed 11 (by decide) (by decide)
          (by decide) (by decide)).trans hinterval
      have hcomparedRadix :
          compared (Layout.chunkRadix regs) = 2 ^ width :=
        (hcomparedFixed 8 (by decide) (by decide)
          (by decide) (by decide)).trans hradix
      have hcomparedBlock :
          compared (Layout.blockLength regs) = blockLength :=
        (hcomparedFixed 2 (by decide) (by decide)
          (by decide) (by decide)).trans hblock
      have hcomparedWord :
          compared (bankRegisters regs).word = word :=
        (hcomparedFixed 32 (by decide) (by decide)
          (by decide) (by decide)).trans hword
      have hcomparedOne :
          compared (CombineValue.rangeRegisters regs).one = 1 :=
        (hcomparedFixed 17 (by decide) (by decide)
          (by decide) (by decide)).trans hone
      have hcomparedCursor :
          compared (Layout.active regs) = cursor :=
        (hcomparedFixed 28 (by decide) (by decide)
          (by decide) (by decide)).trans hcursor
      have hcomparedOuter :
          compared (CombineValue.rangeRegisters regs).accumulator =
            store (CombineValue.rangeRegisters regs).accumulator :=
        hcomparedFixed 18 (by decide) (by decide)
          (by decide) (by decide)
      by_cases hmatch : targetSlot = candidate
      · subst candidate
        have hzero :
            compared (CombineTerm.packedValue regs) = 0 := by
          rw [hcompareValue]
          simp
        obtain ⟨final, hselected, hselectedPacked,
            hselectedWord, hselectedRemaining, hselectedOuter,
            hselectedOne, hselectedBlock, hselectedCursor, _⟩ :=
          computeTapeSlot_runs tm order blockLength hpositive centers
            cfg tape targetSlot suffix word controller regs compared
            guessWord interval cursor width hcomparedGuess
            hcomparedTape hcomparedInterval hcenter hcomparedRadix
            hcomparedBlock hcomparedWord hrep hcomparedOne
            hcomparedCursor hheadLower hheadUpper
        have hbranch :
            Runs
              (.ifZero (CombineTerm.packedValue regs)
                (computeTapeSlot tm controller tape targetSlot regs)
                (dispatchSlots tm controller tape regs slots))
              compared final :=
          Runs.ifZero hzero hselected
        have hrun :
            Runs
              (dispatchSlots tm controller tape regs
                (targetSlot :: slots))
              store final := by
          exact Runs.seq hcompare hbranch
        refine
          ⟨final, hrun, hselectedPacked, hselectedWord,
            hselectedRemaining,
            hselectedOuter.trans hcomparedOuter,
            hselectedOne, hselectedBlock, hselectedCursor, ?_⟩
        intro address haddress
        exact Footprint.runs_eq_outside
          (dispatchSlots_writesWithin tm controller tape regs
            (targetSlot :: slots))
          hrun haddress
      · have htail : targetSlot ∈ slots :=
          (List.mem_cons.mp hmember).resolve_left hmatch
        have hnonzero :
            compared (CombineTerm.packedValue regs) ≠ 0 := by
          rw [hcompareValue]
          cases targetSlot <;> cases candidate <;>
            simp_all [Slot.toFin]
        obtain ⟨final, hrecurse, hrecursePacked,
            hrecurseWord, hrecurseRemaining, hrecurseOuter,
            hrecurseOne, hrecurseBlock, hrecurseCursor, _⟩ :=
          ih htail compared hcomparedGuess hcomparedTape
            hcomparedSlot hcomparedInterval hcomparedRadix
            hcomparedBlock hcomparedWord hcomparedOne
            hcomparedCursor
        have hbranch :
            Runs
              (.ifZero (CombineTerm.packedValue regs)
                (computeTapeSlot tm controller tape candidate regs)
                (dispatchSlots tm controller tape regs slots))
              compared final :=
          Runs.ifNonzero hnonzero hrecurse
        have hrun :
            Runs
              (dispatchSlots tm controller tape regs
                (candidate :: slots))
              store final := by
          exact Runs.seq hcompare hbranch
        refine
          ⟨final, hrun, hrecursePacked, hrecurseWord,
            hrecurseRemaining, hrecurseOuter.trans hcomparedOuter,
            hrecurseOne, hrecurseBlock, hrecurseCursor, ?_⟩
        intro address haddress
        exact Footprint.runs_eq_outside
          (dispatchSlots_writesWithin tm controller tape regs
            (candidate :: slots))
          hrun haddress

private theorem dispatchTapes_writesWithin
    (tm : TM workTapeCount)
    (controller : SearchProgram.Registers)
    (regs : NeighborhoodTrial.Registers controller)
    (tapes : List (TapeIndex workTapeCount)) :
    Footprint.CmdWritesWithin
      (PackedLocalStep.footprint regs)
      (dispatchTapes tm controller regs tapes) := by
  induction tapes with
  | nil =>
      trivial
  | cons tape tapes ih =>
      simp only [dispatchTapes, Footprint.CmdWritesWithin]
      exact
        ⟨compareImmediatePacked_writesWithin regs
            (ControlDecode.nodeTape regs) tape.val,
          dispatchSlots_writesWithin tm controller tape regs
            [.lower, .center, .upper],
          ih⟩

private theorem dispatchTapes_runs
    (tm : TM workTapeCount)
    (order :
      NeighborhoodExecutableEvaluation.FiniteEncoding.StateOrder tm)
    (blockLength : ℕ) (hpositive : 0 < blockLength)
    (centers : TapeIndex workTapeCount → ℕ)
    (cfg : Cfg workTapeCount tm.Q)
    (targetTape : TapeIndex workTapeCount)
    (targetSlot : Slot)
    (tapes : List (TapeIndex workTapeCount))
    (hmember : targetTape ∈ tapes)
    (suffix word : ℕ)
    (controller : SearchProgram.Registers)
    (regs : NeighborhoodTrial.Registers controller)
    (store : Store)
    (guessWord interval cursor width : ℕ)
    (hguess : store controller.guess = guessWord)
    (htape :
      store (ControlDecode.nodeTape regs) = targetTape.val)
    (hslot :
      store (ControlDecode.nodePayload0 regs) =
        targetSlot.toFin.val)
    (hinterval :
      store (ControlDecode.nodePayload1 regs) = interval)
    (hcenter :
      ChildNode.centerOutputValue
          (ChildNode.derivedCenterValue
            workTapeCount guessWord targetTape.val interval) =
        centers targetTape)
    (hradix : store (Layout.chunkRadix regs) = 2 ^ width)
    (hblock : store (Layout.blockLength regs) = blockLength)
    (hword : store (bankRegisters regs).word = word)
    (hrep :
      PackedLocalRepresentation.Represents tm order blockLength
        centers cfg suffix word)
    (hone :
      store (CombineValue.rangeRegisters regs).one = 1)
    (hcursor : store (Layout.active regs) = cursor)
    (hheadLower :
      PackedLocalConfiguration.windowStart
          blockLength (centers targetTape) ≤
        (tapeAt cfg targetTape).head)
    (hheadUpper :
      (tapeAt cfg targetTape).head <
        PackedLocalConfiguration.windowStart
            blockLength (centers targetTape) +
          PackedLocalConfiguration.tapeSpan blockLength) :
    ∃ final,
      Runs (dispatchTapes tm controller regs tapes) store final ∧
      final (CombineTerm.packedValue regs) =
        PackedOutputChunkSemantics.packedOutputChunk
          tm blockLength (centers targetTape) targetTape
            targetSlot word cursor width ∧
      final (bankRegisters regs).word = word ∧
      final (remaining regs) = 0 ∧
      final (CombineValue.rangeRegisters regs).accumulator =
        store (CombineValue.rangeRegisters regs).accumulator ∧
      final (CombineValue.rangeRegisters regs).one = 1 ∧
      final (Layout.blockLength regs) = blockLength ∧
      final (Layout.active regs) = cursor ∧
      ∀ address,
        address ∉ PackedLocalStep.footprint regs →
          final address = store address := by
  induction tapes generalizing store with
  | nil =>
      simp at hmember
  | cons candidate tapes ih =>
      obtain ⟨compared, hcompare, hcompareValue,
          hcompareOutside⟩ :=
        compareImmediate_runs regs (ControlDecode.nodeTape regs)
          (CombineTerm.packedValue regs) candidate.val store
          targetTape.val htape
          (regs.injective.ne (by decide))
          (regs.injective.ne (by decide))
      have hcomparedFixed
          (fixedSlot : Fin 34)
          (hzero : fixedSlot ≠ 0)
          (hfour : fixedSlot ≠ 4)
          (hfive : fixedSlot ≠ 5)
          (hsix : fixedSlot ≠ 6) :
          compared (regs.index fixedSlot) =
            store (regs.index fixedSlot) :=
        hcompareOutside _ (regs.injective.ne hzero)
          (regs.injective.ne hfour)
          (regs.injective.ne hfive)
          (regs.injective.ne hsix)
      have hcomparedGuess :
          compared controller.guess = guessWord := by
        calc
          compared controller.guess = store controller.guess :=
            hcompareOutside _
              ((regs.index_ne_controller 0 2).symm)
              ((regs.index_ne_controller 4 2).symm)
              ((regs.index_ne_controller 5 2).symm)
              ((regs.index_ne_controller 6 2).symm)
          _ = guessWord := hguess
      have hcomparedTape :
          compared (ControlDecode.nodeTape regs) =
            targetTape.val :=
        (hcomparedFixed 9 (by decide) (by decide)
          (by decide) (by decide)).trans htape
      have hcomparedSlot :
          compared (ControlDecode.nodePayload0 regs) =
            targetSlot.toFin.val :=
        (hcomparedFixed 10 (by decide) (by decide)
          (by decide) (by decide)).trans hslot
      have hcomparedInterval :
          compared (ControlDecode.nodePayload1 regs) = interval :=
        (hcomparedFixed 11 (by decide) (by decide)
          (by decide) (by decide)).trans hinterval
      have hcomparedRadix :
          compared (Layout.chunkRadix regs) = 2 ^ width :=
        (hcomparedFixed 8 (by decide) (by decide)
          (by decide) (by decide)).trans hradix
      have hcomparedBlock :
          compared (Layout.blockLength regs) = blockLength :=
        (hcomparedFixed 2 (by decide) (by decide)
          (by decide) (by decide)).trans hblock
      have hcomparedWord :
          compared (bankRegisters regs).word = word :=
        (hcomparedFixed 32 (by decide) (by decide)
          (by decide) (by decide)).trans hword
      have hcomparedOne :
          compared (CombineValue.rangeRegisters regs).one = 1 :=
        (hcomparedFixed 17 (by decide) (by decide)
          (by decide) (by decide)).trans hone
      have hcomparedCursor :
          compared (Layout.active regs) = cursor :=
        (hcomparedFixed 28 (by decide) (by decide)
          (by decide) (by decide)).trans hcursor
      have hcomparedOuter :
          compared (CombineValue.rangeRegisters regs).accumulator =
            store (CombineValue.rangeRegisters regs).accumulator :=
        hcomparedFixed 18 (by decide) (by decide)
          (by decide) (by decide)
      by_cases hmatch : targetTape = candidate
      · subst candidate
        have hzero :
            compared (CombineTerm.packedValue regs) = 0 := by
          rw [hcompareValue]
          simp
        obtain ⟨final, hselected, hselectedPacked,
            hselectedWord, hselectedRemaining, hselectedOuter,
            hselectedOne, hselectedBlock, hselectedCursor, _⟩ :=
          dispatchSlots_runs tm order blockLength hpositive centers
            cfg targetTape targetSlot [.lower, .center, .upper]
            (by cases targetSlot <;> simp) suffix word controller regs
            compared guessWord
            interval cursor width hcomparedGuess hcomparedTape
            hcomparedSlot hcomparedInterval hcenter hcomparedRadix
            hcomparedBlock hcomparedWord hrep hcomparedOne
            hcomparedCursor hheadLower hheadUpper
        have hbranch :
            Runs
              (.ifZero (CombineTerm.packedValue regs)
                (dispatchSlots tm controller targetTape regs
                  [.lower, .center, .upper])
                (dispatchTapes tm controller regs tapes))
              compared final :=
          Runs.ifZero hzero hselected
        have hrun :
            Runs
              (dispatchTapes tm controller regs
                (targetTape :: tapes))
              store final :=
          Runs.seq hcompare hbranch
        refine
          ⟨final, hrun, hselectedPacked, hselectedWord,
            hselectedRemaining,
            hselectedOuter.trans hcomparedOuter,
            hselectedOne, hselectedBlock, hselectedCursor, ?_⟩
        intro address haddress
        exact Footprint.runs_eq_outside
          (dispatchTapes_writesWithin tm controller regs
            (targetTape :: tapes))
          hrun haddress
      · have htail : targetTape ∈ tapes :=
          (List.mem_cons.mp hmember).resolve_left hmatch
        have hvalues : targetTape.val ≠ candidate.val := by
          intro heq
          exact hmatch (Fin.ext heq)
        have hnonzero :
            compared (CombineTerm.packedValue regs) ≠ 0 := by
          rw [hcompareValue]
          omega
        obtain ⟨final, hrecurse, hrecursePacked,
            hrecurseWord, hrecurseRemaining, hrecurseOuter,
            hrecurseOne, hrecurseBlock, hrecurseCursor, _⟩ :=
          ih htail compared hcomparedGuess hcomparedTape
            hcomparedSlot hcomparedInterval hcomparedRadix
            hcomparedBlock hcomparedWord hcomparedOne
            hcomparedCursor
        have hbranch :
            Runs
              (.ifZero (CombineTerm.packedValue regs)
                (dispatchSlots tm controller candidate regs
                  [.lower, .center, .upper])
                (dispatchTapes tm controller regs tapes))
              compared final :=
          Runs.ifNonzero hnonzero hrecurse
        have hrun :
            Runs
              (dispatchTapes tm controller regs
                (candidate :: tapes))
              store final :=
          Runs.seq hcompare hbranch
        refine
          ⟨final, hrun, hrecursePacked, hrecurseWord,
            hrecurseRemaining, hrecurseOuter.trans hcomparedOuter,
            hrecurseOne, hrecurseBlock, hrecurseCursor, ?_⟩
        intro address haddress
        exact Footprint.runs_eq_outside
          (dispatchTapes_writesWithin tm controller regs
            (candidate :: tapes))
          hrun haddress

private theorem decode_footprint_subset_step
    (regs : NeighborhoodTrial.Registers controller) :
    ControlDecode.scratchFootprint regs ⊆
      PackedLocalStep.footprint regs := by
  intro address haddress
  simp only [ControlDecode.scratchFootprint, Finset.mem_image,
    Finset.mem_univ, true_and] at haddress
  obtain ⟨decodeSlot, rfl⟩ := haddress
  apply Finset.mem_image.mpr
  fin_cases decodeSlot <;>
    first
    | exact ⟨(0 : Fin 17), Finset.mem_univ _, rfl⟩
    | exact ⟨(4 : Fin 17), Finset.mem_univ _, rfl⟩
    | exact ⟨(5 : Fin 17), Finset.mem_univ _, rfl⟩
    | exact ⟨(6 : Fin 17), Finset.mem_univ _, rfl⟩
    | exact ⟨(7 : Fin 17), Finset.mem_univ _, rfl⟩
    | exact ⟨(8 : Fin 17), Finset.mem_univ _, rfl⟩
    | exact ⟨(10 : Fin 17), Finset.mem_univ _, rfl⟩

private theorem fixed_index_not_mem_decode
    (regs : NeighborhoodTrial.Registers controller)
    (slot : Fin 34)
    (hslot :
      ∀ decodeSlot,
        slot ≠ ControlDecode.scratchMap decodeSlot) :
    regs.index slot ∉ ControlDecode.scratchFootprint regs := by
  simp [ControlDecode.scratchFootprint, regs.injective.eq_iff]
  intro decodeSlot heq
  exact hslot decodeSlot heq.symm

private theorem controller_guess_not_mem_decode
    (regs : NeighborhoodTrial.Registers controller) :
    controller.guess ∉ ControlDecode.scratchFootprint regs := by
  intro hmember
  simp only [ControlDecode.scratchFootprint, Finset.mem_image,
    Finset.mem_univ, true_and] at hmember
  obtain ⟨decodeSlot, hslot⟩ := hmember
  exact regs.index_ne_controller
    (ControlDecode.scratchMap decodeSlot) 2 hslot

private theorem fixed_index_not_mem_step
    (regs : NeighborhoodTrial.Registers controller)
    (slot : Fin 34)
    (hslot :
      ∀ writeSlot,
        slot ≠ PackedLocalStep.writeMap writeSlot) :
    regs.index slot ∉ PackedLocalStep.footprint regs := by
  simp [PackedLocalStep.footprint, regs.injective.eq_iff]
  intro writeSlot heq
  exact hslot writeSlot heq.symm

theorem build_writesWithin_internal
    (tm : TM workTapeCount)
    (controller : SearchProgram.Registers)
    (regs : NeighborhoodTrial.Registers controller) :
    Footprint.CmdWritesWithin
      (PackedLocalStep.footprint regs)
      (build tm controller regs) := by
  simp only [build, Cmd.seqList, Footprint.CmdWritesWithin]
  exact
    ⟨copy_writesWithin regs _ _ (step_slot_mem regs 11),
      cmdWritesWithin_mono
        (ControlDecode.decodeNode_writesWithin regs)
        (decode_footprint_subset_step regs),
      copy_writesWithin regs _ _ (step_slot_mem regs 10),
      dispatchTapes_writesWithin tm controller regs
        (List.finRange (workTapeCount + 2))⟩

theorem build_runs_internal
    (tm : TM workTapeCount)
    (order :
      NeighborhoodExecutableEvaluation.FiniteEncoding.StateOrder tm)
    (horizon blockLength : ℕ) (hpositive : 0 < blockLength)
    (guess : NeighborhoodGraph.Guess.CenterGuess
      workTapeCount horizon)
    (guessCode :
      Fin
        (3 ^
          NeighborhoodGraph.Guess.Enumeration.movementCount
            workTapeCount horizon))
    (hguess :
      guess =
        NeighborhoodGraph.Guess.Enumeration.candidateGuess guessCode)
    (interval : Fin horizon)
    (targetTape : TapeIndex workTapeCount)
    (targetSlot : Slot)
    (cfg : Cfg workTapeCount tm.Q)
    (suffix word : ℕ)
    (controller : SearchProgram.Registers)
    (regs : NeighborhoodTrial.Registers controller)
    (store : Store)
    (cursor width : ℕ)
    (hfits :
      ∀ digit ∈
          FrameCodec.nodeDigits
            (show
              NeighborhoodEvaluator.QueryNode workTapeCount horizon
              from .graph
                (.computation targetTape targetSlot interval.val)),
        digit < 2 ^ width)
    (hnode :
      store (Layout.nodeCode regs) =
        FrameCodec.encodeNode (2 ^ width)
          (show
            NeighborhoodEvaluator.QueryNode workTapeCount horizon
            from .graph
              (.computation targetTape targetSlot interval.val)))
    (hradix : store (Layout.chunkRadix regs) = 2 ^ width)
    (hguessStore : store controller.guess = guessCode.val)
    (hblock : store (Layout.blockLength regs) = blockLength)
    (hword : store (bankRegisters regs).word = word)
    (hrep :
      PackedLocalRepresentation.Represents tm order blockLength
        (NeighborhoodGraph.Guess.Consistency.guessedCenters
          guess interval.val)
        cfg suffix word)
    (hone :
      store (CombineValue.rangeRegisters regs).one = 1)
    (hcursor : store (Layout.active regs) = cursor)
    (hheadLower :
      PackedLocalConfiguration.windowStart blockLength
          (NeighborhoodGraph.Guess.Consistency.guessedCenters
            guess interval.val targetTape) ≤
        (tapeAt cfg targetTape).head)
    (hheadUpper :
      (tapeAt cfg targetTape).head <
        PackedLocalConfiguration.windowStart blockLength
            (NeighborhoodGraph.Guess.Consistency.guessedCenters
              guess interval.val targetTape) +
          PackedLocalConfiguration.tapeSpan blockLength) :
    ∃ final,
      Runs (build tm controller regs) store final ∧
      Post tm blockLength
        (NeighborhoodGraph.Guess.Consistency.guessedCenters
          guess interval.val targetTape)
        targetTape targetSlot word cursor width regs store final := by
  let node :
      NeighborhoodEvaluator.QueryNode workTapeCount horizon :=
    .graph (.computation targetTape targetSlot interval.val)
  let outerValue :=
    store (CombineValue.rangeRegisters regs).accumulator
  obtain ⟨saved, hsave, hsaveValue, hsaveOutside⟩ :=
    copy_runs (chunkBits regs)
      (CombineValue.rangeRegisters regs).accumulator store
      (regs.injective.ne (by decide))
  have hsavedNode :
      saved (Layout.nodeCode regs) =
        FrameCodec.encodeNode (2 ^ width) node := by
    exact
      (hsaveOutside _ (regs.injective.ne (by decide))).trans
        (by simpa [node] using hnode)
  have hsavedRadix :
      saved (Layout.chunkRadix regs) = 2 ^ width :=
    (hsaveOutside _ (regs.injective.ne (by decide))).trans hradix
  obtain ⟨decoded, hdecode, _, hdecodedNode, hdecodeABI⟩ :=
    ControlDecode.decodeNode_encodeNode_runs regs saved
      (2 ^ width) node (by positivity) hfits hsavedNode hsavedRadix
  have hdecodeOutside :
      ∀ address,
        address ∉ ControlDecode.scratchFootprint regs →
        decoded address = saved address := by
    intro address haddress
    exact Footprint.runs_eq_outside
      (ControlDecode.decodeNode_writesWithin regs)
      hdecode haddress
  have hdecodedTerm :
      decoded (chunkBits regs) = outerValue := by
    calc
      decoded (chunkBits regs) = saved (chunkBits regs) :=
        hdecodeOutside _
          (fixed_index_not_mem_decode regs 19
            (by
              intro decodeSlot
              fin_cases decodeSlot <;> decide))
      _ = store (CombineValue.rangeRegisters regs).accumulator :=
        hsaveValue
      _ = outerValue := rfl
  have hdecodedWord :
      decoded (bankRegisters regs).word = word := by
    calc
      decoded (bankRegisters regs).word =
          saved (bankRegisters regs).word :=
        hdecodeOutside _
          (fixed_index_not_mem_decode regs 32
            (by
              intro decodeSlot
              fin_cases decodeSlot <;> decide))
      _ = store (bankRegisters regs).word :=
        hsaveOutside _ (regs.injective.ne (by decide))
      _ = word := hword
  have hdecodedOne :
      decoded (CombineValue.rangeRegisters regs).one = 1 := by
    calc
      decoded (CombineValue.rangeRegisters regs).one =
          saved (CombineValue.rangeRegisters regs).one :=
        hdecodeOutside _
          (fixed_index_not_mem_decode regs 17
            (by
              intro decodeSlot
              fin_cases decodeSlot <;> decide))
      _ = store (CombineValue.rangeRegisters regs).one :=
        hsaveOutside _ (regs.injective.ne (by decide))
      _ = 1 := hone
  have hdecodedGuess :
      decoded controller.guess = guessCode.val := by
    calc
      decoded controller.guess = saved controller.guess :=
        hdecodeOutside _ (controller_guess_not_mem_decode regs)
      _ = store controller.guess :=
        hsaveOutside _
          ((regs.index_ne_controller 19 2).symm)
      _ = guessCode.val := hguessStore
  obtain ⟨restored, hrestoreOuter, hrestoredOuterValue,
      hrestoreOutside⟩ :=
    copy_runs (CombineValue.rangeRegisters regs).accumulator
      (chunkBits regs) decoded (regs.injective.ne (by decide))
  have hrestoredOuter :
      restored (CombineValue.rangeRegisters regs).accumulator =
        store (CombineValue.rangeRegisters regs).accumulator :=
    hrestoredOuterValue.trans hdecodedTerm
  have hrestoredTape :
      restored (ControlDecode.nodeTape regs) = targetTape.val := by
    rw [hrestoreOutside _ (regs.injective.ne (by decide))]
    simpa [node, ControlDecode.expectedNodeValues] using
      hdecodedNode.tape_eq
  have hrestoredSlot :
      restored (ControlDecode.nodePayload0 regs) =
        targetSlot.toFin.val := by
    rw [hrestoreOutside _ (regs.injective.ne (by decide))]
    simpa [node, ControlDecode.expectedNodeValues] using
      hdecodedNode.payload0_eq
  have hrestoredInterval :
      restored (ControlDecode.nodePayload1 regs) = interval.val := by
    rw [hrestoreOutside _ (regs.injective.ne (by decide))]
    simpa [node, ControlDecode.expectedNodeValues] using
      hdecodedNode.payload1_eq
  have hrestoredGuess :
      restored controller.guess = guessCode.val := by
    exact
      (hrestoreOutside _
        ((regs.index_ne_controller 18 2).symm)).trans
        hdecodedGuess
  have hrestoredRadix :
      restored (Layout.chunkRadix regs) = 2 ^ width := by
    calc
      restored (Layout.chunkRadix regs) =
          decoded (Layout.chunkRadix regs) :=
        hrestoreOutside _ (regs.injective.ne (by decide))
      _ = saved (Layout.chunkRadix regs) :=
        hdecodeABI.chunkRadix_eq
      _ = 2 ^ width := hsavedRadix
  have hrestoredBlock :
      restored (Layout.blockLength regs) = blockLength := by
    calc
      restored (Layout.blockLength regs) =
          decoded (Layout.blockLength regs) :=
        hrestoreOutside _ (regs.injective.ne (by decide))
      _ = saved (Layout.blockLength regs) :=
        hdecodeABI.blockLength_eq
      _ = store (Layout.blockLength regs) :=
        hsaveOutside _ (regs.injective.ne (by decide))
      _ = blockLength := hblock
  have hrestoredWord :
      restored (bankRegisters regs).word = word :=
    (hrestoreOutside _ (regs.injective.ne (by decide))).trans
      hdecodedWord
  have hrestoredOne :
      restored (CombineValue.rangeRegisters regs).one = 1 :=
    (hrestoreOutside _ (regs.injective.ne (by decide))).trans
      hdecodedOne
  have hrestoredCursor :
      restored (Layout.active regs) = cursor := by
    calc
      restored (Layout.active regs) =
          decoded (Layout.active regs) :=
        hrestoreOutside _ (regs.injective.ne (by decide))
      _ = saved (Layout.active regs) := hdecodeABI.active_eq
      _ = store (Layout.active regs) :=
        hsaveOutside _ (regs.injective.ne (by decide))
      _ = cursor := hcursor
  have hcenter :
      ChildNode.centerOutputValue
          (ChildNode.derivedCenterValue workTapeCount guessCode.val
            targetTape.val interval.val) =
        NeighborhoodGraph.Guess.Consistency.guessedCenters
          guess interval.val targetTape := by
    rw [ChildNode.derivedCenterValue_candidateGuess
      guessCode targetTape interval.val
      (Nat.le_of_lt interval.isLt)]
    rw [← hguess]
    simp only [
      NeighborhoodGraph.Guess.Consistency.guessedCenters]
    cases guess.derivedCenter targetTape interval.val <;> rfl
  obtain ⟨final, hdispatch, hdispatchPacked, hdispatchWord,
      hdispatchRemaining, hdispatchOuter, hdispatchOne,
      hdispatchBlock, hdispatchCursor, _⟩ :=
    dispatchTapes_runs tm order blockLength hpositive
      (NeighborhoodGraph.Guess.Consistency.guessedCenters
        guess interval.val)
      cfg targetTape targetSlot
      (List.finRange (workTapeCount + 2))
      (by simp) suffix word controller regs restored guessCode.val
      interval.val cursor width hrestoredGuess hrestoredTape
      hrestoredSlot hrestoredInterval hcenter hrestoredRadix
      hrestoredBlock hrestoredWord hrep hrestoredOne
      hrestoredCursor hheadLower hheadUpper
  have hrun :
      Runs (build tm controller regs) store final := by
    simpa [build, Cmd.seqList, node] using
      Runs.seq hsave
        (Runs.seq hdecode
          (Runs.seq hrestoreOuter hdispatch))
  have houtside :
      ∀ address,
        address ∉ PackedLocalStep.footprint regs →
        final address = store address := by
    intro address haddress
    exact Footprint.runs_eq_outside
      (build_writesWithin_internal tm controller regs)
      hrun haddress
  have hfixed
      (fixedSlot : Fin 34)
      (hslot :
        ∀ writeSlot,
          fixedSlot ≠ PackedLocalStep.writeMap writeSlot) :
      final (regs.index fixedSlot) = store (regs.index fixedSlot) :=
    houtside _ (fixed_index_not_mem_step regs fixedSlot hslot)
  refine ⟨final, hrun, ?_⟩
  exact
    { packed_eq := hdispatchPacked
      word_eq := hdispatchWord
      remaining_eq := hdispatchRemaining
      assignment_eq :=
        hfixed 21 (by
          intro writeSlot
          fin_cases writeSlot <;> decide)
      outerAccumulator_eq :=
        hdispatchOuter.trans hrestoredOuter
      one_eq := hdispatchOne
      catalyticWord_eq := by
        simpa [NeighborhoodTrial.Registers.layout] using
          hfixed 33 (by
            intro writeSlot
            fin_cases writeSlot <;> decide)
      abi :=
        { fuel_eq :=
            hfixed 22 (by
              intro writeSlot
              fin_cases writeSlot <;> decide)
          nodeCode_eq :=
            hfixed 23 (by
              intro writeSlot
              fin_cases writeSlot <;> decide)
          scalar_eq :=
            hfixed 25 (by
              intro writeSlot
              fin_cases writeSlot <;> decide)
          out_eq :=
            hfixed 26 (by
              intro writeSlot
              fin_cases writeSlot <;> decide)
          phaseCode_eq :=
            hfixed 27 (by
              intro writeSlot
              fin_cases writeSlot <;> decide)
          active_eq :=
            hfixed 28 (by
              intro writeSlot
              fin_cases writeSlot <;> decide)
          blockLength_eq :=
            hfixed 2 (by
              intro writeSlot
              fin_cases writeSlot <;> decide)
          horizon_eq :=
            hfixed 3 (by
              intro writeSlot
              fin_cases writeSlot <;> decide)
          chunkCount_eq :=
            hfixed 7 (by
              intro writeSlot
              fin_cases writeSlot <;> decide)
          chunkRadix_eq :=
            hfixed 8 (by
              intro writeSlot
              fin_cases writeSlot <;> decide)
          frameRadix_eq :=
            hfixed 13 (by
              intro writeSlot
              fin_cases writeSlot <;> decide)
          bankRadix_eq :=
            hfixed 14 (by
              intro writeSlot
              fin_cases writeSlot <;> decide)
          bankDigitCount_eq :=
            hfixed 15 (by
              intro writeSlot
              fin_cases writeSlot <;> decide)
          modulusPred_eq :=
            hfixed 16 (by
              intro writeSlot
              fin_cases writeSlot <;> decide)
          modulus_eq :=
            hfixed 24 (by
              intro writeSlot
              fin_cases writeSlot <;> decide) }
      eq_outside := houtside }

end Internal
end PackedLocalOutputChunk
end NeighborhoodMicrocode
end Runtime
end TimeSpaceSimulation
end Complexity
