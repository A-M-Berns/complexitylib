/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/
import
  Complexitylib.TimeSpaceSimulation.Runtime.NeighborhoodMicrocode.FrameTransfer.Defs
import
  Complexitylib.TimeSpaceSimulation.Runtime.NeighborhoodMicrocode.Layout
import Complexitylib.Models.RandomAccessMachine.Structured.Footprint

/-!
# First-order transfer of neighborhood-scheduler frames -- proofs
-/

namespace Complexity
namespace TimeSpaceSimulation
namespace Runtime
namespace NeighborhoodMicrocode
namespace FrameTransfer
namespace Internal

open RAM Structured

variable {controller : SearchProgram.Registers}

theorem writeFootprint_subset_layout_internal
    (regs : NeighborhoodTrial.Registers controller) :
    writeFootprint regs ⊆ regs.layout.footprint := by
  intro address haddress
  simp only [writeFootprint, Finset.mem_insert,
    Finset.mem_singleton] at haddress
  rcases haddress with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl |
      rfl | rfl | rfl | rfl | rfl | rfl | rfl
  all_goals exact Layout.index_mem_layout_footprint regs _

private theorem basics_runs
    (ops : List Basic) (store : Store) :
    Runs (Cmd.basics ops) store (Basic.execList ops store) := by
  obtain ⟨cost, space, hexec⟩ :=
    RAM.Structured.Internal.exec_basics_exists ops store
  exact ⟨ops.length, cost, space, hexec⟩

theorem copy_runs_internal
    {destination source : ℕ} (store : Store)
    (hne : destination ≠ source) :
    Runs (copy destination source) store
      (Function.update store destination (store source)) := by
  apply Runs.seq (Runs.basic (.imm destination 0) store)
  simpa [Basic.exec, Function.update_of_ne, hne, Ne.symm hne] using
    Runs.basic
      (.add destination source destination)
      (Basic.exec (.imm destination 0) store)

private theorem basic_index_writesWithin
    (regs : NeighborhoodTrial.Registers controller)
    (slot : Fin 34) (op : Basic)
    (hop :
      match op with
      | .imm destination _ => destination = regs.index slot
      | .add destination _ _ => destination = regs.index slot
      | .sub destination _ _ => destination = regs.index slot
      | .mul destination _ _ => destination = regs.index slot
      | .load destination _ => destination = regs.index slot
      | .store _ _ => False) :
    RAM.Structured.Footprint.BasicWritesWithin
      regs.layout.footprint op := by
  cases op <;>
    simp_all [RAM.Structured.Footprint.BasicWritesWithin,
      Layout.index_mem_layout_footprint]

theorem copy_writesWithin_internal
    (regs : NeighborhoodTrial.Registers controller)
    (destinationSlot : Fin 34) (source : ℕ) :
    RAM.Structured.Footprint.CmdWritesWithin
      regs.layout.footprint
      (copy (regs.index destinationSlot) source) := by
  simp [copy, RAM.Structured.Footprint.CmdWritesWithin,
    RAM.Structured.Footprint.BasicWritesWithin,
    Layout.index_mem_layout_footprint]

private theorem stack_command_writesWithin
    (regs : NeighborhoodTrial.Registers controller)
    (stack : NeighborhoodProgram.StackRegisters)
    (hstack : stack.footprint ⊆ regs.layout.footprint)
    (command : Cmd)
    (hwrites :
      RAM.Structured.Footprint.CmdWritesWithin
        stack.footprint command) :
    RAM.Structured.Footprint.CmdWritesWithin
      regs.layout.footprint command := by
  induction command with
  | skip => trivial
  | basic op =>
      cases op <;>
        simp_all [RAM.Structured.Footprint.CmdWritesWithin,
          RAM.Structured.Footprint.BasicWritesWithin] <;>
        exact hstack hwrites
  | seq first second firstIH secondIH =>
      exact ⟨firstIH hwrites.1, secondIH hwrites.2⟩
  | ifZero test onZero onNonzero zeroIH nonzeroIH =>
      exact ⟨zeroIH hwrites.1, nonzeroIH hwrites.2⟩
  | whileNonzero test body bodyIH =>
      exact bodyIH hwrites

private theorem pop_sourceWritesWithin
    (stack : NeighborhoodProgram.StackRegisters) :
    RAM.Structured.Footprint.CmdWritesWithin
      stack.footprint (NeighborhoodProgram.pop stack) := by
  simp [NeighborhoodProgram.pop, NeighborhoodProgram.popBody,
    NeighborhoodProgram.popTestOp, Cmd.seqList,
    RAM.Structured.Footprint.CmdWritesWithin,
    RAM.Structured.Footprint.BasicWritesWithin,
    NeighborhoodProgram.StackRegisters.index_mem_footprint]

private theorem peek_sourceWritesWithin
    (stack : NeighborhoodProgram.StackRegisters) :
    RAM.Structured.Footprint.CmdWritesWithin
      stack.footprint (NeighborhoodProgram.peek stack) := by
  simp [NeighborhoodProgram.peek, RuntimeArithmetic.reduce,
    RuntimeArithmetic.reduceBody, RuntimeArithmetic.reduceTestOp,
    NeighborhoodProgram.StackRegisters.reduceRegisters,
    Cmd.seqList, RAM.Structured.Footprint.CmdWritesWithin,
    RAM.Structured.Footprint.BasicWritesWithin,
    NeighborhoodProgram.StackRegisters.index_mem_footprint]

private theorem peek_sourceWritesWithin_withoutOne
    (stack : NeighborhoodProgram.StackRegisters) :
    RAM.Structured.Footprint.CmdWritesWithin
      (stack.footprint.erase stack.one)
      (NeighborhoodProgram.peek stack) := by
  simp [NeighborhoodProgram.peek, RuntimeArithmetic.reduce,
    RuntimeArithmetic.reduceBody, RuntimeArithmetic.reduceTestOp,
    NeighborhoodProgram.StackRegisters.reduceRegisters,
    Cmd.seqList, RAM.Structured.Footprint.CmdWritesWithin,
    RAM.Structured.Footprint.BasicWritesWithin,
    NeighborhoodProgram.StackRegisters.footprint,
    stack.injective.eq_iff]

private theorem pop_sourceWritesWithin_withoutValue
    (stack : NeighborhoodProgram.StackRegisters) :
    RAM.Structured.Footprint.CmdWritesWithin
      (stack.footprint.erase stack.value)
      (NeighborhoodProgram.pop stack) := by
  simp [NeighborhoodProgram.pop, NeighborhoodProgram.popBody,
    NeighborhoodProgram.popTestOp, Cmd.seqList,
    RAM.Structured.Footprint.CmdWritesWithin,
    RAM.Structured.Footprint.BasicWritesWithin,
    NeighborhoodProgram.StackRegisters.footprint,
    stack.injective.eq_iff]

private theorem push_sourceWritesWithin
    (stack : NeighborhoodProgram.StackRegisters) :
    RAM.Structured.Footprint.CmdWritesWithin
      stack.footprint (NeighborhoodProgram.push stack) := by
  simp [NeighborhoodProgram.push, Cmd.seqList,
    RAM.Structured.Footprint.CmdWritesWithin,
    RAM.Structured.Footprint.BasicWritesWithin,
    NeighborhoodProgram.StackRegisters.index_mem_footprint]

private theorem codec_pop_writesWithin
    (regs : NeighborhoodTrial.Registers controller) :
    RAM.Structured.Footprint.CmdWritesWithin
      regs.layout.footprint
      (NeighborhoodProgram.pop (Layout.frameCodecRegisters regs)) :=
  stack_command_writesWithin regs _ (Layout.frameCodec_footprint_subset regs)
    _ (pop_sourceWritesWithin _)

private theorem codec_peek_writesWithin
    (regs : NeighborhoodTrial.Registers controller) :
    RAM.Structured.Footprint.CmdWritesWithin
      regs.layout.footprint
      (NeighborhoodProgram.peek (Layout.frameCodecRegisters regs)) :=
  stack_command_writesWithin regs _ (Layout.frameCodec_footprint_subset regs)
    _ (peek_sourceWritesWithin _)

private theorem popMany_writesWithin
    (regs : NeighborhoodTrial.Registers controller) :
    ∀ count,
      RAM.Structured.Footprint.CmdWritesWithin
        regs.layout.footprint (popMany regs count)
  | 0 => trivial
  | count + 1 =>
      ⟨codec_pop_writesWithin regs,
        popMany_writesWithin regs count⟩

private theorem popMany_sourceWritesWithin
    (regs : NeighborhoodTrial.Registers controller) :
    ∀ count,
      RAM.Structured.Footprint.CmdWritesWithin
        (Layout.frameCodecRegisters regs).footprint
        (popMany regs count)
  | 0 => trivial
  | count + 1 =>
      ⟨pop_sourceWritesWithin _,
        popMany_sourceWritesWithin regs count⟩

private theorem physical_not_mem_codec_footprint
    (regs : NeighborhoodTrial.Registers controller)
    (slot : Fin 34)
    (hslot : ∀ index, Layout.frameCodecMap index ≠ slot) :
    regs.index slot ∉
      (Layout.frameCodecRegisters regs).footprint := by
  simp only [NeighborhoodProgram.StackRegisters.footprint,
    Layout.frameCodecRegisters, Finset.mem_image, Finset.mem_univ,
    true_and, not_exists]
  intro index
  rw [regs.injective.eq_iff]
  exact hslot index

private theorem codec_run_preserves_physical
    (regs : NeighborhoodTrial.Registers controller)
    (slot : Fin 34)
    (hslot : ∀ index, Layout.frameCodecMap index ≠ slot)
    {command : Cmd} {initial final : Store}
    (hwrites :
      RAM.Structured.Footprint.CmdWritesWithin
        (Layout.frameCodecRegisters regs).footprint command)
    (hrun : Runs command initial final) :
    final (regs.index slot) = initial (regs.index slot) := by
  exact RAM.Structured.Footprint.runs_eq_outside hwrites hrun
    (physical_not_mem_codec_footprint regs slot hslot)

theorem popMany_runs_internal
    (regs : NeighborhoodTrial.Registers controller)
    (store : Store) (base word count : ℕ)
    (hbase : 0 < base)
    (hword :
      store (Layout.frameCodecRegisters regs).word = word)
    (hbaseValue :
      store (Layout.frameCodecRegisters regs).base = base)
    (hbasePred :
      store (Layout.frameCodecRegisters regs).basePred = base - 1)
    (hone :
      store (Layout.frameCodecRegisters regs).one = 1) :
    ∃ final,
      Runs (popMany regs count) store final ∧
      final (Layout.frameCodecRegisters regs).word =
        (PackedDigits.pop base)^[count] word ∧
      final (Layout.frameCodecRegisters regs).base = base ∧
      final (Layout.frameCodecRegisters regs).basePred = base - 1 ∧
      final (Layout.frameCodecRegisters regs).one = 1 := by
  induction count generalizing store word with
  | zero =>
      exact ⟨store, Runs.skip store, by simpa, hbaseValue,
        hbasePred, hone⟩
  | succ count ih =>
      obtain ⟨middle, hpop, hmiddleWord, _hquotient, _htest,
          hmiddleBase, hmiddleBasePred, hmiddleOne⟩ :=
        NeighborhoodProgram.pop_runs
          (Layout.frameCodecRegisters regs) store base word hbase
          hword hbaseValue hbasePred hone
      obtain ⟨final, hrest, hfinalWord, hfinalBase,
          hfinalBasePred, hfinalOne⟩ :=
        ih middle (PackedDigits.pop base word)
          hmiddleWord hmiddleBase hmiddleBasePred hmiddleOne
      refine ⟨final, Runs.seq hpop hrest, ?_,
        hfinalBase, hfinalBasePred, hfinalOne⟩
      simpa [Function.iterate_succ_apply] using hfinalWord

private theorem frame_push_writesWithin
    (regs : NeighborhoodTrial.Registers controller) :
    RAM.Structured.Footprint.CmdWritesWithin
      regs.layout.footprint
      (NeighborhoodProgram.push (Layout.frameStackRegisters regs)) :=
  stack_command_writesWithin regs _ (Layout.frameStack_footprint_subset regs)
    _ (push_sourceWritesWithin _)

private theorem frame_pop_writesWithin
    (regs : NeighborhoodTrial.Registers controller) :
    RAM.Structured.Footprint.CmdWritesWithin
      regs.layout.footprint
      (NeighborhoodProgram.pop (Layout.frameStackRegisters regs)) :=
  stack_command_writesWithin regs _ (Layout.frameStack_footprint_subset regs)
    _ (pop_sourceWritesWithin _)

private theorem frame_peek_writesWithin
    (regs : NeighborhoodTrial.Registers controller) :
    RAM.Structured.Footprint.CmdWritesWithin
      regs.layout.footprint
      (NeighborhoodProgram.peek (Layout.frameStackRegisters regs)) :=
  stack_command_writesWithin regs _ (Layout.frameStack_footprint_subset regs)
    _ (peek_sourceWritesWithin _)

private theorem codec_index_mem
    (regs : NeighborhoodTrial.Registers controller) (slot : Fin 7) :
    (Layout.frameCodecRegisters regs).index slot ∈
      regs.layout.footprint :=
  Layout.frameCodec_footprint_subset regs
    ((Layout.frameCodecRegisters regs).index_mem_footprint slot)

private theorem frame_index_mem
    (regs : NeighborhoodTrial.Registers controller) (slot : Fin 7) :
    (Layout.frameStackRegisters regs).index slot ∈
      regs.layout.footprint :=
  Layout.frameStack_footprint_subset regs
    ((Layout.frameStackRegisters regs).index_mem_footprint slot)

theorem encodeActive_writesWithin_internal
    (regs : NeighborhoodTrial.Registers controller) :
    RAM.Structured.Footprint.CmdWritesWithin
      regs.layout.footprint (encodeActive regs) := by
  simp [encodeActive, encodeActiveOps, Cmd.basics, Cmd.seqList,
    RAM.Structured.Footprint.CmdWritesWithin,
    RAM.Structured.Footprint.BasicWritesWithin,
    Layout.index_mem_layout_footprint,
    codec_index_mem]

theorem encodeActive_runs_internal
    (regs : NeighborhoodTrial.Registers controller) (store : Store) :
    Runs (encodeActive regs) store
      (Basic.execList (encodeActiveOps regs) store) := by
  exact basics_runs (encodeActiveOps regs) store

theorem encodeActive_frameCode_internal
    (regs : NeighborhoodTrial.Registers controller) (store : Store) :
    (Basic.execList (encodeActiveOps regs) store)
        (Layout.frameCode regs) =
      activeCode
        (store (Layout.chunkRadix regs))
        (store (Layout.bankRadix regs))
        (store (Layout.fuel regs))
        (store (Layout.nodeCode regs))
        (store (Layout.scalar regs))
        (store (Layout.out regs))
        (store (Layout.phaseCode regs)) := by
  simp [encodeActiveOps, Basic.execList, Basic.exec, activeCode,
    Layout.frameCodecRegisters, Layout.frameCodecMap,
    regs.injective.eq_iff]

private theorem initializeCodec_runs_internal
    (regs : NeighborhoodTrial.Registers controller)
    (store : Store) (radix bankRadix code : ℕ)
    (hword :
      store (Layout.frameCodecRegisters regs).word = code)
    (hbase :
      store (Layout.frameCodecRegisters regs).base = radix)
    (hbank :
      store (Layout.bankRadix regs) = bankRadix) :
    ∃ final,
      Runs (initializeCodec regs) store final ∧
      final (Layout.frameCodecRegisters regs).word = code ∧
      final (Layout.frameCodecRegisters regs).base = radix ∧
      final (Layout.frameCodecRegisters regs).basePred = radix - 1 ∧
      final (Layout.frameCodecRegisters regs).one = 1 ∧
      final (Layout.bankRadix regs) = bankRadix := by
  let codec := Layout.frameCodecRegisters regs
  change store codec.word = code at hword
  change store codec.base = radix at hbase
  let ops : List Basic :=
    [.imm codec.one 1,
      .sub codec.basePred codec.base codec.one]
  let final := Basic.execList ops store
  refine ⟨final, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simpa [initializeCodec, codec, ops] using
      basics_runs ops store
  · change final codec.word = code
    simp [final, ops, Basic.execList, Basic.exec,
      codec.injective.eq_iff, hword]
  · change final codec.base = radix
    simp [final, ops, Basic.execList, Basic.exec,
      codec.injective.eq_iff, hbase]
  · change final codec.basePred = radix - 1
    simp [final, ops, Basic.execList, Basic.exec,
      codec.injective.eq_iff, hbase]
  · change final codec.one = 1
    simp [final, ops, Basic.execList, Basic.exec,
      codec.injective.eq_iff]
  · change final (regs.index 14) = bankRadix
    simp [final, ops, Basic.execList, Basic.exec, codec,
      Layout.frameCodecRegisters, Layout.frameCodecMap,
      regs.injective.eq_iff, hbank]

private theorem readFuel_runs_internal
    (regs : NeighborhoodTrial.Registers controller)
    (store : Store) (radix bankRadix code : ℕ)
    (hradix : 0 < radix)
    (hword :
      store (Layout.frameCodecRegisters regs).word = code)
    (hbase :
      store (Layout.frameCodecRegisters regs).base = radix)
    (hbasePred :
      store (Layout.frameCodecRegisters regs).basePred = radix - 1)
    (hone :
      store (Layout.frameCodecRegisters regs).one = 1)
    (hbank :
      store (Layout.bankRadix regs) = bankRadix) :
    ∃ final,
      Runs (readFuel regs) store final ∧
      final (Layout.fuel regs) =
        PackedDigits.digit radix code 0 ∧
      final (Layout.frameCodecRegisters regs).word = code ∧
      final (Layout.frameCodecRegisters regs).base = radix ∧
      final (Layout.frameCodecRegisters regs).basePred = radix - 1 ∧
      final (Layout.frameCodecRegisters regs).one = 1 ∧
      final (Layout.bankRadix regs) = bankRadix := by
  let codec := Layout.frameCodecRegisters regs
  change store codec.word = code at hword
  change store codec.base = radix at hbase
  change store codec.basePred = radix - 1 at hbasePred
  change store codec.one = 1 at hone
  obtain ⟨middle, hpeek, hmiddleWord, hmiddleValue, _hmiddleTest,
      hmiddleBase, hmiddleBasePred⟩ :=
    NeighborhoodProgram.peek_runs codec store radix code hradix
      hword hbase hbasePred
  have hmiddleOne : middle codec.one = 1 := by
    rw [RAM.Structured.Footprint.runs_eq_outside
      (peek_sourceWritesWithin_withoutOne codec) hpeek (by simp)]
    exact hone
  have hmiddleBank :
      middle (Layout.bankRadix regs) = bankRadix := by
    rw [codec_run_preserves_physical regs 14
      (by
        intro index
        fin_cases index <;> decide)
      (peek_sourceWritesWithin codec) hpeek]
    exact hbank
  have hne :
      Layout.fuel regs ≠ codec.value := by
    simp [codec, Layout.frameCodecRegisters, Layout.frameCodecMap,
      regs.injective.eq_iff]
  have hfuelWord :
      Layout.fuel regs ≠ codec.word := by
    simp [codec, Layout.frameCodecRegisters, Layout.frameCodecMap,
      regs.injective.eq_iff]
  have hfuelBase :
      Layout.fuel regs ≠ codec.base := by
    simp [codec, Layout.frameCodecRegisters, Layout.frameCodecMap,
      regs.injective.eq_iff]
  have hfuelBasePred :
      Layout.fuel regs ≠ codec.basePred := by
    simp [codec, Layout.frameCodecRegisters, Layout.frameCodecMap,
      regs.injective.eq_iff]
  have hfuelOne :
      Layout.fuel regs ≠ codec.one := by
    simp [codec, Layout.frameCodecRegisters, Layout.frameCodecMap,
      regs.injective.eq_iff]
  let final :=
    Function.update middle (Layout.fuel regs) (middle codec.value)
  have hcopy :
      Runs (copy (Layout.fuel regs) codec.value) middle final := by
    exact copy_runs_internal middle hne
  refine ⟨final, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact Runs.seq hpeek hcopy
  · simp [final, hmiddleValue]
  · change final codec.word = code
    simpa [final, hfuelWord, Ne.symm hfuelWord] using hmiddleWord
  · change final codec.base = radix
    simpa [final, hfuelBase, Ne.symm hfuelBase] using hmiddleBase
  · change final codec.basePred = radix - 1
    simpa [final, hfuelBasePred, Ne.symm hfuelBasePred] using
      hmiddleBasePred
  · change final codec.one = 1
    simpa [final, hfuelOne, Ne.symm hfuelOne] using hmiddleOne
  · change final (regs.index 14) = bankRadix
    simp [final, regs.injective.eq_iff, hmiddleBank]

private theorem captureNode_runs_internal
    (regs : NeighborhoodTrial.Registers controller)
    (store : Store) (radix bankRadix code fuelValue : ℕ)
    (hradix : 0 < radix)
    (hfuel :
      store (Layout.fuel regs) = fuelValue)
    (hword :
      store (Layout.frameCodecRegisters regs).word = code)
    (hbase :
      store (Layout.frameCodecRegisters regs).base = radix)
    (hbasePred :
      store (Layout.frameCodecRegisters regs).basePred = radix - 1)
    (hone :
      store (Layout.frameCodecRegisters regs).one = 1)
    (hbank :
      store (Layout.bankRadix regs) = bankRadix) :
    ∃ final,
      Runs (captureNode regs) store final ∧
      final (Layout.fuel regs) = fuelValue ∧
      final (Layout.nodeCode regs) = PackedDigits.pop radix code ∧
      final (Layout.frameCodecRegisters regs).word =
        PackedDigits.pop radix code ∧
      final (Layout.frameCodecRegisters regs).base = radix ∧
      final (Layout.frameCodecRegisters regs).basePred = radix - 1 ∧
      final (Layout.frameCodecRegisters regs).one = 1 ∧
      final (Layout.bankRadix regs) = bankRadix := by
  let codec := Layout.frameCodecRegisters regs
  change store codec.word = code at hword
  change store codec.base = radix at hbase
  change store codec.basePred = radix - 1 at hbasePred
  change store codec.one = 1 at hone
  obtain ⟨middle, hpop, hmiddleWord, _hmiddleQuotient,
      _hmiddleTest, hmiddleBase, hmiddleBasePred, hmiddleOne⟩ :=
    NeighborhoodProgram.pop_runs codec store radix code hradix
      hword hbase hbasePred hone
  have hmiddleFuel :
      middle (Layout.fuel regs) = fuelValue := by
    rw [codec_run_preserves_physical regs 22
      (by
        intro index
        fin_cases index <;> decide)
      (pop_sourceWritesWithin codec) hpop]
    exact hfuel
  have hmiddleBank :
      middle (Layout.bankRadix regs) = bankRadix := by
    rw [codec_run_preserves_physical regs 14
      (by
        intro index
        fin_cases index <;> decide)
      (pop_sourceWritesWithin codec) hpop]
    exact hbank
  have hne :
      Layout.nodeCode regs ≠ codec.word := by
    simp [codec, Layout.frameCodecRegisters, Layout.frameCodecMap,
      regs.injective.eq_iff]
  have hnodeFuel :
      Layout.nodeCode regs ≠ Layout.fuel regs := by
    exact regs.injective.ne (by decide)
  have hnodeBase :
      Layout.nodeCode regs ≠ codec.base := by
    simp [codec, Layout.frameCodecRegisters, Layout.frameCodecMap,
      regs.injective.eq_iff]
  have hnodeBasePred :
      Layout.nodeCode regs ≠ codec.basePred := by
    simp [codec, Layout.frameCodecRegisters, Layout.frameCodecMap,
      regs.injective.eq_iff]
  have hnodeOne :
      Layout.nodeCode regs ≠ codec.one := by
    simp [codec, Layout.frameCodecRegisters, Layout.frameCodecMap,
      regs.injective.eq_iff]
  let final :=
    Function.update middle (Layout.nodeCode regs) (middle codec.word)
  have hcopy :
      Runs (copy (Layout.nodeCode regs) codec.word) middle final := by
    exact copy_runs_internal middle hne
  refine ⟨final, Runs.seq hpop hcopy, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simpa [final, hnodeFuel, Ne.symm hnodeFuel] using hmiddleFuel
  · simp [final, hmiddleWord]
  · change final codec.word = PackedDigits.pop radix code
    simpa [final, hne, Ne.symm hne] using hmiddleWord
  · change final codec.base = radix
    simpa [final, hnodeBase, Ne.symm hnodeBase] using hmiddleBase
  · change final codec.basePred = radix - 1
    simpa [final, hnodeBasePred, Ne.symm hnodeBasePred] using
      hmiddleBasePred
  · change final codec.one = 1
    simpa [final, hnodeOne, Ne.symm hnodeOne] using hmiddleOne
  · change final (regs.index 14) = bankRadix
    simp [final, regs.injective.eq_iff, hmiddleBank]

private theorem recoverNode_runs_internal
    (regs : NeighborhoodTrial.Registers controller)
    (store : Store)
    (radix bankRadix word fuelValue nodeSnapshot : ℕ)
    (hradix : 0 < radix)
    (hfuel :
      store (Layout.fuel regs) = fuelValue)
    (hnode :
      store (Layout.nodeCode regs) = nodeSnapshot)
    (hword :
      store (Layout.frameCodecRegisters regs).word = word)
    (hbase :
      store (Layout.frameCodecRegisters regs).base = radix)
    (hbasePred :
      store (Layout.frameCodecRegisters regs).basePred = radix - 1)
    (hone :
      store (Layout.frameCodecRegisters regs).one = 1)
    (hbank :
      store (Layout.bankRadix regs) = bankRadix) :
    ∃ final,
      Runs (recoverNode regs) store final ∧
      final (Layout.fuel regs) = fuelValue ∧
      final (Layout.nodeCode regs) =
        nodeSnapshot -
          bankRadix * bankRadix *
            (PackedDigits.pop radix)^[4] word ∧
      final (Layout.frameCodecRegisters regs).word =
        (PackedDigits.pop radix)^[4] word ∧
      final (Layout.frameCodecRegisters regs).base = radix ∧
      final (Layout.frameCodecRegisters regs).basePred = radix - 1 ∧
      final (Layout.frameCodecRegisters regs).one = 1 ∧
      final (Layout.bankRadix regs) = bankRadix := by
  let codec := Layout.frameCodecRegisters regs
  change store codec.word = word at hword
  change store codec.base = radix at hbase
  change store codec.basePred = radix - 1 at hbasePred
  change store codec.one = 1 at hone
  obtain ⟨middle, hpops, hmiddleWord, hmiddleBase,
      hmiddleBasePred, hmiddleOne⟩ :=
    popMany_runs_internal regs store radix word 4 hradix hword
      hbase hbasePred hone
  have hmiddleFuel :
      middle (Layout.fuel regs) = fuelValue := by
    rw [codec_run_preserves_physical regs 22
      (by
        intro index
        fin_cases index <;> decide)
      (popMany_sourceWritesWithin regs 4) hpops]
    exact hfuel
  have hmiddleNode :
      middle (Layout.nodeCode regs) = nodeSnapshot := by
    rw [codec_run_preserves_physical regs 23
      (by
        intro index
        fin_cases index <;> decide)
      (popMany_sourceWritesWithin regs 4) hpops]
    exact hnode
  have hmiddleBank :
      middle (Layout.bankRadix regs) = bankRadix := by
    rw [codec_run_preserves_physical regs 14
      (by
        intro index
        fin_cases index <;> decide)
      (popMany_sourceWritesWithin regs 4) hpops]
    exact hbank
  let ops : List Basic :=
    [.mul (Layout.codecDigit regs)
        (Layout.bankRadix regs) (Layout.bankRadix regs),
      .mul codec.quotient
        (Layout.codecDigit regs) codec.word,
      .sub (Layout.nodeCode regs)
        (Layout.nodeCode regs) codec.quotient]
  let final := Basic.execList ops middle
  have hbasics :
      Runs (Cmd.basics ops) middle final := by
    exact basics_runs ops middle
  refine ⟨final, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simpa [recoverNode, popNodeCode, codec, ops] using
      Runs.seq hpops hbasics
  · change final (regs.index 22) = fuelValue
    change middle (regs.index 22) = fuelValue at hmiddleFuel
    simp [final, ops, Basic.execList, Basic.exec, codec,
      Layout.frameCodecRegisters, Layout.frameCodecMap,
      regs.injective.eq_iff, hmiddleFuel]
  · change final (regs.index 23) =
      nodeSnapshot -
        bankRadix * bankRadix *
          (PackedDigits.pop radix)^[4] word
    change middle (regs.index 23) = nodeSnapshot at hmiddleNode
    change middle (regs.index 14) = bankRadix at hmiddleBank
    change middle (regs.index 29) =
      (PackedDigits.pop radix)^[4] word at hmiddleWord
    simp [final, ops, Basic.execList, Basic.exec, codec,
      NeighborhoodProgram.StackRegisters.word,
      Layout.frameCodecRegisters, Layout.frameCodecMap,
      regs.injective.eq_iff,
      hmiddleNode, hmiddleBank, hmiddleWord]
  · change final (regs.index 29) =
      (PackedDigits.pop radix)^[4] word
    change middle (regs.index 29) =
      (PackedDigits.pop radix)^[4] word at hmiddleWord
    simp [final, ops, Basic.execList, Basic.exec, codec,
      NeighborhoodProgram.StackRegisters.word,
      Layout.frameCodecRegisters, Layout.frameCodecMap,
      regs.injective.eq_iff, hmiddleWord]
  · change final (regs.index 8) = radix
    change middle (regs.index 8) = radix at hmiddleBase
    simp [final, ops, Basic.execList, Basic.exec, codec,
      Layout.frameCodecRegisters, Layout.frameCodecMap,
      regs.injective.eq_iff, hmiddleBase]
  · change final (regs.index 1) = radix - 1
    change middle (regs.index 1) = radix - 1 at hmiddleBasePred
    simp [final, ops, Basic.execList, Basic.exec, codec,
      Layout.frameCodecRegisters, Layout.frameCodecMap,
      regs.injective.eq_iff, hmiddleBasePred]
  · change final (regs.index 17) = 1
    change middle (regs.index 17) = 1 at hmiddleOne
    simp [final, ops, Basic.execList, Basic.exec, codec,
      Layout.frameCodecRegisters, Layout.frameCodecMap,
      regs.injective.eq_iff, hmiddleOne]
  · change final (regs.index 14) = bankRadix
    simp [final, ops, Basic.execList, Basic.exec, codec,
      Layout.frameCodecRegisters, Layout.frameCodecMap,
      regs.injective.eq_iff, hmiddleBank]

private theorem captureScalar_runs_internal
    (regs : NeighborhoodTrial.Registers controller)
    (store : Store)
    (radix bankRadix word fuelValue nodeValue : ℕ)
    (hfuel :
      store (Layout.fuel regs) = fuelValue)
    (hnode :
      store (Layout.nodeCode regs) = nodeValue)
    (hword :
      store (Layout.frameCodecRegisters regs).word = word)
    (hbase :
      store (Layout.frameCodecRegisters regs).base = radix)
    (hbasePred :
      store (Layout.frameCodecRegisters regs).basePred = radix - 1)
    (hone :
      store (Layout.frameCodecRegisters regs).one = 1)
    (hbank :
      store (Layout.bankRadix regs) = bankRadix) :
    ∃ final,
      Runs (captureScalar regs) store final ∧
      final (Layout.fuel regs) = fuelValue ∧
      final (Layout.nodeCode regs) = nodeValue ∧
      final (Layout.scalar regs) = word ∧
      final (Layout.frameCodecRegisters regs).word = word ∧
      final (Layout.frameCodecRegisters regs).base = radix ∧
      final (Layout.frameCodecRegisters regs).basePred = radix - 1 ∧
      final (Layout.frameCodecRegisters regs).one = 1 ∧
      final (Layout.bankRadix regs) = bankRadix := by
  let codec := Layout.frameCodecRegisters regs
  change store codec.word = word at hword
  change store codec.base = radix at hbase
  change store codec.basePred = radix - 1 at hbasePred
  change store codec.one = 1 at hone
  have hne :
      Layout.scalar regs ≠ codec.word := by
    simp [codec, NeighborhoodProgram.StackRegisters.word,
      Layout.frameCodecRegisters, Layout.frameCodecMap,
      regs.injective.eq_iff]
  have hscalarFuel :
      Layout.scalar regs ≠ Layout.fuel regs :=
    regs.injective.ne (by decide)
  have hscalarNode :
      Layout.scalar regs ≠ Layout.nodeCode regs :=
    regs.injective.ne (by decide)
  have hscalarBase :
      Layout.scalar regs ≠ codec.base := by
    simp [codec, Layout.frameCodecRegisters, Layout.frameCodecMap,
      regs.injective.eq_iff]
  have hscalarBasePred :
      Layout.scalar regs ≠ codec.basePred := by
    simp [codec, Layout.frameCodecRegisters, Layout.frameCodecMap,
      regs.injective.eq_iff]
  have hscalarOne :
      Layout.scalar regs ≠ codec.one := by
    simp [codec, Layout.frameCodecRegisters, Layout.frameCodecMap,
      regs.injective.eq_iff]
  let final :=
    Function.update store (Layout.scalar regs) (store codec.word)
  have hcopy :
      Runs (copy (Layout.scalar regs) codec.word) store final := by
    exact copy_runs_internal store hne
  refine ⟨final, hcopy, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simpa [final, hscalarFuel, Ne.symm hscalarFuel] using hfuel
  · simpa [final, hscalarNode, Ne.symm hscalarNode] using hnode
  · simp [final, hword]
  · change final codec.word = word
    simpa [final, hne, Ne.symm hne] using hword
  · change final codec.base = radix
    simpa [final, hscalarBase, Ne.symm hscalarBase] using hbase
  · change final codec.basePred = radix - 1
    simpa [final, hscalarBasePred, Ne.symm hscalarBasePred] using
      hbasePred
  · change final codec.one = 1
    simpa [final, hscalarOne, Ne.symm hscalarOne] using hone
  · change final (regs.index 14) = bankRadix
    simp [final, regs.injective.eq_iff, hbank]

private theorem recoverScalar_runs_internal
    (regs : NeighborhoodTrial.Registers controller)
    (store : Store)
    (radix bankRadix word fuelValue nodeValue scalarSnapshot : ℕ)
    (hradix : 0 < radix)
    (hfuel :
      store (Layout.fuel regs) = fuelValue)
    (hnode :
      store (Layout.nodeCode regs) = nodeValue)
    (hscalar :
      store (Layout.scalar regs) = scalarSnapshot)
    (hword :
      store (Layout.frameCodecRegisters regs).word = word)
    (hbase :
      store (Layout.frameCodecRegisters regs).base = radix)
    (hbasePred :
      store (Layout.frameCodecRegisters regs).basePred = radix - 1)
    (hone :
      store (Layout.frameCodecRegisters regs).one = 1)
    (hbank :
      store (Layout.bankRadix regs) = bankRadix) :
    ∃ final,
      Runs (recoverScalar regs) store final ∧
      final (Layout.fuel regs) = fuelValue ∧
      final (Layout.nodeCode regs) = nodeValue ∧
      final (Layout.scalar regs) =
        scalarSnapshot -
          bankRadix * (PackedDigits.pop radix)^[2] word ∧
      final (Layout.frameCodecRegisters regs).word =
        (PackedDigits.pop radix)^[2] word ∧
      final (Layout.frameCodecRegisters regs).base = radix ∧
      final (Layout.frameCodecRegisters regs).basePred = radix - 1 ∧
      final (Layout.frameCodecRegisters regs).one = 1 ∧
      final (Layout.bankRadix regs) = bankRadix := by
  let codec := Layout.frameCodecRegisters regs
  change store codec.word = word at hword
  change store codec.base = radix at hbase
  change store codec.basePred = radix - 1 at hbasePred
  change store codec.one = 1 at hone
  obtain ⟨middle, hpops, hmiddleWord, hmiddleBase,
      hmiddleBasePred, hmiddleOne⟩ :=
    popMany_runs_internal regs store radix word 2 hradix hword
      hbase hbasePred hone
  have hmiddleFuel :
      middle (Layout.fuel regs) = fuelValue := by
    rw [codec_run_preserves_physical regs 22
      (by
        intro index
        fin_cases index <;> decide)
      (popMany_sourceWritesWithin regs 2) hpops]
    exact hfuel
  have hmiddleNode :
      middle (Layout.nodeCode regs) = nodeValue := by
    rw [codec_run_preserves_physical regs 23
      (by
        intro index
        fin_cases index <;> decide)
      (popMany_sourceWritesWithin regs 2) hpops]
    exact hnode
  have hmiddleScalar :
      middle (Layout.scalar regs) = scalarSnapshot := by
    rw [codec_run_preserves_physical regs 25
      (by
        intro index
        fin_cases index <;> decide)
      (popMany_sourceWritesWithin regs 2) hpops]
    exact hscalar
  have hmiddleBank :
      middle (Layout.bankRadix regs) = bankRadix := by
    rw [codec_run_preserves_physical regs 14
      (by
        intro index
        fin_cases index <;> decide)
      (popMany_sourceWritesWithin regs 2) hpops]
    exact hbank
  let ops : List Basic :=
    [.mul codec.quotient
        (Layout.bankRadix regs) codec.word,
      .sub (Layout.scalar regs)
        (Layout.scalar regs) codec.quotient]
  let final := Basic.execList ops middle
  have hbasics :
      Runs (Cmd.basics ops) middle final := by
    exact basics_runs ops middle
  refine ⟨final, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simpa [recoverScalar, popScalar, codec, ops] using
      Runs.seq hpops hbasics
  · change final (regs.index 22) = fuelValue
    change middle (regs.index 22) = fuelValue at hmiddleFuel
    simp [final, ops, Basic.execList, Basic.exec, codec,
      Layout.frameCodecRegisters, Layout.frameCodecMap,
      regs.injective.eq_iff, hmiddleFuel]
  · change final (regs.index 23) = nodeValue
    change middle (regs.index 23) = nodeValue at hmiddleNode
    simp [final, ops, Basic.execList, Basic.exec, codec,
      Layout.frameCodecRegisters, Layout.frameCodecMap,
      regs.injective.eq_iff, hmiddleNode]
  · change final (regs.index 25) =
      scalarSnapshot -
        bankRadix * (PackedDigits.pop radix)^[2] word
    change middle (regs.index 25) =
      scalarSnapshot at hmiddleScalar
    change middle (regs.index 14) = bankRadix at hmiddleBank
    change middle (regs.index 29) =
      (PackedDigits.pop radix)^[2] word at hmiddleWord
    simp [final, ops, Basic.execList, Basic.exec, codec,
      NeighborhoodProgram.StackRegisters.word,
      Layout.frameCodecRegisters, Layout.frameCodecMap,
      regs.injective.eq_iff,
      hmiddleScalar, hmiddleBank, hmiddleWord]
  · change final (regs.index 29) =
      (PackedDigits.pop radix)^[2] word
    change middle (regs.index 29) =
      (PackedDigits.pop radix)^[2] word at hmiddleWord
    simp [final, ops, Basic.execList, Basic.exec, codec,
      NeighborhoodProgram.StackRegisters.word,
      Layout.frameCodecRegisters, Layout.frameCodecMap,
      regs.injective.eq_iff, hmiddleWord]
  · change final (regs.index 8) = radix
    change middle (regs.index 8) = radix at hmiddleBase
    simp [final, ops, Basic.execList, Basic.exec, codec,
      Layout.frameCodecRegisters, Layout.frameCodecMap,
      regs.injective.eq_iff, hmiddleBase]
  · change final (regs.index 1) = radix - 1
    change middle (regs.index 1) = radix - 1 at hmiddleBasePred
    simp [final, ops, Basic.execList, Basic.exec, codec,
      Layout.frameCodecRegisters, Layout.frameCodecMap,
      regs.injective.eq_iff, hmiddleBasePred]
  · change final (regs.index 17) = 1
    change middle (regs.index 17) = 1 at hmiddleOne
    simp [final, ops, Basic.execList, Basic.exec, codec,
      Layout.frameCodecRegisters, Layout.frameCodecMap,
      regs.injective.eq_iff, hmiddleOne]
  · change final (regs.index 14) = bankRadix
    simp [final, ops, Basic.execList, Basic.exec, codec,
      Layout.frameCodecRegisters, Layout.frameCodecMap,
      regs.injective.eq_iff, hmiddleBank]

private theorem readOut_runs_internal
    (regs : NeighborhoodTrial.Registers controller)
    (store : Store)
    (radix bankRadix word fuelValue nodeValue scalarValue : ℕ)
    (hradix : 0 < radix)
    (hfuel :
      store (Layout.fuel regs) = fuelValue)
    (hnode :
      store (Layout.nodeCode regs) = nodeValue)
    (hscalar :
      store (Layout.scalar regs) = scalarValue)
    (hword :
      store (Layout.frameCodecRegisters regs).word = word)
    (hbase :
      store (Layout.frameCodecRegisters regs).base = radix)
    (hbasePred :
      store (Layout.frameCodecRegisters regs).basePred = radix - 1)
    (hone :
      store (Layout.frameCodecRegisters regs).one = 1)
    (hbank :
      store (Layout.bankRadix regs) = bankRadix) :
    ∃ final,
      Runs (readOut regs) store final ∧
      final (Layout.fuel regs) = fuelValue ∧
      final (Layout.nodeCode regs) = nodeValue ∧
      final (Layout.scalar regs) = scalarValue ∧
      final (Layout.out regs) =
        PackedDigits.digit radix word 0 ∧
      final (Layout.frameCodecRegisters regs).word =
        PackedDigits.pop radix word ∧
      final (Layout.frameCodecRegisters regs).base = radix ∧
      final (Layout.frameCodecRegisters regs).basePred = radix - 1 ∧
      final (Layout.frameCodecRegisters regs).one = 1 ∧
      final (Layout.bankRadix regs) = bankRadix := by
  let codec := Layout.frameCodecRegisters regs
  change store codec.word = word at hword
  change store codec.base = radix at hbase
  change store codec.basePred = radix - 1 at hbasePred
  change store codec.one = 1 at hone
  obtain ⟨middle, hpeek, hmiddleWord, hmiddleValue, _hmiddleTest,
      hmiddleBase, hmiddleBasePred⟩ :=
    NeighborhoodProgram.peek_runs codec store radix word hradix
      hword hbase hbasePred
  have hmiddleOne : middle codec.one = 1 := by
    rw [RAM.Structured.Footprint.runs_eq_outside
      (peek_sourceWritesWithin_withoutOne codec) hpeek (by simp)]
    exact hone
  have hmiddleFuel :
      middle (Layout.fuel regs) = fuelValue := by
    rw [codec_run_preserves_physical regs 22
      (by
        intro index
        fin_cases index <;> decide)
      (peek_sourceWritesWithin codec) hpeek]
    exact hfuel
  have hmiddleNode :
      middle (Layout.nodeCode regs) = nodeValue := by
    rw [codec_run_preserves_physical regs 23
      (by
        intro index
        fin_cases index <;> decide)
      (peek_sourceWritesWithin codec) hpeek]
    exact hnode
  have hmiddleScalar :
      middle (Layout.scalar regs) = scalarValue := by
    rw [codec_run_preserves_physical regs 25
      (by
        intro index
        fin_cases index <;> decide)
      (peek_sourceWritesWithin codec) hpeek]
    exact hscalar
  have hmiddleBank :
      middle (Layout.bankRadix regs) = bankRadix := by
    rw [codec_run_preserves_physical regs 14
      (by
        intro index
        fin_cases index <;> decide)
      (peek_sourceWritesWithin codec) hpeek]
    exact hbank
  have hne :
      Layout.out regs ≠ codec.value := by
    simp [codec, Layout.frameCodecRegisters, Layout.frameCodecMap,
      regs.injective.eq_iff]
  have houtFuel :
      Layout.out regs ≠ Layout.fuel regs :=
    regs.injective.ne (by decide)
  have houtNode :
      Layout.out regs ≠ Layout.nodeCode regs :=
    regs.injective.ne (by decide)
  have houtScalar :
      Layout.out regs ≠ Layout.scalar regs :=
    regs.injective.ne (by decide)
  have houtWord :
      Layout.out regs ≠ codec.word := by
    simp [codec, NeighborhoodProgram.StackRegisters.word,
      Layout.frameCodecRegisters, Layout.frameCodecMap,
      regs.injective.eq_iff]
  have houtBase :
      Layout.out regs ≠ codec.base := by
    simp [codec, Layout.frameCodecRegisters, Layout.frameCodecMap,
      regs.injective.eq_iff]
  have houtBasePred :
      Layout.out regs ≠ codec.basePred := by
    simp [codec, Layout.frameCodecRegisters, Layout.frameCodecMap,
      regs.injective.eq_iff]
  have houtOne :
      Layout.out regs ≠ codec.one := by
    simp [codec, Layout.frameCodecRegisters, Layout.frameCodecMap,
      regs.injective.eq_iff]
  let copied :=
    Function.update middle (Layout.out regs) (middle codec.value)
  have hcopy :
      Runs (copy (Layout.out regs) codec.value) middle copied := by
    exact copy_runs_internal middle hne
  have hcopiedFuel :
      copied (Layout.fuel regs) = fuelValue := by
    simpa [copied, houtFuel, Ne.symm houtFuel] using hmiddleFuel
  have hcopiedNode :
      copied (Layout.nodeCode regs) = nodeValue := by
    simpa [copied, houtNode, Ne.symm houtNode] using hmiddleNode
  have hcopiedScalar :
      copied (Layout.scalar regs) = scalarValue := by
    simpa [copied, houtScalar, Ne.symm houtScalar] using hmiddleScalar
  have hcopiedOut :
      copied (Layout.out regs) =
        PackedDigits.digit radix word 0 := by
    simp [copied, hmiddleValue]
  have hcopiedWord :
      copied codec.word = word := by
    simpa [copied, houtWord, Ne.symm houtWord] using hmiddleWord
  have hcopiedBase :
      copied codec.base = radix := by
    simpa [copied, houtBase, Ne.symm houtBase] using hmiddleBase
  have hcopiedBasePred :
      copied codec.basePred = radix - 1 := by
    simpa [copied, houtBasePred, Ne.symm houtBasePred] using
      hmiddleBasePred
  have hcopiedOne :
      copied codec.one = 1 := by
    simpa [copied, houtOne, Ne.symm houtOne] using hmiddleOne
  have hcopiedBank :
      copied (Layout.bankRadix regs) = bankRadix := by
    simp [copied, regs.injective.eq_iff, hmiddleBank]
  obtain ⟨final, hpop, hfinalWord, _hfinalQuotient,
      _hfinalTest, hfinalBase, hfinalBasePred, hfinalOne⟩ :=
    NeighborhoodProgram.pop_runs codec copied radix word hradix
      hcopiedWord hcopiedBase hcopiedBasePred hcopiedOne
  have hfinalFuel :
      final (Layout.fuel regs) = copied (Layout.fuel regs) :=
    codec_run_preserves_physical regs 22
      (by
        intro index
        fin_cases index <;> decide)
      (pop_sourceWritesWithin codec) hpop
  have hfinalNode :
      final (Layout.nodeCode regs) = copied (Layout.nodeCode regs) :=
    codec_run_preserves_physical regs 23
      (by
        intro index
        fin_cases index <;> decide)
      (pop_sourceWritesWithin codec) hpop
  have hfinalScalar :
      final (Layout.scalar regs) = copied (Layout.scalar regs) :=
    codec_run_preserves_physical regs 25
      (by
        intro index
        fin_cases index <;> decide)
      (pop_sourceWritesWithin codec) hpop
  have hfinalOut :
      final (Layout.out regs) = copied (Layout.out regs) :=
    codec_run_preserves_physical regs 26
      (by
        intro index
        fin_cases index <;> decide)
      (pop_sourceWritesWithin codec) hpop
  have hfinalBank :
      final (Layout.bankRadix regs) =
        copied (Layout.bankRadix regs) :=
    codec_run_preserves_physical regs 14
      (by
        intro index
        fin_cases index <;> decide)
      (pop_sourceWritesWithin codec) hpop
  refine ⟨final, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simpa [readOut, codec] using
      Runs.seq hpeek (Runs.seq hcopy hpop)
  · exact hfinalFuel.trans hcopiedFuel
  · exact hfinalNode.trans hcopiedNode
  · exact hfinalScalar.trans hcopiedScalar
  · exact hfinalOut.trans hcopiedOut
  · exact hfinalWord
  · exact hfinalBase
  · exact hfinalBasePred
  · exact hfinalOne
  · exact hfinalBank.trans hcopiedBank

private theorem finishLoad_runs_internal
    (regs : NeighborhoodTrial.Registers controller)
    (store : Store)
    (fuelValue nodeValue scalarValue outValue phaseValue : ℕ)
    (hfuel :
      store (Layout.fuel regs) = fuelValue)
    (hnode :
      store (Layout.nodeCode regs) = nodeValue)
    (hscalar :
      store (Layout.scalar regs) = scalarValue)
    (hout :
      store (Layout.out regs) = outValue)
    (hword :
      store (Layout.frameCodecRegisters regs).word = phaseValue) :
    ∃ final,
      Runs (finishLoad regs) store final ∧
      final (Layout.fuel regs) = fuelValue ∧
      final (Layout.nodeCode regs) = nodeValue ∧
      final (Layout.scalar regs) = scalarValue ∧
      final (Layout.out regs) = outValue ∧
      final (Layout.phaseCode regs) = phaseValue ∧
      final (Layout.active regs) = 1 := by
  let codec := Layout.frameCodecRegisters regs
  change store codec.word = phaseValue at hword
  have hne :
      Layout.phaseCode regs ≠ codec.word := by
    simp [codec, NeighborhoodProgram.StackRegisters.word,
      Layout.frameCodecRegisters, Layout.frameCodecMap,
      regs.injective.eq_iff]
  let middle :=
    Function.update store (Layout.phaseCode regs) (store codec.word)
  have hcopy :
      Runs (copy (Layout.phaseCode regs) codec.word) store middle := by
    exact copy_runs_internal store hne
  let ops : List Basic :=
    [.imm (Layout.active regs) 1,
      .imm codec.word 0,
      .imm codec.quotient 0,
      .imm codec.test 0,
      .imm codec.value 0]
  let final := Basic.execList ops middle
  have hbasics :
      Runs (Cmd.basics ops) middle final := by
    exact basics_runs ops middle
  refine ⟨final, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simpa [finishLoad, codec, ops] using Runs.seq hcopy hbasics
  · change final (regs.index 22) = fuelValue
    change store (regs.index 22) = fuelValue at hfuel
    simp [final, middle, ops, Basic.execList, Basic.exec, codec,
      NeighborhoodProgram.StackRegisters.word,
      NeighborhoodProgram.StackRegisters.quotient,
      NeighborhoodProgram.StackRegisters.test,
      NeighborhoodProgram.StackRegisters.value,
      Layout.frameCodecRegisters, Layout.frameCodecMap,
      regs.injective.eq_iff, hfuel]
  · change final (regs.index 23) = nodeValue
    change store (regs.index 23) = nodeValue at hnode
    simp [final, middle, ops, Basic.execList, Basic.exec, codec,
      NeighborhoodProgram.StackRegisters.word,
      NeighborhoodProgram.StackRegisters.quotient,
      NeighborhoodProgram.StackRegisters.test,
      NeighborhoodProgram.StackRegisters.value,
      Layout.frameCodecRegisters, Layout.frameCodecMap,
      regs.injective.eq_iff, hnode]
  · change final (regs.index 25) = scalarValue
    change store (regs.index 25) = scalarValue at hscalar
    simp [final, middle, ops, Basic.execList, Basic.exec, codec,
      NeighborhoodProgram.StackRegisters.word,
      NeighborhoodProgram.StackRegisters.quotient,
      NeighborhoodProgram.StackRegisters.test,
      NeighborhoodProgram.StackRegisters.value,
      Layout.frameCodecRegisters, Layout.frameCodecMap,
      regs.injective.eq_iff, hscalar]
  · change final (regs.index 26) = outValue
    change store (regs.index 26) = outValue at hout
    simp [final, middle, ops, Basic.execList, Basic.exec, codec,
      NeighborhoodProgram.StackRegisters.word,
      NeighborhoodProgram.StackRegisters.quotient,
      NeighborhoodProgram.StackRegisters.test,
      NeighborhoodProgram.StackRegisters.value,
      Layout.frameCodecRegisters, Layout.frameCodecMap,
      regs.injective.eq_iff, hout]
  · change final (regs.index 27) = phaseValue
    change store (regs.index 29) = phaseValue at hword
    simp [final, middle, ops, Basic.execList, Basic.exec, codec,
      NeighborhoodProgram.StackRegisters.word,
      NeighborhoodProgram.StackRegisters.quotient,
      NeighborhoodProgram.StackRegisters.test,
      NeighborhoodProgram.StackRegisters.value,
      Layout.frameCodecRegisters, Layout.frameCodecMap,
      regs.injective.eq_iff, hword]
  · change final (regs.index 28) = 1
    simp [final, middle, ops, Basic.execList, Basic.exec, codec,
      NeighborhoodProgram.StackRegisters.word,
      NeighborhoodProgram.StackRegisters.quotient,
      NeighborhoodProgram.StackRegisters.test,
      NeighborhoodProgram.StackRegisters.value,
      Layout.frameCodecRegisters, Layout.frameCodecMap,
      regs.injective.eq_iff]

theorem loadActive_runs_internal
    (regs : NeighborhoodTrial.Registers controller)
    (store : Store) (radix bankRadix code : ℕ)
    (hradix : 0 < radix)
    (hword :
      store (Layout.frameCodecRegisters regs).word = code)
    (hbase :
      store (Layout.frameCodecRegisters regs).base = radix)
    (hbank :
      store (Layout.bankRadix regs) = bankRadix) :
    ∃ final,
      Runs (loadActive regs) store final ∧
      LoadPost regs radix bankRadix code final := by
  let popped1 := PackedDigits.pop radix code
  let popped5 := (PackedDigits.pop radix)^[4] popped1
  let popped7 := (PackedDigits.pop radix)^[2] popped5
  let popped8 := PackedDigits.pop radix popped7
  let fuelValue := PackedDigits.digit radix code 0
  let nodeValue := popped1 - bankRadix * bankRadix * popped5
  let scalarValue := popped5 - bankRadix * popped7
  let outValue := PackedDigits.digit radix popped7 0
  obtain ⟨afterInit, hinit, hinitWord, hinitBase,
      hinitBasePred, hinitOne, hinitBank⟩ :=
    initializeCodec_runs_internal regs store radix bankRadix code
      hword hbase hbank
  obtain ⟨afterFuel, hfuelRun, hafterFuel, hafterFuelWord,
      hafterFuelBase, hafterFuelBasePred, hafterFuelOne,
      hafterFuelBank⟩ :=
    readFuel_runs_internal regs afterInit radix bankRadix code
      hradix hinitWord hinitBase hinitBasePred hinitOne hinitBank
  obtain ⟨afterNodeCapture, hnodeCaptureRun,
      hnodeCaptureFuel, hnodeCaptureNode, hnodeCaptureWord,
      hnodeCaptureBase, hnodeCaptureBasePred, hnodeCaptureOne,
      hnodeCaptureBank⟩ :=
    captureNode_runs_internal regs afterFuel radix bankRadix code
      fuelValue hradix
      (by simpa [fuelValue] using hafterFuel)
      hafterFuelWord hafterFuelBase hafterFuelBasePred
      hafterFuelOne hafterFuelBank
  obtain ⟨afterNode, hnodeRun, hafterNodeFuel, hafterNode,
      hafterNodeWord, hafterNodeBase, hafterNodeBasePred,
      hafterNodeOne, hafterNodeBank⟩ :=
    recoverNode_runs_internal regs afterNodeCapture
      radix bankRadix popped1 fuelValue popped1 hradix
      hnodeCaptureFuel
      (by simpa [popped1] using hnodeCaptureNode)
      (by simpa [popped1] using hnodeCaptureWord)
      hnodeCaptureBase hnodeCaptureBasePred hnodeCaptureOne
      hnodeCaptureBank
  obtain ⟨afterScalarCapture, hscalarCaptureRun,
      hscalarCaptureFuel, hscalarCaptureNode,
      hscalarCaptureScalar, hscalarCaptureWord,
      hscalarCaptureBase, hscalarCaptureBasePred,
      hscalarCaptureOne, hscalarCaptureBank⟩ :=
    captureScalar_runs_internal regs afterNode
      radix bankRadix popped5 fuelValue nodeValue
      hafterNodeFuel
      (by simpa [nodeValue, popped5] using hafterNode)
      (by simpa [popped5] using hafterNodeWord)
      hafterNodeBase hafterNodeBasePred hafterNodeOne
      hafterNodeBank
  obtain ⟨afterScalar, hscalarRun, hafterScalarFuel,
      hafterScalarNode, hafterScalar, hafterScalarWord,
      hafterScalarBase, hafterScalarBasePred, hafterScalarOne,
      hafterScalarBank⟩ :=
    recoverScalar_runs_internal regs afterScalarCapture
      radix bankRadix popped5 fuelValue nodeValue popped5 hradix
      hscalarCaptureFuel hscalarCaptureNode
      (by simpa [popped5] using hscalarCaptureScalar)
      hscalarCaptureWord hscalarCaptureBase hscalarCaptureBasePred
      hscalarCaptureOne hscalarCaptureBank
  obtain ⟨afterOut, houtRun, hafterOutFuel, hafterOutNode,
      hafterOutScalar, hafterOut, hafterOutWord, hafterOutBase,
      hafterOutBasePred, hafterOutOne, _hafterOutBank⟩ :=
    readOut_runs_internal regs afterScalar
      radix bankRadix popped7 fuelValue nodeValue scalarValue hradix
      hafterScalarFuel hafterScalarNode
      (by simpa [scalarValue, popped7] using hafterScalar)
      (by simpa [popped7] using hafterScalarWord)
      hafterScalarBase hafterScalarBasePred hafterScalarOne
      hafterScalarBank
  obtain ⟨final, hfinishRun, hfinalFuel, hfinalNode,
      hfinalScalar, hfinalOut, hfinalPhase, hfinalActive⟩ :=
    finishLoad_runs_internal regs afterOut fuelValue nodeValue
      scalarValue outValue popped8 hafterOutFuel hafterOutNode
      hafterOutScalar
      (by simpa [outValue] using hafterOut)
      (by simpa [popped8] using hafterOutWord)
  have hrun : Runs (loadActive regs) store final := by
    simpa [loadActive, Cmd.seqList] using
      Runs.seq hinit
        (Runs.seq hfuelRun
          (Runs.seq hnodeCaptureRun
            (Runs.seq hnodeRun
              (Runs.seq hscalarCaptureRun
                (Runs.seq hscalarRun
                  (Runs.seq houtRun hfinishRun))))))
  refine ⟨final, hrun, ?_⟩
  constructor
  · simpa [decodedFuel, fuelValue] using hfinalFuel
  · simpa [decodedNodeCode, poppedCode, nodeValue, popped1,
      popped5, Function.iterate_succ_apply] using hfinalNode
  · simpa [decodedScalar, poppedCode, scalarValue, popped5,
      popped7, popped1, Function.iterate_succ_apply] using
      hfinalScalar
  · simpa [decodedOut, poppedCode, outValue, popped7, popped5,
      popped1, Function.iterate_succ_apply] using hfinalOut
  · simpa [decodedPhase, poppedCode, popped8, popped7, popped5,
      popped1, Function.iterate_succ_apply] using hfinalPhase
  · exact hfinalActive

private theorem poppedCode_encodeFrame_internal
    {tm : TM workTapeCount}
    {instanceData : NeighborhoodProgram.ResidueInstance tm}
    {base : ℕ}
    (frame : NeighborhoodScheduler.Frame tm instanceData)
    (hbase : 0 < base)
    (hfits : FrameCodec.FrameFits base frame)
    (count : ℕ)
    (hcount : count ≤ FrameCodec.frameDigitCount) :
    poppedCode base (FrameCodec.encodeFrame base frame) count =
      FrameCodec.encodeList base
        ((FrameCodec.frameDigits base frame).drop count) := by
  apply FrameCodec.pop_iterate_encodeList hbase _ hfits
  simpa [FrameCodec.Internal.frameDigits_length_internal] using hcount

private theorem digit_poppedCode_zero_internal
    (base code count : ℕ) :
    PackedDigits.digit base (poppedCode base code count) 0 =
      PackedDigits.digit base code count := by
  induction count generalizing code with
  | zero =>
      simp [poppedCode]
  | succ count ih =>
      rw [poppedCode, Function.iterate_succ_apply]
      change
        PackedDigits.digit base
            (poppedCode base (PackedDigits.pop base code) count) 0 =
          PackedDigits.digit base code (count + 1)
      rw [ih]
      rw [PackedDigits.digit_pop]

private theorem poppedCode_encodeFrame_one_internal
    {tm : TM workTapeCount}
    {instanceData : NeighborhoodProgram.ResidueInstance tm}
    {base : ℕ}
    (frame : NeighborhoodScheduler.Frame tm instanceData)
    (hbase : 0 < base)
    (hfits : FrameCodec.FrameFits base frame) :
    poppedCode base (FrameCodec.encodeFrame base frame) 1 =
      FrameCodec.encodeList base
        (FrameCodec.nodeDigits frame.node ++
          (FrameCodec.scalarDigits base frame.scalar ++
            (frame.out.val ::
              (FrameCodec.phaseDigits base frame.phase ++
                List.replicate FrameCodec.reservedDigitCount 0)))) := by
  rw [poppedCode_encodeFrame_internal frame hbase hfits 1
    (by simp [FrameCodec.frameDigitCount])]
  simp [FrameCodec.frameDigits]

private theorem poppedCode_encodeFrame_five_internal
    {tm : TM workTapeCount}
    {instanceData : NeighborhoodProgram.ResidueInstance tm}
    {base : ℕ}
    (frame : NeighborhoodScheduler.Frame tm instanceData)
    (hbase : 0 < base)
    (hfits : FrameCodec.FrameFits base frame) :
    poppedCode base (FrameCodec.encodeFrame base frame) 5 =
      FrameCodec.encodeList base
        (FrameCodec.scalarDigits base frame.scalar ++
          (frame.out.val ::
            (FrameCodec.phaseDigits base frame.phase ++
              List.replicate FrameCodec.reservedDigitCount 0))) := by
  rw [poppedCode_encodeFrame_internal frame hbase hfits 5
    (by simp [FrameCodec.frameDigitCount])]
  simp [FrameCodec.frameDigits,
    FrameCodec.Internal.nodeDigits_length_internal,
    FrameCodec.nodeDigitCount]

private theorem poppedCode_encodeFrame_seven_internal
    {tm : TM workTapeCount}
    {instanceData : NeighborhoodProgram.ResidueInstance tm}
    {base : ℕ}
    (frame : NeighborhoodScheduler.Frame tm instanceData)
    (hbase : 0 < base)
    (hfits : FrameCodec.FrameFits base frame) :
    poppedCode base (FrameCodec.encodeFrame base frame) 7 =
      FrameCodec.encodeList base
        (frame.out.val ::
          (FrameCodec.phaseDigits base frame.phase ++
            List.replicate FrameCodec.reservedDigitCount 0)) := by
  rw [poppedCode_encodeFrame_internal frame hbase hfits 7
    (by simp [FrameCodec.frameDigitCount])]
  cases hnode : frame.node with
  | failure =>
      simp [FrameCodec.frameDigits, FrameCodec.nodeDigits,
        FrameCodec.scalarDigits, hnode]
  | graph node =>
      cases node <;>
        simp [FrameCodec.frameDigits, FrameCodec.nodeDigits,
          FrameCodec.scalarDigits, hnode]

private theorem poppedCode_encodeFrame_eight_internal
    {tm : TM workTapeCount}
    {instanceData : NeighborhoodProgram.ResidueInstance tm}
    {base : ℕ}
    (frame : NeighborhoodScheduler.Frame tm instanceData)
    (hbase : 0 < base)
    (hfits : FrameCodec.FrameFits base frame) :
    poppedCode base (FrameCodec.encodeFrame base frame) 8 =
      FrameCodec.encodeList base
        (FrameCodec.phaseDigits base frame.phase ++
          List.replicate FrameCodec.reservedDigitCount 0) := by
  rw [poppedCode_encodeFrame_internal frame hbase hfits 8
    (by simp [FrameCodec.frameDigitCount])]
  cases hnode : frame.node with
  | failure =>
      simp [FrameCodec.frameDigits, FrameCodec.nodeDigits,
        FrameCodec.scalarDigits, hnode]
  | graph node =>
      cases node <;>
        simp [FrameCodec.frameDigits, FrameCodec.nodeDigits,
          FrameCodec.scalarDigits, hnode]

theorem decodedFuel_encodeFrame_internal
    {tm : TM workTapeCount}
    {instanceData : NeighborhoodProgram.ResidueInstance tm}
    {base : ℕ}
    (frame : NeighborhoodScheduler.Frame tm instanceData)
    (hfits : FrameCodec.FrameFits base frame) :
    decodedFuel base (FrameCodec.encodeFrame base frame) =
      frame.fuel := by
  exact FrameCodec.encodeFrame_fuel frame hfits

theorem decodedNodeCode_encodeFrame_internal
    {tm : TM workTapeCount}
    {instanceData : NeighborhoodProgram.ResidueInstance tm}
    {base : ℕ}
    (frame : NeighborhoodScheduler.Frame tm instanceData)
    (hbase : 0 < base)
    (hfits : FrameCodec.FrameFits base frame) :
    decodedNodeCode base (base ^ FrameCodec.scalarDigitCount)
        (FrameCodec.encodeFrame base frame) =
      FrameCodec.encodeNode base frame.node := by
  rw [decodedNodeCode]
  rw [poppedCode_encodeFrame_one_internal frame hbase hfits]
  rw [poppedCode_encodeFrame_five_internal frame hbase hfits]
  rw [FrameCodec.encodeList_append]
  rw [FrameCodec.Internal.nodeDigits_length_internal]
  simp only [FrameCodec.encodeNode, FrameCodec.nodeDigitCount,
    FrameCodec.scalarDigitCount]
  ring_nf
  omega

theorem decodedScalar_encodeFrame_internal
    {tm : TM workTapeCount}
    {instanceData : NeighborhoodProgram.ResidueInstance tm}
    {base : ℕ}
    (frame : NeighborhoodScheduler.Frame tm instanceData)
    (hbase : 0 < base)
    (hfits : FrameCodec.FrameFits base frame)
    (hscalar :
      frame.scalar < base ^ FrameCodec.scalarDigitCount) :
    decodedScalar base (base ^ FrameCodec.scalarDigitCount)
        (FrameCodec.encodeFrame base frame) =
      frame.scalar := by
  rw [decodedScalar]
  rw [poppedCode_encodeFrame_five_internal frame hbase hfits]
  rw [poppedCode_encodeFrame_seven_internal frame hbase hfits]
  rw [FrameCodec.encodeList_append]
  rw [FrameCodec.Internal.scalarDigits_length_internal]
  rw [FrameCodec.encodeList_scalarDigits hbase hscalar]
  omega

theorem decodedOut_encodeFrame_internal
    {tm : TM workTapeCount}
    {instanceData : NeighborhoodProgram.ResidueInstance tm}
    {base : ℕ}
    (frame : NeighborhoodScheduler.Frame tm instanceData)
    (hfits : FrameCodec.FrameFits base frame) :
    decodedOut base (FrameCodec.encodeFrame base frame) =
      frame.out.val := by
  rw [decodedOut, digit_poppedCode_zero_internal]
  exact FrameCodec.encodeFrame_out frame hfits

theorem decodedPhase_encodeFrame_internal
    {tm : TM workTapeCount}
    {instanceData : NeighborhoodProgram.ResidueInstance tm}
    {base : ℕ}
    (frame : NeighborhoodScheduler.Frame tm instanceData)
    (hbase : 0 < base)
    (hfits : FrameCodec.FrameFits base frame) :
    decodedPhase base (FrameCodec.encodeFrame base frame) =
      FrameCodec.encodePhase base frame.phase := by
  rw [decodedPhase]
  rw [poppedCode_encodeFrame_eight_internal frame hbase hfits]
  rw [FrameCodec.encodeList_append]
  rw [FrameCodec.encodeList_replicate_zero]
  simp [FrameCodec.encodePhase]

theorem activeCode_encodeFrame_internal
    {tm : TM workTapeCount}
    {instanceData : NeighborhoodProgram.ResidueInstance tm}
    {base : ℕ}
    (frame : NeighborhoodScheduler.Frame tm instanceData)
    (hbase : 0 < base)
    (hscalar :
      frame.scalar < base ^ FrameCodec.scalarDigitCount) :
    activeCode base (base ^ FrameCodec.scalarDigitCount)
        frame.fuel (FrameCodec.encodeNode base frame.node)
        frame.scalar frame.out.val
        (FrameCodec.encodePhase base frame.phase) =
      FrameCodec.encodeFrame base frame := by
  rw [FrameCodec.encodeFrame, FrameCodec.frameDigits]
  simp only [FrameCodec.encodeList, PackedDigits.push]
  rw [FrameCodec.encodeList_append]
  rw [FrameCodec.encodeList_append]
  simp only [FrameCodec.encodeList, PackedDigits.push]
  rw [FrameCodec.encodeList_append]
  rw [FrameCodec.encodeList_replicate_zero]
  rw [FrameCodec.encodeList_scalarDigits hbase hscalar]
  rw [FrameCodec.Internal.nodeDigits_length_internal]
  rw [FrameCodec.Internal.scalarDigits_length_internal]
  rw [FrameCodec.Internal.phaseDigits_length_internal]
  simp only [FrameCodec.encodeNode, FrameCodec.encodePhase,
    FrameCodec.nodeDigitCount, FrameCodec.scalarDigitCount,
    FrameCodec.phaseDigitCount, activeCode]
  ring

theorem loadActive_encodeFrame_runs_internal
    {tm : TM workTapeCount}
    {instanceData : NeighborhoodProgram.ResidueInstance tm}
    (regs : NeighborhoodTrial.Registers controller)
    (store : Store) (base : ℕ)
    (frame : NeighborhoodScheduler.Frame tm instanceData)
    (hbase : 0 < base)
    (hfits : FrameCodec.FrameFits base frame)
    (hscalar :
      frame.scalar < base ^ FrameCodec.scalarDigitCount)
    (hword :
      store (Layout.frameCodecRegisters regs).word =
        FrameCodec.encodeFrame base frame)
    (hbaseValue :
      store (Layout.frameCodecRegisters regs).base = base)
    (hbank :
      store (Layout.bankRadix regs) =
        base ^ FrameCodec.scalarDigitCount) :
    ∃ final,
      Runs (loadActive regs) store final ∧
      FrameLoadPost regs base frame final := by
  obtain ⟨final, hrun, hpost⟩ :=
    loadActive_runs_internal regs store base
      (base ^ FrameCodec.scalarDigitCount)
      (FrameCodec.encodeFrame base frame)
      hbase hword hbaseValue hbank
  refine ⟨final, hrun, ?_⟩
  constructor
  · exact hpost.fuel_eq.trans
      (decodedFuel_encodeFrame_internal frame hfits)
  · exact hpost.nodeCode_eq.trans
      (decodedNodeCode_encodeFrame_internal frame hbase hfits)
  · exact hpost.scalar_eq.trans
      (decodedScalar_encodeFrame_internal
        frame hbase hfits hscalar)
  · exact hpost.out_eq.trans
      (decodedOut_encodeFrame_internal frame hfits)
  · exact hpost.phaseCode_eq.trans
      (decodedPhase_encodeFrame_internal frame hbase hfits)
  · exact hpost.active_eq

private def loadActiveFootprint
    (regs : NeighborhoodTrial.Registers controller) : Finset ℕ :=
  {regs.index 1, regs.index 4, regs.index 5, regs.index 17,
    regs.index 22, regs.index 23, regs.index 25, regs.index 26,
    regs.index 27, regs.index 28, regs.index 29, regs.index 30}

private theorem loadActive_writesSmall
    (regs : NeighborhoodTrial.Registers controller) :
    RAM.Structured.Footprint.CmdWritesWithin
      (loadActiveFootprint regs) (loadActive regs) := by
  simp [loadActiveFootprint, loadActive, initializeCodec,
    readFuel, captureNode, recoverNode, captureScalar, recoverScalar,
    readOut, finishLoad, popNodeCode, popScalar, popMany, copy,
    Cmd.basics, Cmd.seqList,
    RAM.Structured.Footprint.CmdWritesWithin,
    RAM.Structured.Footprint.BasicWritesWithin,
    NeighborhoodProgram.pop, NeighborhoodProgram.peek,
    NeighborhoodProgram.popBody, NeighborhoodProgram.popTestOp,
    RuntimeArithmetic.reduce, RuntimeArithmetic.reduceBody,
    RuntimeArithmetic.reduceTestOp,
    NeighborhoodProgram.StackRegisters.reduceRegisters,
    Layout.frameCodecRegisters, Layout.frameCodecMap,
    regs.injective.eq_iff]

private theorem loadActive_preserves_stack
    (regs : NeighborhoodTrial.Registers controller)
    {initial final : Store}
    (hrun : Runs (loadActive regs) initial final) :
    final (Layout.frameStackRegisters regs).word =
        initial (Layout.frameStackRegisters regs).word ∧
      final (Layout.frameStackRegisters regs).base =
        initial (Layout.frameStackRegisters regs).base := by
  constructor
  · exact RAM.Structured.Footprint.runs_eq_outside
      (loadActive_writesSmall regs) hrun (by
        simp [loadActiveFootprint, Layout.frameStackRegisters,
          Layout.frameStackMap, regs.injective.eq_iff])
  · exact RAM.Structured.Footprint.runs_eq_outside
      (loadActive_writesSmall regs) hrun (by
        simp [loadActiveFootprint, Layout.frameStackRegisters,
          Layout.frameStackMap, regs.injective.eq_iff])

/-- Encoding and pushing the active frame extends the represented suspended
continuation stack by exactly that frame. -/
theorem pushParent_frame_runs_internal
    {tm : TM workTapeCount}
    {instanceData : NeighborhoodProgram.ResidueInstance tm}
    (regs : NeighborhoodTrial.Registers controller)
    (store : Store) (digitBase frameBase : ℕ)
    (frame : NeighborhoodScheduler.Frame tm instanceData)
    (rest : List (NeighborhoodScheduler.Frame tm instanceData))
    (hdigitBase : 0 < digitBase)
    (hscalar :
      frame.scalar < digitBase ^ FrameCodec.scalarDigitCount)
    (hchunkRadix :
      store (Layout.chunkRadix regs) = digitBase)
    (hbankRadix :
      store (Layout.bankRadix regs) =
        digitBase ^ FrameCodec.scalarDigitCount)
    (hfuel : store (Layout.fuel regs) = frame.fuel)
    (hnode :
      store (Layout.nodeCode regs) =
        FrameCodec.encodeNode digitBase frame.node)
    (hscalarValue : store (Layout.scalar regs) = frame.scalar)
    (hout : store (Layout.out regs) = frame.out.val)
    (hphase :
      store (Layout.phaseCode regs) =
        FrameCodec.encodePhase digitBase frame.phase)
    (hframeBase :
      store (Layout.frameStackRegisters regs).base = frameBase)
    (hstack :
      RepresentsStack regs digitBase frameBase rest store) :
    ∃ final,
      Runs (pushParent regs) store final ∧
      RepresentsStack regs digitBase frameBase (frame :: rest) final := by
  let encoded := Basic.execList (encodeActiveOps regs) store
  have hencode : Runs (encodeActive regs) store encoded := by
    simpa [encoded] using encodeActive_runs_internal regs store
  have hframeCode :
      encoded (Layout.frameStackRegisters regs).value =
        FrameCodec.encodeFrame digitBase frame := by
    change encoded (Layout.frameCode regs) =
      FrameCodec.encodeFrame digitBase frame
    rw [show encoded (Layout.frameCode regs) =
      activeCode
        (store (Layout.chunkRadix regs))
        (store (Layout.bankRadix regs))
        (store (Layout.fuel regs))
        (store (Layout.nodeCode regs))
        (store (Layout.scalar regs))
        (store (Layout.out regs))
        (store (Layout.phaseCode regs)) from
      encodeActive_frameCode_internal regs store]
    rw [hchunkRadix, hbankRadix, hfuel, hnode, hscalarValue,
      hout, hphase]
    exact activeCode_encodeFrame_internal frame hdigitBase hscalar
  have hword :
      encoded (Layout.frameStackRegisters regs).word =
        encodeStack digitBase frameBase rest := by
    unfold RepresentsStack at hstack
    simpa [encoded, encodeActiveOps, Basic.execList, Basic.exec,
      Layout.frameStackRegisters, Layout.frameStackMap,
      Layout.frameCodecRegisters, Layout.frameCodecMap,
      regs.injective.eq_iff] using hstack
  have hbase :
      encoded (Layout.frameStackRegisters regs).base = frameBase := by
    simpa [encoded, encodeActiveOps, Basic.execList, Basic.exec,
      Layout.frameStackRegisters, Layout.frameStackMap,
      Layout.frameCodecRegisters, Layout.frameCodecMap,
      regs.injective.eq_iff] using hframeBase
  let stack := Layout.frameStackRegisters regs
  let withOne := Basic.exec (.imm stack.one 1) encoded
  let shifted :=
    Basic.exec (.add stack.value stack.value stack.one) withOne
  have hframeCode' :
      encoded stack.value =
        FrameCodec.encodeFrame digitBase frame := by
    simpa [stack] using hframeCode
  have hword' :
      encoded stack.word =
        encodeStack digitBase frameBase rest := by
    simpa [stack] using hword
  have hbase' : encoded stack.base = frameBase := by
    simpa [stack] using hbase
  have hshiftedFrameCode :
      shifted stack.value =
        FrameCodec.encodeFrame digitBase frame + 1 := by
    simp [shifted, withOne, Basic.exec, stack.injective.eq_iff,
      hframeCode']
  have hshiftedWord :
      shifted stack.word =
        encodeStack digitBase frameBase rest := by
    simp [shifted, withOne, Basic.exec, stack.injective.eq_iff,
      hword']
  have hshiftedBase : shifted stack.base = frameBase := by
    simp [shifted, withOne, Basic.exec, stack.injective.eq_iff,
      hbase']
  obtain ⟨final, hpush, hfinalWord, _hquotient, _hbase, _hvalue⟩ :=
    NeighborhoodProgram.push_runs
      stack shifted frameBase
      (encodeStack digitBase frameBase rest)
      (FrameCodec.encodeFrame digitBase frame + 1)
      hshiftedWord hshiftedBase hshiftedFrameCode
  refine ⟨final, ?_, ?_⟩
  · simpa [pushParent, stack, Cmd.seqList] using
      Runs.seq hencode
        (Runs.seq
          (Runs.basic (.imm stack.one 1) encoded)
          (Runs.seq
            (Runs.basic
              (.add stack.value stack.value stack.one) withOne)
            hpush))
  · unfold RepresentsStack
    simpa [encodeStack] using hfinalWord

/-- Popping an empty continuation stack clears the active flag without
changing its empty representation. -/
theorem popParent_empty_runs_internal
    {tm : TM workTapeCount}
    {instanceData : NeighborhoodProgram.ResidueInstance tm}
    (regs : NeighborhoodTrial.Registers controller)
    (store : Store) (digitBase frameBase : ℕ)
    (hstack :
      RepresentsStack regs digitBase frameBase
        ([] : List (NeighborhoodScheduler.Frame tm instanceData))
        store) :
    ∃ final,
      Runs (popParent regs) store final ∧
      final (Layout.active regs) = 0 ∧
      RepresentsStack regs digitBase frameBase
        ([] : List (NeighborhoodScheduler.Frame tm instanceData))
        final := by
  let stack := Layout.frameStackRegisters regs
  have hzero : store stack.word = 0 := by
    simpa [stack, RepresentsStack, encodeStack] using hstack
  let final := Basic.exec (.imm (Layout.active regs) 0) store
  refine ⟨final, ?_, ?_, ?_⟩
  · simpa [popParent, stack] using
      Runs.ifZero hzero
        (Runs.basic (.imm (Layout.active regs) 0) store)
  · simp [final, Basic.exec]
  · unfold RepresentsStack at hstack ⊢
    simpa [final, Basic.exec, encodeStack,
      Layout.frameStackRegisters, Layout.frameStackMap,
      regs.injective.eq_iff] using hstack

/-- Popping a represented nonempty continuation stack restores its top
frame exactly and leaves the representation of the remaining frames. -/
theorem popParent_frame_runs_internal
    {tm : TM workTapeCount}
    {instanceData : NeighborhoodProgram.ResidueInstance tm}
    (regs : NeighborhoodTrial.Registers controller)
    (store : Store) (digitBase frameBase : ℕ)
    (frame : NeighborhoodScheduler.Frame tm instanceData)
    (rest : List (NeighborhoodScheduler.Frame tm instanceData))
    (hdigitBase : 0 < digitBase)
    (hfits : FrameCodec.FrameFits digitBase frame)
    (hscalar :
      frame.scalar < digitBase ^ FrameCodec.scalarDigitCount)
    (hshiftedFits :
      FrameCodec.encodeFrame digitBase frame + 1 < frameBase)
    (hchunkRadix : store (Layout.chunkRadix regs) = digitBase)
    (hbankRadix :
      store (Layout.bankRadix regs) =
        digitBase ^ FrameCodec.scalarDigitCount)
    (hframeBase :
      store (Layout.frameStackRegisters regs).base = frameBase)
    (hstack :
      RepresentsStack regs digitBase frameBase
        (frame :: rest) store) :
    ∃ final,
      Runs (popParent regs) store final ∧
      FrameLoadPost regs digitBase frame final ∧
      RepresentsStack regs digitBase frameBase rest final ∧
      final (Layout.frameStackRegisters regs).base = frameBase := by
  let stack := Layout.frameStackRegisters regs
  have hframeBasePos : 0 < frameBase := by omega
  have hword :
      store stack.word =
        PackedDigits.push frameBase
          (FrameCodec.encodeFrame digitBase frame + 1)
          (encodeStack digitBase frameBase rest) := by
    simpa [stack, RepresentsStack, encodeStack] using hstack
  have hnonzero : store stack.word ≠ 0 := by
    rw [hword]
    simp [PackedDigits.push]
  let withOne := Basic.exec (.imm stack.one 1) store
  let withPred :=
    Basic.exec (.sub stack.basePred stack.base stack.one) withOne
  have hbase' : store stack.base = frameBase := by
    simpa [stack] using hframeBase
  have hwithPredWord :
      withPred stack.word =
        PackedDigits.push frameBase
          (FrameCodec.encodeFrame digitBase frame + 1)
          (encodeStack digitBase frameBase rest) := by
    simp [withPred, withOne, Basic.exec, stack.injective.eq_iff,
      hword]
  have hwithPredBase : withPred stack.base = frameBase := by
    simp [withPred, withOne, Basic.exec, stack.injective.eq_iff,
      hbase']
  have hwithPredBasePred :
      withPred stack.basePred = frameBase - 1 := by
    simp [withPred, withOne, Basic.exec, stack.injective.eq_iff,
      hbase']
  have hwithPredOne : withPred stack.one = 1 := by
    simp [withPred, withOne, Basic.exec, stack.injective.eq_iff]
  obtain ⟨afterPeek, hpeek, hpeekWord, hpeekValue,
      _hpeekTest, hpeekBase, hpeekBasePred⟩ :=
    NeighborhoodProgram.peek_runs stack withPred frameBase
      (PackedDigits.push frameBase
        (FrameCodec.encodeFrame digitBase frame + 1)
        (encodeStack digitBase frameBase rest))
      hframeBasePos hwithPredWord hwithPredBase hwithPredBasePred
  have hpeekOne : afterPeek stack.one = 1 := by
    rw [RAM.Structured.Footprint.runs_eq_outside
      (peek_sourceWritesWithin_withoutOne stack) hpeek (by simp)]
    exact hwithPredOne
  have hpeekValueCode :
      afterPeek stack.value =
        FrameCodec.encodeFrame digitBase frame + 1 := by
    rw [hpeekValue]
    exact PackedDigits.digit_push_zero hshiftedFits
  let unshifted :=
    Basic.exec (.sub stack.value stack.value stack.one) afterPeek
  have hunshiftedValue :
      unshifted stack.value =
        FrameCodec.encodeFrame digitBase frame := by
    simp [unshifted, Basic.exec, hpeekValueCode, hpeekOne]
  have hunshiftedWord :
      unshifted stack.word =
        PackedDigits.push frameBase
          (FrameCodec.encodeFrame digitBase frame + 1)
          (encodeStack digitBase frameBase rest) := by
    simp [unshifted, Basic.exec, stack.injective.eq_iff,
      hpeekWord]
  have hunshiftedBase : unshifted stack.base = frameBase := by
    simp [unshifted, Basic.exec, stack.injective.eq_iff,
      hpeekBase]
  have hunshiftedBasePred :
      unshifted stack.basePred = frameBase - 1 := by
    simp [unshifted, Basic.exec, stack.injective.eq_iff,
      hpeekBasePred]
  have hunshiftedOne : unshifted stack.one = 1 := by
    simp [unshifted, Basic.exec, stack.injective.eq_iff,
      hpeekOne]
  obtain ⟨afterPop, hpop, hpopWord, _hpopQuotient,
      _hpopTest, hpopBase, _hpopBasePred, _hpopOne⟩ :=
    NeighborhoodProgram.pop_runs stack unshifted frameBase
      (PackedDigits.push frameBase
        (FrameCodec.encodeFrame digitBase frame + 1)
        (encodeStack digitBase frameBase rest))
      hframeBasePos hunshiftedWord hunshiftedBase
      hunshiftedBasePred hunshiftedOne
  have hpopValue :
      afterPop stack.value =
        FrameCodec.encodeFrame digitBase frame := by
    rw [RAM.Structured.Footprint.runs_eq_outside
      (pop_sourceWritesWithin_withoutValue stack) hpop (by simp)]
    exact hunshiftedValue
  have hpopWordRest :
      afterPop stack.word =
        encodeStack digitBase frameBase rest := by
    rw [hpopWord,
      PackedDigits.pop_push hframeBasePos hshiftedFits]
  have hprefixRun :
      Runs
        (Cmd.seqList
          [.basic (.imm stack.one 1),
            .basic (.sub stack.basePred stack.base stack.one),
            NeighborhoodProgram.peek stack,
            .basic (.sub stack.value stack.value stack.one),
            NeighborhoodProgram.pop stack])
        store afterPop := by
    simpa [Cmd.seqList] using
      Runs.seq (Runs.basic (.imm stack.one 1) store)
        (Runs.seq
          (Runs.basic
            (.sub stack.basePred stack.base stack.one) withOne)
          (Runs.seq hpeek
            (Runs.seq
              (Runs.basic
                (.sub stack.value stack.value stack.one) afterPeek)
              hpop)))
  have hprefixWrites :
      RAM.Structured.Footprint.CmdWritesWithin stack.footprint
        (Cmd.seqList
          [.basic (.imm stack.one 1),
            .basic (.sub stack.basePred stack.base stack.one),
            NeighborhoodProgram.peek stack,
            .basic (.sub stack.value stack.value stack.one),
            NeighborhoodProgram.pop stack]) := by
    simp [Cmd.seqList,
      RAM.Structured.Footprint.CmdWritesWithin,
      RAM.Structured.Footprint.BasicWritesWithin,
      NeighborhoodProgram.StackRegisters.index_mem_footprint,
      peek_sourceWritesWithin, pop_sourceWritesWithin]
  have hchunkOutside :
      Layout.chunkRadix regs ∉ stack.footprint := by
    simp only [stack,
      NeighborhoodProgram.StackRegisters.footprint,
      Layout.frameStackRegisters, Finset.mem_image,
      Finset.mem_univ, true_and, not_exists]
    intro index
    rw [regs.injective.eq_iff]
    fin_cases index <;> decide
  have hbankOutside :
      Layout.bankRadix regs ∉ stack.footprint := by
    simp only [stack,
      NeighborhoodProgram.StackRegisters.footprint,
      Layout.frameStackRegisters, Finset.mem_image,
      Finset.mem_univ, true_and, not_exists]
    intro index
    rw [regs.injective.eq_iff]
    fin_cases index <;> decide
  have hpopChunk :
      afterPop (Layout.chunkRadix regs) = digitBase := by
    rw [RAM.Structured.Footprint.runs_eq_outside
      hprefixWrites hprefixRun hchunkOutside]
    exact hchunkRadix
  have hpopBank :
      afterPop (Layout.bankRadix regs) =
        digitBase ^ FrameCodec.scalarDigitCount := by
    rw [RAM.Structured.Footprint.runs_eq_outside
      hprefixWrites hprefixRun hbankOutside]
    exact hbankRadix
  have hcodecWord :
      afterPop (Layout.frameCodecRegisters regs).word =
        FrameCodec.encodeFrame digitBase frame := by
    simpa [stack, Layout.frameStackRegisters,
      Layout.frameStackMap, Layout.frameCodecRegisters,
      Layout.frameCodecMap] using hpopValue
  have hcodecBase :
      afterPop (Layout.frameCodecRegisters regs).base =
        digitBase := by
    simpa [Layout.frameCodecRegisters,
      Layout.frameCodecMap] using hpopChunk
  obtain ⟨final, hload, hpost⟩ :=
    loadActive_encodeFrame_runs_internal regs afterPop
      digitBase frame hdigitBase hfits hscalar
      hcodecWord hcodecBase hpopBank
  have hpreserved := loadActive_preserves_stack regs hload
  refine ⟨final, ?_, hpost, ?_, ?_⟩
  · simpa [popParent, stack, Cmd.seqList] using
      Runs.ifNonzero hnonzero
        (Runs.seq (Runs.basic (.imm stack.one 1) store)
          (Runs.seq
            (Runs.basic
              (.sub stack.basePred stack.base stack.one) withOne)
            (Runs.seq hpeek
              (Runs.seq
                (Runs.basic
                  (.sub stack.value stack.value stack.one)
                  afterPeek)
                (Runs.seq hpop hload)))))
  · unfold RepresentsStack
    rw [hpreserved.1, hpopWordRest]
  · rw [hpreserved.2, hpopBase]

theorem popParent_writesWithin_writeFootprint_internal
    (regs : NeighborhoodTrial.Registers controller) :
    RAM.Structured.Footprint.CmdWritesWithin
      (writeFootprint regs) (popParent regs) := by
  have hFrameWord :
      (Layout.frameStackRegisters regs).word = regs.index 32 := rfl
  have hFrameBase :
      (Layout.frameStackRegisters regs).base = regs.index 13 := rfl
  have hFrameBasePred :
      (Layout.frameStackRegisters regs).basePred = regs.index 0 := rfl
  have hFrameQuotient :
      (Layout.frameStackRegisters regs).quotient = regs.index 4 := rfl
  have hFrameTest :
      (Layout.frameStackRegisters regs).test = regs.index 5 := rfl
  have hFrameOne :
      (Layout.frameStackRegisters regs).one = regs.index 17 := rfl
  have hFrameValue :
      (Layout.frameStackRegisters regs).value = regs.index 29 := rfl
  have hCodecWord :
      (Layout.frameCodecRegisters regs).word = regs.index 29 := rfl
  have hCodecBase :
      (Layout.frameCodecRegisters regs).base = regs.index 8 := rfl
  have hCodecBasePred :
      (Layout.frameCodecRegisters regs).basePred = regs.index 1 := rfl
  have hCodecQuotient :
      (Layout.frameCodecRegisters regs).quotient = regs.index 4 := rfl
  have hCodecTest :
      (Layout.frameCodecRegisters regs).test = regs.index 5 := rfl
  have hCodecOne :
      (Layout.frameCodecRegisters regs).one = regs.index 17 := rfl
  have hCodecValue :
      (Layout.frameCodecRegisters regs).value = regs.index 30 := rfl
  simp [writeFootprint, popParent, loadActive,
    initializeCodec, readFuel, captureNode, recoverNode,
    captureScalar, recoverScalar, readOut, finishLoad,
    popNodeCode, popScalar, popMany, copy, Cmd.basics, Cmd.seqList,
    RAM.Structured.Footprint.CmdWritesWithin,
    RAM.Structured.Footprint.BasicWritesWithin,
    NeighborhoodProgram.pop, NeighborhoodProgram.peek,
    NeighborhoodProgram.popBody, NeighborhoodProgram.popTestOp,
    RuntimeArithmetic.reduce, RuntimeArithmetic.reduceBody,
    RuntimeArithmetic.reduceTestOp,
    NeighborhoodProgram.StackRegisters.reduceRegisters,
    hFrameWord, hFrameBase, hFrameBasePred, hFrameQuotient,
    hFrameTest, hFrameOne, hFrameValue, hCodecWord, hCodecBase,
    hCodecBasePred, hCodecQuotient, hCodecTest, hCodecOne,
    hCodecValue]

theorem pushParent_writesWithin_writeFootprint_internal
    (regs : NeighborhoodTrial.Registers controller) :
    RAM.Structured.Footprint.CmdWritesWithin
      (writeFootprint regs) (pushParent regs) := by
  have hFrameWord :
      (Layout.frameStackRegisters regs).word = regs.index 32 := rfl
  have hFrameQuotient :
      (Layout.frameStackRegisters regs).quotient = regs.index 4 := rfl
  have hFrameOne :
      (Layout.frameStackRegisters regs).one = regs.index 17 := rfl
  have hFrameValue :
      (Layout.frameStackRegisters regs).value = regs.index 29 := rfl
  have hCodecQuotient :
      (Layout.frameCodecRegisters regs).quotient = regs.index 4 := rfl
  simp [writeFootprint, pushParent, encodeActive, encodeActiveOps,
    Cmd.basics, Cmd.seqList,
    RAM.Structured.Footprint.CmdWritesWithin,
    RAM.Structured.Footprint.BasicWritesWithin,
    NeighborhoodProgram.push,
    hFrameWord, hFrameQuotient,
    hFrameOne, hFrameValue, hCodecQuotient]

theorem pushParent_writesWithin_pushWriteFootprint_internal
    (regs : NeighborhoodTrial.Registers controller) :
    RAM.Structured.Footprint.CmdWritesWithin
      (pushWriteFootprint regs) (pushParent regs) := by
  have hFrameWord :
      (Layout.frameStackRegisters regs).word = regs.index 32 := rfl
  have hFrameQuotient :
      (Layout.frameStackRegisters regs).quotient = regs.index 4 := rfl
  have hFrameOne :
      (Layout.frameStackRegisters regs).one = regs.index 17 := rfl
  have hFrameValue :
      (Layout.frameStackRegisters regs).value = regs.index 29 := rfl
  have hCodecQuotient :
      (Layout.frameCodecRegisters regs).quotient = regs.index 4 := rfl
  simp [pushWriteFootprint, pushParent, encodeActive, encodeActiveOps,
    Cmd.basics, Cmd.seqList,
    RAM.Structured.Footprint.CmdWritesWithin,
    RAM.Structured.Footprint.BasicWritesWithin,
    NeighborhoodProgram.push,
    hFrameWord, hFrameQuotient,
    hFrameOne, hFrameValue, hCodecQuotient]

theorem loadActive_writesWithin_internal
    (regs : NeighborhoodTrial.Registers controller) :
    RAM.Structured.Footprint.CmdWritesWithin
      regs.layout.footprint (loadActive regs) := by
  simp [loadActive, initializeCodec, readFuel, captureNode,
    recoverNode, captureScalar, recoverScalar, readOut, finishLoad,
    popNodeCode, popScalar, copy, Cmd.basics, Cmd.seqList,
    RAM.Structured.Footprint.CmdWritesWithin,
    RAM.Structured.Footprint.BasicWritesWithin,
    codec_pop_writesWithin, codec_peek_writesWithin,
    popMany_writesWithin,
    codec_index_mem, Layout.index_mem_layout_footprint]

theorem pushParent_writesWithin_internal
    (regs : NeighborhoodTrial.Registers controller) :
    RAM.Structured.Footprint.CmdWritesWithin
      regs.layout.footprint (pushParent regs) := by
  simp [pushParent, Cmd.seqList,
    RAM.Structured.Footprint.CmdWritesWithin,
    RAM.Structured.Footprint.BasicWritesWithin,
    encodeActive_writesWithin_internal, frame_push_writesWithin,
    frame_index_mem]

theorem popParent_writesWithin_internal
    (regs : NeighborhoodTrial.Registers controller) :
    RAM.Structured.Footprint.CmdWritesWithin
      regs.layout.footprint (popParent regs) := by
  simp only [popParent, RAM.Structured.Footprint.CmdWritesWithin]
  constructor
  · simp [RAM.Structured.Footprint.BasicWritesWithin,
      Layout.index_mem_layout_footprint]
  · simp [Cmd.seqList,
      RAM.Structured.Footprint.CmdWritesWithin,
      RAM.Structured.Footprint.BasicWritesWithin,
      frame_peek_writesWithin, frame_pop_writesWithin,
      loadActive_writesWithin_internal, frame_index_mem]

end Internal
end FrameTransfer
end NeighborhoodMicrocode
end Runtime
end TimeSpaceSimulation
end Complexity
