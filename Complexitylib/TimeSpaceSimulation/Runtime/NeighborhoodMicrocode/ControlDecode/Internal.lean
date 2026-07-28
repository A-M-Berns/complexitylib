/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/
import
  Complexitylib.Models.RandomAccessMachine.Structured.Footprint
import
  Complexitylib.Models.RandomAccessMachine.Structured.Run
import
  Complexitylib.TimeSpaceSimulation.Runtime.NeighborhoodMicrocode.ControlDecode.Defs
import
  Complexitylib.TimeSpaceSimulation.Runtime.NeighborhoodMicrocode.FrameCodec
import
  Complexitylib.TimeSpaceSimulation.Runtime.NeighborhoodMicrocode.Layout

/-!
# Concrete control-field decoding -- proofs
-/

namespace Complexity
namespace TimeSpaceSimulation
namespace Runtime
namespace NeighborhoodMicrocode
namespace ControlDecode
namespace Internal

open RAM Structured

variable {controller : SearchProgram.Registers}

private theorem division_index_ne
    (regs : DivisionRegisters) {first second : Fin 5}
    (hne : first ≠ second) :
    regs.index first ≠ regs.index second :=
  fun heq => hne (regs.injective heq)

private theorem divRemLoop_runs
    (regs : DivisionRegisters) (store : Store)
    (base remainder remaining completed : ℕ)
    (hremainder : remainder < base)
    (hvalue :
      store regs.value = remaining * base + remainder)
    (hquotient : store regs.quotient = completed)
    (htest :
      store regs.test =
        remaining * base + remainder + 1 - base)
    (hone : store regs.one = 1)
    (hdivisor : store regs.divisor = base) :
    ∃ final,
      Runs (.whileNonzero regs.test (divRemBody regs)) store final ∧
      final regs.value = remainder ∧
      final regs.quotient = completed + remaining ∧
      final regs.test = 0 ∧
      final regs.one = 1 ∧
      final regs.divisor = base := by
  induction remaining generalizing store completed with
  | zero =>
      have htestZero : store regs.test = 0 := by
        rw [htest]
        omega
      exact ⟨store, Runs.whileZero htestZero, by simpa using hvalue,
        by simpa using hquotient, htestZero, hone, hdivisor⟩
  | succ remaining ih =>
      have htestNonzero : store regs.test ≠ 0 := by
        rw [htest]
        simp only [Nat.succ_mul]
        omega
      let afterSub :=
        (Basic.sub regs.value regs.value regs.divisor).exec store
      let afterIncrement :=
        (Basic.add regs.quotient regs.quotient regs.one).exec afterSub
      let afterAdd :=
        (Basic.add regs.test regs.value regs.one).exec afterIncrement
      let afterTest :=
        (Basic.sub regs.test regs.test regs.divisor).exec afterAdd
      have hbody : Runs (divRemBody regs) store afterTest := by
        simpa [divRemBody, divRemTest, Cmd.seqList] using
          Runs.seq (Runs.basic (Basic.sub regs.value regs.value
            regs.divisor) store)
            (Runs.seq
              (Runs.basic (Basic.add regs.quotient regs.quotient
                regs.one) afterSub)
              (Runs.seq
                (Runs.basic (Basic.add regs.test regs.value
                  regs.one) afterIncrement)
                (Runs.basic (Basic.sub regs.test regs.test
                  regs.divisor) afterAdd)))
      have hafterSubValue :
          afterSub regs.value = remaining * base + remainder := by
        simp only [afterSub, Basic.exec, Function.update_self]
        rw [hvalue, hdivisor]
        simp only [Nat.succ_mul]
        omega
      have hnextValue :
          afterTest regs.value = remaining * base + remainder := by
        rw [← hafterSubValue]
        simp [afterTest, afterAdd, afterIncrement, Basic.exec,
          regs.injective.eq_iff]
      have hnextQuotient :
          afterTest regs.quotient = completed + 1 := by
        simp [afterTest, afterAdd, afterIncrement, afterSub, Basic.exec,
          regs.injective.eq_iff, hquotient, hone]
      have hnextOne : afterTest regs.one = 1 := by
        simp [afterTest, afterAdd, afterIncrement, afterSub, Basic.exec,
          regs.injective.eq_iff, hone]
      have hnextDivisor : afterTest regs.divisor = base := by
        simp [afterTest, afterAdd, afterIncrement, afterSub, Basic.exec,
          regs.injective.eq_iff, hdivisor]
      have hnextTest :
          afterTest regs.test =
            remaining * base + remainder + 1 - base := by
        simp only [afterTest, Basic.exec, Function.update_self]
        have hafterAddTest :
            afterAdd regs.test =
              remaining * base + remainder + 1 := by
          simp only [afterAdd, Basic.exec, Function.update_self]
          have hafterIncrementValue :
              afterIncrement regs.value =
                remaining * base + remainder := by
            rw [← hafterSubValue]
            simp [afterIncrement, Basic.exec,
              regs.injective.eq_iff]
          have hafterIncrementOne :
              afterIncrement regs.one = 1 := by
            simp [afterIncrement, afterSub, Basic.exec,
              regs.injective.eq_iff, hone]
          rw [hafterIncrementValue, hafterIncrementOne]
        have hafterAddDivisor :
            afterAdd regs.divisor = base := by
          simp [afterAdd, afterIncrement, afterSub, Basic.exec,
            regs.injective.eq_iff, hdivisor]
        rw [hafterAddTest, hafterAddDivisor]
      obtain ⟨final, hloop, hfinalValue, hfinalQuotient,
          hfinalTest, hfinalOne, hfinalDivisor⟩ :=
        ih afterTest (completed + 1) hnextValue hnextQuotient
          hnextTest hnextOne hnextDivisor
      refine ⟨final, Runs.whileNonzero htestNonzero hbody hloop,
        hfinalValue, ?_, hfinalTest, hfinalOne, hfinalDivisor⟩
      rw [hfinalQuotient]
      omega

theorem divRem_writesWithin_internal
    (regs : DivisionRegisters) :
    RAM.Structured.Footprint.CmdWritesWithin
      regs.writeFootprint (divRem regs) := by
  simp [divRem, divRemBody, divRemTest, Cmd.seqList,
    RAM.Structured.Footprint.CmdWritesWithin,
    RAM.Structured.Footprint.BasicWritesWithin,
    DivisionRegisters.writeFootprint]

theorem divRem_runs_internal
    (regs : DivisionRegisters) (store : Store)
    (base input : ℕ)
    (hbase : 0 < base)
    (hvalue : store regs.value = input)
    (hdivisor : store regs.divisor = base) :
    ∃ final,
      Runs (divRem regs) store final ∧
      DivRemPost regs base input store final := by
  let oneStore := (Basic.imm regs.one 1).exec store
  let quotientStore := (Basic.imm regs.quotient 0).exec oneStore
  let addedStore :=
    (Basic.add regs.test regs.value regs.one).exec quotientStore
  let testedStore :=
    (Basic.sub regs.test regs.test regs.divisor).exec addedStore
  have htestedValue : testedStore regs.value = input := by
    simp [testedStore, addedStore, quotientStore, oneStore, Basic.exec,
      regs.injective.eq_iff, hvalue]
  have htestedQuotient : testedStore regs.quotient = 0 := by
    simp [testedStore, addedStore, quotientStore, oneStore, Basic.exec,
      regs.injective.eq_iff]
  have htestedOne : testedStore regs.one = 1 := by
    simp [testedStore, addedStore, quotientStore, oneStore, Basic.exec,
      regs.injective.eq_iff]
  have htestedDivisor : testedStore regs.divisor = base := by
    simp [testedStore, addedStore, quotientStore, oneStore, Basic.exec,
      regs.injective.eq_iff, hdivisor]
  have hdecompose :
      input / base * base + input % base = input := by
    simpa [Nat.mul_comm, Nat.add_comm] using
      (Nat.mod_add_div input base)
  have htestedDecompose :
      testedStore regs.value =
        input / base * base + input % base := by
    rw [htestedValue, hdecompose]
  have htestedTest :
      testedStore regs.test =
        input / base * base + input % base + 1 - base := by
    simp only [testedStore, Basic.exec, Function.update_self]
    have haddedTest : addedStore regs.test = input + 1 := by
      simp [addedStore, quotientStore, oneStore, Basic.exec,
        regs.injective.eq_iff, hvalue]
    have haddedDivisor : addedStore regs.divisor = base := by
      simp [addedStore, quotientStore, oneStore, Basic.exec,
        regs.injective.eq_iff, hdivisor]
    rw [haddedTest, haddedDivisor, hdecompose]
  obtain ⟨final, hloop, hfinalValue, hfinalQuotient,
      hfinalTest, hfinalOne, hfinalDivisor⟩ :=
    divRemLoop_runs regs testedStore base (input % base)
      (input / base) 0 (Nat.mod_lt input hbase)
      htestedDecompose htestedQuotient htestedTest
      htestedOne htestedDivisor
  have hrun : Runs (divRem regs) store final := by
    simpa [divRem, divRemTest, Cmd.seqList] using
      Runs.seq (Runs.basic (Basic.imm regs.one 1) store)
        (Runs.seq
          (Runs.basic (Basic.imm regs.quotient 0) oneStore)
          (Runs.seq
            (Runs.seq
              (Runs.basic (Basic.add regs.test regs.value regs.one)
                quotientStore)
              (Runs.basic
                (Basic.sub regs.test regs.test regs.divisor)
                addedStore))
            hloop))
  refine ⟨final, hrun, ?_⟩
  refine
    { value_eq := hfinalValue
      quotient_eq := by simpa using hfinalQuotient
      test_eq := hfinalTest
      one_eq := hfinalOne
      divisor_eq := hfinalDivisor
      eq_outside := ?_ }
  intro address haddress
  exact RAM.Structured.Footprint.runs_eq_outside
    (divRem_writesWithin_internal regs) hrun haddress

private theorem copy_writesWithin
    (destination source : ℕ) :
    RAM.Structured.Footprint.CmdWritesWithin
      {destination} (copy destination source) := by
  simp [copy, RAM.Structured.Footprint.CmdWritesWithin,
    RAM.Structured.Footprint.BasicWritesWithin]

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

private theorem scratch_mem
    (regs : NeighborhoodTrial.Registers controller)
    (slot : Fin 7) :
    regs.index (scratchMap slot) ∈ scratchFootprint regs := by
  exact Finset.mem_image.mpr ⟨slot, Finset.mem_univ _, rfl⟩

theorem scratchFootprint_subset_layout_internal
    (regs : NeighborhoodTrial.Registers controller) :
    scratchFootprint regs ⊆ regs.layout.footprint := by
  intro address haddress
  obtain ⟨slot, _, rfl⟩ := Finset.mem_image.mp haddress
  exact Layout.index_mem_layout_footprint regs (scratchMap slot)

private theorem cmdWritesWithin_mono
    {smaller larger : Finset ℕ}
    (hsubset : smaller ⊆ larger) :
    ∀ command,
      RAM.Structured.Footprint.CmdWritesWithin smaller command →
      RAM.Structured.Footprint.CmdWritesWithin larger command := by
  intro command hwrites
  induction command with
  | skip => trivial
  | basic op =>
      cases op <;>
        simp_all [RAM.Structured.Footprint.CmdWritesWithin,
          RAM.Structured.Footprint.BasicWritesWithin] <;>
        exact hsubset hwrites
  | seq first second firstIH secondIH =>
      exact ⟨firstIH hwrites.1, secondIH hwrites.2⟩
  | ifZero test onZero onNonzero zeroIH nonzeroIH =>
      exact ⟨zeroIH hwrites.1, nonzeroIH hwrites.2⟩
  | whileNonzero test body bodyIH =>
      exact bodyIH hwrites

private theorem divRem_scratch_writesWithin
    (regs : NeighborhoodTrial.Registers controller)
    (division : DivisionRegisters)
    (hmutable :
      division.value ∈ scratchFootprint regs ∧
      division.quotient ∈ scratchFootprint regs ∧
      division.test ∈ scratchFootprint regs ∧
      division.one ∈ scratchFootprint regs) :
    RAM.Structured.Footprint.CmdWritesWithin
      (scratchFootprint regs) (divRem division) := by
  simp only [divRem, divRemBody, divRemTest, Cmd.seqList,
    RAM.Structured.Footprint.CmdWritesWithin,
    RAM.Structured.Footprint.BasicWritesWithin]
  aesop

theorem decodeNode_writesWithin_internal
    (regs : NeighborhoodTrial.Registers controller) :
    RAM.Structured.Footprint.CmdWritesWithin
      (scratchFootprint regs) (decodeNode regs) := by
  have h0 := scratch_mem regs (0 : Fin 7)
  have h1 := scratch_mem regs (1 : Fin 7)
  have h2 := scratch_mem regs (2 : Fin 7)
  have h3 := scratch_mem regs (3 : Fin 7)
  have h4 := scratch_mem regs (4 : Fin 7)
  have h5 := scratch_mem regs (5 : Fin 7)
  have h6 := scratch_mem regs (6 : Fin 7)
  change word regs ∈ scratchFootprint regs at h0
  change tag regs ∈ scratchFootprint regs at h1
  change first regs ∈ scratchFootprint regs at h2
  change second regs ∈ scratchFootprint regs at h3
  change third regs ∈ scratchFootprint regs at h4
  change fourth regs ∈ scratchFootprint regs at h5
  change loopScratch regs ∈ scratchFootprint regs at h6
  simp only [decodeNode, Cmd.seqList,
    RAM.Structured.Footprint.CmdWritesWithin]
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · simpa [copy, RAM.Structured.Footprint.CmdWritesWithin,
      RAM.Structured.Footprint.BasicWritesWithin] using h0
  · apply divRem_scratch_writesWithin
    simpa [firstStage] using
      (show word regs ∈ scratchFootprint regs ∧
        first regs ∈ scratchFootprint regs ∧
        second regs ∈ scratchFootprint regs ∧
        third regs ∈ scratchFootprint regs from
        ⟨h0, h2, h3, h4⟩)
  · simpa [copy, RAM.Structured.Footprint.CmdWritesWithin,
      RAM.Structured.Footprint.BasicWritesWithin] using h1
  · apply divRem_scratch_writesWithin
    simpa [nodeSecondStage] using
      (show first regs ∈ scratchFootprint regs ∧
        second regs ∈ scratchFootprint regs ∧
        third regs ∈ scratchFootprint regs ∧
        fourth regs ∈ scratchFootprint regs from
        ⟨h2, h3, h4, h5⟩)
  · apply divRem_scratch_writesWithin
    simpa [nodeThirdStage] using
      (show second regs ∈ scratchFootprint regs ∧
        third regs ∈ scratchFootprint regs ∧
        fourth regs ∈ scratchFootprint regs ∧
        loopScratch regs ∈ scratchFootprint regs from
        ⟨h3, h4, h5, h6⟩)

theorem decodePhase_writesWithin_internal
    (regs : NeighborhoodTrial.Registers controller) :
    RAM.Structured.Footprint.CmdWritesWithin
      (scratchFootprint regs) (decodePhase regs) := by
  have h0 := scratch_mem regs (0 : Fin 7)
  have h1 := scratch_mem regs (1 : Fin 7)
  have h2 := scratch_mem regs (2 : Fin 7)
  have h3 := scratch_mem regs (3 : Fin 7)
  have h4 := scratch_mem regs (4 : Fin 7)
  have h5 := scratch_mem regs (5 : Fin 7)
  have h6 := scratch_mem regs (6 : Fin 7)
  change word regs ∈ scratchFootprint regs at h0
  change tag regs ∈ scratchFootprint regs at h1
  change first regs ∈ scratchFootprint regs at h2
  change second regs ∈ scratchFootprint regs at h3
  change third regs ∈ scratchFootprint regs at h4
  change fourth regs ∈ scratchFootprint regs at h5
  change loopScratch regs ∈ scratchFootprint regs at h6
  simp only [decodePhase, Cmd.seqList,
    RAM.Structured.Footprint.CmdWritesWithin]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · simpa [copy, RAM.Structured.Footprint.CmdWritesWithin,
      RAM.Structured.Footprint.BasicWritesWithin] using h0
  · apply divRem_scratch_writesWithin
    simpa [firstStage] using
      (show word regs ∈ scratchFootprint regs ∧
        first regs ∈ scratchFootprint regs ∧
        second regs ∈ scratchFootprint regs ∧
        third regs ∈ scratchFootprint regs from
        ⟨h0, h2, h3, h4⟩)
  · simpa [copy, RAM.Structured.Footprint.CmdWritesWithin,
      RAM.Structured.Footprint.BasicWritesWithin] using h1
  · apply divRem_scratch_writesWithin
    simpa [phaseSecondStage] using
      (show first regs ∈ scratchFootprint regs ∧
        second regs ∈ scratchFootprint regs ∧
        third regs ∈ scratchFootprint regs ∧
        fourth regs ∈ scratchFootprint regs from
        ⟨h2, h3, h4, h5⟩)
  · apply divRem_scratch_writesWithin
    simpa [phaseThirdStage] using
      (show second regs ∈ scratchFootprint regs ∧
        third regs ∈ scratchFootprint regs ∧
        fourth regs ∈ scratchFootprint regs ∧
        loopScratch regs ∈ scratchFootprint regs from
        ⟨h3, h4, h5, h6⟩)
  · apply divRem_scratch_writesWithin
    simpa [phaseFourthStage] using
      (show third regs ∈ scratchFootprint regs ∧
        fourth regs ∈ scratchFootprint regs ∧
        loopScratch regs ∈ scratchFootprint regs ∧
        word regs ∈ scratchFootprint regs from
        ⟨h4, h5, h6, h0⟩)

theorem decodeNode_layout_writesWithin_internal
    (regs : NeighborhoodTrial.Registers controller) :
    RAM.Structured.Footprint.CmdWritesWithin
      regs.layout.footprint (decodeNode regs) :=
  cmdWritesWithin_mono (scratchFootprint_subset_layout_internal regs) _
    (decodeNode_writesWithin_internal regs)

theorem decodePhase_layout_writesWithin_internal
    (regs : NeighborhoodTrial.Registers controller) :
    RAM.Structured.Footprint.CmdWritesWithin
      regs.layout.footprint (decodePhase regs) :=
  cmdWritesWithin_mono (scratchFootprint_subset_layout_internal regs) _
    (decodePhase_writesWithin_internal regs)

private theorem abi_outside_scratch
    (regs : NeighborhoodTrial.Registers controller) :
    Layout.fuel regs ∉ scratchFootprint regs ∧
    Layout.nodeCode regs ∉ scratchFootprint regs ∧
    Layout.scalar regs ∉ scratchFootprint regs ∧
    Layout.out regs ∉ scratchFootprint regs ∧
    Layout.phaseCode regs ∉ scratchFootprint regs ∧
    Layout.active regs ∉ scratchFootprint regs ∧
    Layout.blockLength regs ∉ scratchFootprint regs ∧
    Layout.horizon regs ∉ scratchFootprint regs ∧
    Layout.chunkCount regs ∉ scratchFootprint regs ∧
    Layout.chunkRadix regs ∉ scratchFootprint regs ∧
    Layout.frameRadix regs ∉ scratchFootprint regs ∧
    Layout.bankRadix regs ∉ scratchFootprint regs ∧
    Layout.bankDigitCount regs ∉ scratchFootprint regs ∧
    Layout.modulusPred regs ∉ scratchFootprint regs ∧
    Layout.modulus regs ∉ scratchFootprint regs := by
  refine
    ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
    simp only [scratchFootprint, Finset.mem_image, Finset.mem_univ,
      true_and, not_exists] <;>
    intro slot heq <;>
    have hslot := regs.injective heq <;>
    change scratchMap slot = _ at hslot <;>
    fin_cases slot <;>
    contradiction

private theorem preservesABI_of_run
    (regs : NeighborhoodTrial.Registers controller)
    {command : Cmd} {initial final : Store}
    (hwrites :
      RAM.Structured.Footprint.CmdWritesWithin
        (scratchFootprint regs) command)
    (hrun : Runs command initial final) :
    PreservesABI regs initial final := by
  rcases abi_outside_scratch regs with
    ⟨hfuel, hnode, hscalar, hout, hphase, hactive,
      hblock, hhorizon, hcount, hradix, hframeRadix,
      hbankRadix, hbankCount, hmodulusPred, hmodulus⟩
  exact
    { fuel_eq :=
        RAM.Structured.Footprint.runs_eq_outside hwrites hrun hfuel
      nodeCode_eq :=
        RAM.Structured.Footprint.runs_eq_outside hwrites hrun hnode
      scalar_eq :=
        RAM.Structured.Footprint.runs_eq_outside hwrites hrun hscalar
      out_eq :=
        RAM.Structured.Footprint.runs_eq_outside hwrites hrun hout
      phaseCode_eq :=
        RAM.Structured.Footprint.runs_eq_outside hwrites hrun hphase
      active_eq :=
        RAM.Structured.Footprint.runs_eq_outside hwrites hrun hactive
      blockLength_eq :=
        RAM.Structured.Footprint.runs_eq_outside hwrites hrun hblock
      horizon_eq :=
        RAM.Structured.Footprint.runs_eq_outside hwrites hrun hhorizon
      chunkCount_eq :=
        RAM.Structured.Footprint.runs_eq_outside hwrites hrun hcount
      chunkRadix_eq :=
        RAM.Structured.Footprint.runs_eq_outside hwrites hrun hradix
      frameRadix_eq :=
        RAM.Structured.Footprint.runs_eq_outside
          hwrites hrun hframeRadix
      bankRadix_eq :=
        RAM.Structured.Footprint.runs_eq_outside
          hwrites hrun hbankRadix
      bankDigitCount_eq :=
        RAM.Structured.Footprint.runs_eq_outside
          hwrites hrun hbankCount
      modulusPred_eq :=
        RAM.Structured.Footprint.runs_eq_outside
          hwrites hrun hmodulusPred
      modulus_eq :=
        RAM.Structured.Footprint.runs_eq_outside hwrites hrun hmodulus }

theorem decodeNode_preservesABI_internal
    (regs : NeighborhoodTrial.Registers controller)
    {initial final : Store}
    (hrun : Runs (decodeNode regs) initial final) :
    PreservesABI regs initial final :=
  preservesABI_of_run regs (decodeNode_writesWithin_internal regs) hrun

theorem decodePhase_preservesABI_internal
    (regs : NeighborhoodTrial.Registers controller)
    {initial final : Store}
    (hrun : Runs (decodePhase regs) initial final) :
    PreservesABI regs initial final :=
  preservesABI_of_run regs (decodePhase_writesWithin_internal regs) hrun

private theorem nodeValues_encodeList_four
    {base firstDigit secondDigit thirdDigit fourthDigit : ℕ}
    (hbase : 0 < base)
    (hfirst : firstDigit < base)
    (hsecond : secondDigit < base)
    (hthird : thirdDigit < base) :
    nodeValues base
        (FrameCodec.encodeList base
          [firstDigit, secondDigit, thirdDigit, fourthDigit]) =
      ⟨firstDigit, secondDigit, thirdDigit, fourthDigit⟩ := by
  have hpopFirst :
      FrameCodec.encodeList base
          [firstDigit, secondDigit, thirdDigit, fourthDigit] / base =
        FrameCodec.encodeList base
          [secondDigit, thirdDigit, fourthDigit] := by
    simpa [FrameCodec.encodeList, PackedDigits.pop] using
      (PackedDigits.pop_push
        (word := FrameCodec.encodeList base
          [secondDigit, thirdDigit, fourthDigit])
        hbase hfirst)
  have hpopSecond :
      FrameCodec.encodeList base
          [secondDigit, thirdDigit, fourthDigit] / base =
        FrameCodec.encodeList base [thirdDigit, fourthDigit] := by
    simpa [FrameCodec.encodeList, PackedDigits.pop] using
      (PackedDigits.pop_push
        (word := FrameCodec.encodeList base
          [thirdDigit, fourthDigit])
        hbase hsecond)
  have hpopThird :
      FrameCodec.encodeList base [thirdDigit, fourthDigit] / base =
        FrameCodec.encodeList base [fourthDigit] := by
    simpa [FrameCodec.encodeList, PackedDigits.pop] using
      (PackedDigits.pop_push
        (word := FrameCodec.encodeList base [fourthDigit])
        hbase hthird)
  have hmodFirst :
      FrameCodec.encodeList base
          [firstDigit, secondDigit, thirdDigit, fourthDigit] % base =
        firstDigit := by
    simpa [FrameCodec.encodeList, PackedDigits.digit] using
      (PackedDigits.digit_push_zero
        (word := FrameCodec.encodeList base
          [secondDigit, thirdDigit, fourthDigit])
        hfirst)
  have hmodSecond :
      FrameCodec.encodeList base
          [secondDigit, thirdDigit, fourthDigit] % base =
        secondDigit := by
    simpa [FrameCodec.encodeList, PackedDigits.digit] using
      (PackedDigits.digit_push_zero
        (word := FrameCodec.encodeList base
          [thirdDigit, fourthDigit])
        hsecond)
  have hmodThird :
      FrameCodec.encodeList base [thirdDigit, fourthDigit] % base =
        thirdDigit := by
    simpa [FrameCodec.encodeList, PackedDigits.digit] using
      (PackedDigits.digit_push_zero
        (word := FrameCodec.encodeList base [fourthDigit])
        hthird)
  simp only [nodeValues, hpopFirst, hpopSecond, hpopThird,
    hmodFirst, hmodSecond, hmodThird]
  simp [FrameCodec.encodeList, PackedDigits.push]

theorem nodeValues_encodeNode_internal
    {base : ℕ}
    (node : NeighborhoodEvaluator.QueryNode workTapeCount horizon)
    (hbase : 0 < base)
    (hfits :
      ∀ digit ∈ FrameCodec.nodeDigits node, digit < base) :
    nodeValues base (FrameCodec.encodeNode base node) =
      expectedNodeValues node := by
  cases node with
  | failure =>
      simpa [FrameCodec.encodeNode, FrameCodec.nodeDigits,
        expectedNodeValues] using
        nodeValues_encodeList_four hbase
          (hfits 0 (by simp [FrameCodec.nodeDigits]))
          (hfits 0 (by simp [FrameCodec.nodeDigits]))
          (hfits 0 (by simp [FrameCodec.nodeDigits]))
          (fourthDigit := 0)
  | graph node =>
      cases node with
      | source tape block =>
          simpa [FrameCodec.encodeNode, FrameCodec.nodeDigits,
            expectedNodeValues] using
            nodeValues_encodeList_four hbase
              (hfits 1 (by simp [FrameCodec.nodeDigits]))
              (hfits tape.val (by simp [FrameCodec.nodeDigits]))
              (hfits block (by simp [FrameCodec.nodeDigits]))
              (fourthDigit := 0)
      | computation tape slot interval =>
          simpa [FrameCodec.encodeNode, FrameCodec.nodeDigits,
            expectedNodeValues] using
            nodeValues_encodeList_four hbase
              (hfits 2 (by simp [FrameCodec.nodeDigits]))
              (hfits tape.val (by simp [FrameCodec.nodeDigits]))
              (hfits slot.toFin.val
                (by simp [FrameCodec.nodeDigits]))
              (fourthDigit := interval)

private theorem phaseEncoding_eq_mixed
    {base tagValue residue residuesLeft child next : ℕ}
    (hbase : 0 < base)
    (hresidue :
      residue < base ^ FrameCodec.scalarDigitCount)
    (hresiduesLeft :
      residuesLeft < base ^ FrameCodec.scalarDigitCount) :
    FrameCodec.encodeList base
        ([tagValue] ++ FrameCodec.scalarDigits base residue ++
          FrameCodec.scalarDigits base residuesLeft ++ [child, next]) =
      PackedDigits.push base tagValue
        (PackedDigits.push
          (base ^ FrameCodec.scalarDigitCount) residue
          (PackedDigits.push
            (base ^ FrameCodec.scalarDigitCount) residuesLeft
            (PackedDigits.push base child next))) := by
  change FrameCodec.encodeList base
      (tagValue ::
        (FrameCodec.scalarDigits base residue ++
          (FrameCodec.scalarDigits base residuesLeft ++
            [child, next]))) = _
  simp only [FrameCodec.encodeList]
  have happendResidue :=
    FrameCodec.encodeList_append base
      (FrameCodec.scalarDigits base residue)
      (FrameCodec.scalarDigits base residuesLeft ++ [child, next])
  rw [happendResidue]
  have hencodeResidue :=
    FrameCodec.encodeList_scalarDigits hbase hresidue
  rw [hencodeResidue]
  have happendResiduesLeft :=
    FrameCodec.encodeList_append base
      (FrameCodec.scalarDigits base residuesLeft) [child, next]
  rw [happendResiduesLeft]
  have hencodeResiduesLeft :=
    FrameCodec.encodeList_scalarDigits hbase hresiduesLeft
  rw [hencodeResiduesLeft]
  simp [FrameCodec.scalarDigits, FrameCodec.scalarDigitCount,
    FrameCodec.encodeList, PackedDigits.push]

private theorem phaseValues_mixed
    {base residueBase tagValue residue residuesLeft child next : ℕ}
    (hbase : 0 < base)
    (hresidueBase : 0 < residueBase)
    (htag : tagValue < base)
    (hresidue : residue < residueBase)
    (hresiduesLeft : residuesLeft < residueBase)
    (hchild : child < base) :
    phaseValues base residueBase
        (PackedDigits.push base tagValue
          (PackedDigits.push residueBase residue
            (PackedDigits.push residueBase residuesLeft
              (PackedDigits.push base child next)))) =
      ⟨tagValue, residue, residuesLeft, child, next⟩ := by
  let childTail := PackedDigits.push base child next
  let residuesLeftTail :=
    PackedDigits.push residueBase residuesLeft childTail
  let residueTail :=
    PackedDigits.push residueBase residue residuesLeftTail
  let code := PackedDigits.push base tagValue residueTail
  have hpopTag : code / base = residueTail := by
    simpa [code, PackedDigits.pop] using
      (PackedDigits.pop_push (word := residueTail) hbase htag)
  have hpopResidue : residueTail / residueBase = residuesLeftTail := by
    simpa [residueTail, PackedDigits.pop] using
      (PackedDigits.pop_push
        (word := residuesLeftTail) hresidueBase hresidue)
  have hpopResiduesLeft :
      residuesLeftTail / residueBase = childTail := by
    simpa [residuesLeftTail, PackedDigits.pop] using
      (PackedDigits.pop_push
        (word := childTail) hresidueBase hresiduesLeft)
  have hpopChild : childTail / base = next := by
    simpa [childTail, PackedDigits.pop] using
      (PackedDigits.pop_push (word := next) hbase hchild)
  have hmodTag : code % base = tagValue := by
    simpa [code, PackedDigits.digit] using
      (PackedDigits.digit_push_zero (word := residueTail) htag)
  have hmodResidue : residueTail % residueBase = residue := by
    simpa [residueTail, PackedDigits.digit] using
      (PackedDigits.digit_push_zero
        (word := residuesLeftTail) hresidue)
  have hmodResiduesLeft :
      residuesLeftTail % residueBase = residuesLeft := by
    simpa [residuesLeftTail, PackedDigits.digit] using
      (PackedDigits.digit_push_zero
        (word := childTail) hresiduesLeft)
  have hmodChild : childTail % base = child := by
    simpa [childTail, PackedDigits.digit] using
      (PackedDigits.digit_push_zero (word := next) hchild)
  change phaseValues base residueBase code = _
  simp only [phaseValues, hpopTag, hpopResidue,
    hpopResiduesLeft, hpopChild, hmodTag, hmodResidue,
    hmodResiduesLeft, hmodChild]

theorem phaseValues_encodePhase_internal
    {base : ℕ}
    (phase : NeighborhoodScheduler.Phase workTapeCount)
    (hbase : 0 < base)
    (hfits :
      ∀ digit ∈ FrameCodec.phaseDigits base phase, digit < base)
    (hresidue :
      (expectedPhaseValues phase).residue <
        base ^ FrameCodec.scalarDigitCount)
    (hresiduesLeft :
      (expectedPhaseValues phase).residuesLeft <
        base ^ FrameCodec.scalarDigitCount) :
    phaseValues base (base ^ FrameCodec.scalarDigitCount)
        (FrameCodec.encodePhase base phase) =
      expectedPhaseValues phase := by
  have hresidueBase :
      0 < base ^ FrameCodec.scalarDigitCount :=
    pow_pos hbase _
  cases phase with
  | enter =>
      have hzero :
          0 < base ^ FrameCodec.scalarDigitCount := by
        simpa [expectedPhaseValues] using hresidue
      rw [show FrameCodec.encodePhase base .enter =
          PackedDigits.push base 0
            (PackedDigits.push
              (base ^ FrameCodec.scalarDigitCount) 0
              (PackedDigits.push
                (base ^ FrameCodec.scalarDigitCount) 0
                (PackedDigits.push base 0 0))) by
        simpa [FrameCodec.encodePhase, FrameCodec.phaseDigits,
          FrameCodec.scalarDigits, PackedDigits.digit, hbase] using
          phaseEncoding_eq_mixed hbase hzero hzero
            (tagValue := 0) (child := 0) (next := 0)]
      simpa [expectedPhaseValues] using
        phaseValues_mixed hbase hresidueBase
          (hfits 0 (by simp [FrameCodec.phaseDigits]))
          hzero hzero
          (hfits 0 (by simp [FrameCodec.phaseDigits]))
  | prepare residue residuesLeft childIndex =>
      rw [show FrameCodec.encodePhase base
            (.prepare residue residuesLeft childIndex) =
          PackedDigits.push base 1
            (PackedDigits.push
              (base ^ FrameCodec.scalarDigitCount) residue
              (PackedDigits.push
                (base ^ FrameCodec.scalarDigitCount) residuesLeft
                (PackedDigits.push base childIndex 0))) by
        simpa [FrameCodec.encodePhase, FrameCodec.phaseDigits] using
          phaseEncoding_eq_mixed hbase hresidue hresiduesLeft
            (tagValue := 1) (child := childIndex) (next := 0)]
      simpa [expectedPhaseValues] using
        phaseValues_mixed hbase hresidueBase
          (hfits 1 (by simp [FrameCodec.phaseDigits]))
          hresidue hresiduesLeft
          (hfits childIndex (by simp [FrameCodec.phaseDigits]))
  | combine residue residuesLeft =>
      rw [show FrameCodec.encodePhase base
            (.combine residue residuesLeft) =
          PackedDigits.push base 2
            (PackedDigits.push
              (base ^ FrameCodec.scalarDigitCount) residue
              (PackedDigits.push
                (base ^ FrameCodec.scalarDigitCount) residuesLeft
                (PackedDigits.push base 0 0))) by
        simpa [FrameCodec.encodePhase, FrameCodec.phaseDigits] using
          phaseEncoding_eq_mixed hbase hresidue hresiduesLeft
            (tagValue := 2) (child := 0) (next := 0)]
      simpa [expectedPhaseValues] using
        phaseValues_mixed hbase hresidueBase
          (hfits 2 (by simp [FrameCodec.phaseDigits]))
          hresidue hresiduesLeft
          (hfits 0 (by simp [FrameCodec.phaseDigits]))
  | cleanupCall residue residuesLeft childIndex =>
      rw [show FrameCodec.encodePhase base
            (.cleanupCall residue residuesLeft childIndex) =
          PackedDigits.push base 3
            (PackedDigits.push
              (base ^ FrameCodec.scalarDigitCount) residue
              (PackedDigits.push
                (base ^ FrameCodec.scalarDigitCount) residuesLeft
                (PackedDigits.push base childIndex 0))) by
        simpa [FrameCodec.encodePhase, FrameCodec.phaseDigits] using
          phaseEncoding_eq_mixed hbase hresidue hresiduesLeft
            (tagValue := 3) (child := childIndex) (next := 0)]
      simpa [expectedPhaseValues] using
        phaseValues_mixed hbase hresidueBase
          (hfits 3 (by simp [FrameCodec.phaseDigits]))
          hresidue hresiduesLeft
          (hfits childIndex (by simp [FrameCodec.phaseDigits]))
  | cleanupScale residue residuesLeft child nextChildIndex =>
      rw [show FrameCodec.encodePhase base
            (.cleanupScale residue residuesLeft child nextChildIndex) =
          PackedDigits.push base 4
            (PackedDigits.push
              (base ^ FrameCodec.scalarDigitCount) residue
              (PackedDigits.push
                (base ^ FrameCodec.scalarDigitCount) residuesLeft
                (PackedDigits.push base child.val nextChildIndex))) by
        simpa [FrameCodec.encodePhase, FrameCodec.phaseDigits] using
          phaseEncoding_eq_mixed hbase hresidue hresiduesLeft
            (tagValue := 4) (child := child.val)
            (next := nextChildIndex)]
      simpa [expectedPhaseValues] using
        phaseValues_mixed hbase hresidueBase
          (hfits 4 (by simp [FrameCodec.phaseDigits]))
          hresidue hresiduesLeft
          (hfits child.val (by simp [FrameCodec.phaseDigits]))

theorem decodeNode_runs_internal
    (regs : NeighborhoodTrial.Registers controller)
    (store : Store) (base code : ℕ)
    (hbase : 0 < base)
    (hsource : store (Layout.nodeCode regs) = code)
    (hbaseValue : store (Layout.chunkRadix regs) = base) :
    ∃ final,
      Runs (decodeNode regs) store final ∧
      NodePost regs base code final ∧
      PreservesABI regs store final := by
  obtain ⟨afterCopy, hcopy, hcopyWord, hcopyOutside⟩ :=
    copy_runs (word regs) (Layout.nodeCode regs) store
      (regs.injective.ne (by decide))
  have hcopyBase :
      afterCopy (Layout.chunkRadix regs) = base := by
    rw [hcopyOutside _ (regs.injective.ne (by decide))]
    exact hbaseValue
  obtain ⟨afterFirst, hfirst, hfirstPost⟩ :=
    divRem_runs_internal (firstStage regs) afterCopy base code
      hbase (by simpa [firstStage, hsource] using hcopyWord)
      (by simpa [firstStage] using hcopyBase)
  obtain ⟨afterTag, htagCopy, htag, htagOutside⟩ :=
    copy_runs (tag regs) (word regs) afterFirst
      (regs.injective.ne (by decide))
  have hsecondInput :
      afterTag (nodeSecondStage regs).value = code / base := by
    change afterTag (first regs) = code / base
    rw [htagOutside (first regs) (regs.injective.ne (by decide))]
    simpa [firstStage, nodeSecondStage] using
      hfirstPost.quotient_eq
  have hsecondBase :
      afterTag (nodeSecondStage regs).divisor = base := by
    change afterTag (Layout.chunkRadix regs) = base
    rw [htagOutside (Layout.chunkRadix regs)
      (regs.injective.ne (by decide))]
    simpa [firstStage, nodeSecondStage] using
      hfirstPost.divisor_eq
  obtain ⟨afterSecond, hsecond, hsecondPost⟩ :=
    divRem_runs_internal (nodeSecondStage regs) afterTag
      base (code / base) hbase hsecondInput hsecondBase
  have hthirdInput :
      afterSecond (nodeThirdStage regs).value =
        code / base / base := by
    simpa [nodeSecondStage, nodeThirdStage] using
      hsecondPost.quotient_eq
  have hthirdBase :
      afterSecond (nodeThirdStage regs).divisor = base := by
    change afterSecond (Layout.chunkRadix regs) = base
    have houtside :=
      hsecondPost.eq_outside (Layout.chunkRadix regs)
        (by
          simp [DivisionRegisters.writeFootprint,
            nodeSecondStage, regs.injective.eq_iff])
    rw [houtside]
    simpa [nodeSecondStage] using hsecondBase
  obtain ⟨final, hthird, hthirdPost⟩ :=
    divRem_runs_internal (nodeThirdStage regs) afterSecond
      base (code / base / base) hbase hthirdInput hthirdBase
  have hrun : Runs (decodeNode regs) store final := by
    simpa [decodeNode, Cmd.seqList] using
      Runs.seq hcopy
        (Runs.seq hfirst
          (Runs.seq htagCopy (Runs.seq hsecond hthird)))
  refine ⟨final, hrun, ?_, decodeNode_preservesABI_internal regs hrun⟩
  refine
    { tag_eq := ?_
      tape_eq := ?_
      payload0_eq := ?_
      payload1_eq := ?_
      fourth_eq := ?_ }
  · have htagAfterFirst :
        afterTag (tag regs) = code % base := by
      simpa [firstStage] using
        htag.trans hfirstPost.value_eq
    have htagAfterSecond :
        afterSecond (tag regs) = code % base := by
      rw [hsecondPost.eq_outside (tag regs)
        (by
          simp [DivisionRegisters.writeFootprint,
            nodeSecondStage, regs.injective.eq_iff])]
      exact htagAfterFirst
    rw [hthirdPost.eq_outside (tag regs)
      (by
        simp [DivisionRegisters.writeFootprint,
          nodeThirdStage, regs.injective.eq_iff])]
    simpa [nodeValues] using htagAfterSecond
  · have htape :
        afterSecond (nodeTape regs) = code / base % base := by
      simpa [nodeSecondStage] using hsecondPost.value_eq
    rw [hthirdPost.eq_outside (nodeTape regs)
      (by
        simp [DivisionRegisters.writeFootprint,
          nodeThirdStage, regs.injective.eq_iff])]
    simpa [nodeValues] using htape
  · simpa [nodeValues, nodeThirdStage] using hthirdPost.value_eq
  · simpa [nodeValues, nodeThirdStage] using
      hthirdPost.quotient_eq
  · simpa [nodeThirdStage] using hthirdPost.test_eq

theorem decodePhase_runs_internal
    (regs : NeighborhoodTrial.Registers controller)
    (store : Store) (base residueBase code : ℕ)
    (hbase : 0 < base)
    (hresidueBase : 0 < residueBase)
    (hsource : store (Layout.phaseCode regs) = code)
    (hbaseValue : store (Layout.chunkRadix regs) = base)
    (hresidueBaseValue :
      store (Layout.bankRadix regs) = residueBase) :
    ∃ final,
      Runs (decodePhase regs) store final ∧
      PhasePost regs base residueBase code final ∧
      PreservesABI regs store final := by
  obtain ⟨afterCopy, hcopy, hcopyWord, hcopyOutside⟩ :=
    copy_runs (word regs) (Layout.phaseCode regs) store
      (regs.injective.ne (by decide))
  have hcopyBase :
      afterCopy (Layout.chunkRadix regs) = base := by
    rw [hcopyOutside _ (regs.injective.ne (by decide))]
    exact hbaseValue
  have hcopyResidueBase :
      afterCopy (Layout.bankRadix regs) = residueBase := by
    rw [hcopyOutside _ (regs.injective.ne (by decide))]
    exact hresidueBaseValue
  obtain ⟨afterFirst, hfirst, hfirstPost⟩ :=
    divRem_runs_internal (firstStage regs) afterCopy base code
      hbase (by simpa [firstStage, hsource] using hcopyWord)
      (by simpa [firstStage] using hcopyBase)
  obtain ⟨afterTag, htagCopy, htag, htagOutside⟩ :=
    copy_runs (tag regs) (word regs) afterFirst
      (regs.injective.ne (by decide))
  have hsecondInput :
      afterTag (phaseSecondStage regs).value = code / base := by
    change afterTag (first regs) = code / base
    rw [htagOutside (first regs) (regs.injective.ne (by decide))]
    simpa [firstStage, phaseSecondStage] using
      hfirstPost.quotient_eq
  have hfirstResidueBase :
      afterFirst (Layout.bankRadix regs) = residueBase := by
    rw [hfirstPost.eq_outside (Layout.bankRadix regs)
      (by
        simp [DivisionRegisters.writeFootprint, firstStage,
          regs.injective.eq_iff])]
    exact hcopyResidueBase
  have hsecondBase :
      afterTag (phaseSecondStage regs).divisor = residueBase := by
    change afterTag (Layout.bankRadix regs) = residueBase
    rw [htagOutside (Layout.bankRadix regs)
      (regs.injective.ne (by decide))]
    exact hfirstResidueBase
  obtain ⟨afterSecond, hsecond, hsecondPost⟩ :=
    divRem_runs_internal (phaseSecondStage regs) afterTag
      residueBase (code / base) hresidueBase
      hsecondInput hsecondBase
  have hthirdInput :
      afterSecond (phaseThirdStage regs).value =
        code / base / residueBase := by
    simpa [phaseSecondStage, phaseThirdStage] using
      hsecondPost.quotient_eq
  have hthirdBase :
      afterSecond (phaseThirdStage regs).divisor = residueBase := by
    simpa [phaseSecondStage, phaseThirdStage] using
      hsecondPost.divisor_eq
  obtain ⟨afterThird, hthird, hthirdPost⟩ :=
    divRem_runs_internal (phaseThirdStage regs) afterSecond
      residueBase (code / base / residueBase) hresidueBase
      hthirdInput hthirdBase
  have hfourthInput :
      afterThird (phaseFourthStage regs).value =
        code / base / residueBase / residueBase := by
    simpa [phaseThirdStage, phaseFourthStage] using
      hthirdPost.quotient_eq
  have hfirstBaseAfterTag :
      afterTag (Layout.chunkRadix regs) = base := by
    rw [htagOutside (Layout.chunkRadix regs)
      (regs.injective.ne (by decide))]
    simpa [firstStage] using hfirstPost.divisor_eq
  have hbaseAfterSecond :
      afterSecond (Layout.chunkRadix regs) = base := by
    rw [hsecondPost.eq_outside (Layout.chunkRadix regs)
      (by
        simp [DivisionRegisters.writeFootprint, phaseSecondStage,
          regs.injective.eq_iff])]
    exact hfirstBaseAfterTag
  have hbaseAfterThird :
      afterThird (Layout.chunkRadix regs) = base := by
    rw [hthirdPost.eq_outside (Layout.chunkRadix regs)
      (by
        simp [DivisionRegisters.writeFootprint, phaseThirdStage,
          regs.injective.eq_iff])]
    exact hbaseAfterSecond
  obtain ⟨final, hfourth, hfourthPost⟩ :=
    divRem_runs_internal (phaseFourthStage regs) afterThird
      base (code / base / residueBase / residueBase) hbase
      hfourthInput
      (by simpa [phaseFourthStage] using hbaseAfterThird)
  have hrun : Runs (decodePhase regs) store final := by
    simpa [decodePhase, Cmd.seqList] using
      Runs.seq hcopy
        (Runs.seq hfirst
          (Runs.seq htagCopy
            (Runs.seq hsecond (Runs.seq hthird hfourth))))
  refine ⟨final, hrun, ?_, decodePhase_preservesABI_internal regs hrun⟩
  refine
    { tag_eq := ?_
      residue_eq := ?_
      residuesLeft_eq := ?_
      child_eq := ?_
      next_eq := ?_ }
  · have htagAfterTag :
        afterTag (tag regs) = code % base := by
      simpa [firstStage] using
        htag.trans hfirstPost.value_eq
    have htagAfterSecond :
        afterSecond (tag regs) = code % base := by
      rw [hsecondPost.eq_outside (tag regs)
        (by
          simp [DivisionRegisters.writeFootprint,
            phaseSecondStage, regs.injective.eq_iff])]
      exact htagAfterTag
    have htagAfterThird :
        afterThird (tag regs) = code % base := by
      rw [hthirdPost.eq_outside (tag regs)
        (by
          simp [DivisionRegisters.writeFootprint,
            phaseThirdStage, regs.injective.eq_iff])]
      exact htagAfterSecond
    rw [hfourthPost.eq_outside (tag regs)
      (by
        simp [DivisionRegisters.writeFootprint,
          phaseFourthStage, regs.injective.eq_iff])]
    simpa [phaseValues] using htagAfterThird
  · have hresidue :
        afterSecond (phaseResidue regs) =
          code / base % residueBase := by
      simpa [phaseSecondStage] using hsecondPost.value_eq
    have hresidueAfterThird :
        afterThird (phaseResidue regs) =
          code / base % residueBase := by
      rw [hthirdPost.eq_outside (phaseResidue regs)
        (by
          simp [DivisionRegisters.writeFootprint,
            phaseThirdStage, regs.injective.eq_iff])]
      exact hresidue
    rw [hfourthPost.eq_outside (phaseResidue regs)
      (by
        simp [DivisionRegisters.writeFootprint,
          phaseFourthStage, regs.injective.eq_iff])]
    simpa [phaseValues] using hresidueAfterThird
  · have hresiduesLeft :
        afterThird (phaseResiduesLeft regs) =
          code / base / residueBase % residueBase := by
      simpa [phaseThirdStage] using hthirdPost.value_eq
    rw [hfourthPost.eq_outside (phaseResiduesLeft regs)
      (by
        simp [DivisionRegisters.writeFootprint,
          phaseFourthStage, regs.injective.eq_iff])]
    simpa [phaseValues] using hresiduesLeft
  · simpa [phaseValues, phaseFourthStage] using
      hfourthPost.value_eq
  · simpa [phaseValues, phaseFourthStage] using
      hfourthPost.quotient_eq

theorem decodeNode_encodeNode_runs_internal
    (regs : NeighborhoodTrial.Registers controller)
    (store : Store) (base : ℕ)
    (node : NeighborhoodEvaluator.QueryNode workTapeCount horizon)
    (hbase : 0 < base)
    (hfits :
      ∀ digit ∈ FrameCodec.nodeDigits node, digit < base)
    (hsource :
      store (Layout.nodeCode regs) =
        FrameCodec.encodeNode base node)
    (hbaseValue : store (Layout.chunkRadix regs) = base) :
    ∃ final,
      Runs (decodeNode regs) store final ∧
      NodePost regs base (FrameCodec.encodeNode base node) final ∧
      EncodedNodePost regs node final ∧
      PreservesABI regs store final := by
  obtain ⟨final, hrun, hpost, habi⟩ :=
    decodeNode_runs_internal regs store base
      (FrameCodec.encodeNode base node) hbase hsource hbaseValue
  have hvalues :=
    nodeValues_encodeNode_internal node hbase hfits
  refine ⟨final, hrun, hpost, ?_, habi⟩
  exact
    { tag_eq :=
        hpost.tag_eq.trans (congrArg NodeValues.tag hvalues)
      tape_eq :=
        hpost.tape_eq.trans (congrArg NodeValues.tape hvalues)
      payload0_eq :=
        hpost.payload0_eq.trans
          (congrArg NodeValues.payload0 hvalues)
      payload1_eq :=
        hpost.payload1_eq.trans
          (congrArg NodeValues.payload1 hvalues) }

theorem decodePhase_encodePhase_runs_internal
    (regs : NeighborhoodTrial.Registers controller)
    (store : Store) (base : ℕ)
    (phase : NeighborhoodScheduler.Phase workTapeCount)
    (hbase : 0 < base)
    (hfits :
      ∀ digit ∈ FrameCodec.phaseDigits base phase, digit < base)
    (hresidue :
      (expectedPhaseValues phase).residue <
        base ^ FrameCodec.scalarDigitCount)
    (hresiduesLeft :
      (expectedPhaseValues phase).residuesLeft <
        base ^ FrameCodec.scalarDigitCount)
    (hsource :
      store (Layout.phaseCode regs) =
        FrameCodec.encodePhase base phase)
    (hbaseValue : store (Layout.chunkRadix regs) = base)
    (hresidueBaseValue :
      store (Layout.bankRadix regs) =
        base ^ FrameCodec.scalarDigitCount) :
    ∃ final,
      Runs (decodePhase regs) store final ∧
      PhasePost regs base (base ^ FrameCodec.scalarDigitCount)
        (FrameCodec.encodePhase base phase) final ∧
      EncodedPhasePost regs phase final ∧
      PreservesABI regs store final := by
  have hresidueBase :
      0 < base ^ FrameCodec.scalarDigitCount :=
    pow_pos hbase _
  obtain ⟨final, hrun, hpost, habi⟩ :=
    decodePhase_runs_internal regs store base
      (base ^ FrameCodec.scalarDigitCount)
      (FrameCodec.encodePhase base phase) hbase hresidueBase
      hsource hbaseValue hresidueBaseValue
  have hvalues :=
    phaseValues_encodePhase_internal phase hbase hfits
      hresidue hresiduesLeft
  refine ⟨final, hrun, hpost, ?_, habi⟩
  exact
    { tag_eq :=
        hpost.tag_eq.trans (congrArg PhaseValues.tag hvalues)
      residue_eq :=
        hpost.residue_eq.trans
          (congrArg PhaseValues.residue hvalues)
      residuesLeft_eq :=
        hpost.residuesLeft_eq.trans
          (congrArg PhaseValues.residuesLeft hvalues)
      child_eq :=
        hpost.child_eq.trans (congrArg PhaseValues.child hvalues)
      next_eq :=
        hpost.next_eq.trans (congrArg PhaseValues.next hvalues) }

end Internal
end ControlDecode
end NeighborhoodMicrocode
end Runtime
end TimeSpaceSimulation
end Complexity
