/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/
import
  Complexitylib.TimeSpaceSimulation.Runtime.NeighborhoodMicrocode.ResidueBankOps.Defs
import
  Complexitylib.Models.RandomAccessMachine.Structured.Footprint
import
  Complexitylib.Models.RandomAccessMachine.Structured.Invariant

/-!
# Concrete catalytic residue-bank operations -- proofs
-/

namespace Complexity
namespace TimeSpaceSimulation
namespace Runtime
namespace NeighborhoodMicrocode
namespace ResidueBankOps
namespace Internal

open RAM Structured

variable {controller : SearchProgram.Registers}

private theorem basics_runs (ops : List Basic) (store : Store) :
    Runs (Cmd.basics ops) store (Basic.execList ops store) := by
  obtain ⟨cost, space, hexec⟩ :=
    RAM.Structured.Internal.exec_basics_exists ops store
  exact ⟨ops.length, cost, space, hexec⟩

private theorem valuesWithin_update
    (allowed : Finset ℕ) (bound address value : ℕ)
    (store : Store)
    (hstore : NeighborhoodProgram.ValuesWithin allowed bound store)
    (hvalue : value ≤ bound) :
    NeighborhoodProgram.ValuesWithin allowed bound
      (Function.update store address value) := by
  intro current hcurrent
  by_cases heq : current = address
  · subst current
    simp [hvalue]
  · simp [heq, hstore current hcurrent]

private theorem copy_invariantRuns
    (allowed : Finset ℕ) (bound destination source : ℕ)
    (store : Store)
    (hne : destination ≠ source)
    (hsource : store source ≤ bound)
    (hstore : NeighborhoodProgram.ValuesWithin allowed bound store) :
    ∃ final,
      InvariantRuns
        (NeighborhoodProgram.ValuesWithin allowed bound)
        (copy destination source) store final 2 ∧
      final destination = store source ∧
      ∀ address, address ≠ destination →
        final address = store address := by
  let cleared := (Basic.imm destination 0).exec store
  let final :=
    (Basic.add destination source destination).exec cleared
  have hcleared :
      NeighborhoodProgram.ValuesWithin allowed bound cleared := by
    apply valuesWithin_update allowed bound destination 0 store
      hstore
    omega
  have hclearedSource : cleared source = store source := by
    simp [cleared, Basic.exec, hne.symm]
  have hclearedDestination : cleared destination = 0 := by
    simp [cleared, Basic.exec]
  have hfinal :
      NeighborhoodProgram.ValuesWithin allowed bound final := by
    apply valuesWithin_update allowed bound destination
      (cleared source + cleared destination) cleared hcleared
    rw [hclearedSource, hclearedDestination, Nat.add_zero]
    exact hsource
  refine ⟨final, ?_, ?_, ?_⟩
  · exact InvariantRuns.seq
      (InvariantRuns.basic (Basic.imm destination 0) store
        hstore hcleared)
      (InvariantRuns.basic
        (Basic.add destination source destination) cleared
        hcleared hfinal)
  · simp [final, cleared, Basic.exec, hne.symm]
  · intro address haddress
    simp [final, cleared, Basic.exec, haddress]

private theorem cmdWritesWithin_mono
    {small large : Finset ℕ} (hsub : small ⊆ large)
    {cmd : Cmd}
    (hwrites :
      RAM.Structured.Footprint.CmdWritesWithin small cmd) :
    RAM.Structured.Footprint.CmdWritesWithin large cmd := by
  induction cmd with
  | skip =>
      trivial
  | basic op =>
      cases op <;>
        simp only [RAM.Structured.Footprint.CmdWritesWithin,
          RAM.Structured.Footprint.BasicWritesWithin] at hwrites ⊢
      all_goals exact hsub hwrites
  | seq first second firstIH secondIH =>
      exact ⟨firstIH hwrites.1, secondIH hwrites.2⟩
  | ifZero test onZero onNonzero zeroIH nonzeroIH =>
      exact ⟨zeroIH hwrites.1, nonzeroIH hwrites.2⟩
  | whileNonzero test body bodyIH =>
      exact bodyIH hwrites

private theorem scale_index_mem
    (regs : NeighborhoodTrial.Registers controller)
    (slot : Fin 17) :
    (Layout.residueScaleRegisters regs).index slot ∈
      regs.layout.footprint :=
  Layout.residueScale_footprint_subset regs
    ((Layout.residueScaleRegisters regs).index_mem_footprint slot)

private theorem bank_index_mem
    (regs : NeighborhoodTrial.Registers controller)
    (slot : Fin 16) :
    (Layout.residueScaleRegisters regs).bank.index slot ∈
      regs.layout.footprint := by
  apply Layout.residueScale_footprint_subset regs
  exact
    (Layout.residueScaleRegisters regs).index_mem_footprint
      (NeighborhoodProgram.ResidueScaleRegisters.bankSlot slot)

private theorem bank_index_mem_scale
    (regs : NeighborhoodTrial.Registers controller)
    (slot : Fin 16) :
    (Layout.residueScaleRegisters regs).bank.index slot ∈
      (Layout.residueScaleRegisters regs).footprint :=
  (Layout.residueScaleRegisters regs).index_mem_footprint
    (NeighborhoodProgram.ResidueScaleRegisters.bankSlot slot)

private theorem bank_footprint_subset_scale
    (regs : NeighborhoodTrial.Registers controller) :
    (Layout.residueScaleRegisters regs).bank.footprint ⊆
      (Layout.residueScaleRegisters regs).footprint := by
  intro address haddress
  obtain ⟨slot, _, rfl⟩ := Finset.mem_image.mp haddress
  exact bank_index_mem_scale regs slot

private theorem scale_index_ne_scalar
    (regs : NeighborhoodTrial.Registers controller)
    (slot : Fin 17) :
    (Layout.residueScaleRegisters regs).index slot ≠
      Layout.scalar regs := by
  intro heq
  have hslot := regs.injective heq
  fin_cases slot <;>
    simp [Layout.residueScaleMap] at hslot

private theorem scale_index_ne_chunkCount
    (regs : NeighborhoodTrial.Registers controller)
    (slot : Fin 17) :
    (Layout.residueScaleRegisters regs).index slot ≠
      Layout.chunkCount regs := by
  intro heq
  have hslot := regs.injective heq
  fin_cases slot <;>
    simp [Layout.residueScaleMap] at hslot

private theorem scale_index_ne_out
    (regs : NeighborhoodTrial.Registers controller)
    (slot : Fin 17) :
    (Layout.residueScaleRegisters regs).index slot ≠
      Layout.out regs := by
  intro heq
  have hslot := regs.injective heq
  fin_cases slot <;>
    simp [Layout.residueScaleMap] at hslot

private theorem scale_index_ne_codecScratch
    (regs : NeighborhoodTrial.Registers controller)
    (slot : Fin 17) :
    (Layout.residueScaleRegisters regs).index slot ≠
      Layout.codecScratch regs := by
  intro heq
  have hslot := regs.injective heq
  fin_cases slot <;>
    simp [Layout.residueScaleMap] at hslot

private theorem zero_represents_internal
    {workTapeCount : ℕ} (tm : TM workTapeCount)
    (blockLength base : ℕ) :
    NeighborhoodProgram.RepresentsResidueBank
      tm blockLength base 0 (zeroRegisters tm blockLength) := by
  intro register chunk
  simp [zeroRegisters, PackedDigits.digit]

theorem clearBank_writesWithin_internal
    (regs : NeighborhoodTrial.Registers controller) :
    RAM.Structured.Footprint.CmdWritesWithin
      regs.layout.footprint (clearBank regs) := by
  simp [clearBank,
    RAM.Structured.Footprint.CmdWritesWithin,
    RAM.Structured.Footprint.BasicWritesWithin, bank_index_mem]

theorem initializeBank_writesWithin_internal
    (regs : NeighborhoodTrial.Registers controller) :
    RAM.Structured.Footprint.CmdWritesWithin
      regs.layout.footprint (initializeBank regs) := by
  simp [initializeBank, initializeBankOps, Cmd.basics, Cmd.seqList,
    RAM.Structured.Footprint.CmdWritesWithin,
    RAM.Structured.Footprint.BasicWritesWithin, bank_index_mem]

theorem prepareScaleActive_writesWithin_internal
    (regs : NeighborhoodTrial.Registers controller) :
    RAM.Structured.Footprint.CmdWritesWithin
      regs.layout.footprint (prepareScaleActive regs) := by
  simp [prepareScaleActive, prepareScaleActiveOps, Cmd.basics,
    Cmd.seqList, RAM.Structured.Footprint.CmdWritesWithin,
    RAM.Structured.Footprint.BasicWritesWithin, bank_index_mem,
    scale_index_mem]

theorem scaleActiveRegister_writesWithin_internal
    (regs : NeighborhoodTrial.Registers controller) :
    RAM.Structured.Footprint.CmdWritesWithin
      regs.layout.footprint (scaleActiveRegister regs) := by
  refine ⟨prepareScaleActive_writesWithin_internal regs, ?_⟩
  apply cmdWritesWithin_mono
    (Layout.residueScale_footprint_subset regs)
  exact NeighborhoodProgram.bankScaleRegister_sourceWritesWithin _

private theorem prepareActiveChunkIndex_scaleWritesWithin
    (regs : NeighborhoodTrial.Registers controller) :
    RAM.Structured.Footprint.CmdWritesWithin
      (Layout.residueScaleRegisters regs).footprint
      (prepareActiveChunkIndex regs) := by
  simp [prepareActiveChunkIndex, prepareActiveChunkIndexOps,
    Cmd.basics, Cmd.seqList,
    RAM.Structured.Footprint.CmdWritesWithin,
    RAM.Structured.Footprint.BasicWritesWithin, bank_index_mem_scale]

private theorem mulMod_scaleWritesWithin
    (regs : NeighborhoodTrial.Registers controller) :
    RAM.Structured.Footprint.CmdWritesWithin
      (Layout.residueScaleRegisters regs).footprint
      (RuntimeArithmetic.mulMod
        (Layout.residueScaleRegisters regs).bank.reduceRegisters
        (Layout.residueScaleRegisters regs).bank.operand
        (Layout.scalar regs)) := by
  simp [RuntimeArithmetic.mulMod, RuntimeArithmetic.reduce,
    RuntimeArithmetic.reduceBody, RuntimeArithmetic.reduceTestOp,
    NeighborhoodProgram.ResidueBankRegisters.reduceRegisters,
    RAM.Structured.Footprint.CmdWritesWithin,
    RAM.Structured.Footprint.BasicWritesWithin, bank_index_mem_scale]

private theorem copy_operand_scaleWritesWithin
    (regs : NeighborhoodTrial.Registers controller) :
    RAM.Structured.Footprint.CmdWritesWithin
      (Layout.residueScaleRegisters regs).footprint
      (copy
        (Layout.residueScaleRegisters regs).bank.operand
        (Layout.residueScaleRegisters regs).bank.bank.replacement) := by
  simp [copy, RAM.Structured.Footprint.CmdWritesWithin,
    RAM.Structured.Footprint.BasicWritesWithin, bank_index_mem_scale]

theorem addScaledActiveChunk_scaleWritesWithin_internal
    (regs : NeighborhoodTrial.Registers controller) :
    RAM.Structured.Footprint.CmdWritesWithin
      (Layout.residueScaleRegisters regs).footprint
      (addScaledActiveChunk regs) := by
  let bank := (Layout.residueScaleRegisters regs).bank
  have hbank :
      RAM.Structured.Footprint.CmdWritesWithin
        (Layout.residueScaleRegisters regs).footprint
        (NeighborhoodProgram.bankAddAt bank) := by
    apply cmdWritesWithin_mono
      (small := bank.footprint)
      (large := (Layout.residueScaleRegisters regs).footprint)
      (bank_footprint_subset_scale regs)
    exact NeighborhoodProgram.bankUpdateAt_sourceWritesWithin
      bank .add
  simpa [addScaledActiveChunk, Cmd.seqList, bank] using
    And.intro (mulMod_scaleWritesWithin regs)
      (And.intro (copy_operand_scaleWritesWithin regs)
        (And.intro
          (prepareActiveChunkIndex_scaleWritesWithin regs)
          hbank))

theorem addScaledActiveChunk_writesWithin_internal
    (regs : NeighborhoodTrial.Registers controller) :
    RAM.Structured.Footprint.CmdWritesWithin
      regs.layout.footprint (addScaledActiveChunk regs) := by
  apply cmdWritesWithin_mono
    (Layout.residueScale_footprint_subset regs)
  exact addScaledActiveChunk_scaleWritesWithin_internal regs

theorem initializeBank_runs_internal
    {workTapeCount : ℕ} (tm : TM workTapeCount)
    (blockLength base : ℕ)
    (regs : NeighborhoodTrial.Registers controller) (store : Store)
    (hbase :
      store (Layout.residueScaleRegisters regs).bank.bank.base =
        base) :
    ∃ final,
      Runs (initializeBank regs) store final ∧
      final (Layout.residueScaleRegisters regs).bank.bank.word = 0 ∧
      final (Layout.residueScaleRegisters regs).bank.bank.one = 1 ∧
      final (Layout.residueScaleRegisters regs).bank.bank.base = base ∧
      final (Layout.residueScaleRegisters regs).bank.bank.basePred =
        base - 1 ∧
      final (Layout.residueScaleRegisters regs).bank.bank.indexCount =
        0 ∧
      NeighborhoodProgram.RepresentsResidueBank
        tm blockLength base
          (final
            (Layout.residueScaleRegisters regs).bank.bank.word)
          (zeroRegisters tm blockLength) := by
  let scale := Layout.residueScaleRegisters regs
  let final := Basic.execList
    [.imm scale.bank.bank.word 0,
      .imm scale.bank.bank.one 1,
      .sub scale.bank.bank.basePred
        scale.bank.bank.base scale.bank.bank.one,
      .imm scale.bank.bank.indexCount 0] store
  have hbase' : store scale.bank.bank.base = base := by
    simpa [scale] using hbase
  change store (scale.bank.index (2 : Fin 16)) = base at hbase'
  refine ⟨final, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simpa [initializeBank, initializeBankOps, scale, final] using
      basics_runs
        [.imm scale.bank.bank.word 0,
          .imm scale.bank.bank.one 1,
          .sub scale.bank.bank.basePred
            scale.bank.bank.base scale.bank.bank.one,
          .imm scale.bank.bank.indexCount 0] store
  · change final scale.bank.bank.word = 0
    simp [final, Basic.execList, Basic.exec,
      scale.bank.injective.eq_iff]
  · change final scale.bank.bank.one = 1
    simp [final, Basic.execList, Basic.exec,
      scale.bank.injective.eq_iff]
  · change final scale.bank.bank.base = base
    simpa [final, Basic.execList, Basic.exec,
      scale.bank.injective.eq_iff] using hbase'
  · change final scale.bank.bank.basePred = base - 1
    simp [final, Basic.execList, Basic.exec,
      scale.bank.injective.eq_iff, hbase']
  · change final scale.bank.bank.indexCount = 0
    simp [final, Basic.execList, Basic.exec,
      scale.bank.injective.eq_iff]
  · change NeighborhoodProgram.RepresentsResidueBank
      tm blockLength base (final scale.bank.bank.word)
        (zeroRegisters tm blockLength)
    rw [show final scale.bank.bank.word = 0 by
      simp [final, Basic.execList, Basic.exec,
        scale.bank.injective.eq_iff]]
    exact zero_represents_internal tm blockLength base

set_option linter.unusedSimpArgs false in
theorem scaleActiveRegister_runs_internal
    {workTapeCount : ℕ} (tm : TM workTapeCount)
    (blockLength scalar base word : ℕ)
    (original :
      NeighborhoodExecutableEvaluation.Residue.Registers
        tm blockLength)
    (register :
      Fin
        (NeighborhoodExecutableEvaluation.graphFanIn
          workTapeCount + 1))
    (regs : NeighborhoodTrial.Registers controller) (store : Store)
    (hbase : 0 < base)
    (hmodulus :
      0 < NeighborhoodExecutableEvaluation.modulus tm blockLength)
    (hmodulusBase :
      NeighborhoodExecutableEvaluation.modulus tm blockLength ≤ base)
    (hword :
      store (Layout.residueScaleRegisters regs).bank.bank.word = word)
    (hrep :
      NeighborhoodProgram.RepresentsResidueBank
        tm blockLength base word original)
    (hwordLt :
      word <
        base ^
          ((NeighborhoodExecutableEvaluation.graphFanIn
              workTapeCount + 1) *
            TreeEval.CookMertz.PrimeGrouped.Logarithmic.chunkCount
              (NeighborhoodExecutableEvaluation.payloadWidth
                tm blockLength)
              (NeighborhoodExecutableEvaluation.graphFanIn
                workTapeCount)))
    (hbaseValue :
      store (Layout.residueScaleRegisters regs).bank.bank.base = base)
    (hmodulusValue :
      store (Layout.residueScaleRegisters regs).bank.modulus =
        NeighborhoodExecutableEvaluation.modulus tm blockLength)
    (hmodulusPred :
      store (Layout.residueScaleRegisters regs).bank.modulusPred =
        NeighborhoodExecutableEvaluation.modulus tm blockLength - 1)
    (hscalar : store (Layout.scalar regs) = scalar)
    (hout : store (Layout.out regs) = register.val)
    (hchunkCount :
      store (Layout.chunkCount regs) =
        TreeEval.CookMertz.PrimeGrouped.Logarithmic.chunkCount
          (NeighborhoodExecutableEvaluation.payloadWidth tm blockLength)
          (NeighborhoodExecutableEvaluation.graphFanIn
            workTapeCount)) :
    ∃ final finalWord,
      Runs (scaleActiveRegister regs) store final ∧
      final (Layout.residueScaleRegisters regs).bank.bank.word =
        finalWord ∧
      NeighborhoodProgram.RepresentsResidueBank
        tm blockLength base finalWord
        (NeighborhoodExecutableEvaluation.Residue.scaleAt
          tm blockLength scalar original register) ∧
      finalWord <
        base ^
          ((NeighborhoodExecutableEvaluation.graphFanIn
              workTapeCount + 1) *
            TreeEval.CookMertz.PrimeGrouped.Logarithmic.chunkCount
              (NeighborhoodExecutableEvaluation.payloadWidth
                tm blockLength)
              (NeighborhoodExecutableEvaluation.graphFanIn
                workTapeCount)) ∧
      final
          (Layout.residueScaleRegisters regs).bank.bank.base =
        base ∧
      final
          (Layout.residueScaleRegisters regs).bank.bank.basePred =
        base - 1 ∧
      final
          (Layout.residueScaleRegisters regs).bank.bank.one =
        1 ∧
      final (Layout.residueScaleRegisters regs).bank.modulus =
        NeighborhoodExecutableEvaluation.modulus tm blockLength ∧
      final (Layout.residueScaleRegisters regs).bank.modulusPred =
        NeighborhoodExecutableEvaluation.modulus tm blockLength - 1 ∧
      final (Layout.residueScaleRegisters regs).bank.operand =
        scalar := by
  let scale := Layout.residueScaleRegisters regs
  let prepared :=
    Basic.execList (prepareScaleActiveOps regs) store
  have hword' : store scale.bank.bank.word = word := by
    simpa [scale] using hword
  have hbaseValue' : store scale.bank.bank.base = base := by
    simpa [scale] using hbaseValue
  have hmodulusValue' :
      store scale.bank.modulus =
        NeighborhoodExecutableEvaluation.modulus tm blockLength := by
    simpa [scale] using hmodulusValue
  have hmodulusPred' :
      store scale.bank.modulusPred =
        NeighborhoodExecutableEvaluation.modulus tm blockLength - 1 := by
    simpa [scale] using hmodulusPred
  have hscaleScalar (slot : Fin 17) :
      scale.index slot ≠ Layout.scalar regs := by
    simpa [scale] using scale_index_ne_scalar regs slot
  have hscaleChunkCount (slot : Fin 17) :
      scale.index slot ≠ Layout.chunkCount regs := by
    simpa [scale] using scale_index_ne_chunkCount regs slot
  have hscaleOut (slot : Fin 17) :
      scale.index slot ≠ Layout.out regs := by
    simpa [scale] using scale_index_ne_out regs slot
  have hbankScalar (slot : Fin 16) :
      scale.bank.index slot ≠ Layout.scalar regs := by
    exact hscaleScalar
      (NeighborhoodProgram.ResidueScaleRegisters.bankSlot slot)
  have hbankChunkCount (slot : Fin 16) :
      scale.bank.index slot ≠ Layout.chunkCount regs := by
    exact hscaleChunkCount
      (NeighborhoodProgram.ResidueScaleRegisters.bankSlot slot)
  have hbankOut (slot : Fin 16) :
      scale.bank.index slot ≠ Layout.out regs := by
    exact hscaleOut
      (NeighborhoodProgram.ResidueScaleRegisters.bankSlot slot)
  have hremainingBank (slot : Fin 16) :
      scale.remaining ≠ scale.bank.index slot := by
    intro heq
    have hslot := scale.injective heq
    have hval := congrArg Fin.val hslot
    simp [NeighborhoodProgram.ResidueScaleRegisters.bankSlot] at hval
    omega
  have hremainingScalar :
      scale.remaining ≠ Layout.scalar regs :=
    hscaleScalar 16
  have hremainingChunkCount :
      scale.remaining ≠ Layout.chunkCount regs :=
    hscaleChunkCount 16
  have hremainingOut :
      scale.remaining ≠ Layout.out regs :=
    hscaleOut 16
  have hremainingBankLayout (slot : Fin 16) :
      (Layout.residueScaleRegisters regs).remaining ≠
        (Layout.residueScaleRegisters regs).bank.index slot := by
    simpa [scale] using hremainingBank slot
  have hbankRemainingLayout (slot : Fin 16) :
      (Layout.residueScaleRegisters regs).bank.index slot ≠
        (Layout.residueScaleRegisters regs).remaining :=
    (hremainingBankLayout slot).symm
  have hscalarBank (slot : Fin 16) :
      Layout.scalar regs ≠ scale.bank.index slot :=
    (hbankScalar slot).symm
  have hchunkCountBank (slot : Fin 16) :
      Layout.chunkCount regs ≠ scale.bank.index slot :=
    (hbankChunkCount slot).symm
  have houtBank (slot : Fin 16) :
      Layout.out regs ≠ scale.bank.index slot :=
    (hbankOut slot).symm
  have hscalarRemaining :
      Layout.scalar regs ≠ scale.remaining :=
    hremainingScalar.symm
  have hchunkCountRemaining :
      Layout.chunkCount regs ≠ scale.remaining :=
    hremainingChunkCount.symm
  have houtRemaining :
      Layout.out regs ≠ scale.remaining :=
    hremainingOut.symm
  have hprepare :
      Runs (prepareScaleActive regs) store prepared := by
    simpa [prepareScaleActive, prepared] using
      basics_runs (prepareScaleActiveOps regs) store
  have hpreparedWord :
      prepared scale.bank.bank.word = word := by
    simpa [prepared, prepareScaleActiveOps, Basic.execList, scale,
      Basic.exec, NeighborhoodProgram.ResidueBankRegisters.operand,
      NeighborhoodProgram.ResidueBankRegisters.modulus,
      NeighborhoodProgram.ResidueBankRegisters.modulusPred,
      NeighborhoodProgram.ResidueScaleRegisters.remaining,
      scale.bank.injective.eq_iff, hbankScalar,
      hbankChunkCount, hbankOut, hremainingBankLayout,
      hbankRemainingLayout] using hword'
  have hpreparedBase :
      prepared scale.bank.bank.base = base := by
    simpa [prepared, prepareScaleActiveOps, Basic.execList, scale,
      Basic.exec, NeighborhoodProgram.ResidueBankRegisters.operand,
      NeighborhoodProgram.ResidueBankRegisters.modulus,
      NeighborhoodProgram.ResidueBankRegisters.modulusPred,
      NeighborhoodProgram.ResidueScaleRegisters.remaining,
      scale.bank.injective.eq_iff, hbankScalar,
      hbankChunkCount, hbankOut, hremainingBankLayout,
      hbankRemainingLayout] using hbaseValue'
  have hpreparedBasePred :
      prepared scale.bank.bank.basePred = base - 1 := by
    have hpred := congrArg (fun value => value - 1) hbaseValue
    simpa [prepared, prepareScaleActiveOps, Basic.execList, scale,
      Basic.exec, NeighborhoodProgram.ResidueBankRegisters.operand,
      NeighborhoodProgram.ResidueBankRegisters.modulus,
      NeighborhoodProgram.ResidueBankRegisters.modulusPred,
      NeighborhoodProgram.ResidueScaleRegisters.remaining,
      scale.bank.injective.eq_iff, hbankScalar,
      hbankChunkCount, hbankOut, hremainingBankLayout,
      hbankRemainingLayout] using hpred
  have hpreparedOne :
      prepared scale.bank.bank.one = 1 := by
    simp [prepared, prepareScaleActiveOps, Basic.execList, scale,
      Basic.exec, NeighborhoodProgram.ResidueBankRegisters.operand,
      NeighborhoodProgram.ResidueBankRegisters.modulus,
      NeighborhoodProgram.ResidueBankRegisters.modulusPred,
      NeighborhoodProgram.ResidueScaleRegisters.remaining,
      scale.bank.injective.eq_iff, hbankScalar,
      hbankChunkCount, hbankOut, hremainingBankLayout,
      hbankRemainingLayout]
  have hpreparedIndex :
      prepared scale.bank.bank.indexCount =
        register.val *
          TreeEval.CookMertz.PrimeGrouped.Logarithmic.chunkCount
            (NeighborhoodExecutableEvaluation.payloadWidth
              tm blockLength)
            (NeighborhoodExecutableEvaluation.graphFanIn
              workTapeCount) := by
    simp [prepared, prepareScaleActiveOps, Basic.execList, scale,
      Basic.exec, NeighborhoodProgram.ResidueBankRegisters.operand,
      NeighborhoodProgram.ResidueBankRegisters.modulus,
      NeighborhoodProgram.ResidueBankRegisters.modulusPred,
      NeighborhoodProgram.ResidueScaleRegisters.remaining,
      scale.bank.injective.eq_iff, hbankScalar,
      hbankChunkCount, hbankOut, hremainingBankLayout,
      hbankRemainingLayout, houtBank, hchunkCountBank,
      houtRemaining, hchunkCountRemaining, hout, hchunkCount]
  have hpreparedModulus :
      prepared scale.bank.modulus =
        NeighborhoodExecutableEvaluation.modulus tm blockLength := by
    simpa [prepared, prepareScaleActiveOps, Basic.execList, scale,
      Basic.exec, NeighborhoodProgram.ResidueBankRegisters.operand,
      NeighborhoodProgram.ResidueBankRegisters.modulus,
      NeighborhoodProgram.ResidueBankRegisters.modulusPred,
      NeighborhoodProgram.ResidueScaleRegisters.remaining,
      scale.bank.injective.eq_iff, hbankScalar,
      hbankChunkCount, hbankOut, hremainingBankLayout,
      hbankRemainingLayout] using
        hmodulusValue'
  have hpreparedModulusPred :
      prepared scale.bank.modulusPred =
        NeighborhoodExecutableEvaluation.modulus tm blockLength - 1 := by
    simpa [prepared, prepareScaleActiveOps, Basic.execList, scale,
      Basic.exec, NeighborhoodProgram.ResidueBankRegisters.operand,
      NeighborhoodProgram.ResidueBankRegisters.modulus,
      NeighborhoodProgram.ResidueBankRegisters.modulusPred,
      NeighborhoodProgram.ResidueScaleRegisters.remaining,
      scale.bank.injective.eq_iff, hbankScalar,
      hbankChunkCount, hbankOut, hremainingBankLayout,
      hbankRemainingLayout] using
        hmodulusPred'
  have hpreparedOperand :
      prepared scale.bank.operand = scalar := by
    simp [prepared, prepareScaleActiveOps, Basic.execList, scale,
      Basic.exec, NeighborhoodProgram.ResidueBankRegisters.operand,
      NeighborhoodProgram.ResidueBankRegisters.modulus,
      NeighborhoodProgram.ResidueBankRegisters.modulusPred,
      NeighborhoodProgram.ResidueScaleRegisters.remaining,
      scale.bank.injective.eq_iff, hbankScalar,
      hbankChunkCount, hbankOut, hremainingBankLayout,
      hbankRemainingLayout, hscalarBank, hscalarRemaining, hscalar]
  have hpreparedRemaining :
      prepared scale.remaining =
        TreeEval.CookMertz.PrimeGrouped.Logarithmic.chunkCount
          (NeighborhoodExecutableEvaluation.payloadWidth tm blockLength)
          (NeighborhoodExecutableEvaluation.graphFanIn
            workTapeCount) := by
    simp [prepared, prepareScaleActiveOps, Basic.execList, scale,
      Basic.exec, NeighborhoodProgram.ResidueBankRegisters.operand,
      NeighborhoodProgram.ResidueBankRegisters.modulus,
      NeighborhoodProgram.ResidueBankRegisters.modulusPred,
      NeighborhoodProgram.ResidueScaleRegisters.remaining,
      scale.bank.injective.eq_iff, hbankScalar,
      hbankChunkCount, hbankOut, hremainingBankLayout,
      hbankRemainingLayout, hchunkCountBank, hchunkCountRemaining,
      hremainingScalar, hremainingChunkCount, hremainingOut,
      hchunkCount]
  obtain ⟨final, finalWord, hloop, hfinalWord, hfinalRep,
      hfinalWordLt, _hfinalSelected, _hfinalOther,
      _hfinalRemaining, _hfinalIndex, hfinalBase,
      hfinalBasePred, hfinalOne, hfinalModulus,
      hfinalModulusPred, hfinalOperand⟩ :=
    NeighborhoodProgram.bankScaleRegister_runs tm blockLength scalar
      base word original register scale prepared hbase hmodulus
      hmodulusBase hpreparedWord hrep hwordLt hpreparedBase
      hpreparedBasePred hpreparedOne hpreparedIndex hpreparedModulus
      hpreparedModulusPred hpreparedOperand hpreparedRemaining
  refine ⟨final, finalWord, ?_, ?_, hfinalRep, hfinalWordLt,
    ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simpa [scaleActiveRegister, scale] using
      Runs.seq hprepare hloop
  · simpa [scale] using hfinalWord
  · simpa [scale] using hfinalBase
  · simpa [scale] using hfinalBasePred
  · simpa [scale] using hfinalOne
  · simpa [scale] using hfinalModulus
  · simpa [scale] using hfinalModulusPred
  · simpa [scale] using hfinalOperand

theorem scaleActiveRegister_invariantRuns_internal
    {workTapeCount : ℕ} (tm : TM workTapeCount)
    (blockLength scalar base word : ℕ)
    (original :
      NeighborhoodExecutableEvaluation.Residue.Registers
        tm blockLength)
    (register :
      Fin
        (NeighborhoodExecutableEvaluation.graphFanIn
          workTapeCount + 1))
    (regs : NeighborhoodTrial.Registers controller)
    (allowed : Finset ℕ) (bound : ℕ) (store : Store)
    (hbase : 0 < base)
    (hmodulus :
      0 < NeighborhoodExecutableEvaluation.modulus tm blockLength)
    (hmodulusBase :
      NeighborhoodExecutableEvaluation.modulus tm blockLength ≤ base)
    (hword :
      store (Layout.residueScaleRegisters regs).bank.bank.word = word)
    (hrep :
      NeighborhoodProgram.RepresentsResidueBank
        tm blockLength base word original)
    (hwordLt :
      word <
        base ^
          ((NeighborhoodExecutableEvaluation.graphFanIn
              workTapeCount + 1) *
            TreeEval.CookMertz.PrimeGrouped.Logarithmic.chunkCount
              (NeighborhoodExecutableEvaluation.payloadWidth
                tm blockLength)
              (NeighborhoodExecutableEvaluation.graphFanIn
                workTapeCount)))
    (hbaseValue :
      store (Layout.residueScaleRegisters regs).bank.bank.base = base)
    (hmodulusValue :
      store (Layout.residueScaleRegisters regs).bank.modulus =
        NeighborhoodExecutableEvaluation.modulus tm blockLength)
    (hmodulusPred :
      store (Layout.residueScaleRegisters regs).bank.modulusPred =
        NeighborhoodExecutableEvaluation.modulus tm blockLength - 1)
    (hscalar : store (Layout.scalar regs) = scalar)
    (hout : store (Layout.out regs) = register.val)
    (hchunkCount :
      store (Layout.chunkCount regs) =
        TreeEval.CookMertz.PrimeGrouped.Logarithmic.chunkCount
          (NeighborhoodExecutableEvaluation.payloadWidth tm blockLength)
          (NeighborhoodExecutableEvaluation.graphFanIn
            workTapeCount))
    (hpackedBound :
      base ^
          ((NeighborhoodExecutableEvaluation.graphFanIn
              workTapeCount + 1) *
            TreeEval.CookMertz.PrimeGrouped.Logarithmic.chunkCount
              (NeighborhoodExecutableEvaluation.payloadWidth
                tm blockLength)
              (NeighborhoodExecutableEvaluation.graphFanIn
                workTapeCount)) ≤
        bound)
    (hbaseBound : base ≤ bound)
    (hdigitCountBound :
      (NeighborhoodExecutableEvaluation.graphFanIn
          workTapeCount + 1) *
          TreeEval.CookMertz.PrimeGrouped.Logarithmic.chunkCount
            (NeighborhoodExecutableEvaluation.payloadWidth
              tm blockLength)
            (NeighborhoodExecutableEvaluation.graphFanIn
              workTapeCount) ≤
        bound)
    (hscalarProductBound : base * scalar ≤ bound)
    (hindexProductBound :
      register.val *
          TreeEval.CookMertz.PrimeGrouped.Logarithmic.chunkCount
            (NeighborhoodExecutableEvaluation.payloadWidth
              tm blockLength)
            (NeighborhoodExecutableEvaluation.graphFanIn
              workTapeCount) ≤
        bound)
    (hstore :
      NeighborhoodProgram.ValuesWithin allowed bound store) :
    ∃ final finalWord steps,
      InvariantRuns
        (NeighborhoodProgram.ValuesWithin allowed bound)
        (scaleActiveRegister regs) store final steps ∧
      final (Layout.residueScaleRegisters regs).bank.bank.word =
        finalWord ∧
      NeighborhoodProgram.RepresentsResidueBank
        tm blockLength base finalWord
        (NeighborhoodExecutableEvaluation.Residue.scaleAt
          tm blockLength scalar original register) := by
  let scale := Layout.residueScaleRegisters regs
  let chunks :=
    TreeEval.CookMertz.PrimeGrouped.Logarithmic.chunkCount
      (NeighborhoodExecutableEvaluation.payloadWidth tm blockLength)
      (NeighborhoodExecutableEvaluation.graphFanIn workTapeCount)
  let afterOne :=
    (Basic.imm scale.bank.bank.one 1).exec store
  let afterBasePred :=
    (Basic.sub scale.bank.bank.basePred
      scale.bank.bank.base scale.bank.bank.one).exec afterOne
  let afterOperandZero :=
    (Basic.imm scale.bank.operand 0).exec afterBasePred
  let afterOperand :=
    (Basic.add scale.bank.operand
      (Layout.scalar regs) scale.bank.operand).exec afterOperandZero
  let afterRemainingZero :=
    (Basic.imm scale.remaining 0).exec afterOperand
  let afterRemaining :=
    (Basic.add scale.remaining
      (Layout.chunkCount regs) scale.remaining).exec
        afterRemainingZero
  let prepared :=
    (Basic.mul scale.bank.bank.indexCount
      (Layout.out regs) (Layout.chunkCount regs)).exec
        afterRemaining
  have hbankScalar (slot : Fin 16) :
      scale.bank.index slot ≠ Layout.scalar regs := by
    exact scale_index_ne_scalar regs
      (NeighborhoodProgram.ResidueScaleRegisters.bankSlot slot)
  have hbankChunkCount (slot : Fin 16) :
      scale.bank.index slot ≠ Layout.chunkCount regs := by
    exact scale_index_ne_chunkCount regs
      (NeighborhoodProgram.ResidueScaleRegisters.bankSlot slot)
  have hbankOut (slot : Fin 16) :
      scale.bank.index slot ≠ Layout.out regs := by
    exact scale_index_ne_out regs
      (NeighborhoodProgram.ResidueScaleRegisters.bankSlot slot)
  have hremainingBank (slot : Fin 16) :
      scale.remaining ≠ scale.bank.index slot := by
    intro heq
    have hslot := scale.injective heq
    have hval := congrArg Fin.val hslot
    simp [NeighborhoodProgram.ResidueScaleRegisters.bankSlot] at hval
    omega
  have hbankRemaining (slot : Fin 16) :
      scale.bank.index slot ≠ scale.remaining :=
    (hremainingBank slot).symm
  have hscalarBank (slot : Fin 16) :
      Layout.scalar regs ≠ scale.bank.index slot :=
    (hbankScalar slot).symm
  have hchunkCountBank (slot : Fin 16) :
      Layout.chunkCount regs ≠ scale.bank.index slot :=
    (hbankChunkCount slot).symm
  have houtBank (slot : Fin 16) :
      Layout.out regs ≠ scale.bank.index slot :=
    (hbankOut slot).symm
  have hremainingScalar :
      scale.remaining ≠ Layout.scalar regs :=
    scale_index_ne_scalar regs 16
  have hremainingChunkCount :
      scale.remaining ≠ Layout.chunkCount regs :=
    scale_index_ne_chunkCount regs 16
  have hremainingOut :
      scale.remaining ≠ Layout.out regs :=
    scale_index_ne_out regs 16
  have hscalarRemaining :
      Layout.scalar regs ≠ scale.remaining :=
    hremainingScalar.symm
  have hchunkCountRemaining :
      Layout.chunkCount regs ≠ scale.remaining :=
    hremainingChunkCount.symm
  have houtRemaining :
      Layout.out regs ≠ scale.remaining :=
    hremainingOut.symm
  have honeBound : 1 ≤ bound := by
    exact le_trans (by omega : 1 ≤ base) hbaseBound
  have hbasePredBound : base - 1 ≤ bound :=
    le_trans (Nat.sub_le base 1) hbaseBound
  have hscalarBound : scalar ≤ bound :=
    le_trans (Nat.le_mul_of_pos_left scalar hbase)
      hscalarProductBound
  have hchunksBound : chunks ≤ bound := by
    apply le_trans
      (Nat.le_mul_of_pos_left chunks
        (by omega :
          0 <
            NeighborhoodExecutableEvaluation.graphFanIn
              workTapeCount + 1))
    simpa [chunks] using hdigitCountBound
  have hafterOne :
      NeighborhoodProgram.ValuesWithin allowed bound afterOne := by
    simpa [afterOne, Basic.exec] using
      valuesWithin_update allowed bound
        scale.bank.bank.one 1 store hstore honeBound
  have hafterOneBase :
      afterOne scale.bank.bank.base = base := by
    simpa [afterOne, Basic.exec, scale.bank.injective.eq_iff,
      scale] using hbaseValue
  have hafterOneOne :
      afterOne scale.bank.bank.one = 1 := by
    simp [afterOne, Basic.exec]
  have hafterBasePred :
      NeighborhoodProgram.ValuesWithin allowed bound
        afterBasePred := by
    apply valuesWithin_update allowed bound
      scale.bank.bank.basePred
      (afterOne scale.bank.bank.base -
        afterOne scale.bank.bank.one)
      afterOne hafterOne
    rw [hafterOneBase, hafterOneOne]
    exact hbasePredBound
  have hafterOperandZero :
      NeighborhoodProgram.ValuesWithin allowed bound
        afterOperandZero := by
    simpa [afterOperandZero, Basic.exec] using
      valuesWithin_update allowed bound
        scale.bank.operand 0 afterBasePred hafterBasePred
        (by omega)
  have hoperandZero :
      afterOperandZero scale.bank.operand = 0 := by
    simp [afterOperandZero, Basic.exec,
      NeighborhoodProgram.ResidueBankRegisters.operand]
  have hscalarValue :
      afterOperandZero (Layout.scalar regs) = scalar := by
    simp [afterOperandZero, afterBasePred, afterOne, Basic.exec,
      NeighborhoodProgram.ResidueBankRegisters.operand,
      scale.bank.injective.eq_iff, hscalarBank, hscalar]
  have hafterOperand :
      NeighborhoodProgram.ValuesWithin allowed bound afterOperand := by
    apply valuesWithin_update allowed bound scale.bank.operand
      (afterOperandZero (Layout.scalar regs) +
        afterOperandZero scale.bank.operand)
      afterOperandZero hafterOperandZero
    rw [hscalarValue, hoperandZero, Nat.add_zero]
    exact hscalarBound
  have hafterRemainingZero :
      NeighborhoodProgram.ValuesWithin allowed bound
        afterRemainingZero := by
    simpa [afterRemainingZero, Basic.exec] using
      valuesWithin_update allowed bound scale.remaining 0
        afterOperand hafterOperand (by omega)
  have hremainingZero :
      afterRemainingZero scale.remaining = 0 := by
    simp [afterRemainingZero, Basic.exec]
  have hchunkCountValue :
      afterRemainingZero (Layout.chunkCount regs) = chunks := by
    simp [afterRemainingZero, afterOperand, afterOperandZero,
      afterBasePred, afterOne, Basic.exec,
      NeighborhoodProgram.ResidueBankRegisters.operand,
      NeighborhoodProgram.ResidueScaleRegisters.remaining,
      scale.bank.injective.eq_iff, hchunkCountBank,
      hchunkCountRemaining, hchunkCount, chunks]
  have hafterRemaining :
      NeighborhoodProgram.ValuesWithin allowed bound
        afterRemaining := by
    apply valuesWithin_update allowed bound scale.remaining
      (afterRemainingZero (Layout.chunkCount regs) +
        afterRemainingZero scale.remaining)
      afterRemainingZero hafterRemainingZero
    rw [hchunkCountValue, hremainingZero, Nat.add_zero]
    exact hchunksBound
  have houtValue :
      afterRemaining (Layout.out regs) = register.val := by
    simp [afterRemaining, afterRemainingZero, afterOperand,
      afterOperandZero, afterBasePred, afterOne, Basic.exec,
      NeighborhoodProgram.ResidueBankRegisters.operand,
      NeighborhoodProgram.ResidueScaleRegisters.remaining,
      scale.bank.injective.eq_iff, houtBank, houtRemaining, hout]
  have hchunkCountValue' :
      afterRemaining (Layout.chunkCount regs) = chunks := by
    simp [afterRemaining, afterRemainingZero, afterOperand,
      afterOperandZero, afterBasePred, afterOne, Basic.exec,
      NeighborhoodProgram.ResidueBankRegisters.operand,
      NeighborhoodProgram.ResidueScaleRegisters.remaining,
      scale.bank.injective.eq_iff, hchunkCountBank,
      hchunkCountRemaining, hchunkCount, chunks]
  have hpreparedWithin :
      NeighborhoodProgram.ValuesWithin allowed bound prepared := by
    apply valuesWithin_update allowed bound
      scale.bank.bank.indexCount
      (afterRemaining (Layout.out regs) *
        afterRemaining (Layout.chunkCount regs))
      afterRemaining hafterRemaining
    rw [houtValue, hchunkCountValue']
    simpa [chunks] using hindexProductBound
  have hprefix :
      InvariantRuns
        (NeighborhoodProgram.ValuesWithin allowed bound)
        (prepareScaleActive regs) store prepared 7 := by
    simpa [prepareScaleActive, prepareScaleActiveOps, Cmd.basics,
      Cmd.seqList, scale, afterOne, afterBasePred,
      afterOperandZero, afterOperand, afterRemainingZero,
      afterRemaining, prepared] using
      InvariantRuns.seq
        (InvariantRuns.basic
          (Basic.imm scale.bank.bank.one 1) store
          hstore hafterOne)
        (InvariantRuns.seq
          (InvariantRuns.basic
            (Basic.sub scale.bank.bank.basePred
              scale.bank.bank.base scale.bank.bank.one)
            afterOne hafterOne hafterBasePred)
          (InvariantRuns.seq
            (InvariantRuns.basic
              (Basic.imm scale.bank.operand 0)
              afterBasePred hafterBasePred hafterOperandZero)
            (InvariantRuns.seq
              (InvariantRuns.basic
                (Basic.add scale.bank.operand
                  (Layout.scalar regs) scale.bank.operand)
                afterOperandZero hafterOperandZero hafterOperand)
              (InvariantRuns.seq
                (InvariantRuns.basic
                  (Basic.imm scale.remaining 0)
                  afterOperand hafterOperand hafterRemainingZero)
                (InvariantRuns.seq
                  (InvariantRuns.basic
                    (Basic.add scale.remaining
                      (Layout.chunkCount regs) scale.remaining)
                    afterRemainingZero hafterRemainingZero
                    hafterRemaining)
                  (InvariantRuns.basic
                    (Basic.mul scale.bank.bank.indexCount
                      (Layout.out regs) (Layout.chunkCount regs))
                    afterRemaining hafterRemaining
                    hpreparedWithin))))))
  have hpreparedWord :
      prepared scale.bank.bank.word = word := by
    simpa [prepared, afterRemaining, afterRemainingZero,
      afterOperand, afterOperandZero, afterBasePred, afterOne,
      Basic.exec, NeighborhoodProgram.ResidueBankRegisters.operand,
      NeighborhoodProgram.ResidueScaleRegisters.remaining,
      scale.bank.injective.eq_iff, hbankRemaining] using hword
  have hpreparedBase :
      prepared scale.bank.bank.base = base := by
    simpa [prepared, afterRemaining, afterRemainingZero,
      afterOperand, afterOperandZero, afterBasePred, afterOne,
      Basic.exec, NeighborhoodProgram.ResidueBankRegisters.operand,
      NeighborhoodProgram.ResidueScaleRegisters.remaining,
      scale.bank.injective.eq_iff, hbankRemaining] using hbaseValue
  have hpreparedBasePred :
      prepared scale.bank.bank.basePred = base - 1 := by
    have hpred := congrArg (fun value => value - 1) hbaseValue
    simpa [prepared, afterRemaining, afterRemainingZero,
      afterOperand, afterOperandZero, afterBasePred, afterOne,
      Basic.exec, NeighborhoodProgram.ResidueBankRegisters.operand,
      NeighborhoodProgram.ResidueScaleRegisters.remaining,
      scale.bank.injective.eq_iff, hbankRemaining] using hpred
  have hpreparedOne :
      prepared scale.bank.bank.one = 1 := by
    simp [prepared, afterRemaining, afterRemainingZero,
      afterOperand, afterOperandZero, afterBasePred, afterOne,
      Basic.exec, NeighborhoodProgram.ResidueBankRegisters.operand,
      NeighborhoodProgram.ResidueScaleRegisters.remaining,
      scale.bank.injective.eq_iff, hbankRemaining]
  have hpreparedIndex :
      prepared scale.bank.bank.indexCount = register.val * chunks := by
    simp [prepared, Basic.exec, houtValue, hchunkCountValue']
  have hpreparedModulus :
      prepared scale.bank.modulus =
        NeighborhoodExecutableEvaluation.modulus tm blockLength := by
    simpa [prepared, afterRemaining, afterRemainingZero,
      afterOperand, afterOperandZero, afterBasePred, afterOne,
      Basic.exec, NeighborhoodProgram.ResidueBankRegisters.operand,
      NeighborhoodProgram.ResidueBankRegisters.modulus,
      NeighborhoodProgram.ResidueScaleRegisters.remaining,
      scale.bank.injective.eq_iff, hbankRemaining] using
        hmodulusValue
  have hpreparedModulusPred :
      prepared scale.bank.modulusPred =
        NeighborhoodExecutableEvaluation.modulus tm blockLength - 1 := by
    simpa [prepared, afterRemaining, afterRemainingZero,
      afterOperand, afterOperandZero, afterBasePred, afterOne,
      Basic.exec, NeighborhoodProgram.ResidueBankRegisters.operand,
      NeighborhoodProgram.ResidueBankRegisters.modulusPred,
      NeighborhoodProgram.ResidueScaleRegisters.remaining,
      scale.bank.injective.eq_iff, hbankRemaining] using hmodulusPred
  have hpreparedOperand :
      prepared scale.bank.operand = scalar := by
    simp [prepared, afterRemaining, afterRemainingZero,
      afterOperand, Basic.exec,
      NeighborhoodProgram.ResidueBankRegisters.operand,
      NeighborhoodProgram.ResidueScaleRegisters.remaining,
      scale.bank.injective.eq_iff, hbankRemaining, hscalarValue,
      hoperandZero]
  have hpreparedRemaining :
      prepared scale.remaining = chunks := by
    have hremainingValue :
        afterRemaining scale.remaining = chunks := by
      simp [afterRemaining, Basic.exec, hchunkCountValue,
        hremainingZero]
    change Function.update afterRemaining
      scale.bank.bank.indexCount
      (afterRemaining (Layout.out regs) *
        afterRemaining (Layout.chunkCount regs))
      scale.remaining = chunks
    rw [Function.update_of_ne]
    · exact hremainingValue
    · simpa using hremainingBank (8 : Fin 16)
  obtain ⟨final, finalWord, loopSteps, hloop, hfinalWord,
      hfinalRep, _⟩ :=
    NeighborhoodProgram.bankScaleRegister_invariantRuns
      tm blockLength scalar base word original register scale
      allowed bound prepared hbase hmodulus hmodulusBase
      hpreparedWord hrep hwordLt hpreparedBase hpreparedBasePred
      hpreparedOne hpreparedIndex hpreparedModulus
      hpreparedModulusPred hpreparedOperand hpreparedRemaining
      hpackedBound hbaseBound hdigitCountBound
      hscalarProductBound hpreparedWithin
  refine ⟨final, finalWord, 7 + loopSteps, ?_, ?_, hfinalRep⟩
  · simpa [scaleActiveRegister, scale] using
      InvariantRuns.seq hprefix hloop
  · simpa [scale] using hfinalWord

set_option linter.unusedSimpArgs false in
theorem addScaledActiveChunk_runs_internal
    {workTapeCount : ℕ} (tm : TM workTapeCount)
    (blockLength scalar base word value : ℕ)
    (original :
      NeighborhoodExecutableEvaluation.Residue.Registers
        tm blockLength)
    (register :
      Fin
        (NeighborhoodExecutableEvaluation.graphFanIn
          workTapeCount + 1))
    (chunk :
      Fin
        (TreeEval.CookMertz.PrimeGrouped.Logarithmic.chunkCount
          (NeighborhoodExecutableEvaluation.payloadWidth tm blockLength)
          (NeighborhoodExecutableEvaluation.graphFanIn
            workTapeCount)))
    (regs : NeighborhoodTrial.Registers controller) (store : Store)
    (hbase : 0 < base)
    (hmodulus :
      0 < NeighborhoodExecutableEvaluation.modulus tm blockLength)
    (hmodulusBase :
      NeighborhoodExecutableEvaluation.modulus tm blockLength ≤ base)
    (hword :
      store (Layout.residueScaleRegisters regs).bank.bank.word = word)
    (hrep :
      NeighborhoodProgram.RepresentsResidueBank
        tm blockLength base word original)
    (hbaseValue :
      store (Layout.residueScaleRegisters regs).bank.bank.base = base)
    (hmodulusValue :
      store (Layout.residueScaleRegisters regs).bank.modulus =
        NeighborhoodExecutableEvaluation.modulus tm blockLength)
    (hmodulusPred :
      store (Layout.residueScaleRegisters regs).bank.modulusPred =
        NeighborhoodExecutableEvaluation.modulus tm blockLength - 1)
    (hvalue :
      store (Layout.residueScaleRegisters regs).bank.operand = value)
    (hscalar : store (Layout.scalar regs) = scalar)
    (hout : store (Layout.out regs) = register.val)
    (hchunkCount :
      store (Layout.chunkCount regs) =
        TreeEval.CookMertz.PrimeGrouped.Logarithmic.chunkCount
          (NeighborhoodExecutableEvaluation.payloadWidth tm blockLength)
          (NeighborhoodExecutableEvaluation.graphFanIn
            workTapeCount))
    (hcursor : store (Layout.codecScratch regs) = chunk.val) :
    ∃ final,
      Runs (addScaledActiveChunk regs) store final ∧
      NeighborhoodProgram.RepresentsResidueBank
        tm blockLength base
        (final
          (Layout.residueScaleRegisters regs).bank.bank.word)
        (NeighborhoodProgram.updateResidueCoordinate
          tm blockLength original register chunk
          (NeighborhoodProgram.ResidueBankOp.add.apply
            (NeighborhoodExecutableEvaluation.modulus tm blockLength)
            (original register chunk)
            ((value * scalar) %
              NeighborhoodExecutableEvaluation.modulus
                tm blockLength))) ∧
      final
          (Layout.residueScaleRegisters regs).bank.bank.word =
        NeighborhoodProgram.replaceAt base word
          (NeighborhoodProgram.residueBankIndex
            tm blockLength register chunk)
          (NeighborhoodProgram.ResidueBankOp.add.apply
            (NeighborhoodExecutableEvaluation.modulus tm blockLength)
            (original register chunk)
            ((value * scalar) %
              NeighborhoodExecutableEvaluation.modulus
                tm blockLength)) ∧
      final
          (Layout.residueScaleRegisters regs).bank.bank.base =
        base ∧
      final (Layout.residueScaleRegisters regs).bank.modulus =
        NeighborhoodExecutableEvaluation.modulus tm blockLength ∧
      final (Layout.residueScaleRegisters regs).bank.modulusPred =
        NeighborhoodExecutableEvaluation.modulus tm blockLength - 1 := by
  let bank := (Layout.residueScaleRegisters regs).bank
  let modulus :=
    NeighborhoodExecutableEvaluation.modulus tm blockLength
  let scaled := (value * scalar) % modulus
  let reduced :=
    RuntimeArithmetic.reduceResultStore bank.reduceRegisters
      scaled store
  let afterClear :=
    (Basic.imm bank.operand 0).exec reduced
  let copied :=
    (Basic.add bank.operand bank.bank.replacement
      bank.operand).exec afterClear
  let prepared :=
    Basic.execList (prepareActiveChunkIndexOps regs) copied
  have hbankScalar (slot : Fin 16) :
      bank.index slot ≠ Layout.scalar regs := by
    exact scale_index_ne_scalar regs
      (NeighborhoodProgram.ResidueScaleRegisters.bankSlot slot)
  have hbankChunkCount (slot : Fin 16) :
      bank.index slot ≠ Layout.chunkCount regs := by
    exact scale_index_ne_chunkCount regs
      (NeighborhoodProgram.ResidueScaleRegisters.bankSlot slot)
  have hbankOut (slot : Fin 16) :
      bank.index slot ≠ Layout.out regs := by
    exact scale_index_ne_out regs
      (NeighborhoodProgram.ResidueScaleRegisters.bankSlot slot)
  have hbankCursor (slot : Fin 16) :
      bank.index slot ≠ Layout.codecScratch regs := by
    exact scale_index_ne_codecScratch regs
      (NeighborhoodProgram.ResidueScaleRegisters.bankSlot slot)
  have houtBank (slot : Fin 16) :
      Layout.out regs ≠ bank.index slot :=
    (hbankOut slot).symm
  have hchunkCountBank (slot : Fin 16) :
      Layout.chunkCount regs ≠ bank.index slot :=
    (hbankChunkCount slot).symm
  have hcursorBank (slot : Fin 16) :
      Layout.codecScratch regs ≠ bank.index slot :=
    (hbankCursor slot).symm
  have hvalue' : store bank.operand = value := by
    simpa [bank] using hvalue
  have hmul :
      Runs
        (RuntimeArithmetic.mulMod bank.reduceRegisters
          bank.operand (Layout.scalar regs))
        store reduced := by
    simpa [reduced, scaled, modulus, hvalue', hscalar] using
      RuntimeArithmetic.mulMod_runs bank.reduceRegisters
        bank.operand (Layout.scalar regs) store modulus hmodulus
        (by simpa [bank, modulus] using hmodulusValue)
        (by simpa [bank, modulus] using hmodulusPred)
  have hcopy :
      Runs (copy bank.operand bank.bank.replacement)
        reduced copied := by
    simpa [copy, afterClear, copied] using
      Runs.seq
        (Runs.basic (Basic.imm bank.operand 0) reduced)
        (Runs.basic
          (Basic.add bank.operand bank.bank.replacement
            bank.operand) afterClear)
  have hprepare :
      Runs (prepareActiveChunkIndex regs) copied prepared := by
    simpa [prepareActiveChunkIndex, prepared] using
      basics_runs (prepareActiveChunkIndexOps regs) copied
  have hpreparedWord :
      prepared bank.bank.word = word := by
    simpa [prepared, prepareActiveChunkIndexOps, Basic.execList, bank,
      copied, afterClear, reduced, Basic.exec,
      RuntimeArithmetic.reduceResultStore,
      NeighborhoodProgram.ResidueBankRegisters.reduceRegisters,
      NeighborhoodProgram.ResidueBankRegisters.operand,
      bank.injective.eq_iff] using hword
  have hpreparedBase :
      prepared bank.bank.base = base := by
    simpa [prepared, prepareActiveChunkIndexOps, Basic.execList, bank,
      copied, afterClear, reduced, Basic.exec,
      RuntimeArithmetic.reduceResultStore,
      NeighborhoodProgram.ResidueBankRegisters.reduceRegisters,
      NeighborhoodProgram.ResidueBankRegisters.operand,
      bank.injective.eq_iff] using hbaseValue
  have hpreparedBasePred :
      prepared bank.bank.basePred = base - 1 := by
    have hpred := congrArg (fun current => current - 1) hbaseValue
    simpa [prepared, prepareActiveChunkIndexOps, Basic.execList, bank,
      copied, afterClear, reduced, Basic.exec,
      RuntimeArithmetic.reduceResultStore,
      NeighborhoodProgram.ResidueBankRegisters.reduceRegisters,
      NeighborhoodProgram.ResidueBankRegisters.operand,
      bank.injective.eq_iff] using hpred
  have hpreparedOne :
      prepared bank.bank.one = 1 := by
    simp [prepared, prepareActiveChunkIndexOps, Basic.execList, bank,
      copied, afterClear, reduced, Basic.exec,
      RuntimeArithmetic.reduceResultStore,
      NeighborhoodProgram.ResidueBankRegisters.reduceRegisters,
      NeighborhoodProgram.ResidueBankRegisters.operand,
      bank.injective.eq_iff]
  have hpreparedModulus :
      prepared bank.modulus = modulus := by
    simpa [prepared, prepareActiveChunkIndexOps, Basic.execList, bank,
      copied, afterClear, reduced, Basic.exec,
      RuntimeArithmetic.reduceResultStore,
      NeighborhoodProgram.ResidueBankRegisters.reduceRegisters,
      NeighborhoodProgram.ResidueBankRegisters.operand,
      NeighborhoodProgram.ResidueBankRegisters.modulus,
      bank.injective.eq_iff, modulus] using hmodulusValue
  have hpreparedModulusPred :
      prepared bank.modulusPred = modulus - 1 := by
    simpa [prepared, prepareActiveChunkIndexOps, Basic.execList, bank,
      copied, afterClear, reduced, Basic.exec,
      RuntimeArithmetic.reduceResultStore,
      NeighborhoodProgram.ResidueBankRegisters.reduceRegisters,
      NeighborhoodProgram.ResidueBankRegisters.operand,
      NeighborhoodProgram.ResidueBankRegisters.modulusPred,
      bank.injective.eq_iff, modulus] using hmodulusPred
  have hpreparedOperand :
      prepared bank.operand = scaled := by
    simp [prepared, prepareActiveChunkIndexOps, Basic.execList, bank,
      copied, afterClear, reduced, Basic.exec,
      RuntimeArithmetic.reduceResultStore,
      NeighborhoodProgram.ResidueBankRegisters.reduceRegisters,
      NeighborhoodProgram.ResidueBankRegisters.operand,
      bank.injective.eq_iff]
  have hpreparedIndex :
      prepared bank.bank.indexCount =
        NeighborhoodProgram.residueBankIndex
          tm blockLength register chunk := by
    simp [prepared, prepareActiveChunkIndexOps, Basic.execList, bank,
      copied, afterClear, reduced, Basic.exec,
      RuntimeArithmetic.reduceResultStore,
      NeighborhoodProgram.ResidueBankRegisters.reduceRegisters,
      NeighborhoodProgram.ResidueBankRegisters.operand,
      bank.injective.eq_iff, hbankOut, hbankChunkCount,
      hbankCursor, houtBank, hchunkCountBank, hcursorBank,
      hout, hchunkCount, hcursor,
      NeighborhoodProgram.residueBankIndex]
  obtain ⟨final, hupdate, hfinalWord, _hbuffer, _hindex,
      _hcompleted, _hresult, hfinalBase, _hfinalBasePred,
      _hfinalOne, _hreplacement, hfinalModulus,
      hfinalModulusPred, _hfinalOperand, _hsavedIndex⟩ :=
    NeighborhoodProgram.bankUpdateAt_runs
      bank .add prepared base word
      (NeighborhoodProgram.residueBankIndex
        tm blockLength register chunk)
      modulus scaled hbase hmodulus hpreparedWord hpreparedBase
      hpreparedBasePred hpreparedOne hpreparedIndex
      hpreparedModulus hpreparedModulusPred hpreparedOperand
  have hvalueLt :
      NeighborhoodProgram.ResidueBankOp.add.apply modulus
          (original register chunk) scaled <
        base :=
    NeighborhoodProgram.ResidueBankOp.apply_lt hmodulus
      (by simpa [modulus] using hmodulusBase)
  have hfinalWord' :
      final bank.bank.word =
        NeighborhoodProgram.replaceAt base word
          (NeighborhoodProgram.residueBankIndex
            tm blockLength register chunk)
          (NeighborhoodProgram.ResidueBankOp.add.apply modulus
            (original register chunk) scaled) := by
    rw [hfinalWord, hrep register chunk]
  have hfinalRep :
      NeighborhoodProgram.RepresentsResidueBank
        tm blockLength base (final bank.bank.word)
        (NeighborhoodProgram.updateResidueCoordinate
          tm blockLength original register chunk
          (NeighborhoodProgram.ResidueBankOp.add.apply modulus
            (original register chunk) scaled)) := by
    rw [hfinalWord']
    exact NeighborhoodProgram.representsResidueBank_replaceAt
      tm blockLength base word original register chunk
      (NeighborhoodProgram.ResidueBankOp.add.apply modulus
        (original register chunk) scaled)
      hrep hbase hvalueLt
  refine ⟨final, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simpa [addScaledActiveChunk, bank] using
      Runs.seq hmul (Runs.seq hcopy (Runs.seq hprepare hupdate))
  · simpa [bank, modulus, scaled] using hfinalRep
  · simpa [bank, modulus, scaled] using hfinalWord'
  · simpa [bank] using hfinalBase
  · simpa [bank, modulus] using hfinalModulus
  · simpa [bank, modulus] using hfinalModulusPred

end Internal
end ResidueBankOps
end NeighborhoodMicrocode
end Runtime
end TimeSpaceSimulation
end Complexity
