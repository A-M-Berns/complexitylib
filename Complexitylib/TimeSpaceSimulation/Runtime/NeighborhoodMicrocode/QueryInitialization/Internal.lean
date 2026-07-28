/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/
import
  Complexitylib.TimeSpaceSimulation.Runtime.NeighborhoodMicrocode.QueryInitialization.Defs
import
  Complexitylib.TimeSpaceSimulation.Runtime.NeighborhoodMicrocode.Representation
import
  Complexitylib.TimeSpaceSimulation.Runtime.NeighborhoodMicrocode.ResidueBankOps

/-!
# Initializing one represented neighborhood query -- proofs
-/

namespace Complexity
namespace TimeSpaceSimulation
namespace Runtime
namespace NeighborhoodMicrocode
namespace QueryInitialization
namespace Internal

open RAM Structured
open NeighborhoodExecutableEvaluation

variable {controller : SearchProgram.Registers}

private theorem basics_runs
    (operations : List Basic) (store : Store) :
    Runs (Cmd.basics operations) store
      (Basic.execList operations store) := by
  obtain ⟨cost, space, hexec⟩ :=
    RAM.Structured.Internal.exec_basics_exists operations store
  exact ⟨operations.length, cost, space, hexec⟩

theorem initialize_writesWithin_internal
    (workTapeCount : ℕ)
    (regs : NeighborhoodTrial.Registers controller) :
    Footprint.CmdWritesWithin regs.layout.footprint
      (initializeQuery workTapeCount regs) := by
  refine ⟨ResidueBankOps.initializeBank_writesWithin regs, ?_⟩
  simp only [activeOps, Cmd.basics]
  exact
    ⟨Layout.index_mem_layout_footprint regs 32,
      Layout.index_mem_layout_footprint regs 22,
      Layout.index_mem_layout_footprint regs 22,
      Layout.index_mem_layout_footprint regs 25,
      Layout.index_mem_layout_footprint regs 26,
      Layout.index_mem_layout_footprint regs 27,
      Layout.index_mem_layout_footprint regs 28⟩

theorem initialize_runs_internal
    {tm : TM workTapeCount}
    (regs : NeighborhoodTrial.Registers controller)
    (instanceData : NeighborhoodProgram.ResidueInstance tm)
    (node :
      NeighborhoodEvaluator.QueryNode
        workTapeCount instanceData.horizon)
    (store : Store)
    (hparameters :
      Representation.Parameters regs instanceData store)
    (hnodeCode :
      store (Layout.nodeCode regs) =
        FrameCodec.encodeNode
          (Representation.digitBase instanceData) node)
    (hnodeBound :
      NeighborhoodScheduler.FrameBounds.QueryBound
        instanceData.horizon node) :
    ∃ final,
      Runs (initializeQuery workTapeCount regs) store final ∧
      Representation.QueryState regs instanceData
        (NeighborhoodScheduler.State.initial
          instanceData.horizon node 1
          (Fin.last (graphFanIn workTapeCount))
          (ResidueBankOps.zeroRegisters tm instanceData.blockLength))
        final := by
  have hbase :
      store
          (Layout.residueScaleRegisters regs).bank.bank.base =
        Representation.fieldBase instanceData := by
    simpa [Layout.residueScaleRegisters, Layout.residueScaleMap] using
      hparameters.bankBase_eq
  obtain
      ⟨banked, hbankRun, hbankWord, _hbankOne, _hbankBase,
        _hbankBasePred, _hbankCount, hbankRep⟩ :=
    ResidueBankOps.initializeBank_runs
      tm instanceData.blockLength
      (Representation.fieldBase instanceData) regs store hbase
  let final :=
    Basic.execList (activeOps workTapeCount regs) banked
  have hactiveRun :
      Runs (Cmd.basics (activeOps workTapeCount regs)) banked final := by
    exact basics_runs _ _
  have hbankWrites :
      Footprint.CmdWritesWithin
        {regs.index 33, regs.index 17, regs.index 1, regs.index 10}
        (ResidueBankOps.initializeBank regs) := by
    simp [ResidueBankOps.initializeBank,
      ResidueBankOps.initializeBankOps,
      Layout.residueScaleRegisters, Layout.residueScaleMap,
      NeighborhoodProgram.ResidueScaleRegisters.bank,
      NeighborhoodProgram.ResidueScaleRegisters.bankSlot,
      NeighborhoodProgram.ResidueBankRegisters.bank,
      NeighborhoodProgram.ResidueBankRegisters.bankSlot,
      NeighborhoodProgram.BankRegisters.word,
      NeighborhoodProgram.BankRegisters.one,
      NeighborhoodProgram.BankRegisters.base,
      NeighborhoodProgram.BankRegisters.basePred,
      NeighborhoodProgram.BankRegisters.indexCount,
      Cmd.basics, Cmd.seqList, Footprint.CmdWritesWithin,
      Footprint.BasicWritesWithin]
  have hbankPhysical (slot : Fin 34)
      (hne33 : slot ≠ 33) (hne17 : slot ≠ 17)
      (hne1 : slot ≠ 1) (hne10 : slot ≠ 10) :
      banked (regs.index slot) = store (regs.index slot) := by
    apply Footprint.runs_eq_outside hbankWrites hbankRun
    simp [regs.injective.eq_iff, hne33, hne17, hne1, hne10]
  have hfinalPhysical (slot : Fin 34)
      (hne32 : slot ≠ 32) (hne22 : slot ≠ 22)
      (hne25 : slot ≠ 25) (hne26 : slot ≠ 26)
      (hne27 : slot ≠ 27) (hne28 : slot ≠ 28) :
      final (regs.index slot) = banked (regs.index slot) := by
    simp [final, activeOps, Basic.execList, Basic.exec,
      Layout.frameStackRegisters, Layout.frameStackMap,
      Layout.fuel, Layout.horizon, Layout.scalar, Layout.out,
      Layout.phaseCode, Layout.active, regs.injective.eq_iff,
      hne32, hne22, hne25, hne26, hne27, hne28]
  have hfinalParameters :
      Representation.Parameters regs instanceData final := by
    refine
      { blockLength_eq := ?_
        horizon_eq := ?_
        digitBase_eq := ?_
        bankBase_eq := ?_
        frameBase_eq := ?_
        chunkCount_eq := ?_
        bankDigitCount_eq := ?_
        modulus_eq := ?_
        modulusPred_eq := ?_ }
    all_goals
      first
      | exact
          (hfinalPhysical _ (by decide) (by decide) (by decide)
            (by decide) (by decide) (by decide)).trans
            ((hbankPhysical _ (by decide) (by decide) (by decide)
              (by decide)).trans hparameters.blockLength_eq)
      | exact
          (hfinalPhysical _ (by decide) (by decide) (by decide)
            (by decide) (by decide) (by decide)).trans
            ((hbankPhysical _ (by decide) (by decide) (by decide)
              (by decide)).trans hparameters.horizon_eq)
      | exact
          (hfinalPhysical _ (by decide) (by decide) (by decide)
            (by decide) (by decide) (by decide)).trans
            ((hbankPhysical _ (by decide) (by decide) (by decide)
              (by decide)).trans hparameters.digitBase_eq)
      | exact
          (hfinalPhysical _ (by decide) (by decide) (by decide)
            (by decide) (by decide) (by decide)).trans
            ((hbankPhysical _ (by decide) (by decide) (by decide)
              (by decide)).trans hparameters.bankBase_eq)
      | exact
          (hfinalPhysical _ (by decide) (by decide) (by decide)
            (by decide) (by decide) (by decide)).trans
            ((hbankPhysical _ (by decide) (by decide) (by decide)
              (by decide)).trans hparameters.frameBase_eq)
      | exact
          (hfinalPhysical _ (by decide) (by decide) (by decide)
            (by decide) (by decide) (by decide)).trans
            ((hbankPhysical _ (by decide) (by decide) (by decide)
              (by decide)).trans hparameters.chunkCount_eq)
      | exact
          (hfinalPhysical _ (by decide) (by decide) (by decide)
            (by decide) (by decide) (by decide)).trans
            ((hbankPhysical _ (by decide) (by decide) (by decide)
              (by decide)).trans hparameters.bankDigitCount_eq)
      | exact
          (hfinalPhysical _ (by decide) (by decide) (by decide)
            (by decide) (by decide) (by decide)).trans
            ((hbankPhysical _ (by decide) (by decide) (by decide)
              (by decide)).trans hparameters.modulus_eq)
      | exact
          (hfinalPhysical _ (by decide) (by decide) (by decide)
            (by decide) (by decide) (by decide)).trans
            ((hbankPhysical _ (by decide) (by decide) (by decide)
              (by decide)).trans hparameters.modulusPred_eq)
  refine ⟨final, ?_, ?_⟩
  · exact Runs.seq hbankRun hactiveRun
  · refine
      { parameters := hfinalParameters
        stack := ?_
        bank := ?_
        bank_lt := ?_
        bounds := ?_ }
    · change
        Representation.ActiveFrame regs
            { fuel := instanceData.horizon
              node := node
              scalar := 1
              out := Fin.last (graphFanIn workTapeCount)
              phase := .enter }
            final ∧
          FrameTransfer.RepresentsStack regs
            (Representation.digitBase instanceData)
            (Representation.frameBase instanceData) [] final
      constructor
      · refine
          { fuel_eq := ?_
            node_eq := ?_
            scalar_eq := ?_
            out_eq := ?_
            phase_eq := ?_
            active_eq := ?_ }
        · simp [final, activeOps, Basic.execList, Basic.exec,
            Layout.frameStackRegisters, Layout.frameStackMap,
            Layout.fuel, Layout.horizon, Layout.scalar, Layout.out,
            Layout.phaseCode, Layout.active, regs.injective.eq_iff]
          exact
            (hbankPhysical (3 : Fin 34) (by decide) (by decide)
              (by decide) (by decide)).trans
              hparameters.horizon_eq
        · exact
            (hfinalPhysical (23 : Fin 34) (by decide) (by decide)
              (by decide) (by decide) (by decide) (by decide)).trans
              ((hbankPhysical (23 : Fin 34) (by decide) (by decide)
                (by decide) (by decide)).trans hnodeCode)
        · simp [final, activeOps, Basic.execList, Basic.exec,
            Layout.frameStackRegisters, Layout.frameStackMap,
            Layout.fuel, Layout.horizon, Layout.scalar, Layout.out,
            Layout.phaseCode, Layout.active, regs.injective.eq_iff]
        · simp [final, activeOps, Basic.execList, Basic.exec,
            Layout.frameStackRegisters, Layout.frameStackMap,
            Layout.fuel, Layout.horizon, Layout.scalar, Layout.out,
            Layout.phaseCode, Layout.active, regs.injective.eq_iff]
        · simp [final, activeOps, Basic.execList, Basic.exec,
            Layout.frameStackRegisters, Layout.frameStackMap,
            Layout.fuel, Layout.horizon, Layout.scalar, Layout.out,
            Layout.phaseCode, Layout.active, regs.injective.eq_iff,
            FrameCodec.encodePhase, FrameCodec.phaseDigits,
            FrameCodec.encodeList, PackedDigits.push]
        · simp [final, activeOps, Basic.execList, Basic.exec,
            Layout.frameStackRegisters, Layout.frameStackMap,
            Layout.fuel, Layout.horizon, Layout.scalar, Layout.out,
            Layout.phaseCode, Layout.active, regs.injective.eq_iff]
      · simp [FrameTransfer.RepresentsStack,
          FrameTransfer.encodeStack, final, activeOps,
          Basic.execList, Basic.exec, Layout.frameStackRegisters,
          Layout.frameStackMap, Layout.fuel, Layout.horizon,
          Layout.scalar, Layout.out, Layout.phaseCode, Layout.active,
          regs.injective.eq_iff]
    · change
        NeighborhoodProgram.RepresentsResidueBank
          tm instanceData.blockLength
          (Representation.fieldBase instanceData)
          (final (regs.index 33))
          (ResidueBankOps.zeroRegisters tm instanceData.blockLength)
      rw [hfinalPhysical (33 : Fin 34) (by decide) (by decide)
        (by decide) (by decide) (by decide) (by decide)]
      change
        NeighborhoodProgram.RepresentsResidueBank
          tm instanceData.blockLength
          (Representation.fieldBase instanceData)
          (banked
            (Layout.residueScaleRegisters regs).bank.bank.word)
          (ResidueBankOps.zeroRegisters tm instanceData.blockLength)
      exact hbankRep
    · change
        final (regs.index 33) <
          Representation.fieldBase instanceData ^
            ((graphFanIn workTapeCount + 1) *
              TreeEval.CookMertz.PrimeGrouped.Logarithmic.chunkCount
                (payloadWidth tm instanceData.blockLength)
                (graphFanIn workTapeCount))
      rw [hfinalPhysical (33 : Fin 34) (by decide) (by decide)
        (by decide) (by decide) (by decide) (by decide)]
      have hbankWord' : banked (regs.index 33) = 0 := by
        simpa [Layout.residueScaleRegisters, Layout.residueScaleMap,
          NeighborhoodProgram.ResidueScaleRegisters.bank,
          NeighborhoodProgram.ResidueScaleRegisters.bankSlot,
          NeighborhoodProgram.ResidueBankRegisters.bank,
          NeighborhoodProgram.ResidueBankRegisters.bankSlot] using
          hbankWord
      rw [hbankWord']
      have hbasePositive :
          0 < Representation.fieldBase instanceData := by
        unfold Representation.fieldBase Representation.digitBase
          CandidateParameters.domainSize
        exact pow_pos
          (TreeEval.CookMertz.PrimeGrouped.Logarithmic.domainSize_pos
            _ _) _
      exact pow_pos hbasePositive _
    · apply NeighborhoodScheduler.FrameBounds.stateBound_initial
      · exact Nat.le_refl _
      · exact hnodeBound
      · exact
          NeighborhoodScheduler.FrameBounds.fieldModulus_one_lt
            instanceData

end Internal
end QueryInitialization
end NeighborhoodMicrocode
end Runtime
end TimeSpaceSimulation
end Complexity
