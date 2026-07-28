/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/
import
  Complexitylib.TimeSpaceSimulation.Runtime.NeighborhoodMicrocode.CursorFinish
import
  Complexitylib.TimeSpaceSimulation.Runtime.NeighborhoodMicrocode.EnterComputation.Defs
import
  Complexitylib.TimeSpaceSimulation.Runtime.NeighborhoodMicrocode.EnterLeaf

/-!
# Successful computation-node entry -- proofs
-/

namespace Complexity
namespace TimeSpaceSimulation
namespace Runtime
namespace NeighborhoodMicrocode
namespace EnterComputation
namespace Internal

open RAM Structured

variable {controller : SearchProgram.Registers}

private theorem cmdWritesWithin_mono
    {small large : Finset ℕ} {command : Cmd}
    (hwrites : Footprint.CmdWritesWithin small command)
    (hsubset : small ⊆ large) :
    Footprint.CmdWritesWithin large command := by
  induction command with
  | skip =>
      trivial
  | basic op =>
      cases op <;>
        simp only [Footprint.CmdWritesWithin,
          Footprint.BasicWritesWithin] at hwrites ⊢
      all_goals exact hsubset hwrites
  | seq first second ihFirst ihSecond =>
      exact ⟨ihFirst hwrites.1, ihSecond hwrites.2⟩
  | ifZero test onZero onNonzero ihZero ihNonzero =>
      exact ⟨ihZero hwrites.1, ihNonzero hwrites.2⟩
  | whileNonzero test body ih =>
      exact ih hwrites

private theorem phaseWriteFootprint_subset_layout
    (regs : NeighborhoodTrial.Registers controller) :
    CursorFinish.phaseWriteFootprint regs ⊆
      regs.layout.footprint := by
  intro address haddress
  rw [CursorFinish.phaseWriteFootprint,
    Finset.mem_union] at haddress
  rcases haddress with hdecode | hphase
  · exact ControlDecode.scratchFootprint_subset_layout regs hdecode
  · simp only [Finset.mem_insert, Finset.mem_singleton] at hphase
    rcases hphase with rfl | rfl | rfl
    · exact Layout.index_mem_layout_footprint regs 27
    · simpa [Layout.frameCodecRegisters, Layout.frameCodecMap] using
        Layout.index_mem_layout_footprint regs 4
    · exact Layout.index_mem_layout_footprint regs 30

private theorem decodeScratch_mem_phase
    (regs : NeighborhoodTrial.Registers controller)
    (slot : Fin 7) :
    regs.index (ControlDecode.scratchMap slot) ∈
      CursorFinish.phaseWriteFootprint regs := by
  apply Finset.mem_union_left
  exact Finset.mem_image.mpr ⟨slot, Finset.mem_univ _, rfl⟩

theorem start_writesWithin_phase_internal
    (regs : NeighborhoodTrial.Registers controller) :
    Footprint.CmdWritesWithin
      (CursorFinish.phaseWriteFootprint regs) (start regs) := by
  simp only [start, Cmd.seqList, Footprint.CmdWritesWithin]
  refine ⟨?_, ?_, CursorFinish.nextResidueAfterDecode_writesWithin regs⟩
  · simpa [Footprint.BasicWritesWithin,
      ControlDecode.scratchMap] using
        decodeScratch_mem_phase regs (2 : Fin 7)
  · have hmember :
        Dispatcher.decodedResiduesLeft regs ∈
          CursorFinish.phaseWriteFootprint regs := by
      simpa [ControlDecode.scratchMap] using
        decodeScratch_mem_phase regs (3 : Fin 7)
    simpa [Dispatcher.copy, Footprint.CmdWritesWithin,
      Footprint.BasicWritesWithin] using And.intro hmember hmember

theorem start_writesWithin_internal
    (regs : NeighborhoodTrial.Registers controller) :
    Footprint.CmdWritesWithin regs.layout.footprint
      (start regs) :=
  cmdWritesWithin_mono
    (start_writesWithin_phase_internal regs)
    (phaseWriteFootprint_subset_layout regs)

theorem step_writesWithin_internal
    (regs : NeighborhoodTrial.Registers controller) :
    Footprint.CmdWritesWithin regs.layout.footprint
      (step regs) := by
  simp only [step, Footprint.CmdWritesWithin]
  exact
    ⟨EnterLeaf.failure_writesWithin regs,
      ⟨Layout.index_mem_layout_footprint regs 31,
        EnterLeaf.failure_writesWithin regs,
        start_writesWithin_internal regs⟩⟩

private theorem layoutWritesWithin_trial
    (regs : NeighborhoodTrial.Registers controller)
    {command : Cmd}
    (hwrites :
      Footprint.CmdWritesWithin regs.layout.footprint command) :
    Footprint.CmdWritesWithin regs.footprint command :=
  cmdWritesWithin_mono hwrites (by
    intro address haddress
    exact Finset.mem_union_left _ haddress)

private theorem inputFrame_of_layout_run
    (regs : NeighborhoodTrial.Registers controller)
    (input : List Bool)
    {command : Cmd} {initial final : Store}
    (hwrites :
      Footprint.CmdWritesWithin regs.layout.footprint command)
    (hrun : Runs command initial final)
    (hframe :
      SearchProgram.InputFrame
        controller regs.footprint input initial) :
    SearchProgram.InputFrame
      controller regs.footprint input final :=
  NeighborhoodTrial.Registers.runs_preserves_inputFrame
    regs (layoutWritesWithin_trial regs hwrites) hrun hframe

private theorem inputLength_of_layout_run
    (regs : NeighborhoodTrial.Registers controller)
    {command : Cmd} {initial final : Store}
    (hwrites :
      Footprint.CmdWritesWithin regs.layout.footprint command)
    (hrun : Runs command initial final) :
    final controller.inputLength =
      initial controller.inputLength :=
  NeighborhoodTrial.Registers.runs_preserves_controller_index
    regs (layoutWritesWithin_trial regs hwrites) hrun
    (0 : Fin 17) (by decide) (by decide) (by decide)

private theorem one_of_layout_run
    (regs : NeighborhoodTrial.Registers controller)
    {command : Cmd} {initial final : Store}
    (hwrites :
      Footprint.CmdWritesWithin regs.layout.footprint command)
    (hrun : Runs command initial final) :
    final controller.one = initial controller.one := by
  simpa [SearchProgram.Registers.one,
    SearchProgram.Registers.primeRegisters,
    SearchProgram.Registers.primeSlot] using
      NeighborhoodTrial.Registers.runs_preserves_controller_index
        regs (layoutWritesWithin_trial regs hwrites) hrun
        (14 : Fin 17) (by decide) (by decide) (by decide)

private theorem copy_runs
    {destination source : ℕ} (store : Store)
    (hne : destination ≠ source) :
    Runs (Dispatcher.copy destination source) store
      (Function.update store destination (store source)) := by
  apply Runs.seq (Runs.basic (.imm destination 0) store)
  simpa [Dispatcher.copy, Basic.exec, Function.update_of_ne,
    hne, Ne.symm hne] using
      Runs.basic
        (.add destination source destination)
        (Basic.exec (.imm destination 0) store)

theorem start_runs_internal
    {tm : TM workTapeCount}
    {instanceData : NeighborhoodProgram.ResidueInstance tm}
    (regs : NeighborhoodTrial.Registers controller)
    (frame : NeighborhoodScheduler.Frame tm instanceData)
    (rest : List (NeighborhoodScheduler.Frame tm instanceData))
    (logicalBank :
      NeighborhoodExecutableEvaluation.Residue.Registers
        tm instanceData.blockLength)
    (store : Store)
    (fuel : ℕ)
    (tape : TapeIndex workTapeCount)
    (slot : NeighborhoodGraph.Slot)
    (interval : ℕ)
    (hquery :
      Representation.QueryState regs instanceData
        { stack := frame :: rest
          registers := logicalBank }
        store)
    (hphase : frame.phase = .enter)
    (hnode :
      frame.node =
        .graph (.computation tape slot interval))
    (hfuel : frame.fuel = fuel + 1)
    (hinterval : interval < instanceData.horizon) :
    ∃ final,
      Runs (start regs) store final ∧
      Representation.QueryState regs instanceData
        { stack := prepareFrame frame :: rest
          registers := logicalBank }
        final := by
  have hbase :
      0 < Representation.digitBase instanceData := by
    unfold Representation.digitBase CandidateParameters.domainSize
    exact
      TreeEval.CookMertz.PrimeGrouped.Logarithmic.domainSize_pos _ _
  have hbaseLarge :
      1 < Representation.digitBase instanceData := by
    simpa [Representation.digitBase] using
      CandidateParameters.RadixBounds.one_lt_domainSize
        tm.Q workTapeCount instanceData.candidateTime
  have hfirstFits :
      0 + 1 <
        Representation.digitBase instanceData ^
          FrameCodec.scalarDigitCount := by
    simp only [FrameCodec.scalarDigitCount, pow_two]
    nlinarith
  have hcountPositive :
      0 <
        NeighborhoodScheduler.Frame.residueCount instanceData := by
    unfold NeighborhoodScheduler.Frame.residueCount
    have hmodulus :=
      NeighborhoodScheduler.FrameBounds.fieldModulus_one_lt
        instanceData
    omega
  have hcountFits :
      NeighborhoodScheduler.Frame.residueCount instanceData <
        Representation.fieldBase instanceData := by
    have hmodulus :=
      CandidateParameters.RadixBounds.canonicalModulus_lt_bankRadix
        tm.Q workTapeCount instanceData.candidateTime
    rw [← NeighborhoodTrial.fieldModulus_eq_canonicalModulus
      instanceData, ← Representation.fieldBase_eq_bankRadix
        instanceData] at hmodulus
    unfold NeighborhoodScheduler.Frame.residueCount
    omega
  have hleftFits :
      NeighborhoodScheduler.Frame.residueCount instanceData - 1 <
        Representation.digitBase instanceData ^
          FrameCodec.scalarDigitCount := by
    rw [← Representation.fieldBase]
    omega
  let residueZero :=
    Basic.exec
      (.imm (Dispatcher.decodedResidue regs) 0)
      store
  let seeded :=
    Function.update residueZero
      (Dispatcher.decodedResiduesLeft regs)
      (residueZero (Layout.modulusPred regs))
  have hzero :
      Runs
        (.basic (.imm (Dispatcher.decodedResidue regs) 0))
        store residueZero :=
    Runs.basic _ _
  have hseed :
      Runs
        (Dispatcher.copy
          (Dispatcher.decodedResiduesLeft regs)
          (Layout.modulusPred regs))
        residueZero seeded := by
    exact copy_runs residueZero (by
      change regs.index 10 ≠ regs.index 16
      exact regs.injective.ne (by decide))
  have hseedBase :
      seeded (Layout.chunkRadix regs) =
        Representation.digitBase instanceData := by
    simp [seeded, residueZero, Basic.exec,
      regs.injective.eq_iff, hquery.parameters.digitBase_eq]
  have hseedBankBase :
      seeded (Layout.bankRadix regs) =
        Representation.digitBase instanceData ^
          FrameCodec.scalarDigitCount := by
    simp [seeded, residueZero, Basic.exec,
      regs.injective.eq_iff, hquery.parameters.bankBase_eq,
      Representation.fieldBase]
  have hseedResidue :
      seeded (Dispatcher.decodedResidue regs) = 0 := by
    simp [seeded, residueZero, Basic.exec, regs.injective.eq_iff]
  have hcountOne :
      1 ≤
        NeighborhoodScheduler.Frame.residueCount instanceData :=
    hcountPositive
  have hseedLeft :
      seeded (Dispatcher.decodedResiduesLeft regs) =
        (NeighborhoodScheduler.Frame.residueCount instanceData - 1) + 1 := by
    calc
      seeded (Dispatcher.decodedResiduesLeft regs) =
          store (Layout.modulusPred regs) := by
        simp [seeded, residueZero, Basic.exec,
          regs.injective.eq_iff]
      _ = NeighborhoodScheduler.fieldModulus instanceData - 1 :=
        hquery.parameters.modulusPred_eq
      _ = NeighborhoodScheduler.Frame.residueCount instanceData := rfl
      _ =
          (NeighborhoodScheduler.Frame.residueCount instanceData - 1) + 1 :=
        (Nat.sub_add_cancel hcountOne).symm
  obtain ⟨final, hadvance, hphasePost⟩ :=
    CursorFinish.nextResidueAfterDecode_runs
      (workTapeCount := workTapeCount)
      regs seeded (Representation.digitBase instanceData)
      0
      (NeighborhoodScheduler.Frame.residueCount instanceData - 1)
      hbase hfirstFits hleftFits hseedBase hseedBankBase
      hseedResidue hseedLeft
  have hrun : Runs (start regs) store final := by
    simpa [start, Cmd.seqList] using
      Runs.seq hzero (Runs.seq hseed hadvance)
  have hpost :
      CursorFinish.PhaseUpdatePost regs
        (prepareFrame frame).phase store final :=
    { phaseCode_eq := by
        rw [hquery.parameters.digitBase_eq]
        simpa [prepareFrame, hseedBase] using
          hphasePost.phaseCode_eq
      eq_outside := fun address haddress =>
        Footprint.runs_eq_outside
          (start_writesWithin_phase_internal regs)
          hrun haddress }
  have hbounds :
      NeighborhoodScheduler.FrameBounds.StateBound
        { stack := prepareFrame frame :: rest
          registers := logicalBank } := by
    have hnext :=
      NeighborhoodScheduler.FrameBounds.StateBound.next
        { stack := frame :: rest
          registers := logicalBank }
        hquery.bounds
    have hcountNe :
        NeighborhoodScheduler.Frame.residueCount instanceData ≠ 0 :=
      Nat.ne_of_gt hcountPositive
    obtain ⟨residuesLeft, hcountEq⟩ :=
      Nat.exists_eq_succ_of_ne_zero hcountNe
    simpa [NeighborhoodScheduler.State.next, hphase, hnode, hfuel,
      hinterval, hcountEq, prepareFrame] using hnext
  have hqueryFinal :=
    CursorFinish.PhaseUpdatePost.queryState
      regs frame (prepareFrame frame) rest logicalBank store final
      hquery (by simp [prepareFrame]) hpost hbounds
  exact ⟨final, hrun, hqueryFinal⟩

theorem step_runs_internal
    {tm : TM workTapeCount}
    (regs : NeighborhoodTrial.Registers controller)
    (instanceData : NeighborhoodProgram.ResidueInstance tm)
    (frame : NeighborhoodScheduler.Frame tm instanceData)
    (rest : List (NeighborhoodScheduler.Frame tm instanceData))
    (logicalBank :
      NeighborhoodExecutableEvaluation.Residue.Registers
        tm instanceData.blockLength)
    (store : Store)
    (tape : TapeIndex workTapeCount)
    (slot : NeighborhoodGraph.Slot)
    (interval : ℕ)
    (hnode :
      frame.node =
        .graph (.computation tape slot interval))
    (hphase : frame.phase = .enter)
    (hdecodedInterval :
      store (ControlDecode.nodePayload1 regs) = interval)
    (hquery :
      Representation.QueryState regs instanceData
        { stack := frame :: rest
          registers := logicalBank }
        store)
    (hframe :
      SearchProgram.InputFrame
        controller regs.footprint instanceData.x store)
    (hinputLength :
      store controller.inputLength = instanceData.x.length)
    (hone : store controller.one = 1) :
    ∃ final,
      Runs (step regs) store final ∧
      Representation.QueryState regs instanceData
        (NeighborhoodScheduler.State.next
          { stack := frame :: rest
            registers := logicalBank })
        final ∧
      SearchProgram.InputFrame
        controller regs.footprint instanceData.x final ∧
      final controller.inputLength = instanceData.x.length ∧
      final controller.one = 1 := by
  cases hframeFuel : frame.fuel with
  | zero =>
      have hfuelZero :
          store (Layout.fuel regs) = 0 :=
        hquery.stack.1.fuel_eq.trans hframeFuel
      obtain ⟨final, hfailure, hfinal, hfinalFrame,
          hfinalLength, hfinalOne⟩ :=
        EnterLeaf.failureValue_runs
          regs instanceData frame rest logicalBank store
          hphase hquery hframe hinputLength hone
      refine ⟨final, Runs.ifZero hfuelZero hfailure, ?_,
        hfinalFrame, hfinalLength, hfinalOne⟩
      simpa [NeighborhoodScheduler.State.next, hphase, hnode,
        hframeFuel] using hfinal
  | succ fuel =>
      have hfuelNonzero :
          store (Layout.fuel regs) ≠ 0 := by
        rw [hquery.stack.1.fuel_eq, hframeFuel]
        omega
      let tested :=
        Basic.exec
          (.sub (Layout.codecScratch regs)
            (Layout.horizon regs)
            (ControlDecode.nodePayload1 regs))
          store
      have htestRun :
          Runs
            (.basic
              (.sub (Layout.codecScratch regs)
                (Layout.horizon regs)
                (ControlDecode.nodePayload1 regs)))
            store tested :=
        Runs.basic _ _
      have hphysical (physical : Fin 34) (hne : physical ≠ 31) :
          tested (regs.index physical) =
            store (regs.index physical) := by
        simp [tested, Basic.exec, Layout.codecScratch,
          regs.injective.eq_iff, hne]
      have habi :
          ControlDecode.PreservesABI regs store tested :=
        { fuel_eq := hphysical (22 : Fin 34) (by decide)
          nodeCode_eq := hphysical (23 : Fin 34) (by decide)
          scalar_eq := hphysical (25 : Fin 34) (by decide)
          out_eq := hphysical (26 : Fin 34) (by decide)
          phaseCode_eq := hphysical (27 : Fin 34) (by decide)
          active_eq := hphysical (28 : Fin 34) (by decide)
          blockLength_eq := hphysical (2 : Fin 34) (by decide)
          horizon_eq := hphysical (3 : Fin 34) (by decide)
          chunkCount_eq := hphysical (7 : Fin 34) (by decide)
          chunkRadix_eq := hphysical (8 : Fin 34) (by decide)
          frameRadix_eq := hphysical (13 : Fin 34) (by decide)
          bankRadix_eq := hphysical (14 : Fin 34) (by decide)
          bankDigitCount_eq := hphysical (15 : Fin 34) (by decide)
          modulusPred_eq := hphysical (16 : Fin 34) (by decide)
          modulus_eq := hphysical (24 : Fin 34) (by decide) }
      have hstack :
          tested (Layout.frameStackRegisters regs).word =
            store (Layout.frameStackRegisters regs).word := by
        simpa [Layout.frameStackRegisters, Layout.frameStackMap] using
          hphysical (32 : Fin 34) (by decide)
      have hbank :
          tested regs.layout.bank = store regs.layout.bank := by
        change tested (regs.index 33) = store (regs.index 33)
        exact hphysical (33 : Fin 34) (by decide)
      have hqueryTested :
          Representation.QueryState regs instanceData
            { stack := frame :: rest
              registers := logicalBank }
            tested :=
        Representation.QueryState.of_preservesABI
          regs frame rest logicalBank store tested hquery
          habi hstack hbank
      have hframeTested :
          SearchProgram.InputFrame
            controller regs.footprint instanceData.x tested :=
        inputFrame_of_layout_run regs instanceData.x
          (by
            simpa [Footprint.CmdWritesWithin,
              Footprint.BasicWritesWithin] using
                Layout.index_mem_layout_footprint regs 31)
          htestRun hframe
      have hinputLengthTested :
          tested controller.inputLength = instanceData.x.length :=
        (inputLength_of_layout_run regs
          (by
            simpa [Footprint.CmdWritesWithin,
              Footprint.BasicWritesWithin] using
                Layout.index_mem_layout_footprint regs 31)
          htestRun).trans hinputLength
      have honeTested :
          tested controller.one = 1 :=
        (one_of_layout_run regs
          (by
            simpa [Footprint.CmdWritesWithin,
              Footprint.BasicWritesWithin] using
                Layout.index_mem_layout_footprint regs 31)
          htestRun).trans hone
      have hdecodedIntervalTested :
          tested (ControlDecode.nodePayload1 regs) = interval := by
        simpa using
          (hphysical (11 : Fin 34) (by decide)).trans
            hdecodedInterval
      by_cases hinterval : interval < instanceData.horizon
      · have htestNonzero :
            tested (Layout.codecScratch regs) ≠ 0 := by
          simp [tested, Basic.exec, Layout.codecScratch,
            Layout.horizon, ControlDecode.nodePayload1,
            hquery.parameters.horizon_eq,
            hdecodedInterval]
          omega
        obtain ⟨final, hstart, hfinal⟩ :=
          start_runs_internal
            regs frame rest logicalBank tested fuel tape slot interval
            hqueryTested hphase hnode hframeFuel hinterval
        have hfinalFrame :
            SearchProgram.InputFrame
              controller regs.footprint instanceData.x final :=
          inputFrame_of_layout_run regs instanceData.x
            (start_writesWithin_internal regs) hstart hframeTested
        have hfinalLength :
            final controller.inputLength = instanceData.x.length :=
          (inputLength_of_layout_run regs
            (start_writesWithin_internal regs) hstart).trans
              hinputLengthTested
        have hfinalOne :
            final controller.one = 1 :=
          (one_of_layout_run regs
            (start_writesWithin_internal regs) hstart).trans
              honeTested
        refine ⟨final, ?_, ?_, hfinalFrame,
          hfinalLength, hfinalOne⟩
        · simpa [step] using
            Runs.ifNonzero hfuelNonzero
              (Runs.seq htestRun
                (Runs.ifNonzero htestNonzero hstart))
        · have hcountPositive :
              0 <
                NeighborhoodScheduler.Frame.residueCount
                  instanceData := by
            unfold NeighborhoodScheduler.Frame.residueCount
            have hmodulus :=
              NeighborhoodScheduler.FrameBounds.fieldModulus_one_lt
                instanceData
            omega
          have hcountNe :
              NeighborhoodScheduler.Frame.residueCount
                  instanceData ≠ 0 :=
            Nat.ne_of_gt hcountPositive
          obtain ⟨residuesLeft, hcountEq⟩ :=
            Nat.exists_eq_succ_of_ne_zero hcountNe
          simpa [NeighborhoodScheduler.State.next, hphase, hnode,
            hframeFuel, hinterval, hcountEq, prepareFrame] using hfinal
      · have htestZero :
            tested (Layout.codecScratch regs) = 0 := by
          simp [tested, Basic.exec, Layout.codecScratch,
            Layout.horizon, ControlDecode.nodePayload1,
            hquery.parameters.horizon_eq,
            hdecodedInterval]
          omega
        obtain ⟨final, hfailure, hfinal, hfinalFrame,
            hfinalLength, hfinalOne⟩ :=
          EnterLeaf.failureValue_runs
            regs instanceData frame rest logicalBank tested
            hphase hqueryTested hframeTested hinputLengthTested
            honeTested
        refine ⟨final, ?_, ?_, hfinalFrame,
          hfinalLength, hfinalOne⟩
        · simpa [step] using
            Runs.ifNonzero hfuelNonzero
              (Runs.seq htestRun
                (Runs.ifZero htestZero hfailure))
        · simpa [NeighborhoodScheduler.State.next, hphase, hnode,
            hframeFuel, hinterval] using hfinal

end Internal
end EnterComputation
end NeighborhoodMicrocode
end Runtime
end TimeSpaceSimulation
end Complexity
