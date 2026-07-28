/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/
import
  Complexitylib.TimeSpaceSimulation.Runtime.NeighborhoodMicrocode.CleanupDescent.Defs

/-!
# Concrete cleanup-child descent -- proofs
-/

namespace Complexity
namespace TimeSpaceSimulation
namespace Runtime
namespace NeighborhoodMicrocode
namespace CleanupDescent
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

theorem descendChild_writesWithin_internal
    (workTapeCount : ℕ)
    (controller : SearchProgram.Registers)
    (regs : NeighborhoodTrial.Registers controller) :
    Footprint.CmdWritesWithin regs.layout.footprint
      (descendChild workTapeCount controller regs) := by
  simp only [descendChild, Cmd.seqList, Footprint.CmdWritesWithin]
  exact
    ⟨ParentPhase.suspendCleanup_writesWithin regs,
      cmdWritesWithin_mono
        (ChildReady.prepare_writesWithin
          workTapeCount controller regs)
        (ChildReady.writeFootprint_subset_layout regs),
      cmdWritesWithin_mono
        (FrameInstall.installCleanupChild_writesWithin regs)
        (FrameInstall.writeFootprint_subset_layout regs)⟩

private theorem guess_not_mem_layout
    (controller : SearchProgram.Registers)
    (regs : NeighborhoodTrial.Registers controller) :
    controller.guess ∉ regs.layout.footprint := by
  intro hguess
  exact
    Finset.disjoint_left.mp
      (NeighborhoodTrial.Registers.layout_disjoint_controller regs)
      hguess (controller.index_mem_footprint (2 : Fin 17))

theorem descendChild_computation_runs_internal
    {tm : TM workTapeCount}
    {instanceData : NeighborhoodProgram.ResidueInstance tm}
    (code :
      Fin
        (3 ^
          NeighborhoodGraph.Guess.Enumeration.movementCount
            workTapeCount instanceData.horizon))
    (frame : NeighborhoodScheduler.Frame tm instanceData)
    (rest : List (NeighborhoodScheduler.Frame tm instanceData))
    (logicalBank :
      NeighborhoodExecutableEvaluation.Residue.Registers
        tm instanceData.blockLength)
    (controller : SearchProgram.Registers)
    (regs : NeighborhoodTrial.Registers controller)
    (store : Store)
    (parentTape tape : TapeIndex workTapeCount)
    (parentSlot : NeighborhoodGraph.Slot)
    (kind : NeighborhoodGraph.PredecessorKind)
    (interval residue residuesLeft : ℕ)
    (child :
      Fin (NeighborhoodExecutableEvaluation.graphFanIn workTapeCount))
    (hselected :
      child =
        NeighborhoodGraph.predecessorIndexEquiv
          workTapeCount (kind, tape))
    (hinterval : interval < instanceData.horizon)
    (hquery :
      Representation.QueryState regs instanceData
        { stack := frame :: rest
          registers := logicalBank }
        store)
    (hphase :
      frame.phase =
        .cleanupCall residue residuesLeft child.val)
    (hnode :
      frame.node =
        .graph (.computation parentTape parentSlot interval))
    (hdecodedResidue :
      store (Dispatcher.decodedResidue regs) = residue)
    (hdecodedLeft :
      store (Dispatcher.decodedResiduesLeft regs) = residuesLeft)
    (hdecodedChild :
      store (Dispatcher.decodedChild regs) = child.val)
    (hstoreGuess : store controller.guess = code.val)
    (hguess :
      instanceData.guess =
        NeighborhoodGraph.Guess.Enumeration.candidateGuess code) :
    ∃ final,
      Runs
        (descendChild workTapeCount controller regs)
        store final ∧
      Representation.QueryState regs instanceData
        { stack :=
            frame.cleanupChild child ::
              advancedParent frame residue residuesLeft child ::
              rest
          registers := logicalBank }
        final := by
  have hframeBound :
      NeighborhoodScheduler.FrameBounds.FrameBound frame :=
    hquery.bounds frame (by simp)
  have hbase :
      0 < Representation.digitBase instanceData := by
    unfold Representation.digitBase CandidateParameters.domainSize
    exact
      TreeEval.CookMertz.PrimeGrouped.Logarithmic.domainSize_pos _ _
  have hresidue :
      residue <
        Representation.digitBase instanceData ^
          FrameCodec.scalarDigitCount := by
    simpa [hphase, ControlDecode.expectedPhaseValues] using
      FrameBounds.frameBound_phaseResidue_lt frame hframeBound
  have hleft :
      residuesLeft <
        Representation.digitBase instanceData ^
          FrameCodec.scalarDigitCount := by
    simpa [hphase, ControlDecode.expectedPhaseValues] using
      FrameBounds.frameBound_phaseResiduesLeft_lt frame hframeBound
  have hadvancedBound :
      NeighborhoodScheduler.FrameBounds.FrameBound
        (advancedParent frame residue residuesLeft child) := by
    simpa only [advancedParent] using
      ParentPhase.frameBound_advanceCleanup
        frame residue residuesLeft child hphase hframeBound
  obtain ⟨suspended, hsuspend, hsuspendedStack,
      hparametersSuspended, hbankSuspended, hsavedChild,
      hactiveSuspended⟩ :=
    ParentPhase.suspendCleanup_runs
      regs frame rest store residue residuesLeft child
      hquery.stack hquery.parameters hbase hresidue hleft
      hdecodedResidue hdecodedLeft hdecodedChild hadvancedBound
  have hguessSuspended :
      suspended controller.guess = code.val := by
    calc
      suspended controller.guess = store controller.guess :=
        Footprint.runs_eq_outside
          (ParentPhase.suspendCleanup_writesWithin regs)
          hsuspend (guess_not_mem_layout controller regs)
      _ = code.val := hstoreGuess
  have hsavedSelected :
      suspended (ChildNode.savedChildIndex regs) =
        (NeighborhoodGraph.predecessorIndexEquiv
          workTapeCount (kind, tape)).val := by
    rw [← hselected]
    exact hsavedChild
  have hadvancedNode :
      (advancedParent frame residue residuesLeft child).node =
        .graph (.computation parentTape parentSlot interval) := by
    simpa only [advancedParent] using hnode
  obtain ⟨ready, hreadyRun, hready⟩ :=
    ChildReady.prepare_frameChild_runs
      code (advancedParent frame residue residuesLeft child)
      controller regs suspended parentTape tape parentSlot kind interval
      hinterval hactiveSuspended hparametersSuspended
      hadvancedBound hsavedSelected hguessSuspended hguess
      hadvancedNode
  have hparametersReady :
      Representation.Parameters regs instanceData ready :=
    ChildReady.Parameters.of_readyPost
      regs suspended ready hparametersSuspended hready
  have hsuspendedReady :
      FrameTransfer.RepresentsStack regs
        (Representation.digitBase instanceData)
        (Representation.frameBase instanceData)
        (advancedParent frame residue residuesLeft child :: rest)
        ready := by
    unfold FrameTransfer.RepresentsStack at hsuspendedStack ⊢
    rw [ChildReady.ReadyPost.stackWord_eq regs hready]
    exact hsuspendedStack
  have hbankAtSuspended :
      NeighborhoodProgram.RepresentsResidueBank
        tm instanceData.blockLength
        (Representation.fieldBase instanceData)
        (suspended regs.layout.bank) logicalBank := by
    rw [hbankSuspended]
    exact hquery.bank
  have hbankReady :
      NeighborhoodProgram.RepresentsResidueBank
        tm instanceData.blockLength
        (Representation.fieldBase instanceData)
        (ready regs.layout.bank) logicalBank := by
    rw [ChildReady.ReadyPost.bank_eq regs hready]
    exact hbankAtSuspended
  have hbankLtReady :
      ready regs.layout.bank <
        Representation.fieldBase instanceData ^
          ((NeighborhoodExecutableEvaluation.graphFanIn
              workTapeCount + 1) *
            TreeEval.CookMertz.PrimeGrouped.Logarithmic.chunkCount
              (NeighborhoodExecutableEvaluation.payloadWidth
                tm instanceData.blockLength)
              (NeighborhoodExecutableEvaluation.graphFanIn
                workTapeCount)) := by
    rw [ChildReady.ReadyPost.bank_eq regs hready, hbankSuspended]
    exact hquery.bank_lt
  have hfuelReady :
      ready (Layout.fuel regs) = frame.fuel := by
    calc
      ready (Layout.fuel regs) =
          suspended (Layout.fuel regs) :=
        hready.fuel_eq
      _ = (advancedParent frame residue residuesLeft child).fuel :=
        hactiveSuspended.fuel_eq
      _ = frame.fuel := rfl
  have hnodeReady :
      ready (Layout.nodeCode regs) =
        FrameCodec.encodeNode
          (Representation.digitBase instanceData)
          (frame.childNode child) := by
    calc
      ready (Layout.nodeCode regs) =
          FrameCodec.encodeNode
            (suspended (Layout.chunkRadix regs))
            ((advancedParent frame residue residuesLeft child).childNode
              (NeighborhoodGraph.predecessorIndexEquiv
                workTapeCount (kind, tape))) :=
        hready.nodeCode_eq
      _ = FrameCodec.encodeNode
          (Representation.digitBase instanceData)
          ((advancedParent frame residue residuesLeft child).childNode
            (NeighborhoodGraph.predecessorIndexEquiv
              workTapeCount (kind, tape))) := by
        rw [hparametersSuspended.digitBase_eq]
      _ = FrameCodec.encodeNode
          (Representation.digitBase instanceData)
          (frame.childNode child) := by
        rw [← hselected]
        rfl
  have houtReady :
      ready (Layout.out regs) = (frame.childTarget child).val := by
    calc
      ready (Layout.out regs) =
          ((advancedParent frame residue residuesLeft child).childTarget
            (NeighborhoodGraph.predecessorIndexEquiv
              workTapeCount (kind, tape))).val :=
        hready.out_eq
      _ = (frame.childTarget child).val := by
        rw [← hselected]
        rfl
  have hparentFields :
      (advancedParent frame residue residuesLeft child).fuel =
          frame.fuel ∧
      (advancedParent frame residue residuesLeft child).node =
          frame.node ∧
      (advancedParent frame residue residuesLeft child).scalar =
          frame.scalar ∧
      (advancedParent frame residue residuesLeft child).out =
          frame.out := by
    simp [advancedParent]
  have hrestBounds :
      ∀ candidate ∈ rest,
        NeighborhoodScheduler.FrameBounds.FrameBound candidate := by
    intro candidate hcandidate
    exact hquery.bounds candidate (by simp [hcandidate])
  obtain ⟨final, hfinish, hfinal⟩ :=
    Descent.finishCleanup_runs
      regs frame
      (advancedParent frame residue residuesLeft child)
      rest child logicalBank ready hparentFields hsuspendedReady
      hparametersReady hbankReady hbankLtReady hfuelReady
      hnodeReady houtReady hframeBound hadvancedBound hrestBounds
  refine ⟨final, ?_, hfinal⟩
  simpa [descendChild, Cmd.seqList] using
    Runs.seq hsuspend (Runs.seq hreadyRun hfinish)

end Internal
end CleanupDescent
end NeighborhoodMicrocode
end Runtime
end TimeSpaceSimulation
end Complexity
