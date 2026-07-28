/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/
import
  Complexitylib.TimeSpaceSimulation.Runtime.NeighborhoodMicrocode.CleanupBranch
import
  Complexitylib.TimeSpaceSimulation.Runtime.NeighborhoodMicrocode.CleanupScaleStep
import
  Complexitylib.TimeSpaceSimulation.Runtime.NeighborhoodMicrocode.EnterBranch
import
  Complexitylib.TimeSpaceSimulation.Runtime.NeighborhoodMicrocode.PrepareBranch
import
  Complexitylib.TimeSpaceSimulation.Runtime.NeighborhoodMicrocode.SchedulerStep.Defs
import
  Complexitylib.TimeSpaceSimulation.Runtime.NeighborhoodScheduler.Coherence

/-!
# One uniform neighborhood-scheduler microstep -- proofs
-/

namespace Complexity
namespace TimeSpaceSimulation
namespace Runtime
namespace NeighborhoodMicrocode
namespace SchedulerStep
namespace Internal

open RAM Structured
open NeighborhoodExecutableEvaluation

variable {controller : SearchProgram.Registers}

private theorem cmdWritesWithin_mono
    {smaller larger : Finset ℕ} {command : Cmd}
    (hwrites : Footprint.CmdWritesWithin smaller command)
    (hsubset : smaller ⊆ larger) :
    Footprint.CmdWritesWithin larger command := by
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

private theorem controllerIndex_of_layout_run
    (regs : NeighborhoodTrial.Registers controller)
    {command : Cmd} {initial final : Store}
    (hwrites :
      Footprint.CmdWritesWithin regs.layout.footprint command)
    (hrun : Runs command initial final)
    (slot : Fin 17)
    (hsuccess : slot ≠ 3)
    (hverdict : slot ≠ 4)
    (hhasNext : slot ≠ 5) :
    final (controller.index slot) =
      initial (controller.index slot) :=
  NeighborhoodTrial.Registers.runs_preserves_controller_index
    regs (layoutWritesWithin_trial regs hwrites) hrun
    slot hsuccess hverdict hhasNext

private theorem inputLength_of_layout_run
    (regs : NeighborhoodTrial.Registers controller)
    {command : Cmd} {initial final : Store}
    (hwrites :
      Footprint.CmdWritesWithin regs.layout.footprint command)
    (hrun : Runs command initial final) :
    final controller.inputLength =
      initial controller.inputLength :=
  controllerIndex_of_layout_run regs hwrites hrun
    (0 : Fin 17) (by decide) (by decide) (by decide)

private theorem guess_of_layout_run
    (regs : NeighborhoodTrial.Registers controller)
    {command : Cmd} {initial final : Store}
    (hwrites :
      Footprint.CmdWritesWithin regs.layout.footprint command)
    (hrun : Runs command initial final) :
    final controller.guess = initial controller.guess :=
  controllerIndex_of_layout_run regs hwrites hrun
    (2 : Fin 17) (by decide) (by decide) (by decide)

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
      controllerIndex_of_layout_run regs hwrites hrun
        (14 : Fin 17) (by decide) (by decide) (by decide)

theorem step_writesWithin_internal
    (tm : TM workTapeCount)
    (order : FiniteEncoding.StateOrder tm)
    (controller : SearchProgram.Registers)
    (regs : NeighborhoodTrial.Registers controller)
    (combine : Cmd)
    (hcombine :
      Footprint.CmdWritesWithin regs.layout.footprint combine) :
    Footprint.CmdWritesWithin regs.layout.footprint
      (step tm order controller regs combine) := by
  apply Dispatcher.decodeAndDispatch_writesWithin
  · exact EnterBranch.step_writesWithin tm order regs
  · exact PrepareBranch.step_writesWithin
      workTapeCount controller regs
  · exact hcombine
  · exact CleanupBranch.step_writesWithin
      workTapeCount controller regs
  · exact CleanupScaleStep.step_writesWithin regs

theorem step_runs_internal
    {tm : TM workTapeCount}
    (order : FiniteEncoding.StateOrder tm)
    (controller : SearchProgram.Registers)
    (regs : NeighborhoodTrial.Registers controller)
    (combine : Cmd)
    (instanceData : NeighborhoodProgram.ResidueInstance tm)
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
    (store : Store)
    (hcombineWrites :
      Footprint.CmdWritesWithin regs.layout.footprint combine)
    (hcombine : CombineSpec tm order regs combine)
    (hencoding :
      instanceData.encoding =
        FiniteEncoding.ofStateOrder order instanceData.blockLength)
    (hguess :
      instanceData.guess =
        NeighborhoodGraph.Guess.Enumeration.candidateGuess code)
    (hstoreGuess : store controller.guess = code.val)
    (hquery :
      Representation.QueryState regs instanceData
        { stack := frame :: rest
          registers := logicalBank }
        store)
    (hcoherent :
      NeighborhoodScheduler.Coherence.StateCoherent
        { stack := frame :: rest
          registers := logicalBank })
    (hframe :
      SearchProgram.InputFrame
        controller regs.footprint instanceData.x store)
    (hinputLength :
      store controller.inputLength = instanceData.x.length)
    (hone : store controller.one = 1) :
    ∃ final,
      Runs (step tm order controller regs combine) store final ∧
      Representation.QueryState regs instanceData
        (NeighborhoodScheduler.State.next
          { stack := frame :: rest
            registers := logicalBank })
        final ∧
      SearchProgram.InputFrame
        controller regs.footprint instanceData.x final ∧
      final controller.inputLength = instanceData.x.length ∧
      final controller.one = 1 := by
  obtain ⟨middle, hdecode, hdecoded, hqueryMiddle⟩ :=
    Representation.QueryState.decodePhase_runs
      regs frame rest logicalBank store hquery
  have hdecodeWrites :
      Footprint.CmdWritesWithin regs.layout.footprint
        (ControlDecode.decodePhase regs) :=
    ControlDecode.decodePhase_layout_writesWithin regs
  have hframeMiddle :
      SearchProgram.InputFrame
        controller regs.footprint instanceData.x middle :=
    inputFrame_of_layout_run regs instanceData.x
      hdecodeWrites hdecode hframe
  have hinputLengthMiddle :
      middle controller.inputLength = instanceData.x.length :=
    (inputLength_of_layout_run regs
      hdecodeWrites hdecode).trans hinputLength
  have hguessMiddle :
      middle controller.guess = code.val :=
    (guess_of_layout_run regs
      hdecodeWrites hdecode).trans hstoreGuess
  have honeMiddle :
      middle controller.one = 1 :=
    (one_of_layout_run regs
      hdecodeWrites hdecode).trans hone
  let cleared :=
    RAM.Structured.Switch.cleared middle
      (ControlDecode.tag regs)
  have hclearRun :
      Runs
        (.basic (.imm (ControlDecode.tag regs) 0))
        middle cleared := by
    simpa [cleared, RAM.Structured.Switch.cleared,
      Basic.exec] using
        Runs.basic
          (.imm (ControlDecode.tag regs) 0) middle
  have hclearWrites :
      Footprint.CmdWritesWithin regs.layout.footprint
        (.basic (.imm (ControlDecode.tag regs) 0)) := by
    simpa [Footprint.CmdWritesWithin,
      Footprint.BasicWritesWithin, ControlDecode.tag] using
        Layout.index_mem_layout_footprint regs 6
  have hqueryCleared :
      Representation.QueryState regs instanceData
        { stack := frame :: rest
          registers := logicalBank }
        cleared := by
    simpa [cleared] using
      Representation.QueryState.clearedTag
        regs frame rest logicalBank middle hqueryMiddle
  have hframeCleared :
      SearchProgram.InputFrame
        controller regs.footprint instanceData.x cleared :=
    inputFrame_of_layout_run regs instanceData.x
      hclearWrites hclearRun hframeMiddle
  have hinputLengthCleared :
      cleared controller.inputLength = instanceData.x.length :=
    (inputLength_of_layout_run regs
      hclearWrites hclearRun).trans hinputLengthMiddle
  have hguessCleared :
      cleared controller.guess = code.val :=
    (guess_of_layout_run regs
      hclearWrites hclearRun).trans hguessMiddle
  have honeCleared :
      cleared controller.one = 1 :=
    (one_of_layout_run regs
      hclearWrites hclearRun).trans honeMiddle
  have hclearedPhysical (slot : Fin 34) (hne : slot ≠ 6) :
      cleared (regs.index slot) =
        middle (regs.index slot) := by
    simp [cleared, RAM.Structured.Switch.cleared,
      ControlDecode.tag, regs.injective.eq_iff, hne]
  have hframeCoherent :
      NeighborhoodScheduler.Coherence.FrameCoherent frame :=
    hcoherent frame (by simp)
  have finish
      (final : Store)
      (hbranch :
        Runs
          (Dispatcher.phaseBranches
            (EnterBranch.step tm order regs)
            (PrepareBranch.step workTapeCount controller regs)
            combine
            (CleanupBranch.step workTapeCount controller regs)
            (CleanupScaleStep.step regs)
            ⟨(ControlDecode.expectedPhaseValues frame.phase).tag, by
              cases frame.phase <;>
                simp [ControlDecode.expectedPhaseValues]⟩)
          cleared final)
      (hfinal :
        Representation.QueryState regs instanceData
          (NeighborhoodScheduler.State.next
            { stack := frame :: rest
              registers := logicalBank })
          final) :
      Runs (step tm order controller regs combine) store final ∧
      Representation.QueryState regs instanceData
        (NeighborhoodScheduler.State.next
          { stack := frame :: rest
            registers := logicalBank })
        final ∧
      SearchProgram.InputFrame
        controller regs.footprint instanceData.x final ∧
      final controller.inputLength = instanceData.x.length ∧
      final controller.one = 1 := by
    have hdispatch :=
      Dispatcher.dispatchPhase_runs
        regs
        (EnterBranch.step tm order regs)
        (PrepareBranch.step workTapeCount controller regs)
        combine
        (CleanupBranch.step workTapeCount controller regs)
        (CleanupScaleStep.step regs)
        middle final frame.phase hdecoded honeMiddle
        (by simpa [cleared] using hbranch)
    have hrun :
        Runs (step tm order controller regs combine)
          store final := by
      simpa [step, Dispatcher.decodeAndDispatch] using
        Runs.seq hdecode hdispatch
    have hwrites :
        Footprint.CmdWritesWithin regs.layout.footprint
          (step tm order controller regs combine) :=
      step_writesWithin_internal
        tm order controller regs combine hcombineWrites
    exact
      ⟨hrun, hfinal,
        inputFrame_of_layout_run regs instanceData.x
          hwrites hrun hframe,
        (inputLength_of_layout_run regs
          hwrites hrun).trans hinputLength,
        (one_of_layout_run regs
          hwrites hrun).trans hone⟩
  cases hphase : frame.phase with
  | enter =>
      obtain ⟨final, hbranch, hfinal, _hfinalFrame,
          _hfinalLength, _hfinalOne⟩ :=
        EnterBranch.step_runs
          order regs instanceData frame rest logicalBank cleared
          hphase hencoding hqueryCleared hframeCleared
          hinputLengthCleared honeCleared
      have hselected :
          Runs
            (Dispatcher.phaseBranches
              (EnterBranch.step tm order regs)
              (PrepareBranch.step workTapeCount controller regs)
              combine
              (CleanupBranch.step workTapeCount controller regs)
              (CleanupScaleStep.step regs)
              ⟨(ControlDecode.expectedPhaseValues frame.phase).tag, by
                simp [hphase, ControlDecode.expectedPhaseValues]⟩)
            cleared final := by
        simpa [Dispatcher.phaseBranches, hphase,
          ControlDecode.expectedPhaseValues] using hbranch
      exact ⟨final, finish final hselected hfinal⟩
  | prepare residue residuesLeft childIndex =>
      obtain ⟨parentTape, parentSlot, interval, hnode,
          hinterval, _hfuel⟩ :=
        NeighborhoodScheduler.Coherence.FrameCoherent.of_not_enter
          hframeCoherent (by simp [hphase])
      have hdecodedResidue :
          cleared (Dispatcher.decodedResidue regs) = residue := by
        calc
          cleared (Dispatcher.decodedResidue regs) =
              middle (Dispatcher.decodedResidue regs) := by
            simpa using hclearedPhysical (9 : Fin 34) (by decide)
          _ = residue := by
            simpa [hphase,
              ControlDecode.expectedPhaseValues] using
                hdecoded.residue_eq
      have hdecodedChild :
          cleared (Dispatcher.decodedChild regs) = childIndex := by
        calc
          cleared (Dispatcher.decodedChild regs) =
              middle (Dispatcher.decodedChild regs) := by
            simpa using hclearedPhysical (11 : Fin 34) (by decide)
          _ = childIndex := by
            simpa [hphase,
              ControlDecode.expectedPhaseValues] using
                hdecoded.child_eq
      obtain ⟨final, hbranch, hfinal⟩ :=
        PrepareBranch.step_runs
          code frame rest logicalBank controller regs cleared
          parentTape parentSlot interval residue residuesLeft childIndex
          hqueryCleared hphase hnode hinterval hdecodedResidue
          hdecodedChild hguessCleared hguess
      have hselected :
          Runs
            (Dispatcher.phaseBranches
              (EnterBranch.step tm order regs)
              (PrepareBranch.step workTapeCount controller regs)
              combine
              (CleanupBranch.step workTapeCount controller regs)
              (CleanupScaleStep.step regs)
              ⟨(ControlDecode.expectedPhaseValues frame.phase).tag, by
                simp [hphase, ControlDecode.expectedPhaseValues]⟩)
            cleared final := by
        simpa [Dispatcher.phaseBranches, hphase,
          ControlDecode.expectedPhaseValues] using hbranch
      exact ⟨final, finish final hselected hfinal⟩
  | combine residue residuesLeft =>
      obtain ⟨parentTape, parentSlot, interval, hnode,
          hinterval, _hfuel⟩ :=
        NeighborhoodScheduler.Coherence.FrameCoherent.of_not_enter
          hframeCoherent (by simp [hphase])
      have hdecodedResidue :
          cleared (Dispatcher.decodedResidue regs) = residue := by
        calc
          cleared (Dispatcher.decodedResidue regs) =
              middle (Dispatcher.decodedResidue regs) := by
            simpa using hclearedPhysical (9 : Fin 34) (by decide)
          _ = residue := by
            simpa [hphase,
              ControlDecode.expectedPhaseValues] using
                hdecoded.residue_eq
      have hdecodedLeft :
          cleared (Dispatcher.decodedResiduesLeft regs) =
            residuesLeft := by
        calc
          cleared (Dispatcher.decodedResiduesLeft regs) =
              middle (Dispatcher.decodedResiduesLeft regs) := by
            simpa using hclearedPhysical (10 : Fin 34) (by decide)
          _ = residuesLeft := by
            simpa [hphase,
              ControlDecode.expectedPhaseValues] using
                hdecoded.residuesLeft_eq
      obtain ⟨final, hbranch, hfinal⟩ :=
        hcombine instanceData frame rest logicalBank cleared
          parentTape parentSlot interval residue residuesLeft
          hencoding hphase hnode hinterval hqueryCleared
          hframeCleared hinputLengthCleared honeCleared
          hdecodedResidue hdecodedLeft
      have hselected :
          Runs
            (Dispatcher.phaseBranches
              (EnterBranch.step tm order regs)
              (PrepareBranch.step workTapeCount controller regs)
              combine
              (CleanupBranch.step workTapeCount controller regs)
              (CleanupScaleStep.step regs)
              ⟨(ControlDecode.expectedPhaseValues frame.phase).tag, by
                simp [hphase, ControlDecode.expectedPhaseValues]⟩)
            cleared final := by
        simpa [Dispatcher.phaseBranches, hphase,
          ControlDecode.expectedPhaseValues] using hbranch
      exact ⟨final, finish final hselected hfinal⟩
  | cleanupCall residue residuesLeft childIndex =>
      obtain ⟨parentTape, parentSlot, interval, hnode,
          hinterval, _hfuel⟩ :=
        NeighborhoodScheduler.Coherence.FrameCoherent.of_not_enter
          hframeCoherent (by simp [hphase])
      have hdecodedResidue :
          cleared (Dispatcher.decodedResidue regs) = residue := by
        calc
          cleared (Dispatcher.decodedResidue regs) =
              middle (Dispatcher.decodedResidue regs) := by
            simpa using hclearedPhysical (9 : Fin 34) (by decide)
          _ = residue := by
            simpa [hphase,
              ControlDecode.expectedPhaseValues] using
                hdecoded.residue_eq
      have hdecodedLeft :
          cleared (Dispatcher.decodedResiduesLeft regs) =
            residuesLeft := by
        calc
          cleared (Dispatcher.decodedResiduesLeft regs) =
              middle (Dispatcher.decodedResiduesLeft regs) := by
            simpa using hclearedPhysical (10 : Fin 34) (by decide)
          _ = residuesLeft := by
            simpa [hphase,
              ControlDecode.expectedPhaseValues] using
                hdecoded.residuesLeft_eq
      have hdecodedChild :
          cleared (Dispatcher.decodedChild regs) = childIndex := by
        calc
          cleared (Dispatcher.decodedChild regs) =
              middle (Dispatcher.decodedChild regs) := by
            simpa using hclearedPhysical (11 : Fin 34) (by decide)
          _ = childIndex := by
            simpa [hphase,
              ControlDecode.expectedPhaseValues] using
                hdecoded.child_eq
      obtain ⟨final, hbranch, hfinal⟩ :=
        CleanupBranch.step_runs
          code frame rest logicalBank controller regs cleared
          parentTape parentSlot interval residue residuesLeft childIndex
          hqueryCleared hphase hnode hinterval hdecodedResidue
          hdecodedLeft hdecodedChild hguessCleared hguess
      have hselected :
          Runs
            (Dispatcher.phaseBranches
              (EnterBranch.step tm order regs)
              (PrepareBranch.step workTapeCount controller regs)
              combine
              (CleanupBranch.step workTapeCount controller regs)
              (CleanupScaleStep.step regs)
              ⟨(ControlDecode.expectedPhaseValues frame.phase).tag, by
                simp [hphase, ControlDecode.expectedPhaseValues]⟩)
            cleared final := by
        simpa [Dispatcher.phaseBranches, hphase,
          ControlDecode.expectedPhaseValues] using hbranch
      exact ⟨final, finish final hselected hfinal⟩
  | cleanupScale residue residuesLeft child nextChild =>
      have hdecodedResidue :
          cleared (Dispatcher.decodedResidue regs) = residue := by
        calc
          cleared (Dispatcher.decodedResidue regs) =
              middle (Dispatcher.decodedResidue regs) := by
            simpa using hclearedPhysical (9 : Fin 34) (by decide)
          _ = residue := by
            simpa [hphase,
              ControlDecode.expectedPhaseValues] using
                hdecoded.residue_eq
      have hdecodedLeft :
          cleared (Dispatcher.decodedResiduesLeft regs) =
            residuesLeft := by
        calc
          cleared (Dispatcher.decodedResiduesLeft regs) =
              middle (Dispatcher.decodedResiduesLeft regs) := by
            simpa using hclearedPhysical (10 : Fin 34) (by decide)
          _ = residuesLeft := by
            simpa [hphase,
              ControlDecode.expectedPhaseValues] using
                hdecoded.residuesLeft_eq
      have hdecodedChild :
          cleared (Dispatcher.decodedChild regs) = child.val := by
        calc
          cleared (Dispatcher.decodedChild regs) =
              middle (Dispatcher.decodedChild regs) := by
            simpa using hclearedPhysical (11 : Fin 34) (by decide)
          _ = child.val := by
            simpa [hphase,
              ControlDecode.expectedPhaseValues] using
                hdecoded.child_eq
      have hdecodedNext :
          cleared (Dispatcher.decodedNextChild regs) =
            nextChild := by
        calc
          cleared (Dispatcher.decodedNextChild regs) =
              middle (Dispatcher.decodedNextChild regs) := by
            simpa using hclearedPhysical (12 : Fin 34) (by decide)
          _ = nextChild := by
            simpa [hphase,
              ControlDecode.expectedPhaseValues] using
                hdecoded.next_eq
      obtain ⟨final, hbranch, hfinal⟩ :=
        CleanupScaleStep.step_next_runs
          frame rest logicalBank regs cleared
          residue residuesLeft nextChild child hqueryCleared hphase
          hdecodedResidue hdecodedLeft hdecodedChild hdecodedNext
      have hselected :
          Runs
            (Dispatcher.phaseBranches
              (EnterBranch.step tm order regs)
              (PrepareBranch.step workTapeCount controller regs)
              combine
              (CleanupBranch.step workTapeCount controller regs)
              (CleanupScaleStep.step regs)
              ⟨(ControlDecode.expectedPhaseValues frame.phase).tag, by
                simp [hphase, ControlDecode.expectedPhaseValues]⟩)
            cleared final := by
        simpa [Dispatcher.phaseBranches, hphase,
          ControlDecode.expectedPhaseValues] using hbranch
      exact ⟨final, finish final hselected hfinal⟩

end Internal
end SchedulerStep
end NeighborhoodMicrocode
end Runtime
end TimeSpaceSimulation
end Complexity
