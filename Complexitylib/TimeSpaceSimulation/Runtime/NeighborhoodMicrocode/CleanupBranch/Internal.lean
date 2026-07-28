/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/
import
  Complexitylib.TimeSpaceSimulation.Runtime.NeighborhoodMicrocode.CleanupBranch.Defs
import
  Complexitylib.TimeSpaceSimulation.Runtime.NeighborhoodMicrocode.CleanupDescent
import
  Complexitylib.TimeSpaceSimulation.Runtime.NeighborhoodMicrocode.CursorFinish

/-!
# Concrete cleanup-call branch -- proofs
-/

namespace Complexity
namespace TimeSpaceSimulation
namespace Runtime
namespace NeighborhoodMicrocode
namespace CleanupBranch
namespace Internal

open RAM Structured

variable {controller : SearchProgram.Registers}

theorem step_writesWithin_internal
    (workTapeCount : ℕ)
    (controller : SearchProgram.Registers)
    (regs : NeighborhoodTrial.Registers controller) :
    Footprint.CmdWritesWithin regs.layout.footprint
      (step workTapeCount controller regs) := by
  simp only [step, Cmd.seqList, Footprint.CmdWritesWithin]
  exact
    ⟨Layout.index_mem_layout_footprint regs 31,
      Layout.index_mem_layout_footprint regs 31,
      CursorFinish.finishCleanup_writesWithin regs,
      CleanupDescent.descendChild_writesWithin
        workTapeCount controller regs⟩

theorem step_runs_internal
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
    (parentTape : TapeIndex workTapeCount)
    (parentSlot : NeighborhoodGraph.Slot)
    (interval residue residuesLeft childIndex : ℕ)
    (hquery :
      Representation.QueryState regs instanceData
        { stack := frame :: rest
          registers := logicalBank }
        store)
    (hphase :
      frame.phase =
        .cleanupCall residue residuesLeft childIndex)
    (hnode :
      frame.node =
        .graph (.computation parentTape parentSlot interval))
    (hinterval : interval < instanceData.horizon)
    (hdecodedResidue :
      store (Dispatcher.decodedResidue regs) = residue)
    (hdecodedLeft :
      store (Dispatcher.decodedResiduesLeft regs) = residuesLeft)
    (hdecodedChild :
      store (Dispatcher.decodedChild regs) = childIndex)
    (hstoreGuess : store controller.guess = code.val)
    (hguess :
      instanceData.guess =
        NeighborhoodGraph.Guess.Enumeration.candidateGuess code) :
    ∃ final,
      Runs (step workTapeCount controller regs) store final ∧
      Representation.QueryState regs instanceData
        (NeighborhoodScheduler.State.next
          { stack := frame :: rest
            registers := logicalBank })
        final := by
  let withBound :=
    Basic.exec
      (.imm (Layout.codecScratch regs)
        (NeighborhoodExecutableEvaluation.graphFanIn workTapeCount))
      store
  let tested :=
    Basic.exec
      (.sub (Layout.codecScratch regs)
        (Layout.codecScratch regs)
        (Dispatcher.decodedChild regs))
      withBound
  have hboundRun :
      Runs
        (.basic
          (.imm (Layout.codecScratch regs)
            (NeighborhoodExecutableEvaluation.graphFanIn
              workTapeCount)))
        store withBound :=
    Runs.basic _ _
  have htestRun :
      Runs
        (.basic
          (.sub (Layout.codecScratch regs)
            (Layout.codecScratch regs)
            (Dispatcher.decodedChild regs)))
        withBound tested :=
    Runs.basic _ _
  have hphysical (slot : Fin 34) (hne : slot ≠ 31) :
      tested (regs.index slot) = store (regs.index slot) := by
    simp [tested, withBound, Basic.exec, Layout.codecScratch,
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
  have hdecodedResidueTested :
      tested (Dispatcher.decodedResidue regs) = residue := by
    simpa using
      (hphysical (9 : Fin 34) (by decide)).trans hdecodedResidue
  have hdecodedLeftTested :
      tested (Dispatcher.decodedResiduesLeft regs) =
        residuesLeft := by
    simpa using
      (hphysical (10 : Fin 34) (by decide)).trans hdecodedLeft
  have hdecodedChildTested :
      tested (Dispatcher.decodedChild regs) = childIndex := by
    simpa using
      (hphysical (11 : Fin 34) (by decide)).trans hdecodedChild
  have hguessTested :
      tested controller.guess = code.val := by
    calc
      tested controller.guess = store controller.guess := by
        simp [tested, withBound, Basic.exec, Layout.codecScratch,
          Function.update_of_ne,
          (regs.index_ne_controller (31 : Fin 34) (2 : Fin 17)).symm]
      _ = code.val := hstoreGuess
  by_cases hchild :
      childIndex <
        NeighborhoodExecutableEvaluation.graphFanIn workTapeCount
  · let child :
        Fin
          (NeighborhoodExecutableEvaluation.graphFanIn
            workTapeCount) :=
      ⟨childIndex, hchild⟩
    let selected :=
      (NeighborhoodGraph.predecessorIndexEquiv
        workTapeCount).symm child
    rcases hselectedPair : selected with ⟨kind, tape⟩
    have hselected :
        child =
          NeighborhoodGraph.predecessorIndexEquiv
            workTapeCount (kind, tape) := by
      change child =
        NeighborhoodGraph.predecessorIndexEquiv
          workTapeCount (kind, tape)
      rw [← hselectedPair]
      exact
        (NeighborhoodGraph.predecessorIndexEquiv
          workTapeCount).apply_symm_apply child |>.symm
    have htestNonzero :
        tested (Layout.codecScratch regs) ≠ 0 := by
      simp [tested, withBound, Basic.exec, Layout.codecScratch,
        regs.injective.eq_iff, hdecodedChild]
      omega
    obtain ⟨final, hdescend, hfinal⟩ :=
      CleanupDescent.descendChild_computation_runs
        code frame rest logicalBank controller regs tested
        parentTape tape parentSlot kind interval residue residuesLeft
        child hselected hinterval hqueryTested
        (by simpa [child] using hphase)
        hnode hdecodedResidueTested hdecodedLeftTested
        (by simpa [child] using hdecodedChildTested)
        hguessTested hguess
    refine ⟨final, ?_, ?_⟩
    · simpa [step, Cmd.seqList] using
        Runs.seq hboundRun
          (Runs.seq htestRun
            (Runs.ifNonzero htestNonzero hdescend))
    · simpa [NeighborhoodScheduler.State.next, hphase, hchild,
        child, CleanupDescent.advancedParent] using hfinal
  · have htestZero :
        tested (Layout.codecScratch regs) = 0 := by
      simp [tested, withBound, Basic.exec, Layout.codecScratch,
        regs.injective.eq_iff, hdecodedChild]
      omega
    have hexhausted :
        childIndex =
          NeighborhoodExecutableEvaluation.graphFanIn workTapeCount := by
      have hchildBound :=
        hquery.bounds frame (by simp) |>.2.2.2
      simp only [hphase,
        NeighborhoodScheduler.FrameBounds.PhaseBound] at hchildBound
      omega
    cases residuesLeft with
    | zero =>
        obtain ⟨final, hfinish, hfinal⟩ :=
          CursorFinish.finishCleanup_zero_runs
            regs frame rest logicalBank tested residue childIndex
            hqueryTested hphase hexhausted
        refine ⟨final, ?_, ?_⟩
        · simpa [step, Cmd.seqList] using
            Runs.seq hboundRun
              (Runs.seq htestRun
                (Runs.ifZero htestZero hfinish))
        · simpa [NeighborhoodScheduler.State.next, hphase, hchild,
            NeighborhoodScheduler.State.finishResidue] using hfinal
    | succ remaining =>
        obtain ⟨final, hfinish, hfinal⟩ :=
          CursorFinish.finishCleanup_succ_runs
            regs frame rest logicalBank tested residue remaining
            childIndex hqueryTested hphase hexhausted
        refine ⟨final, ?_, ?_⟩
        · simpa [step, Cmd.seqList] using
            Runs.seq hboundRun
              (Runs.seq htestRun
                (Runs.ifZero htestZero hfinish))
        · simpa [NeighborhoodScheduler.State.next, hphase, hchild,
            NeighborhoodScheduler.State.finishResidue,
            CursorFinish.nextResidueFrame] using hfinal

end Internal
end CleanupBranch
end NeighborhoodMicrocode
end Runtime
end TimeSpaceSimulation
end Complexity
