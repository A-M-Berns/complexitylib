/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/
import
  Complexitylib.TimeSpaceSimulation.Runtime.NeighborhoodMicrocode.CombineBranch.Defs
import
  Complexitylib.TimeSpaceSimulation.Runtime.NeighborhoodMicrocode.CombineBranch.Internal
import
  Complexitylib.TimeSpaceSimulation.Runtime.NeighborhoodMicrocode.SchedulerStep.Defs

/-!
# Uniform combine-branch composition

This surface exposes the fixed-layout chunk-streaming and phase-transition
layer around one uniform runtime-cursor computation-chunk provider.
-/

namespace Complexity
namespace TimeSpaceSimulation
namespace Runtime
namespace NeighborhoodMicrocode
namespace CombineBranch

open RAM Structured

variable {controller : SearchProgram.Registers}

/-- The uniform combine driver stays inside the evaluator layout whenever
its runtime-cursor provider does. -/
theorem step_writesWithin
    (controller : SearchProgram.Registers)
    (regs : NeighborhoodTrial.Registers controller)
    (chunkKernel : Cmd)
    (hkernel :
      Footprint.CmdWritesWithin regs.layout.footprint chunkKernel) :
    Footprint.CmdWritesWithin regs.layout.footprint
      (step controller regs chunkKernel) :=
  Internal.step_writesWithin_internal
    controller regs chunkKernel hkernel

/-- A conforming runtime-cursor provider executes exactly one logical
computation-node combine transition. -/
theorem step_runs
    {tm : TM workTapeCount}
    {instanceData : NeighborhoodProgram.ResidueInstance tm}
    (frame : NeighborhoodScheduler.Frame tm instanceData)
    (rest : List (NeighborhoodScheduler.Frame tm instanceData))
    (logicalBank :
      NeighborhoodExecutableEvaluation.Residue.Registers
        tm instanceData.blockLength)
    (controller : SearchProgram.Registers)
    (regs : NeighborhoodTrial.Registers controller)
    (chunkKernel : Cmd)
    (store : Store)
    (tape : TapeIndex workTapeCount)
    (slot : NeighborhoodGraph.Slot)
    (interval residue residuesLeft : ℕ)
    (hquery :
      Representation.QueryState regs instanceData
        { stack := frame :: rest
          registers := logicalBank }
        store)
    (hphase : frame.phase = .combine residue residuesLeft)
    (hnode :
      frame.node =
        (show
          NeighborhoodEvaluator.QueryNode
            workTapeCount instanceData.horizon
          from .graph (.computation tape slot interval)))
    (hone : store controller.one = 1)
    (hkernel :
      ComputationChunkKernelSpecAt regs instanceData frame tape slot
        interval chunkKernel) :
    ∃ final,
      Runs (step controller regs chunkKernel) store final ∧
      Representation.QueryState regs instanceData
        (NeighborhoodScheduler.State.next
          { stack := frame :: rest
            registers := logicalBank })
        final :=
  Internal.step_runs_internal
    frame rest logicalBank controller regs chunkKernel store tape
    slot interval residue residuesLeft hquery hphase hnode hone
    hkernel

/-- A globally conforming chunk provider turns the uniform combine driver
into the exact combine command required by the five-phase scheduler. -/
theorem step_combineSpec
    {tm : TM workTapeCount}
    (order :
      NeighborhoodExecutableEvaluation.FiniteEncoding.StateOrder tm)
    (controller : SearchProgram.Registers)
    (regs : NeighborhoodTrial.Registers controller)
    (chunkKernel : Cmd)
    (hkernel :
      ComputationChunkKernelSpec tm regs chunkKernel) :
    SchedulerStep.CombineSpec tm order regs
      (step controller regs chunkKernel) := by
  intro instanceData frame rest logicalBank store tape slot interval
    residue residuesLeft _hencoding hphase hnode _hinterval hquery
    _hframe _hinputLength hone _hdecodedResidue _hdecodedLeft
  exact
    step_runs frame rest logicalBank controller regs chunkKernel store
      tape slot interval residue residuesLeft hquery hphase hnode hone
      (hkernel instanceData frame tape slot interval)

end CombineBranch
end NeighborhoodMicrocode
end Runtime
end TimeSpaceSimulation
end Complexity
