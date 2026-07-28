/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/
import
  Complexitylib.TimeSpaceSimulation.Runtime.NeighborhoodMicrocode.EnterComputation.Defs
import
  Complexitylib.TimeSpaceSimulation.Runtime.NeighborhoodMicrocode.EnterComputation.Internal

/-!
# Successful computation-node entry
-/

namespace Complexity
namespace TimeSpaceSimulation
namespace Runtime
namespace NeighborhoodMicrocode
namespace EnterComputation

open RAM Structured

variable {controller : SearchProgram.Registers}

/-- Successful computation entry writes only inside the evaluator layout. -/
theorem start_writesWithin
    (regs : NeighborhoodTrial.Registers controller) :
    Footprint.CmdWritesWithin regs.layout.footprint
      (start regs) :=
  Internal.start_writesWithin_internal regs

/-- Complete computation entry writes only inside the evaluator layout. -/
theorem step_writesWithin
    (regs : NeighborhoodTrial.Registers controller) :
    Footprint.CmdWritesWithin regs.layout.footprint
      (step regs) :=
  Internal.step_writesWithin_internal regs

/-- A valid positive-fuel computation call starts the first residue fold and
preserves the catalytic bank exactly. -/
theorem start_runs
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
        final :=
  Internal.start_runs_internal
    regs frame rest logicalBank store fuel tape slot interval
    hquery hphase hnode hfuel hinterval

/-- Fuel and interval tests select exactly the computation-node successor:
failure-value return for invalid calls, and first-residue initialization for
a valid positive-fuel call. -/
theorem step_runs
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
      final controller.one = 1 :=
  Internal.step_runs_internal
    regs instanceData frame rest logicalBank store tape slot interval
    hnode hphase hdecodedInterval hquery hframe hinputLength hone

end EnterComputation
end NeighborhoodMicrocode
end Runtime
end TimeSpaceSimulation
end Complexity
