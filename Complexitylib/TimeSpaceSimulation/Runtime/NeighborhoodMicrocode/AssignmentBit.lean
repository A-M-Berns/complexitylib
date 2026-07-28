/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/
import
  Complexitylib.TimeSpaceSimulation.Runtime.NeighborhoodMicrocode.AssignmentBit.Defs
import
  Complexitylib.TimeSpaceSimulation.Runtime.NeighborhoodMicrocode.AssignmentBit.Internal

/-!
# Uniform Boolean lookup in a streamed grouped assignment
-/

namespace Complexity
namespace TimeSpaceSimulation
namespace Runtime
namespace NeighborhoodMicrocode
namespace AssignmentBit

open RAM Structured

variable {controller : SearchProgram.Registers}

/-- Binary assignment lookup stays inside its exact six-register interface. -/
theorem read_writesWithin
    (regs : NeighborhoodTrial.Registers controller) :
    Footprint.CmdWritesWithin (writeFootprint regs) (read regs) :=
  Internal.read_writesWithin_internal regs

/-- Binary assignment lookup stays inside combine scratch. -/
theorem read_combineScratch_writesWithin
    (regs : NeighborhoodTrial.Registers controller) :
    Footprint.CmdWritesWithin
      (CombineValue.combineScratchFootprint regs) (read regs) :=
  Internal.read_combineScratch_writesWithin_internal regs

/-- Binary assignment lookup stays inside the shared evaluator layout. -/
theorem read_layout_writesWithin
    (regs : NeighborhoodTrial.Registers controller) :
    Footprint.CmdWritesWithin regs.layout.footprint (read regs) :=
  Internal.read_layout_writesWithin_internal regs

/-- The uniform command returns one exact low-order assignment bit while
preserving the range interface and the evaluator ABI. -/
theorem read_runs
    (regs : NeighborhoodTrial.Registers controller)
    (store : Store) (code index : ℕ)
    (hcode :
      store (CombineValue.rangeRegisters regs).remaining = code)
    (hindex : store (digitIndex regs) = index) :
    ∃ final,
      Runs (read regs) store final ∧
      Post regs code index store final ∧
      ControlDecode.PreservesABI regs store final :=
  Internal.read_runs_internal regs store code index hcode hindex

end AssignmentBit
end NeighborhoodMicrocode
end Runtime
end TimeSpaceSimulation
end Complexity
