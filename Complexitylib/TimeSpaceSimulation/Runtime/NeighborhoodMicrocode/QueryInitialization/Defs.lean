/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/
import
  Complexitylib.TimeSpaceSimulation.Runtime.NeighborhoodMicrocode.Representation.Defs
import
  Complexitylib.TimeSpaceSimulation.Runtime.NeighborhoodMicrocode.ResidueBankOps.Defs

/-!
# Initializing one represented neighborhood query

The root-node builder leaves its packed node in `Layout.nodeCode`. This layer
clears the suspended stack and catalytic bank, installs the remaining active
frame fields from runtime parameters, and starts the query in the enter phase.
-/

namespace Complexity
namespace TimeSpaceSimulation
namespace Runtime
namespace NeighborhoodMicrocode
namespace QueryInitialization

open RAM Structured

variable {controller : SearchProgram.Registers}

/-- Straight-line installation of the singleton root frame. -/
def activeOps
    (workTapeCount : ℕ)
    (regs : NeighborhoodTrial.Registers controller) : List Basic :=
  [.imm (Layout.frameStackRegisters regs).word 0,
    .imm (Layout.fuel regs) 0,
    .add (Layout.fuel regs) (Layout.horizon regs) (Layout.fuel regs),
    .imm (Layout.scalar regs) 1,
    .imm (Layout.out regs)
      (NeighborhoodExecutableEvaluation.graphFanIn workTapeCount),
    .imm (Layout.phaseCode regs) 0,
    .imm (Layout.active regs) 1]

/-- Initialize the zero bank and singleton active root frame. The packed root
node itself is supplied by the preceding uniform root builder. -/
def initializeQuery
    (workTapeCount : ℕ)
    (regs : NeighborhoodTrial.Registers controller) : Cmd :=
  Cmd.seq
    (ResidueBankOps.initializeBank regs)
    (Cmd.basics (activeOps workTapeCount regs))

end QueryInitialization
end NeighborhoodMicrocode
end Runtime
end TimeSpaceSimulation
end Complexity
