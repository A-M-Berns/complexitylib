/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/
import
  Complexitylib.TimeSpaceSimulation.Runtime.NeighborhoodMicrocode.Representation.Defs

/-!
# Reinitializing a query while retaining the catalytic bank

The state-root and verdict-root traversals share one catalytic bank. After the
first traversal, this command replaces only the continuation stack and active
frame. In particular it does not clear the packed bank, so the completed state
value can survive the verdict traversal in a catalytic coordinate.
-/

namespace Complexity
namespace TimeSpaceSimulation
namespace Runtime
namespace NeighborhoodMicrocode
namespace QueryReinitialization

open RAM Structured
open NeighborhoodExecutableEvaluation

variable {controller : SearchProgram.Registers}

/-- Straight-line installation of a singleton root frame that leaves the
packed catalytic bank untouched. -/
def activeOps
    (workTapeCount : ℕ)
    (regs : NeighborhoodTrial.Registers controller)
    (out : Fin (graphFanIn workTapeCount + 1)) : List Basic :=
  [.imm (Layout.frameStackRegisters regs).word 0,
    .imm (Layout.fuel regs) 0,
    .add (Layout.fuel regs) (Layout.horizon regs) (Layout.fuel regs),
    .imm (Layout.scalar regs) 1,
    .imm (Layout.out regs) out.val,
    .imm (Layout.phaseCode regs) 0,
    .imm (Layout.active regs) 1]

/-- Replace the current query by a singleton root frame without clearing the
packed catalytic bank. -/
def reinitializeQuery
    (workTapeCount : ℕ)
    (regs : NeighborhoodTrial.Registers controller)
    (out : Fin (graphFanIn workTapeCount + 1)) : Cmd :=
  Cmd.basics (activeOps workTapeCount regs out)

end QueryReinitialization
end NeighborhoodMicrocode
end Runtime
end TimeSpaceSimulation
end Complexity
