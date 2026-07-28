/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/
import
  Complexitylib.TimeSpaceSimulation.Runtime.NeighborhoodMicrocode.ChildNode.Defs
import
  Complexitylib.TimeSpaceSimulation.Runtime.NeighborhoodMicrocode.QueryInitialization.Defs

/-!
# Uniform initialization of local-consistency provider queries

The local boundary checker streams one predecessor coordinate at a time.
During this phase the outer controller's `success` cell holds the interval
cursor and its `verdict` cell holds the role-major predecessor cursor.  Both
cells are outside the neighborhood workspace and therefore survive a complete
query evaluation.

This module turns those two runtime cursors into exactly the guessed
predecessor query node.  The command syntax depends only on the fixed source
machine tape count and register allocation.
-/

namespace Complexity
namespace TimeSpaceSimulation
namespace Runtime
namespace NeighborhoodMicrocode
namespace ProviderRootInitialization

open RAM Structured

variable {controller : SearchProgram.Registers}

/-- The semantic provider root selected by one interval and role-major
predecessor coordinate. -/
def providerRoot
    {tm : TM workTapeCount}
    (instanceData : NeighborhoodProgram.ResidueInstance tm)
    (interval : Fin instanceData.horizon)
    (child :
      Fin
        (NeighborhoodExecutableEvaluation.graphFanIn workTapeCount)) :
    NeighborhoodEvaluator.QueryNode
      workTapeCount instanceData.horizon :=
  NeighborhoodEvaluator.childAt instanceData.guess
    (.graph
      (.computation
        (TapeIndex.input workTapeCount)
        .center interval.val))
    child

/-- Direct cursor-to-parent fields consumed by `ChildNode.regenerateChild`.

The dummy parent tape and slot are irrelevant: every computation node at the
same interval has the same role-major predecessor oracle. -/
def providerFields
    (controller : SearchProgram.Registers)
    (regs : NeighborhoodTrial.Registers controller) : Cmd :=
  Cmd.basics
    [.imm (ControlDecode.tag regs) 2,
      .imm (ControlDecode.nodeTape regs) 0,
      .imm (ControlDecode.nodePayload0 regs)
        NeighborhoodGraph.Slot.center.toFin.val,
      .imm (ControlDecode.nodePayload1 regs) 0,
      .add (ControlDecode.nodePayload1 regs)
        controller.success (ControlDecode.nodePayload1 regs),
      .imm (ChildNode.savedChildIndex regs) 0,
      .add (ChildNode.savedChildIndex regs)
        controller.verdict (ChildNode.savedChildIndex regs)]

/-- Exact fixed write footprint of provider-root construction. -/
def rootFootprint
    (regs : NeighborhoodTrial.Registers controller) : Finset ℕ :=
  ChildNode.priorAssemblyFootprint regs ∪
    {ChildNode.savedChildIndex regs}

/-- Build the packed guessed predecessor root selected by the two controller
cursors. -/
def buildProviderRoot
    (workTapeCount : ℕ)
    (controller : SearchProgram.Registers)
    (regs : NeighborhoodTrial.Registers controller) : Cmd :=
  Cmd.seq
    (providerFields controller regs)
    (ChildNode.regenerateChild workTapeCount controller regs)

/-- Build one provider root and initialize a zero-bank singleton query. -/
def initializeProviderQuery
    (workTapeCount : ℕ)
    (controller : SearchProgram.Registers)
    (regs : NeighborhoodTrial.Registers controller) : Cmd :=
  Cmd.seq
    (buildProviderRoot workTapeCount controller regs)
    (QueryInitialization.initializeQuery workTapeCount regs)

end ProviderRootInitialization
end NeighborhoodMicrocode
end Runtime
end TimeSpaceSimulation
end Complexity
