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
# Uniform initialization of the state-consistency root

The state root has a particularly small runtime description. At horizon zero
it is input block zero, because enumerated guesses fix every initial center at
zero. At a positive horizon it is the center slot of the preceding input-tape
interval. This module builds those fields from the retained horizon register
and then initializes the represented query.
-/

namespace Complexity
namespace TimeSpaceSimulation
namespace Runtime
namespace NeighborhoodMicrocode
namespace StateRootInitialization

open RAM Structured

variable {controller : SearchProgram.Registers}

/-- Direct destinations used while building the packed state-root node. -/
def rootFootprint
    (regs : NeighborhoodTrial.Registers controller) : Finset ℕ :=
  {ControlDecode.nodeTape regs,
    ControlDecode.nodePayload0 regs,
    ControlDecode.nodePayload1 regs,
    Layout.nodeCode regs,
    Layout.codecDigit regs}

/-- Field initialization for the horizon-zero input-source root. -/
def sourceFields
    (regs : NeighborhoodTrial.Registers controller) : Cmd :=
  Cmd.basics
    [.imm (ControlDecode.nodeTape regs) 0,
      .imm (ControlDecode.nodePayload0 regs) 0,
      .imm (ControlDecode.nodePayload1 regs) 0]

/-- Field initialization for a positive-horizon input computation root. -/
def computationFields
    (controller : SearchProgram.Registers)
    (regs : NeighborhoodTrial.Registers controller) : Cmd :=
  Cmd.basics
    [.imm (ControlDecode.nodeTape regs) 0,
      .imm (ControlDecode.nodePayload0 regs)
        NeighborhoodGraph.Slot.center.toFin.val,
      .sub (ControlDecode.nodePayload1 regs)
        (Layout.horizon regs) controller.one]

/-- Build the packed state-consistency root from the retained runtime
horizon. The command is fixed by the source-machine tape count and register
allocation; it does not contain an instance, guess, or frame. -/
def buildStateRoot
    (controller : SearchProgram.Registers)
    (regs : NeighborhoodTrial.Registers controller) : Cmd :=
  .ifZero (Layout.horizon regs)
    (Cmd.seq
      (sourceFields regs)
      (ChildNode.encodeNodeFields regs 1))
    (Cmd.seq
      (computationFields controller regs)
      (ChildNode.encodeNodeFields regs 2))

/-- Build the state root and install the singleton represented query. -/
def initializeStateQuery
    (workTapeCount : ℕ)
    (controller : SearchProgram.Registers)
    (regs : NeighborhoodTrial.Registers controller) : Cmd :=
  Cmd.seq
    (buildStateRoot controller regs)
    (QueryInitialization.initializeQuery workTapeCount regs)

end StateRootInitialization
end NeighborhoodMicrocode
end Runtime
end TimeSpaceSimulation
end Complexity
