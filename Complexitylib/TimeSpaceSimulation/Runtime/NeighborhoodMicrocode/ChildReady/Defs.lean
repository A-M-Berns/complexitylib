/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/
import
  Complexitylib.TimeSpaceSimulation.Runtime.NeighborhoodMicrocode.ChildNode
import
  Complexitylib.TimeSpaceSimulation.Runtime.NeighborhoodMicrocode.Dispatcher
import
  Complexitylib.TimeSpaceSimulation.Runtime.NeighborhoodMicrocode.Representation

/-!
# Regenerating a child node and catalytic target

The generic child-node dispatcher uses the active output field as scratch.
This layer saves the suspended parent's output coordinate in the one spare
physical slot, decodes and regenerates the child, then restores the parent
output and embeds the saved child cursor around it. The result is exactly the
node and target ABI consumed by active-child installation.
-/

namespace Complexity
namespace TimeSpaceSimulation
namespace Runtime
namespace NeighborhoodMicrocode
namespace ChildReady

open RAM Structured

variable {controller : SearchProgram.Registers}

/-- Spare cell retaining the parent output across child regeneration. -/
abbrev savedParentOut
    (regs : NeighborhoodTrial.Registers controller) : ℕ :=
  regs.index 1

/-- Restore the parent output and compute its selected child target. -/
def restoreTarget
    (regs : NeighborhoodTrial.Registers controller) : Cmd :=
  Cmd.seqList
    [ControlDecode.copy
      (Layout.out regs) (savedParentOut regs),
      ControlDecode.copy
        (Dispatcher.decodedChild regs)
        (ChildNode.savedChildIndex regs),
      .basic
        (.imm (Dispatcher.cleanupInverseRegisters regs).one 1),
      Dispatcher.selectChildTarget regs]

/-- Decode the suspended parent, regenerate the selected child node, and
install the child's catalytic target. -/
def prepare
    (workTapeCount : ℕ)
    (controller : SearchProgram.Registers)
    (regs : NeighborhoodTrial.Registers controller) : Cmd :=
  Cmd.seqList
    [ControlDecode.copy
      (savedParentOut regs) (Layout.out regs),
      ControlDecode.decodeNode regs,
      ChildNode.regenerateChild workTapeCount controller regs,
      restoreTarget regs]

/-- One exact footprint for decode, regeneration, and target restoration. -/
def writeFootprint
    (regs : NeighborhoodTrial.Registers controller) : Finset ℕ :=
  insert (savedParentOut regs) (ChildNode.priorAssemblyFootprint regs)

/-- Observable child-node and target result. -/
structure ReadyPost
    (regs : NeighborhoodTrial.Registers controller)
    (node : NeighborhoodEvaluator.QueryNode workTapeCount horizon)
    (target : ℕ) (initial final : Store) : Prop where
  /-- The regenerated node is encoded at the instance radix. -/
  nodeCode_eq :
    final (Layout.nodeCode regs) =
      FrameCodec.encodeNode
        (initial (Layout.chunkRadix regs)) node
  /-- The child catalytic target is installed literally. -/
  out_eq : final (Layout.out regs) = target
  /-- Parent recursion fuel survives regeneration. -/
  fuel_eq :
    final (Layout.fuel regs) = initial (Layout.fuel regs)
  /-- Every cell outside the exact fixed footprint is preserved. -/
  eq_outside :
    ∀ address, address ∉ writeFootprint regs →
      final address = initial address

end ChildReady
end NeighborhoodMicrocode
end Runtime
end TimeSpaceSimulation
end Complexity
