/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/
import
  Complexitylib.TimeSpaceSimulation.Runtime.NeighborhoodMicrocode.Representation.Defs

/-!
# Active child-frame installation

These straight-line fragments finish a recursive descent after the caller has
packed the parent continuation and regenerated the child's node and target.
They decrement the inherited fuel, install the prepare or cleanup scalar, set
the enter phase, and leave the node, target, continuation word, parameters,
and catalytic bank untouched.
-/

namespace Complexity
namespace TimeSpaceSimulation
namespace Runtime
namespace NeighborhoodMicrocode
namespace FrameInstall

open RAM Structured

variable {controller : SearchProgram.Registers}

/-- Mutable cells used when installing a child frame. -/
def writeFootprint
    (regs : NeighborhoodTrial.Registers controller) : Finset ℕ :=
  {Layout.fuel regs, Layout.scalar regs,
    Layout.phaseCode regs, Layout.active regs}

/-- Finish installing a prepare-fold child. -/
def installPrepareChild
    (regs : NeighborhoodTrial.Registers controller) : Cmd :=
  Cmd.basics
    [.imm (Layout.scalar regs) 1,
      .sub (Layout.fuel regs) (Layout.fuel regs) (Layout.scalar regs),
      .imm (Layout.phaseCode regs) 0,
      .imm (Layout.active regs) 1]

/-- Finish installing a cleanup-fold child. -/
def installCleanupChild
    (regs : NeighborhoodTrial.Registers controller) : Cmd :=
  Cmd.basics
    [.imm (Layout.scalar regs) 1,
      .sub (Layout.fuel regs) (Layout.fuel regs) (Layout.scalar regs),
      .imm (Layout.scalar regs) 0,
      .add (Layout.scalar regs)
        (Layout.modulusPred regs) (Layout.scalar regs),
      .imm (Layout.phaseCode regs) 0,
      .imm (Layout.active regs) 1]

/-- Exact observable result shared by both child installers. -/
structure InstallPost
    (regs : NeighborhoodTrial.Registers controller)
    (scalar : ℕ) (initial final : Store) : Prop where
  /-- Child fuel is the predecessor of the parent fuel. -/
  fuel_eq :
    final (Layout.fuel regs) = initial (Layout.fuel regs) - 1
  /-- The regenerated child node is retained. -/
  nodeCode_eq :
    final (Layout.nodeCode regs) = initial (Layout.nodeCode regs)
  /-- The selected recursive-call scalar is installed literally. -/
  scalar_eq : final (Layout.scalar regs) = scalar
  /-- The selected catalytic target is retained. -/
  out_eq : final (Layout.out regs) = initial (Layout.out regs)
  /-- Every recursive child starts in the enter phase. -/
  phaseCode_eq : final (Layout.phaseCode regs) = 0
  /-- The child becomes the live active frame. -/
  active_eq : final (Layout.active regs) = 1
  /-- Every cell outside the exact four-cell footprint is preserved. -/
  eq_outside :
    ∀ address, address ∉ writeFootprint regs →
      final address = initial address

end FrameInstall
end NeighborhoodMicrocode
end Runtime
end TimeSpaceSimulation
end Complexity
