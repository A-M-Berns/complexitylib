/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/
import
  Complexitylib.TimeSpaceSimulation.Runtime.NeighborhoodMicrocode.Layout.Internal

/-!
# Register layout for the concrete neighborhood microcode

This module exposes the collision-free register views shared by parameter
setup, active-frame control, packed continuation transfer, and catalytic-bank
updates.
-/

namespace Complexity
namespace TimeSpaceSimulation
namespace Runtime
namespace NeighborhoodMicrocode
namespace Layout

variable {controller : SearchProgram.Registers}

/-- Every physical workspace cell belongs to the packed evaluator layout. -/
theorem index_mem_layout_footprint
    (regs : NeighborhoodTrial.Registers controller) (slot : Fin 34) :
    regs.index slot ∈ regs.layout.footprint :=
  Internal.index_mem_layout_footprint_internal regs slot

/-- The residue-scaling view writes inside the one shared evaluator
footprint. -/
theorem residueScale_footprint_subset
    (regs : NeighborhoodTrial.Registers controller) :
    (residueScaleRegisters regs).footprint ⊆
      regs.layout.footprint :=
  Internal.residueScale_footprint_subset_internal regs

/-- The complete-frame stack-transfer view writes inside the one shared
evaluator footprint. -/
theorem frameStack_footprint_subset
    (regs : NeighborhoodTrial.Registers controller) :
    (frameStackRegisters regs).footprint ⊆
      regs.layout.footprint :=
  Internal.frameStack_footprint_subset_internal regs

/-- The fixed-width frame-decoding view writes inside the one shared
evaluator footprint. -/
theorem frameCodec_footprint_subset
    (regs : NeighborhoodTrial.Registers controller) :
    (frameCodecRegisters regs).footprint ⊆
      regs.layout.footprint :=
  Internal.frameCodec_footprint_subset_internal regs

end Layout
end NeighborhoodMicrocode
end Runtime
end TimeSpaceSimulation
end Complexity
