/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/
import
  Complexitylib.TimeSpaceSimulation.Runtime.NeighborhoodMicrocode.Layout.Defs

/-!
# Register layout for the concrete neighborhood microcode -- proofs
-/

namespace Complexity
namespace TimeSpaceSimulation
namespace Runtime
namespace NeighborhoodMicrocode
namespace Layout
namespace Internal

open RAM Structured

variable {controller : SearchProgram.Registers}

theorem index_mem_layout_footprint_internal
    (regs : NeighborhoodTrial.Registers controller) (slot : Fin 34) :
    regs.index slot ∈ regs.layout.footprint := by
  by_cases hfixed : slot.val < 32
  · let fixedSlot : Fin NeighborhoodProgram.fixedRegisterCount :=
      ⟨slot.val, by
        simpa [NeighborhoodProgram.fixedRegisterCount] using hfixed⟩
    have hslot :
        slot = NeighborhoodTrial.Registers.fixedSlot fixedSlot := by
      apply Fin.ext
      rfl
    rw [hslot]
    exact NeighborhoodProgram.Layout.fixed_mem_footprint regs.layout fixedSlot
  · have hlast : slot.val = 32 ∨ slot.val = 33 := by
      omega
    rcases hlast with hstack | hbank
    · have hslot : slot = (32 : Fin 34) := Fin.ext hstack
      rw [hslot]
      exact NeighborhoodProgram.Layout.stack_mem_footprint regs.layout
    · have hslot : slot = (33 : Fin 34) := Fin.ext hbank
      rw [hslot]
      exact NeighborhoodProgram.Layout.bank_mem_footprint regs.layout

theorem residueScale_footprint_subset_internal
    (regs : NeighborhoodTrial.Registers controller) :
    (residueScaleRegisters regs).footprint ⊆
      regs.layout.footprint := by
  intro address haddress
  obtain ⟨slot, _, rfl⟩ := Finset.mem_image.mp haddress
  exact index_mem_layout_footprint_internal
    regs (residueScaleMap slot)

theorem frameStack_footprint_subset_internal
    (regs : NeighborhoodTrial.Registers controller) :
    (frameStackRegisters regs).footprint ⊆
      regs.layout.footprint := by
  intro address haddress
  obtain ⟨slot, _, rfl⟩ := Finset.mem_image.mp haddress
  exact index_mem_layout_footprint_internal
    regs (frameStackMap slot)

theorem frameCodec_footprint_subset_internal
    (regs : NeighborhoodTrial.Registers controller) :
    (frameCodecRegisters regs).footprint ⊆
      regs.layout.footprint := by
  intro address haddress
  obtain ⟨slot, _, rfl⟩ := Finset.mem_image.mp haddress
  exact index_mem_layout_footprint_internal
    regs (frameCodecMap slot)

end Internal
end Layout
end NeighborhoodMicrocode
end Runtime
end TimeSpaceSimulation
end Complexity
