/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/
import
  Complexitylib.Models.RandomAccessMachine.Simulation.RegisterStore.DenseOverlay.Footprint.Defs
import Complexitylib.Models.RandomAccessMachine.Structured.Defs

/-!
# Fixed write footprints for structured RAM programs

This source-level predicate rejects indirect stores and checks every direct
destination against one finite register set.
-/

namespace Complexity

namespace RAM

namespace Structured

namespace Footprint

open RegisterStore DenseOverlay FixedRegisters

/-- One source-level data instruction writes only within `allowed`. -/
def BasicWritesWithin (allowed : Finset ℕ) : Basic → Prop
  | .imm destination _ => destination ∈ allowed
  | .add destination _ _ => destination ∈ allowed
  | .sub destination _ _ => destination ∈ allowed
  | .mul destination _ _ => destination ∈ allowed
  | .load destination _ => destination ∈ allowed
  | .store _ _ => False

/-- Every source-level data write in a structured command targets `allowed`. -/
def CmdWritesWithin (allowed : Finset ℕ) : Cmd → Prop
  | .skip => True
  | .basic op => BasicWritesWithin allowed op
  | .seq first second =>
      CmdWritesWithin allowed first ∧ CmdWritesWithin allowed second
  | .ifZero _ onZero onNonzero =>
      CmdWritesWithin allowed onZero ∧
        CmdWritesWithin allowed onNonzero
  | .whileNonzero _ body => CmdWritesWithin allowed body

end Footprint

end Structured

end RAM

end Complexity
