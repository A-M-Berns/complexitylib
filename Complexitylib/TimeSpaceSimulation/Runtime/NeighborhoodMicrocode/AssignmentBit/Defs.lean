/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/
import
  Complexitylib.TimeSpaceSimulation.Runtime.NeighborhoodMicrocode.CombineTerm.Defs

/-!
# Uniform Boolean lookup in a streamed grouped assignment

The grouped combine loop stores its current assignment as one natural number.
This module provides the fixed-register primitive needed by the Boolean local
transition: extract one dynamic binary digit without specializing the command
to the runtime candidate, payload width, or chunk count.
-/

namespace Complexity
namespace TimeSpaceSimulation
namespace Runtime
namespace NeighborhoodMicrocode
namespace AssignmentBit

open RAM Structured

variable {controller : SearchProgram.Registers}

/-- Six scratch registers used by binary digit extraction.

The output is `CombineTerm.packedValue`; the other five cells are disjoint
from the enclosing range interface and every persistent evaluator field.
-/
def digitMap : Fin 6 → Fin 34 :=
  ![6, 20, 4, 9, 11, 30]

theorem digitMap_injective :
    Function.Injective digitMap := by
  decide

/-- Dynamic binary-digit view in the shared combine scratch. -/
def digitRegisters
    (regs : NeighborhoodTrial.Registers controller) :
    CombineTerm.DigitRegisters where
  index := fun slot => regs.index (digitMap slot)
  injective := regs.injective.comp digitMap_injective

/-- Source register containing the requested low-order binary digit index. -/
abbrev digitIndex
    (regs : NeighborhoodTrial.Registers controller) : ℕ :=
  regs.index 29

/-- Exact direct-write footprint, including the scratch divisor initialized
to two. -/
def writeFootprint
    (regs : NeighborhoodTrial.Registers controller) : Finset ℕ :=
  (digitRegisters regs).writeFootprint ∪
    {(digitRegisters regs).divisor}

/-- Extract one dynamic low-order bit from the current assignment code.

The assignment itself remains in the outer range countdown cell. The selected
numeric bit is returned in `CombineTerm.packedValue`.
-/
def read
    (regs : NeighborhoodTrial.Registers controller) : Cmd :=
  let digit := digitRegisters regs
  let range := CombineValue.rangeRegisters regs
  Cmd.seqList
    [CombineTerm.copy digit.value range.remaining,
      CombineTerm.copy digit.cursor (digitIndex regs),
      .basic (.imm digit.divisor 2),
      CombineTerm.seekDigit digit]

/-- Observable result and frame of one assignment-bit lookup. -/
structure Post
    (regs : NeighborhoodTrial.Registers controller)
    (code index : ℕ) (initial final : Store) : Prop where
  /-- The output is the selected low-order binary digit. -/
  value_eq :
    final (CombineTerm.packedValue regs) =
      CombineTerm.radixDigit 2 code index
  /-- The outer range accumulator is preserved. -/
  accumulator_eq :
    final (CombineValue.rangeRegisters regs).accumulator =
      initial (CombineValue.rangeRegisters regs).accumulator
  /-- The assignment code is preserved. -/
  remaining_eq :
    final (CombineValue.rangeRegisters regs).remaining = code
  /-- The field modulus is preserved. -/
  modulus_eq :
    final (CombineValue.rangeRegisters regs).modulus =
      initial (CombineValue.rangeRegisters regs).modulus
  /-- The field-modulus predecessor is preserved. -/
  modulusPred_eq :
    final (CombineValue.rangeRegisters regs).modulusPred =
      initial (CombineValue.rangeRegisters regs).modulusPred
  /-- The outer range constant one is preserved. -/
  one_eq :
    final (CombineValue.rangeRegisters regs).one =
      initial (CombineValue.rangeRegisters regs).one
  /-- The immutable assignment count is preserved. -/
  count_eq :
    final (CombineValue.rangeRegisters regs).count =
      initial (CombineValue.rangeRegisters regs).count
  /-- The requested digit index is preserved. -/
  index_eq : final (digitIndex regs) = index
  /-- Every cell outside the exact write footprint is preserved. -/
  eq_outside :
    ∀ address, address ∉ writeFootprint regs →
      final address = initial address

end AssignmentBit
end NeighborhoodMicrocode
end Runtime
end TimeSpaceSimulation
end Complexity
