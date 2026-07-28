/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/
import
  Complexitylib.TimeSpaceSimulation.Runtime.NeighborhoodTrial.Defs

/-!
# Register layout for the concrete neighborhood microcode

The candidate-parameter pass and the evaluator share one thirty-two-register
scalar allocation, plus separate packed stack and catalytic-bank words.  This
module fixes the time-multiplexed views used by the evaluator:

* parameter cells needed throughout evaluation remain read-only;
* the seventeen-register residue-scaling interface reuses setup scratch;
* six cells hold the active defunctionalized frame and its loop flag;
* three cells support frame encoding and decoding.

All maps below target the single allocation in `NeighborhoodTrial.Registers`;
they do not introduce a second mutable footprint.
-/

namespace Complexity
namespace TimeSpaceSimulation
namespace Runtime
namespace NeighborhoodMicrocode
namespace Layout

open RAM Structured

variable {controller : SearchProgram.Registers}

/-- Physical slots for the residue-scaling interface.  Slot zero is the
separate packed catalytic-bank word.  Slots containing the bank radix,
modulus, and modulus predecessor are parameter outputs preserved after
setup. -/
def residueScaleMap : Fin 17 → Fin 34 :=
  ![33, 0, 14, 1, 4, 5, 17, 9, 10, 11, 12, 18, 24, 16, 19, 20, 21]

theorem residueScaleMap_injective :
    Function.Injective residueScaleMap := by
  decide

/-- Seventeen-register view used by packed catalytic-bank scaling. -/
def residueScaleRegisters
    (regs : NeighborhoodTrial.Registers controller) :
    NeighborhoodProgram.ResidueScaleRegisters where
  index := fun slot => regs.index (residueScaleMap slot)
  injective := regs.injective.comp residueScaleMap_injective

/-- Physical slots used to push and pop complete suspended-frame codes.
The packed stack itself is slot thirty-two and the frame radix is preserved
parameter slot thirteen. -/
def frameStackMap : Fin 7 → Fin 34 :=
  ![32, 13, 0, 4, 5, 17, 29]

theorem frameStackMap_injective :
    Function.Injective frameStackMap := by
  decide

/-- Packed-stack view whose `value` cell is the transient complete frame
code. -/
def frameStackRegisters
    (regs : NeighborhoodTrial.Registers controller) :
    NeighborhoodProgram.StackRegisters where
  index := fun slot => regs.index (frameStackMap slot)
  injective := regs.injective.comp frameStackMap_injective

/-- Physical slots used to stream fixed-width codec digits out of a complete
frame code.  Parameter slot eight contains `2 ^ chunkBits`, the codec radix.
-/
def frameCodecMap : Fin 7 → Fin 34 :=
  ![29, 8, 1, 4, 5, 17, 30]

theorem frameCodecMap_injective :
    Function.Injective frameCodecMap := by
  decide

/-- Packed-stack view used internally while decoding the transient complete
frame code. -/
def frameCodecRegisters
    (regs : NeighborhoodTrial.Registers controller) :
    NeighborhoodProgram.StackRegisters where
  index := fun slot => regs.index (frameCodecMap slot)
  injective := regs.injective.comp frameCodecMap_injective

/-- Remaining codec scratch, available as a digit counter or arithmetic
temporary. -/
abbrev codecScratch
    (regs : NeighborhoodTrial.Registers controller) : ℕ :=
  regs.index 31

/-- Active frame recursion fuel. -/
abbrev fuel (regs : NeighborhoodTrial.Registers controller) : ℕ :=
  regs.index 22

/-- Encoded active query node. -/
abbrev nodeCode (regs : NeighborhoodTrial.Registers controller) : ℕ :=
  regs.index 23

/-- Active field scalar. -/
abbrev scalar (regs : NeighborhoodTrial.Registers controller) : ℕ :=
  regs.index 25

/-- Active catalytic output-register index. -/
abbrev out (regs : NeighborhoodTrial.Registers controller) : ℕ :=
  regs.index 26

/-- Encoded active scheduler phase. -/
abbrev phaseCode (regs : NeighborhoodTrial.Registers controller) : ℕ :=
  regs.index 27

/-- Evaluator loop flag: one for a live active frame and zero for an empty
continuation stack. -/
abbrev active (regs : NeighborhoodTrial.Registers controller) : ℕ :=
  regs.index 28

/-- Transient complete frame code used during suspended-stack transfer. -/
abbrev frameCode (regs : NeighborhoodTrial.Registers controller) : ℕ :=
  regs.index 29

/-- Transient least-significant codec digit. -/
abbrev codecDigit (regs : NeighborhoodTrial.Registers controller) : ℕ :=
  regs.index 30

/-- Canonical block length retained from parameter setup. -/
abbrev blockLength
    (regs : NeighborhoodTrial.Registers controller) : ℕ :=
  regs.index 2

/-- Canonical interval horizon retained from parameter setup. -/
abbrev horizon (regs : NeighborhoodTrial.Registers controller) : ℕ :=
  regs.index 3

/-- Runtime radix `2 ^ chunkBits` used by the frame codec. -/
abbrev chunkRadix
    (regs : NeighborhoodTrial.Registers controller) : ℕ :=
  regs.index 8

/-- Number of grouped field chunks retained from parameter setup. -/
abbrev chunkCount
    (regs : NeighborhoodTrial.Registers controller) : ℕ :=
  regs.index 7

/-- Runtime radix for one suspended continuation frame. -/
abbrev frameRadix
    (regs : NeighborhoodTrial.Registers controller) : ℕ :=
  regs.index 13

/-- Runtime radix for one catalytic-bank digit. -/
abbrev bankRadix
    (regs : NeighborhoodTrial.Registers controller) : ℕ :=
  regs.index 14

/-- Number of packed catalytic-bank digits. -/
abbrev bankDigitCount
    (regs : NeighborhoodTrial.Registers controller) : ℕ :=
  regs.index 15

/-- Canonical field modulus produced by parameter setup. -/
abbrev modulus (regs : NeighborhoodTrial.Registers controller) : ℕ :=
  regs.index 24

/-- Canonical field-modulus predecessor produced by parameter setup. -/
abbrev modulusPred
    (regs : NeighborhoodTrial.Registers controller) : ℕ :=
  regs.index 16

end Layout
end NeighborhoodMicrocode
end Runtime
end TimeSpaceSimulation
end Complexity
