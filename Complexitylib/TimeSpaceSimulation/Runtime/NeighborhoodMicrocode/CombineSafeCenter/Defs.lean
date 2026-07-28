/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/
import
  Complexitylib.TimeSpaceSimulation.Runtime.NeighborhoodMicrocode.ChildNode.Defs
import
  Complexitylib.TimeSpaceSimulation.Runtime.NeighborhoodMicrocode.CombineTerm.Defs

/-!
# Combine-safe guessed-center reconstruction

The general child-regeneration center decoder uses cells owned by the outer
combine range. This definitions layer reallocates the same ternary-prefix
scan entirely into combine scratch. The selected tape and interval are copied
before their decoded-field cells are reused by the digit decoder.
-/

namespace Complexity
namespace TimeSpaceSimulation
namespace Runtime
namespace NeighborhoodMicrocode
namespace CombineSafeCenter

open RAM Structured

variable {controller : SearchProgram.Registers}

/-- Six combine-scratch cells used by dynamic ternary digit lookup.

The order is value, quotient, test, one, divisor, and cursor. -/
def digitMap : Fin 6 → Fin 34 :=
  ![0, 4, 5, 9, 11, 30]

theorem digitMap_injective :
    Function.Injective digitMap := by
  decide

/-- Dynamic digit-decoder view whose mutable cells avoid every live combine
range field. -/
def digitRegisters
    (regs : NeighborhoodTrial.Registers controller) :
    CombineTerm.DigitRegisters where
  index := fun slot => regs.index (digitMap slot)
  injective := regs.injective.comp digitMap_injective

/-- Five combine-scratch cells retained across one center-prefix scan.

The order is stride, center, validity, remaining boundaries, and next digit
index. -/
def centerMap : Fin 5 → Fin 34 :=
  ![6, 1, 12, 20, 29]

theorem centerMap_injective :
    Function.Injective centerMap := by
  decide

/-- Fixed distance between consecutive movement digits for one named tape. -/
abbrev centerStride
    (regs : NeighborhoodTrial.Registers controller) : ℕ :=
  regs.index (centerMap 0)

/-- Current reconstructed center block. -/
abbrev centerValue
    (regs : NeighborhoodTrial.Registers controller) : ℕ :=
  regs.index (centerMap 1)

/-- One exactly while the scanned movement prefix remains valid. -/
abbrev centerValid
    (regs : NeighborhoodTrial.Registers controller) : ℕ :=
  regs.index (centerMap 2)

/-- Number of movement boundaries still to scan. -/
abbrev centerRemaining
    (regs : NeighborhoodTrial.Registers controller) : ℕ :=
  regs.index (centerMap 3)

/-- Packed-guess digit index for the next boundary of the selected tape. -/
abbrev centerNextIndex
    (regs : NeighborhoodTrial.Registers controller) : ℕ :=
  regs.index (centerMap 4)

/-- The eleven collision-free physical cells used by center reconstruction. -/
def scratchMap : Fin 11 → Fin 34 :=
  ![0, 4, 5, 9, 11, 30, 6, 1, 12, 20, 29]

theorem scratchMap_injective :
    Function.Injective scratchMap := by
  decide

/-- Exact mutable footprint of combine-safe center reconstruction. -/
def footprint
    (regs : NeighborhoodTrial.Registers controller) : Finset ℕ :=
  Finset.univ.image fun slot => regs.index (scratchMap slot)

/-- Advance the selected tape's digit index and exhaust one boundary. -/
def advanceCenter
    (regs : NeighborhoodTrial.Registers controller) : Cmd :=
  let digit := digitRegisters regs
  Cmd.basics
    [.add (centerNextIndex regs)
        (centerNextIndex regs) (centerStride regs),
      .sub (centerRemaining regs)
        (centerRemaining regs) digit.one]

/-- Terminate a scan after an invalid left move from block zero. -/
def invalidateCenter
    (regs : NeighborhoodTrial.Registers controller) : Cmd :=
  Cmd.basics
    [.imm (centerValid regs) 0,
      .imm (centerRemaining regs) 0]

/-- Apply a decoded left movement. -/
def applyLeftMovement
    (regs : NeighborhoodTrial.Registers controller) : Cmd :=
  let digit := digitRegisters regs
  .ifZero (centerValue regs)
    (invalidateCenter regs)
    (Cmd.seq
      (.basic
        (.sub (centerValue regs) (centerValue regs) digit.one))
      (advanceCenter regs))

/-- Apply a decoded stay or right movement. -/
def applyNonleftMovement
    (regs : NeighborhoodTrial.Registers controller) : Cmd :=
  let digit := digitRegisters regs
  Cmd.seq
    (.basic (.sub digit.test digit.value digit.one))
    (.ifZero digit.test
      (advanceCenter regs)
      (Cmd.seq
        (.basic
          (.add (centerValue regs) (centerValue regs) digit.one))
        (advanceCenter regs)))

/-- Apply the selected ternary digit to the current center. -/
def applySelectedMovement
    (regs : NeighborhoodTrial.Registers controller) : Cmd :=
  let digit := digitRegisters regs
  .ifZero digit.value
    (applyLeftMovement regs)
    (applyNonleftMovement regs)

/-- One center-prefix iteration: reload the read-only guess, select the
runtime digit, and update the center. -/
def centerStep
    (controller : SearchProgram.Registers)
    (regs : NeighborhoodTrial.Registers controller) : Cmd :=
  let digit := digitRegisters regs
  Cmd.seqList
    [CombineTerm.copy digit.cursor (centerNextIndex regs),
      CombineTerm.copy digit.value controller.guess,
      CombineTerm.seekDigit digit,
      applySelectedMovement regs]

/-- Copy the decoded tape and interval before their cells become the digit
decoder's one and divisor registers, then initialize the canonical scan. -/
def initializeCenter
    (workTapeCount : ℕ)
    (regs : NeighborhoodTrial.Registers controller) : Cmd :=
  let digit := digitRegisters regs
  Cmd.seqList
    [CombineTerm.copy
      (centerRemaining regs) (ControlDecode.nodePayload1 regs),
      CombineTerm.copy
        (centerNextIndex regs) (ControlDecode.nodeTape regs),
      .basic (.imm digit.one 1),
      .basic (.imm digit.divisor 3),
      .basic (.imm (centerValue regs) 0),
      .basic (.imm (centerValid regs) 1),
      .basic (.imm (centerStride regs) (workTapeCount + 2))]

/-- Reconstruct one guessed center without touching live combine fields. -/
def deriveCenter
    (workTapeCount : ℕ)
    (controller : SearchProgram.Registers)
    (regs : NeighborhoodTrial.Registers controller) : Cmd :=
  Cmd.seq
    (initializeCenter workTapeCount regs)
    (.whileNonzero (centerRemaining regs)
      (centerStep controller regs))

/-- Exact observable result of combine-safe center reconstruction. -/
structure Post
    (workTapeCount word tape interval : ℕ)
    (controller : SearchProgram.Registers)
    (regs : NeighborhoodTrial.Registers controller)
    (initial final : Store) : Prop where
  /-- The validity flag is the exact option discriminator. -/
  valid_eq :
    final (centerValid regs) =
      ChildNode.centerValidValue
        (ChildNode.derivedCenterValue
          workTapeCount word tape interval)
  /-- The numeric center is exact, with canonical zero on failure. -/
  center_eq :
    final (centerValue regs) =
      ChildNode.centerOutputValue
        (ChildNode.derivedCenterValue
          workTapeCount word tape interval)
  /-- The boundary countdown is exhausted on success and failure. -/
  remaining_eq : final (centerRemaining regs) = 0
  /-- The read-only movement guess is preserved. -/
  guess_eq : final controller.guess = word
  /-- Every address outside the eleven-cell scratch footprint is preserved. -/
  eq_outside :
    ∀ address, address ∉ footprint regs →
      final address = initial address

/-- The live combine range and stable computation context preserved by the
scratch-only decoder. The packed-factor destination is intentionally absent:
physical slot six is available as center stride scratch until the factor is
finally produced. -/
structure PreservesCombine
    (regs : NeighborhoodTrial.Registers controller)
    (initial final : Store) : Prop where
  /-- Outer modular-sum accumulator is preserved. -/
  accumulator_eq :
    final (CombineValue.rangeRegisters regs).accumulator =
      initial (CombineValue.rangeRegisters regs).accumulator
  /-- Current assignment code is preserved. -/
  assignment_eq :
    final (CombineValue.rangeRegisters regs).remaining =
      initial (CombineValue.rangeRegisters regs).remaining
  /-- Outer term cell is preserved. -/
  term_eq :
    final (CombineValue.rangeRegisters regs).term =
      initial (CombineValue.rangeRegisters regs).term
  /-- Outer range constant one is preserved. -/
  one_eq :
    final (CombineValue.rangeRegisters regs).one =
      initial (CombineValue.rangeRegisters regs).one
  /-- Immutable assignment count is preserved. -/
  count_eq :
    final (CombineValue.rangeRegisters regs).count =
      initial (CombineValue.rangeRegisters regs).count
  /-- Runtime payload-position input is preserved. -/
  codecScratch_eq :
    final (Layout.codecScratch regs) =
      initial (Layout.codecScratch regs)
  /-- Suspended continuation stack is preserved. -/
  stack_eq :
    final regs.layout.stack = initial regs.layout.stack
  /-- Packed catalytic bank is preserved. -/
  bank_eq :
    final regs.layout.bank = initial regs.layout.bank
  /-- Stable parameter and active-frame ABI fields are preserved. -/
  abi : ControlDecode.PreservesABI regs initial final

end CombineSafeCenter
end NeighborhoodMicrocode
end Runtime
end TimeSpaceSimulation
end Complexity
