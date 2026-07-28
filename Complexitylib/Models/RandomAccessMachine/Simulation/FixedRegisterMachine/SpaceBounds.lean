/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/
import
  Complexitylib.Models.RandomAccessMachine.Simulation.FixedRegisterMachine.Defs
import
  Complexitylib.Models.RandomAccessMachine.Simulation.RegisterStore.Machine.DenseInputLookup
import Complexitylib.Models.TuringMachine.Subroutines.BinaryAddConst
import Complexitylib.Models.TuringMachine.Subroutines.BinaryCopy
import Complexitylib.Models.TuringMachine.Subroutines.BinaryPred
import Complexitylib.Models.TuringMachine.Subroutines.BinaryRippleSub
import Complexitylib.Models.TuringMachine.Subroutines.BinaryShiftMul

/-!
# Linear space envelopes for direct fixed-register instructions

The direct RAM compiler represents every mutable word on its own tape.  This
file packages the elementary arithmetic showing that each concrete binary
subroutine fits the compiler's single linear `instructionSpace` budget when
its operands fit the advertised word width.
-/

namespace Complexity
namespace RAM
namespace FixedRegisterMachine

/-- The uniform instruction budget is always nonzero. -/
theorem one_le_instructionSpace (wordBits : ℕ) :
    1 ≤ instructionSpace wordBits := by
  unfold instructionSpace
  omega

/-- Clearing and copying one bounded word fits the uniform instruction
budget. -/
theorem binaryCopySpace_le_instructionSpace
    {source destination wordBits : ℕ}
    (hsource : source.size ≤ wordBits)
    (hdestination : destination.size ≤ wordBits) :
    TM.binaryCopySpace 1 source destination ≤
      instructionSpace wordBits := by
  have hadd := TM.binaryRippleAddTime_le source 0
  simp only [Nat.size_zero] at hadd
  unfold TM.binaryCopySpace
  apply max_le
  · unfold TM.clearWorkTimeBound instructionSpace
    omega
  · unfold instructionSpace
    omega

/-- One successor phase on a bounded word fits the uniform instruction
budget. -/
theorem binarySuccSpace_le_instructionSpace
    {value wordBits : ℕ} (hvalue : value.size ≤ wordBits) :
    1 + TM.binarySuccTime value ≤ instructionSpace wordBits := by
  have htime := TM.binarySuccTime_le value
  simp only [instructionSpace]
  omega

/-- Predecessor on a bounded positive word fits the uniform instruction
budget.  The `value - 1` argument is the predecessor routine's result
parameter. -/
theorem binaryPredSpace_le_instructionSpace
    {value wordBits : ℕ} (hvalue : value.size ≤ wordBits) :
    TM.binaryPredSpace 1 (value - 1) ≤ instructionSpace wordBits := by
  cases value with
  | zero =>
      simp only [Nat.zero_sub, TM.binaryPredSpace, Nat.zero_add,
        Nat.size_one]
      unfold instructionSpace
      omega
  | succ value =>
      simp only [Nat.succ_sub_one, TM.binaryPredSpace]
      have hsize : (value + 1).size ≤ wordBits := by
        simpa [Nat.succ_eq_add_one] using hvalue
      simp only [instructionSpace]
      omega

/-- Ripple addition on two bounded words fits the uniform instruction
budget. -/
theorem binaryRippleAddSpace_le_instructionSpace
    {left right wordBits : ℕ}
    (hleft : left.size ≤ wordBits)
    (hright : right.size ≤ wordBits) :
    1 + TM.binaryRippleAddTime left right ≤
      instructionSpace wordBits := by
  have htime := TM.binaryRippleAddTime_le left right
  simp only [instructionSpace]
  omega

/-- Ripple subtraction on two bounded words fits the uniform instruction
budget. -/
theorem binaryRippleSubSpace_le_instructionSpace
    {left right wordBits : ℕ}
    (hleft : left.size ≤ wordBits)
    (hright : right.size ≤ wordBits) :
    1 + TM.binaryRippleSubTime left right ≤
      instructionSpace wordBits := by
  have htime := TM.binaryRippleSubTime_le left right
  simp only [instructionSpace]
  omega

/-- Shift-and-add multiplication on two bounded words fits the uniform
instruction budget. -/
theorem binaryShiftMulSpace_le_instructionSpace
    {left right wordBits : ℕ}
    (hleft : left.size ≤ wordBits)
    (hright : right.size ≤ wordBits) :
    TM.binaryShiftMulLinearSpace 1 left right ≤
      instructionSpace wordBits := by
  simp only [TM.binaryShiftMulLinearSpace,
    TM.binaryShiftMulWidth, instructionSpace]
  omega

/-- Adding a fixed bounded constant to zero fits the uniform instruction
budget. -/
theorem binaryAddConstSpace_le_instructionSpace
    {constant wordBits : ℕ}
    (hconstant : constant.size ≤ wordBits) :
    TM.binaryAddConstSpace 1 constant 0 ≤
      instructionSpace wordBits := by
  simp only [TM.binaryAddConstSpace, zero_add, instructionSpace]
  omega

/-- Scanning the immutable dense input at a bounded address fits the uniform
instruction budget. -/
theorem denseInputScanSpace_le_instructionSpace
    {address wordBits : ℕ}
    (haddress : address.size ≤ wordBits) :
    RegisterStore.Machine.denseInputScanSpace 1 address ≤
      instructionSpace wordBits := by
  simp only [RegisterStore.Machine.denseInputScanSpace, instructionSpace]
  omega

end FixedRegisterMachine
end RAM
end Complexity
