/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/
import Complexitylib.TimeSpaceSimulation.Runtime.SearchEnvelope.Internal

/-!
# Concrete outer-search resource envelopes

This module discharges reusable all-prefix obligations left abstract by the
generic first-order search controller.
-/

namespace Complexity

namespace TimeSpaceSimulation

namespace Runtime

namespace SearchEnvelope

open RAM Structured

/-- The uniform input-cache prelude satisfies the controller's common
mutable-value invariant at every source-program point. -/
theorem cacheInvariantRuns
    (regs : SearchProgram.Registers)
    (kernel : SearchProgram.TrialKernel regs)
    (input : List Bool) (valueBits : ℕ)
    (hone : 1 ≤ valueBits)
    (hinput : bitlen input.length ≤ valueBits)
    (hlimit :
      SearchProgram.footprintLimit regs kernel.footprint ≤
        valueBits) :
    ∃ cached steps,
      InvariantRuns
        (SearchProgram.MutableValuesWithin
          (regs.footprint ∪ kernel.footprint) valueBits)
        (SearchProgram.cacheInputPrefix regs
          (SearchProgram.footprintLimit regs kernel.footprint))
        (RAM.initRegs input) cached steps ∧
      SearchProgram.InputFrame
        regs kernel.footprint input cached :=
  Internal.cacheInvariantRuns_internal regs kernel input valueBits
    hone hinput hlimit

/-- Assemble the controller's complete all-prefix envelope from concrete
cache bounds, the uniform two-bit prime-search cushion, and the abstract
trial kernel's candidate-range bounds. -/
theorem prefixEnvelopeOfBounds
    (regs : SearchProgram.Registers)
    (kernel : SearchProgram.TrialKernel regs)
    (input : List Bool) (target valueBits : ℕ)
    (hinput : bitlen input.length ≤ valueBits)
    (hlimit :
      SearchProgram.footprintLimit regs kernel.footprint ≤
        valueBits)
    (htarget : bitlen target + 2 ≤ valueBits)
    (hguessCount :
      ∀ candidate,
        input.length ≤ candidate →
        candidate ≤ target →
        bitlen (kernel.guessCount candidate) ≤ valueBits)
    (hkernelPrefix :
      ∀ candidate,
        input.length ≤ candidate →
        candidate ≤ target →
        ∀ prime guess,
          guess < kernel.guessCount candidate →
          kernel.prefixValueBits input candidate prime guess ≤
            valueBits) :
    SearchProgram.PrefixEnvelope
      regs kernel input target valueBits :=
  Internal.prefixEnvelopeOfBounds_internal regs kernel input target
    valueBits hinput hlimit htarget hguessCount hkernelPrefix

end SearchEnvelope

end Runtime

end TimeSpaceSimulation

end Complexity
