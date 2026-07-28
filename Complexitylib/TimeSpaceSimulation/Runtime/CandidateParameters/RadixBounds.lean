/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/
import
  Complexitylib.TimeSpaceSimulation.Runtime.CandidateParameters.RadixBounds.Internal

/-!
# Radix bounds for runtime candidate parameters

These theorems show that the canonical chunk radix covers every compact
graph index and that the canonical searched modulus fits in the two-digit
field radix. They also identify the exact powers used for catalytic-bank
digits and suspended scheduler frames.
-/

namespace Complexity
namespace TimeSpaceSimulation
namespace Runtime
namespace CandidateParameters
namespace RadixBounds

/-- The Boolean neighborhood payload fits in one chunk-radix digit. -/
theorem booleanWidth_lt_domainSize
    (Q : Type*) [Fintype Q] (workTapeCount candidate : ℕ) :
    booleanWidth Q candidate <
      domainSize Q workTapeCount candidate :=
  Internal.booleanWidth_lt_domainSize_internal
    Q workTapeCount candidate

/-- The graph fan-in fits in one chunk-radix digit. -/
theorem fanIn_lt_domainSize
    (Q : Type*) [Fintype Q] (workTapeCount candidate : ℕ) :
    fanIn workTapeCount <
      domainSize Q workTapeCount candidate :=
  Internal.fanIn_lt_domainSize_internal
    Q workTapeCount candidate

/-- The balanced block length fits in one chunk-radix digit. -/
theorem blockLength_lt_domainSize
    (Q : Type*) [Fintype Q] (workTapeCount candidate : ℕ) :
    blockLength candidate <
      domainSize Q workTapeCount candidate :=
  Internal.blockLength_lt_domainSize_internal
    Q workTapeCount candidate

/-- The balanced interval horizon fits in one chunk-radix digit. -/
theorem horizon_lt_domainSize
    (Q : Type*) [Fintype Q] (workTapeCount candidate : ℕ) :
    horizon candidate <
      domainSize Q workTapeCount candidate :=
  Internal.horizon_lt_domainSize_internal
    Q workTapeCount candidate

/-- The source machine state count fits in one chunk-radix digit. -/
theorem card_lt_domainSize
    (Q : Type*) [Fintype Q] (workTapeCount candidate : ℕ) :
    Fintype.card Q <
      domainSize Q workTapeCount candidate :=
  Internal.card_lt_domainSize_internal
    Q workTapeCount candidate

/-- The runtime chunk radix is strictly larger than one. -/
theorem one_lt_domainSize
    (Q : Type*) [Fintype Q] (workTapeCount candidate : ℕ) :
    1 < domainSize Q workTapeCount candidate :=
  Internal.one_lt_domainSize_internal
    Q workTapeCount candidate

/-- One packed catalytic-bank digit is exactly two chunk-radix digits. -/
theorem bankRadix_eq_domainSize_sq
    (Q : Type*) [Fintype Q] (workTapeCount candidate : ℕ) :
    bankRadix Q workTapeCount candidate =
      domainSize Q workTapeCount candidate ^ 2 :=
  Internal.bankRadix_eq_domainSize_sq_internal
    Q workTapeCount candidate

/-- One suspended evaluator frame is exactly twenty-four chunk-radix
digits. -/
theorem frameRadix_eq_domainSize_pow
    (Q : Type*) [Fintype Q] (workTapeCount candidate : ℕ) :
    frameRadix Q workTapeCount candidate =
      domainSize Q workTapeCount candidate ^ 24 :=
  Internal.frameRadix_eq_domainSize_pow_internal
    Q workTapeCount candidate

/-- The canonical searched modulus fits in the two-digit residue radix. -/
theorem canonicalModulus_lt_bankRadix
    (Q : Type*) [Fintype Q] (workTapeCount candidate : ℕ) :
    canonicalModulus Q workTapeCount candidate <
      bankRadix Q workTapeCount candidate :=
  Internal.canonicalModulus_lt_bankRadix_internal
    Q workTapeCount candidate

end RadixBounds
end CandidateParameters
end Runtime
end TimeSpaceSimulation
end Complexity
