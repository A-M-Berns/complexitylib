/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/
import Complexitylib.TreeEvaluation.CookMertz.PrimeGrouped.Logarithmic

/-!
# Runtime bounds for logarithmic grouped Cook--Mertz evaluation

This proof layer records bounds that use the positive parameter regime of
the neighborhood application. In particular, once the Boolean payload has
width at least five and the fan-in is at least eight, the searched field
modulus fits in two chunk-radix digits.
-/

namespace Complexity
namespace TreeEval
namespace CookMertz
namespace PrimeGrouped
namespace Logarithmic
namespace RuntimeBounds
namespace Internal

open GroupedExtension.LogarithmicParameters

theorem searchModulus_lt_domainSize_sq_internal
    (payloadWidth fanIn : ℕ)
    (hpayload : 5 ≤ payloadWidth) (hfanIn : 8 ≤ fanIn) :
    PrimeField.Search.searchModulus
        (degreeEndpoint payloadWidth fanIn) <
      domainSize payloadWidth fanIn ^ 2 := by
  have hproduct : 4 ≤ fanIn * payloadWidth := by
    nlinarith
  have hlog : 2 ≤ Nat.log 2 (fanIn * payloadWidth) := by
    apply Nat.le_log_of_pow_le (by omega)
    norm_num
    omega
  have hchunkBits : 3 ≤ chunkBits payloadWidth fanIn := by
    simp only [GroupedExtension.LogarithmicParameters.chunkBits_eq]
    omega
  have hpayloadHalf :
      payloadWidth ≤
        chunkBits payloadWidth fanIn * (payloadWidth / 2) := by
    have hhalf : payloadWidth ≤ 3 * (payloadWidth / 2) := by
      omega
    exact hhalf.trans
      (Nat.mul_le_mul_right (payloadWidth / 2) hchunkBits)
  have hchunkCountHalf :
      chunkCount payloadWidth fanIn ≤ payloadWidth / 2 := by
    change payloadWidth ⌈/⌉ chunkBits payloadWidth fanIn ≤
      payloadWidth / 2
    exact
      (ceilDiv_le_iff_le_mul (by omega)).2 hpayloadHalf
  have htwiceChunkCount :
      2 * chunkCount payloadWidth fanIn ≤ payloadWidth := by
    have hmul :=
      (Nat.le_div_iff_mul_le (by omega : 0 < 2)).1
        hchunkCountHalf
    simpa [Nat.mul_comm] using hmul
  have hright :
      fanIn * payloadWidth < domainSize payloadWidth fanIn := by
    simpa only [domainSize,
      GroupedExtension.LogarithmicParameters.chunkBits_eq,
      Nat.succ_eq_add_one] using
      (Nat.lt_pow_succ_log_self (by omega : 1 < 2)
        (fanIn * payloadWidth))
  have hcoordinates :
      2 * (fanIn * chunkCount payloadWidth fanIn) <
        domainSize payloadWidth fanIn := by
    calc
      2 * (fanIn * chunkCount payloadWidth fanIn) =
          fanIn * (2 * chunkCount payloadWidth fanIn) := by
        ring
      _ ≤ fanIn * payloadWidth :=
        Nat.mul_le_mul_left fanIn htwiceChunkCount
      _ < domainSize payloadWidth fanIn := hright
  have hdomain : 2 ≤ domainSize payloadWidth fanIn := by
    omega
  have hdegree :
      degreeEndpoint payloadWidth fanIn =
        fanIn * chunkCount payloadWidth fanIn *
          (domainSize payloadWidth fanIn - 1) := by
    rw [degreeEndpoint_eq_groupedDegree payloadWidth fanIn
      (by omega) (by omega)]
    rfl
  calc
    PrimeField.Search.searchModulus
          (degreeEndpoint payloadWidth fanIn) ≤
        2 * (degreeEndpoint payloadWidth fanIn + 1) :=
      (PrimeField.Search.searchModulus_bounds _).2
    _ = 2 *
        ((fanIn * chunkCount payloadWidth fanIn) *
          (domainSize payloadWidth fanIn - 1) + 1) := by
      rw [hdegree]
    _ ≤ (domainSize payloadWidth fanIn - 1) *
          (domainSize payloadWidth fanIn - 1) + 2 := by
      have hcoordinatePred :
          2 * (fanIn * chunkCount payloadWidth fanIn) ≤
            domainSize payloadWidth fanIn - 1 := by
        omega
      have hmul :=
        Nat.mul_le_mul_right
          (domainSize payloadWidth fanIn - 1) hcoordinatePred
      nlinarith
    _ < ((domainSize payloadWidth fanIn - 1) + 1) ^ 2 := by
      have hone : 1 ≤ domainSize payloadWidth fanIn - 1 := by
        omega
      rw [pow_two]
      nlinarith
    _ = domainSize payloadWidth fanIn ^ 2 := by
      congr 1
      omega

end Internal
end RuntimeBounds
end Logarithmic
end PrimeGrouped
end CookMertz
end TreeEval
end Complexity
