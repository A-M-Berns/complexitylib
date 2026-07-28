/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/
import
  Complexitylib.TimeSpaceSimulation.Runtime.CandidateParameters.Defs
import
  Complexitylib.TimeSpaceSimulation.NeighborhoodGraph.WorkspaceAccounting
import
  Complexitylib.TreeEvaluation.CookMertz.PrimeGrouped.Logarithmic.RuntimeBounds

/-!
# Radix bounds for runtime candidate parameters

This proof layer connects the candidate-parameter cells to the mixed-radix
encodings used by the concrete neighborhood evaluator.
-/

namespace Complexity
namespace TimeSpaceSimulation
namespace Runtime
namespace CandidateParameters
namespace RadixBounds
namespace Internal

open NeighborhoodGraph

theorem booleanWidth_lt_domainSize_internal
    (Q : Type*) [Fintype Q] (workTapeCount candidate : ℕ) :
    booleanWidth Q candidate <
      domainSize Q workTapeCount candidate := by
  change WorkspaceAccounting.booleanWidth Q candidate <
    2 ^ (Nat.log 2
      (WorkspaceAccounting.fanIn workTapeCount *
        WorkspaceAccounting.booleanWidth Q candidate) + 1)
  have hfanIn :
      0 < WorkspaceAccounting.fanIn workTapeCount :=
    WorkspaceAccounting.fanIn_pos workTapeCount
  have hwidth :
      WorkspaceAccounting.booleanWidth Q candidate ≤
        WorkspaceAccounting.fanIn workTapeCount *
          WorkspaceAccounting.booleanWidth Q candidate := by
    have hwidthPos :=
      WorkspaceAccounting.booleanWidth_pos Q candidate
    nlinarith
  exact hwidth.trans_lt
    (Nat.lt_pow_succ_log_self (by omega)
      (WorkspaceAccounting.fanIn workTapeCount *
        WorkspaceAccounting.booleanWidth Q candidate))

theorem fanIn_lt_domainSize_internal
    (Q : Type*) [Fintype Q] (workTapeCount candidate : ℕ) :
    fanIn workTapeCount <
      domainSize Q workTapeCount candidate := by
  have hwidth :=
    WorkspaceAccounting.booleanWidth_pos Q candidate
  have hproduct :
      WorkspaceAccounting.fanIn workTapeCount ≤
        WorkspaceAccounting.fanIn workTapeCount *
          WorkspaceAccounting.booleanWidth Q candidate := by
    nlinarith
  change WorkspaceAccounting.fanIn workTapeCount <
    2 ^ (Nat.log 2
      (WorkspaceAccounting.fanIn workTapeCount *
        WorkspaceAccounting.booleanWidth Q candidate) + 1)
  exact hproduct.trans_lt
    (Nat.lt_pow_succ_log_self (by omega)
      (WorkspaceAccounting.fanIn workTapeCount *
        WorkspaceAccounting.booleanWidth Q candidate))

theorem blockLength_lt_domainSize_internal
    (Q : Type*) [Fintype Q] (workTapeCount candidate : ℕ) :
    blockLength candidate <
      domainSize Q workTapeCount candidate := by
  apply lt_of_le_of_lt _ <|
    booleanWidth_lt_domainSize_internal
      Q workTapeCount candidate
  change WorkspaceAccounting.blockLength candidate ≤
    WorkspaceAccounting.booleanWidth Q candidate
  unfold WorkspaceAccounting.booleanWidth
  omega

theorem horizon_lt_domainSize_internal
    (Q : Type*) [Fintype Q] (workTapeCount candidate : ℕ) :
    horizon candidate <
      domainSize Q workTapeCount candidate := by
  have hhorizon :=
    WorkspaceAccounting.horizon_le_two_mul_blockLength candidate
  have hblock :=
    WorkspaceAccounting.blockLength_pos candidate
  have hfanIn :
      8 ≤ WorkspaceAccounting.fanIn workTapeCount := by
    unfold WorkspaceAccounting.fanIn
    omega
  have hwidth :
      5 * WorkspaceAccounting.blockLength candidate ≤
        WorkspaceAccounting.booleanWidth Q candidate := by
    unfold WorkspaceAccounting.booleanWidth
    omega
  have hproduct :
      2 * WorkspaceAccounting.blockLength candidate <
        WorkspaceAccounting.fanIn workTapeCount *
          WorkspaceAccounting.booleanWidth Q candidate := by
    nlinarith
  change WorkspaceAccounting.horizon candidate <
    2 ^ (Nat.log 2
      (WorkspaceAccounting.fanIn workTapeCount *
        WorkspaceAccounting.booleanWidth Q candidate) + 1)
  calc
    WorkspaceAccounting.horizon candidate ≤
        2 * WorkspaceAccounting.blockLength candidate :=
      hhorizon
    _ < WorkspaceAccounting.fanIn workTapeCount *
        WorkspaceAccounting.booleanWidth Q candidate :=
      hproduct
    _ < 2 ^ (Nat.log 2
        (WorkspaceAccounting.fanIn workTapeCount *
          WorkspaceAccounting.booleanWidth Q candidate) + 1) :=
      Nat.lt_pow_succ_log_self (by omega) _

theorem card_lt_domainSize_internal
    (Q : Type*) [Fintype Q] (workTapeCount candidate : ℕ) :
    Fintype.card Q <
      domainSize Q workTapeCount candidate := by
  apply lt_of_le_of_lt _ <|
    booleanWidth_lt_domainSize_internal
      Q workTapeCount candidate
  unfold booleanWidth WorkspaceAccounting.booleanWidth
  omega

theorem one_lt_domainSize_internal
    (Q : Type*) [Fintype Q] (workTapeCount candidate : ℕ) :
    1 < domainSize Q workTapeCount candidate := by
  have hfanIn :
      8 ≤ fanIn workTapeCount := by
    unfold fanIn WorkspaceAccounting.fanIn
    omega
  have hbound :=
    fanIn_lt_domainSize_internal Q workTapeCount candidate
  omega

theorem bankRadix_eq_domainSize_sq_internal
    (Q : Type*) [Fintype Q] (workTapeCount candidate : ℕ) :
    bankRadix Q workTapeCount candidate =
      domainSize Q workTapeCount candidate ^ 2 := by
  change
    2 ^ WorkspaceAccounting.fieldBits Q workTapeCount candidate =
      TreeEval.CookMertz.PrimeGrouped.Logarithmic.domainSize
        (WorkspaceAccounting.booleanWidth Q candidate)
        (WorkspaceAccounting.fanIn workTapeCount) ^ 2
  rw [TreeEval.CookMertz.PrimeGrouped.Logarithmic.domainSize,
    pow_two, ← pow_add]
  congr 1
  simp only [WorkspaceAccounting.fieldBits,
    TreeEval.CookMertz.GroupedExtension.LogarithmicParameters.fieldBits]
  ring

theorem frameRadix_eq_domainSize_pow_internal
    (Q : Type*) [Fintype Q] (workTapeCount candidate : ℕ) :
    frameRadix Q workTapeCount candidate =
      domainSize Q workTapeCount candidate ^ 24 := by
  change
    2 ^ WorkspaceAccounting.frameBits Q workTapeCount candidate =
      TreeEval.CookMertz.PrimeGrouped.Logarithmic.domainSize
        (WorkspaceAccounting.booleanWidth Q candidate)
        (WorkspaceAccounting.fanIn workTapeCount) ^ 24
  rw [WorkspaceAccounting.frameBits_eq,
    TreeEval.CookMertz.PrimeGrouped.Logarithmic.domainSize,
    ← pow_mul]
  congr 1
  simp only [WorkspaceAccounting.chunkBits]
  ring

theorem canonicalModulus_lt_bankRadix_internal
    (Q : Type*) [Fintype Q] (workTapeCount candidate : ℕ) :
    canonicalModulus Q workTapeCount candidate <
      bankRadix Q workTapeCount candidate := by
  have hpayload :
      5 ≤ WorkspaceAccounting.booleanWidth Q candidate := by
    have hblock :=
      WorkspaceAccounting.blockLength_pos candidate
    unfold WorkspaceAccounting.booleanWidth
    omega
  have hfanIn :
      8 ≤ WorkspaceAccounting.fanIn workTapeCount := by
    unfold WorkspaceAccounting.fanIn
    omega
  have hmodulus :=
    TreeEval.CookMertz.PrimeGrouped.Logarithmic.RuntimeBounds.searchModulus_lt_domainSize_sq
      (WorkspaceAccounting.booleanWidth Q candidate)
      (WorkspaceAccounting.fanIn workTapeCount)
      hpayload hfanIn
  change
    TreeEval.CookMertz.PrimeField.Search.searchModulus
        (TreeEval.CookMertz.PrimeGrouped.Logarithmic.degreeEndpoint
          (WorkspaceAccounting.booleanWidth Q candidate)
          (WorkspaceAccounting.fanIn workTapeCount)) <
      2 ^ WorkspaceAccounting.fieldBits Q workTapeCount candidate
  calc
    _ < TreeEval.CookMertz.PrimeGrouped.Logarithmic.domainSize
          (WorkspaceAccounting.booleanWidth Q candidate)
          (WorkspaceAccounting.fanIn workTapeCount) ^ 2 :=
      hmodulus
    _ = 2 ^
        WorkspaceAccounting.fieldBits Q workTapeCount candidate := by
      rw [TreeEval.CookMertz.PrimeGrouped.Logarithmic.domainSize,
        pow_two, ← pow_add]
      congr 1
      simp only [WorkspaceAccounting.fieldBits,
        TreeEval.CookMertz.GroupedExtension.LogarithmicParameters.fieldBits]
      ring

end Internal
end RadixBounds
end CandidateParameters
end Runtime
end TimeSpaceSimulation
end Complexity
