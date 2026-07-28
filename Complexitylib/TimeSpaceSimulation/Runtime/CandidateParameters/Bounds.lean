/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/
import
  Complexitylib.TimeSpaceSimulation.Runtime.CandidateParameters.Defs
import
  Complexitylib.TimeSpaceSimulation.NeighborhoodGraph.WorkspaceAccounting
import Complexitylib.TreeEvaluation.CookMertz.PrimeGrouped.Logarithmic

/-!
# Uniform width bounds for runtime candidate parameters

The parameter-construction program uses one common mutable-value width.  This
module collects the arithmetic bounds for every output and transient used by
its seventeen sequential phases.
-/

namespace Complexity
namespace TimeSpaceSimulation
namespace Runtime
namespace CandidateParameters
namespace Internal

open NeighborhoodGraph

/-- Binary width is subadditive under multiplication. -/
private theorem size_mul_le (left right : ℕ) :
    (left * right).size ≤ left.size + right.size := by
  by_cases hleft : left = 0
  · simp [hleft]
  by_cases hright : right = 0
  · simp [hright]
  rw [Nat.size_le]
  calc
    left * right < 2 ^ left.size * right :=
      Nat.mul_lt_mul_of_pos_right (Nat.lt_size_self left)
        (Nat.pos_of_ne_zero hright)
    _ < 2 ^ left.size * 2 ^ right.size :=
      Nat.mul_lt_mul_of_pos_left (Nat.lt_size_self right)
        (Nat.two_pow_pos _)
    _ = 2 ^ (left.size + right.size) := by
      rw [Nat.pow_add]

/-- Binary width is subadditive under addition, up to one carry bit. -/
private theorem size_add_le (left right : ℕ) :
    (left + right).size ≤ left.size + right.size + 1 := by
  rw [Nat.size_le]
  let width := left.size + right.size
  have hleft :
      left < 2 ^ width :=
    (Nat.lt_size_self left).trans_le
      (Nat.pow_le_pow_right (by omega)
        (Nat.le_add_right left.size right.size))
  have hright :
      right < 2 ^ width :=
    (Nat.lt_size_self right).trans_le
      (Nat.pow_le_pow_right (by omega)
        (Nat.le_add_left right.size left.size))
  calc
    left + right < 2 ^ width + 2 ^ width :=
      Nat.add_lt_add hleft hright
    _ = 2 ^ (width + 1) := by
      rw [Nat.pow_succ]
      ring
    _ = 2 ^ (left.size + right.size + 1) := by
      rfl

/-- Truncated subtraction cannot increase binary width. -/
private theorem size_sub_le (left right : ℕ) :
    (left - right).size ≤ left.size :=
  Nat.size_le_size (Nat.sub_le left right)

/-- A natural bounds its own binary width. -/
private theorem size_le_self (value : ℕ) :
    value.size ≤ value :=
  Nat.size_le.mpr Nat.lt_two_pow_self

/-- Common bit width used by every candidate-parameter program point. -/
def valueWidth (Q : Type*) [Fintype Q]
    (workTapeCount target : ℕ) : ℕ :=
  NeighborhoodProgram.fixedRegisterCount *
    WorkspaceAccounting.trialEnvelopeBits Q workTapeCount target

/-- All parameter outputs and arithmetic transients fit one common width. -/
structure ParameterValueBounds
    (Q : Type*) [Fintype Q] (workTapeCount candidate target : ℕ) : Prop where
  candidate_size : candidate.size ≤ valueWidth Q workTapeCount target
  protectedLog_size :
    (protectedLog candidate).size ≤ valueWidth Q workTapeCount target
  radicand_size :
    (radicand candidate).size ≤ valueWidth Q workTapeCount target
  blockLength_size :
    (blockLength candidate).size ≤ valueWidth Q workTapeCount target
  blockLengthSq_size :
    (blockLength candidate * blockLength candidate).size ≤
      valueWidth Q workTapeCount target
  ceilDividend_size :
    (candidate + (blockLength candidate - 1)).size ≤
      valueWidth Q workTapeCount target
  booleanWidth_size :
    (booleanWidth Q candidate).size ≤ valueWidth Q workTapeCount target
  fanIn_size :
    (fanIn workTapeCount).size ≤ valueWidth Q workTapeCount target
  fanInBooleanWidth_size :
    (fanIn workTapeCount * booleanWidth Q candidate).size ≤
      valueWidth Q workTapeCount target
  chunkBits_size :
    (chunkBits Q workTapeCount candidate).size ≤
      valueWidth Q workTapeCount target
  chunkDividend_size :
    (booleanWidth Q candidate +
      (chunkBits Q workTapeCount candidate - 1)).size ≤
        valueWidth Q workTapeCount target
  chunkCount_size :
    (chunkCount Q workTapeCount candidate).size ≤
      valueWidth Q workTapeCount target
  domainSize_size :
    (domainSize Q workTapeCount candidate).size ≤
      valueWidth Q workTapeCount target
  fanInChunkCount_size :
    (fanIn workTapeCount * chunkCount Q workTapeCount candidate).size ≤
      valueWidth Q workTapeCount target
  groupedDegree_size :
    (groupedDegree Q workTapeCount candidate).size ≤
      valueWidth Q workTapeCount target
  degreeEndpoint_size :
    (degreeEndpoint Q workTapeCount candidate).size ≤
      valueWidth Q workTapeCount target
  fieldBits_size :
    (fieldBits Q workTapeCount candidate).size ≤
      valueWidth Q workTapeCount target
  frameBits_size :
    (frameBits Q workTapeCount candidate).size ≤
      valueWidth Q workTapeCount target
  frameRadix_size :
    (frameRadix Q workTapeCount candidate).size ≤
      valueWidth Q workTapeCount target
  bankRadix_size :
    (bankRadix Q workTapeCount candidate).size ≤
      valueWidth Q workTapeCount target
  fanInSucc_size :
    (fanIn workTapeCount + 1).size ≤
      valueWidth Q workTapeCount target
  bankDigitCount_size :
    (bankDigitCount Q workTapeCount candidate).size ≤
      valueWidth Q workTapeCount target
  primeLower_size :
    (degreeEndpoint Q workTapeCount candidate + 2).size + 2 ≤
      valueWidth Q workTapeCount target
  two_le_cap :
    2 ≤ 2 ^ valueWidth Q workTapeCount target - 1

/-- Every streamed candidate at most `target` satisfies the complete common
width contract. -/
theorem parameterValueBounds_internal
    (Q : Type*) [Fintype Q] (workTapeCount : ℕ)
    {candidate target : ℕ} (hcandidate : candidate ≤ target) :
    ParameterValueBounds Q workTapeCount candidate target := by
  let envelope :=
    WorkspaceAccounting.trialEnvelopeBits Q workTapeCount target
  have htotal :
      WorkspaceAccounting.totalBits Q workTapeCount candidate ≤
        envelope :=
    WorkspaceAccounting.totalBits_le_trialEnvelope
      Q workTapeCount hcandidate
  have hscratchTotal :
      WorkspaceAccounting.scratchBits Q workTapeCount candidate ≤
        WorkspaceAccounting.totalBits Q workTapeCount candidate := by
    unfold WorkspaceAccounting.totalBits
    omega
  have hgraphTotal :
      WorkspaceAccounting.graphBits Q workTapeCount candidate ≤
        WorkspaceAccounting.totalBits Q workTapeCount candidate := by
    unfold WorkspaceAccounting.totalBits
    omega
  have hbooleanScratch :
      booleanWidth Q candidate ≤
        WorkspaceAccounting.scratchBits Q workTapeCount candidate := by
    change
      WorkspaceAccounting.booleanWidth Q candidate ≤
        WorkspaceAccounting.scratchBits Q workTapeCount candidate
    unfold WorkspaceAccounting.scratchBits
    omega
  have hchunkScratch :
      chunkBits Q workTapeCount candidate ≤
        WorkspaceAccounting.scratchBits Q workTapeCount candidate := by
    change
      WorkspaceAccounting.chunkBits Q workTapeCount candidate ≤
        WorkspaceAccounting.scratchBits Q workTapeCount candidate
    unfold WorkspaceAccounting.scratchBits
    omega
  have hlogScratch :
      protectedLog candidate ≤
        WorkspaceAccounting.scratchBits Q workTapeCount candidate := by
    change
      ComplexityBridge.protectedBinaryLog candidate ≤
        WorkspaceAccounting.scratchBits Q workTapeCount candidate
    unfold WorkspaceAccounting.scratchBits
    omega
  have hboolean :
      booleanWidth Q candidate ≤ envelope :=
    hbooleanScratch.trans (hscratchTotal.trans htotal)
  have hchunk :
      chunkBits Q workTapeCount candidate ≤ envelope :=
    hchunkScratch.trans (hscratchTotal.trans htotal)
  have hlog :
      protectedLog candidate ≤ envelope :=
    hlogScratch.trans (hscratchTotal.trans htotal)
  have hchunkPos :
      0 < chunkBits Q workTapeCount candidate := by
    exact
      TreeEval.CookMertz.GroupedExtension.LogarithmicParameters.chunkBits_pos
        (booleanWidth Q candidate) (fanIn workTapeCount)
  have hfanGraph :
      fanIn workTapeCount ≤
        WorkspaceAccounting.graphBits Q workTapeCount candidate := by
    calc
      fanIn workTapeCount = fanIn workTapeCount * 1 := by omega
      _ ≤ fanIn workTapeCount *
          (4 * chunkBits Q workTapeCount candidate) :=
        Nat.mul_le_mul_left _ (by omega)
      _ = WorkspaceAccounting.graphBits
          Q workTapeCount candidate := by
        unfold WorkspaceAccounting.graphBits
        ring
  have hfan :
      fanIn workTapeCount ≤ envelope :=
    hfanGraph.trans (hgraphTotal.trans htotal)
  have hblockBoolean :
      blockLength candidate ≤ booleanWidth Q candidate := by
    change
      WorkspaceAccounting.blockLength candidate ≤
        Fintype.card Q +
          5 * WorkspaceAccounting.blockLength candidate
    omega
  have hblock :
      blockLength candidate ≤ envelope :=
    hblockBoolean.trans hboolean
  have henvelopePos : 0 < envelope :=
    (WorkspaceAccounting.blockLength_pos target).trans_le
      (WorkspaceAccounting.blockLength_le_trialEnvelope
        Q workTapeCount target)
  have hwidth :
      valueWidth Q workTapeCount target = 32 * envelope := by
    simp [valueWidth, NeighborhoodProgram.fixedRegisterCount, envelope]
  have hcandidateSize :
      candidate.size ≤ envelope := by
    calc
      candidate.size ≤ protectedLog candidate :=
        Nat.size_le_log_two_add_one candidate
      _ ≤ envelope := hlog
  have hlogPos : 0 < protectedLog candidate :=
    ComplexityBridge.protectedBinaryLog_pos candidate
  have hlogSize :
      (protectedLog candidate).size ≤ envelope :=
    (size_le_self (protectedLog candidate)).trans hlog
  have hblockPos : 0 < blockLength candidate :=
    WorkspaceAccounting.blockLength_pos candidate
  have hblockSize :
      (blockLength candidate).size ≤ envelope :=
    (size_le_self (blockLength candidate)).trans hblock
  have hbooleanPos : 0 < booleanWidth Q candidate :=
    WorkspaceAccounting.booleanWidth_pos Q candidate
  have hbooleanSize :
      (booleanWidth Q candidate).size ≤ envelope :=
    (size_le_self (booleanWidth Q candidate)).trans hboolean
  have hchunkSize :
      (chunkBits Q workTapeCount candidate).size ≤ envelope :=
    (size_le_self (chunkBits Q workTapeCount candidate)).trans hchunk
  have hfanPos : 0 < fanIn workTapeCount :=
    WorkspaceAccounting.fanIn_pos workTapeCount
  have hfanSize :
      (fanIn workTapeCount).size ≤ envelope :=
    (size_le_self (fanIn workTapeCount)).trans hfan
  have hcountLe :
      chunkCount Q workTapeCount candidate ≤
        booleanWidth Q candidate := by
    exact
      TreeEval.CookMertz.GroupedExtension.LogarithmicParameters.chunkCount_le_payloadWidth
        (booleanWidth Q candidate) (fanIn workTapeCount)
  have hcountSize :
      (chunkCount Q workTapeCount candidate).size ≤ envelope := by
    exact (Nat.size_le_size hcountLe).trans hbooleanSize
  have hdomainSize :
      (domainSize Q workTapeCount candidate).size =
        chunkBits Q workTapeCount candidate + 1 := by
    simp [domainSize,
      TreeEval.CookMertz.PrimeGrouped.Logarithmic.domainSize,
      WorkspaceAccounting.chunkBits,
      TreeEval.CookMertz.GroupedExtension.LogarithmicParameters.chunkBits_eq,
      Nat.size_pow]
  have hcoordinatesLe :
      fanIn workTapeCount * chunkCount Q workTapeCount candidate ≤
        domainSize Q workTapeCount candidate := by
    exact
      TreeEval.CookMertz.GroupedExtension.LogarithmicParameters.inputCoordinates_le
        (booleanWidth Q candidate) (fanIn workTapeCount)
  have hcoordinatesSize :
      (fanIn workTapeCount *
        chunkCount Q workTapeCount candidate).size ≤
          envelope + 1 := by
    calc
      (fanIn workTapeCount *
          chunkCount Q workTapeCount candidate).size ≤
        (domainSize Q workTapeCount candidate).size :=
          Nat.size_le_size hcoordinatesLe
      _ = chunkBits Q workTapeCount candidate + 1 := hdomainSize
      _ ≤ envelope + 1 := Nat.add_le_add_right hchunk 1
  have hdomainPredSize :
      (domainSize Q workTapeCount candidate - 1).size ≤
        envelope + 1 := by
    exact (size_sub_le _ _).trans (by
      rw [hdomainSize]
      exact Nat.add_le_add_right hchunk 1)
  have hgroupedSize :
      (groupedDegree Q workTapeCount candidate).size ≤
        2 * envelope + 2 := by
    unfold groupedDegree
    unfold TreeEval.CookMertz.PrimeGrouped.Logarithmic.groupedDegree
    calc
      (fanIn workTapeCount *
          chunkCount Q workTapeCount candidate *
          (domainSize Q workTapeCount candidate - 1)).size ≤
        (fanIn workTapeCount *
          chunkCount Q workTapeCount candidate).size +
          (domainSize Q workTapeCount candidate - 1).size :=
            size_mul_le _ _
      _ ≤ (envelope + 1) + (envelope + 1) :=
        Nat.add_le_add hcoordinatesSize hdomainPredSize
      _ = 2 * envelope + 2 := by omega
  have hendpointSize :
      (degreeEndpoint Q workTapeCount candidate).size ≤
        2 * envelope + 2 := by
    change
      (max (groupedDegree Q workTapeCount candidate)
        (domainSize Q workTapeCount candidate - 1)).size ≤
          2 * envelope + 2
    by_cases hle :
        groupedDegree Q workTapeCount candidate ≤
          domainSize Q workTapeCount candidate - 1
    · rw [max_eq_right hle]
      exact hdomainPredSize.trans (by omega)
    · rw [max_eq_left (by omega)]
      exact hgroupedSize
  have hfieldBits :
      WorkspaceAccounting.fieldBits Q workTapeCount candidate =
        2 * chunkBits Q workTapeCount candidate := by
    exact
      TreeEval.CookMertz.GroupedExtension.LogarithmicParameters.fieldBits_eq
        (booleanWidth Q candidate) (fanIn workTapeCount)
  have hframeBits :
      WorkspaceAccounting.frameBits Q workTapeCount candidate =
        24 * chunkBits Q workTapeCount candidate := by
    exact
      WorkspaceAccounting.frameBits_eq Q workTapeCount candidate
  have hfieldBitsPos :
      0 < fieldBits Q workTapeCount candidate := by
    change
      0 < WorkspaceAccounting.fieldBits Q workTapeCount candidate
    rw [hfieldBits]
    omega
  have hframeBitsPos :
      0 < frameBits Q workTapeCount candidate := by
    change
      0 < WorkspaceAccounting.frameBits Q workTapeCount candidate
    rw [hframeBits]
    omega
  have hfanSuccSize :
      (fanIn workTapeCount + 1).size ≤ envelope + 2 := by
    calc
      (fanIn workTapeCount + 1).size ≤
          (fanIn workTapeCount).size + (1 : ℕ).size + 1 :=
        size_add_le _ _
      _ ≤ envelope + 2 := by
        simpa using Nat.add_le_add_right hfanSize 2
  have hbankCountSize :
      (bankDigitCount Q workTapeCount candidate).size ≤
        2 * envelope + 2 := by
    unfold bankDigitCount NeighborhoodProgram.bankDigitCount
    calc
      ((WorkspaceAccounting.fanIn workTapeCount + 1) *
          WorkspaceAccounting.chunkCount
            Q workTapeCount candidate).size ≤
        (fanIn workTapeCount + 1).size +
          (chunkCount Q workTapeCount candidate).size :=
            size_mul_le _ _
      _ ≤ (envelope + 2) + envelope :=
        Nat.add_le_add hfanSuccSize hcountSize
      _ = 2 * envelope + 2 := by omega
  refine
    { candidate_size := by omega
      protectedLog_size := by omega
      radicand_size := ?_
      blockLength_size := by omega
      blockLengthSq_size := ?_
      ceilDividend_size := ?_
      booleanWidth_size := by omega
      fanIn_size := by omega
      fanInBooleanWidth_size := ?_
      chunkBits_size := by omega
      chunkDividend_size := ?_
      chunkCount_size := by omega
      domainSize_size := by
        rw [hdomainSize]
        omega
      fanInChunkCount_size := by omega
      groupedDegree_size := by omega
      degreeEndpoint_size := by omega
      fieldBits_size := ?_
      frameBits_size := ?_
      frameRadix_size := ?_
      bankRadix_size := ?_
      fanInSucc_size := by omega
      bankDigitCount_size := by omega
      primeLower_size := ?_
      two_le_cap := ?_ }
  · unfold radicand
    exact (size_mul_le candidate (protectedLog candidate)).trans (by omega)
  · exact
      (size_mul_le (blockLength candidate)
        (blockLength candidate)).trans (by omega)
  · have hpredSize :
        (blockLength candidate - 1).size ≤ envelope :=
      (size_sub_le _ _).trans hblockSize
    exact
      (size_add_le candidate
        (blockLength candidate - 1)).trans (by omega)
  · exact
      (size_mul_le (fanIn workTapeCount)
        (booleanWidth Q candidate)).trans (by omega)
  · have hpredSize :
        (chunkBits Q workTapeCount candidate - 1).size ≤ envelope :=
      (size_sub_le _ _).trans hchunkSize
    exact
      (size_add_le (booleanWidth Q candidate)
        (chunkBits Q workTapeCount candidate - 1)).trans (by omega)
  · exact
      (size_le_self (fieldBits Q workTapeCount candidate)).trans (by
        change
          WorkspaceAccounting.fieldBits Q workTapeCount candidate ≤
            valueWidth Q workTapeCount target
        rw [hfieldBits]
        omega)
  · exact
      (size_le_self (frameBits Q workTapeCount candidate)).trans (by
        change
          WorkspaceAccounting.frameBits Q workTapeCount candidate ≤
            valueWidth Q workTapeCount target
        rw [hframeBits]
        omega)
  · simp only [frameRadix, NeighborhoodProgram.frameRadix,
      Nat.size_pow]
    rw [hframeBits]
    omega
  · simp only [bankRadix, NeighborhoodProgram.bankRadix,
      Nat.size_pow]
    rw [hfieldBits]
    omega
  · have hlower :=
      size_add_le (degreeEndpoint Q workTapeCount candidate) 2
    have htwoSize : (2 : ℕ).size = 2 := by decide
    rw [htwoSize] at hlower
    rw [hwidth]
    omega
  · have hpow :
        2 ^ 2 ≤ 2 ^ (32 * envelope) :=
      Nat.pow_le_pow_right (by omega) (by omega)
    norm_num at hpow
    rw [hwidth]
    omega

end Internal
end CandidateParameters
end Runtime
end TimeSpaceSimulation
end Complexity
