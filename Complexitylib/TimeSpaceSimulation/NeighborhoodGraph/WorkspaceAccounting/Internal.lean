/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/
import Complexitylib.TimeSpaceSimulation.ComplexityBridge
import Complexitylib.TimeSpaceSimulation.NeighborhoodGraph.WorkspaceAccounting.Defs
import Complexitylib.TreeEvaluation.CookMertz.GroupedExtension.LogarithmicParameters
import Complexitylib.Mathlib.NatBits

/-!
# Proof internals for direct-neighborhood workspace accounting

This file proves the total natural-number inequalities behind the concrete
square-root-logarithmic budget.
-/

open Asymptotics

namespace Complexity

namespace TimeSpaceSimulation

namespace NeighborhoodGraph

namespace WorkspaceAccounting

namespace Internal

open TreeEval.CookMertz
open TreeEval.CookMertz.GroupedExtension

theorem protectedBinaryLog_mul_le_add_internal
    {first second : ℕ} (hfirst : 0 < first) (hsecond : 0 < second) :
    ComplexityBridge.protectedBinaryLog (first * second) ≤
      ComplexityBridge.protectedBinaryLog first +
        ComplexityBridge.protectedBinaryLog second := by
  have hfirstLt :=
    Nat.lt_pow_succ_log_self Nat.one_lt_two first
  have hsecondLt :=
    Nat.lt_pow_succ_log_self Nat.one_lt_two second
  have hmulLt :
      first * second <
        2 ^ ((Nat.log 2 first + 1) + (Nat.log 2 second + 1)) := by
    rw [Nat.pow_add]
    calc
      first * second <
          2 ^ (Nat.log 2 first + 1) * second :=
        (Nat.mul_lt_mul_right hsecond).2 hfirstLt
      _ < 2 ^ (Nat.log 2 first + 1) *
          2 ^ (Nat.log 2 second + 1) :=
        (Nat.mul_lt_mul_left (by positivity)).2 hsecondLt
  have hlogLt :=
    Nat.log_lt_of_lt_pow (Nat.mul_pos hfirst hsecond).ne' hmulLt
  simp only [ComplexityBridge.protectedBinaryLog]
  omega

theorem blockLength_pos_internal (time : ℕ) :
    0 < blockLength time := by
  unfold blockLength ComplexityBridge.balancedBlockLength
  exact ComplexityBridge.positiveCeilSqrt_pos _

theorem blockLength_mono_internal {first second : ℕ}
    (h : first ≤ second) :
    blockLength first ≤ blockLength second := by
  have hlog :
      ComplexityBridge.protectedBinaryLog first ≤
        ComplexityBridge.protectedBinaryLog second := by
    simp only [ComplexityBridge.protectedBinaryLog]
    exact Nat.add_le_add_right (Nat.log_mono_right h) 1
  have hradicand :
      first * ComplexityBridge.protectedBinaryLog first ≤
        second * ComplexityBridge.protectedBinaryLog second :=
    Nat.mul_le_mul h hlog
  unfold blockLength ComplexityBridge.balancedBlockLength
  unfold ComplexityBridge.positiveCeilSqrt
  apply max_le_max_left
  apply ComplexityBridge.ceilSqrt_le_iff.mpr
  exact hradicand.trans
    (ComplexityBridge.ceilSqrt_sq_ge
      (second * ComplexityBridge.protectedBinaryLog second))

theorem horizon_le_timeBlockCount_internal (time : ℕ) :
    horizon time ≤ ComplexityBridge.timeBlockCount time := by
  unfold horizon
  apply (ceilDiv_le_iff_le_mul (blockLength_pos_internal time)).2
  calc
    time ≤ ComplexityBridge.timeBlockCount time *
        ComplexityBridge.balancedBlockLength time :=
      ComplexityBridge.time_le_timeBlockCount_mul_blockLength time
    _ = blockLength time * ComplexityBridge.timeBlockCount time := by
      rw [blockLength, Nat.mul_comm]

theorem booleanWidth_pos_internal
    (Q : Type*) [Fintype Q] (time : ℕ) :
    0 < booleanWidth Q time := by
  have hb := blockLength_pos_internal time
  simp only [booleanWidth]
  omega

theorem fanIn_pos_internal (workTapeCount : ℕ) :
    0 < fanIn workTapeCount := by
  simp [fanIn]

theorem booleanWidth_le_mul_blockLength_internal
    (Q : Type*) [Fintype Q] (time : ℕ) :
    booleanWidth Q time ≤
      (Fintype.card Q + 5) * blockLength time := by
  have hb := blockLength_pos_internal time
  simp only [booleanWidth]
  nlinarith

theorem blockLength_le_time_internal {time : ℕ} (htime : 2 ≤ time) :
    blockLength time ≤ time := by
  unfold blockLength ComplexityBridge.balancedBlockLength
  unfold ComplexityBridge.positiveCeilSqrt
  apply max_le
  · omega
  · apply ComplexityBridge.ceilSqrt_le_iff.mpr
    exact Nat.mul_le_mul_left time
      (ComplexityBridge.protectedBinaryLog_le_self_of_pos (by omega))

theorem chunkBits_le_mul_log_internal
    (Q : Type*) [Fintype Q] (workTapeCount time : ℕ) :
    chunkBits Q workTapeCount time ≤
      chunkCoefficient Q workTapeCount *
        ComplexityBridge.protectedBinaryLog time := by
  by_cases htime : 2 ≤ time
  · have hbTime : blockLength time ≤ time :=
      blockLength_le_time_internal htime
    have hwidth :=
      booleanWidth_le_mul_blockLength_internal Q time
    have hproduct :
        fanIn workTapeCount * booleanWidth Q time ≤
          machineFactor Q workTapeCount * blockLength time := by
      calc
        fanIn workTapeCount * booleanWidth Q time ≤
            fanIn workTapeCount *
              ((Fintype.card Q + 5) * blockLength time) :=
          Nat.mul_le_mul_left (fanIn workTapeCount) hwidth
        _ = machineFactor Q workTapeCount * blockLength time := by
          simp only [machineFactor]
          ring
    have hmachine : 0 < machineFactor Q workTapeCount := by
      unfold machineFactor
      exact Nat.mul_pos (fanIn_pos_internal workTapeCount) (by omega)
    have hblock := blockLength_pos_internal time
    have hblockLog :
        ComplexityBridge.protectedBinaryLog (blockLength time) ≤
          ComplexityBridge.protectedBinaryLog time := by
      simp only [ComplexityBridge.protectedBinaryLog]
      exact Nat.add_le_add_right (Nat.log_mono_right hbTime) 1
    have htimeLog := ComplexityBridge.protectedBinaryLog_pos time
    calc
      chunkBits Q workTapeCount time =
          ComplexityBridge.protectedBinaryLog
            (fanIn workTapeCount * booleanWidth Q time) := by
        rfl
      _ ≤ ComplexityBridge.protectedBinaryLog
          (machineFactor Q workTapeCount * blockLength time) := by
        simp only [ComplexityBridge.protectedBinaryLog]
        exact Nat.add_le_add_right (Nat.log_mono_right hproduct) 1
      _ ≤ ComplexityBridge.protectedBinaryLog
            (machineFactor Q workTapeCount) +
          ComplexityBridge.protectedBinaryLog (blockLength time) :=
        protectedBinaryLog_mul_le_add_internal hmachine hblock
      _ ≤ ComplexityBridge.protectedBinaryLog
            (machineFactor Q workTapeCount) +
          ComplexityBridge.protectedBinaryLog time :=
        Nat.add_le_add_left hblockLog _
      _ ≤ chunkCoefficient Q workTapeCount *
          ComplexityBridge.protectedBinaryLog time := by
        unfold chunkCoefficient
        nlinarith
  · have hsmall : time ≤ 1 := by omega
    interval_cases time <;>
      simp [chunkBits, chunkCoefficient, machineFactor, booleanWidth,
        blockLength, ComplexityBridge.balancedBlockLength,
        ComplexityBridge.positiveCeilSqrt, ComplexityBridge.ceilSqrt,
        ComplexityBridge.protectedBinaryLog]

theorem chunkBits_le_mul_blockLength_internal
    (Q : Type*) [Fintype Q] (workTapeCount time : ℕ) :
    chunkBits Q workTapeCount time ≤
      chunkCoefficient Q workTapeCount * blockLength time := by
  calc
    chunkBits Q workTapeCount time ≤
        chunkCoefficient Q workTapeCount *
          ComplexityBridge.protectedBinaryLog time :=
      chunkBits_le_mul_log_internal Q workTapeCount time
    _ ≤ chunkCoefficient Q workTapeCount * blockLength time :=
      Nat.mul_le_mul_left _
        (by
          simpa only [blockLength] using
            ComplexityBridge.protectedBinaryLog_le_balancedBlockLength time)

theorem horizon_mul_chunkBits_le_internal
    (Q : Type*) [Fintype Q] (workTapeCount time : ℕ) :
    horizon time * chunkBits Q workTapeCount time ≤
      2 * chunkCoefficient Q workTapeCount * blockLength time := by
  calc
    horizon time * chunkBits Q workTapeCount time ≤
        ComplexityBridge.timeBlockCount time *
          chunkBits Q workTapeCount time :=
      Nat.mul_le_mul_right _
        (horizon_le_timeBlockCount_internal time)
    _ ≤ ComplexityBridge.timeBlockCount time *
        (chunkCoefficient Q workTapeCount *
          ComplexityBridge.protectedBinaryLog time) :=
      Nat.mul_le_mul_left _
        (chunkBits_le_mul_log_internal Q workTapeCount time)
    _ = chunkCoefficient Q workTapeCount *
        (ComplexityBridge.timeBlockCount time *
          ComplexityBridge.protectedBinaryLog time) := by
      ring
    _ ≤ chunkCoefficient Q workTapeCount *
        (2 * blockLength time) := by
      apply Nat.mul_le_mul_left
      simpa only [blockLength] using
        ComplexityBridge.timeBlockCount_mul_log_le time
    _ = 2 * chunkCoefficient Q workTapeCount * blockLength time := by
      ring

theorem catalyticBankBits_eq_grouped_internal
    (Q : Type*) [Fintype Q] (workTapeCount time : ℕ) :
    catalyticBankBits Q workTapeCount time =
      TreeEval.CookMertz.GroupedExtension.groupedRegisterBitBudget
        (fanIn workTapeCount)
        (chunkCount Q workTapeCount time)
        (fieldBits Q workTapeCount time) := by
  rfl

theorem chunkCount_eq_one_of_small_internal
    (Q : Type*) [Fintype Q] (workTapeCount time : ℕ)
    (hsmall :
      TreeEval.CookMertz.GroupedExtension.LogarithmicParameters.RequiresSmallCase
        (booleanWidth Q time) (fanIn workTapeCount)) :
    chunkCount Q workTapeCount time = 1 := by
  apply Nat.le_antisymm
  · change
      TreeEval.CookMertz.GroupedExtension.LogarithmicParameters.chunkCount
        (booleanWidth Q time) (fanIn workTapeCount) ≤ 1
    rw [TreeEval.CookMertz.GroupedExtension.LogarithmicParameters.chunkCount_eq]
    apply (ceilDiv_le_iff_le_mul
      (TreeEval.CookMertz.GroupedExtension.LogarithmicParameters.chunkBits_pos
        (booleanWidth Q time) (fanIn workTapeCount))).2
    simpa using hsmall.le
  · change
      1 ≤ TreeEval.CookMertz.GroupedExtension.LogarithmicParameters.chunkCount
        (booleanWidth Q time) (fanIn workTapeCount)
    exact
      TreeEval.CookMertz.GroupedExtension.LogarithmicParameters.chunkCount_pos
        (booleanWidth Q time) (fanIn workTapeCount)
        (booleanWidth_pos_internal Q time)

theorem catalyticBankBits_branch_internal
    (Q : Type*) [Fintype Q] (workTapeCount time : ℕ) :
    (TreeEval.CookMertz.GroupedExtension.LogarithmicParameters.InLogarithmicRegime
        (booleanWidth Q time) (fanIn workTapeCount) ∧
      catalyticBankBits Q workTapeCount time ≤
        4 * (fanIn workTapeCount + 1) *
          (Fintype.card Q + 5) * blockLength time) ∨
    (TreeEval.CookMertz.GroupedExtension.LogarithmicParameters.RequiresSmallCase
        (booleanWidth Q time) (fanIn workTapeCount) ∧
      chunkCount Q workTapeCount time = 1 ∧
      catalyticBankBits Q workTapeCount time ≤
        2 * (fanIn workTapeCount + 1) *
          chunkCoefficient Q workTapeCount * blockLength time) := by
  rcases LogarithmicParameters.inLogarithmicRegime_or_small
      (booleanWidth Q time) (fanIn workTapeCount) with
    hregime | hsmall
  · apply Or.inl
    refine ⟨hregime, ?_⟩
    rw [catalyticBankBits_eq_grouped_internal]
    calc
      TreeEval.CookMertz.GroupedExtension.groupedRegisterBitBudget
          (fanIn workTapeCount) (chunkCount Q workTapeCount time)
          (fieldBits Q workTapeCount time) ≤
        4 * (fanIn workTapeCount + 1) * booleanWidth Q time := by
          exact
            LogarithmicParameters.groupedRegisterBitBudget_le_four_mul
              (booleanWidth Q time) (fanIn workTapeCount) hregime
      _ ≤ 4 * (fanIn workTapeCount + 1) *
          ((Fintype.card Q + 5) * blockLength time) :=
        Nat.mul_le_mul_left _
          (booleanWidth_le_mul_blockLength_internal Q time)
      _ = 4 * (fanIn workTapeCount + 1) *
          (Fintype.card Q + 5) * blockLength time := by
        ring
  · apply Or.inr
    have hcount :=
      chunkCount_eq_one_of_small_internal Q workTapeCount time hsmall
    refine ⟨hsmall, hcount, ?_⟩
    rw [catalyticBankBits_eq_grouped_internal]
    calc
      TreeEval.CookMertz.GroupedExtension.groupedRegisterBitBudget
          (fanIn workTapeCount) (chunkCount Q workTapeCount time)
          (fieldBits Q workTapeCount time) =
        2 * (fanIn workTapeCount + 1) *
          chunkBits Q workTapeCount time := by
            simp [GroupedExtension.groupedRegisterBitBudget, fieldBits,
              LogarithmicParameters.fieldBits,
              chunkBits, hcount]
            ring
      _ ≤ 2 * (fanIn workTapeCount + 1) *
          (chunkCoefficient Q workTapeCount * blockLength time) :=
        Nat.mul_le_mul_left _
          (chunkBits_le_mul_blockLength_internal Q workTapeCount time)
      _ = 2 * (fanIn workTapeCount + 1) *
          chunkCoefficient Q workTapeCount * blockLength time := by
        ring

theorem catalyticBankBits_le_internal
    (Q : Type*) [Fintype Q] (workTapeCount time : ℕ) :
    catalyticBankBits Q workTapeCount time ≤
      2 * (fanIn workTapeCount + 1) *
        (Fintype.card Q + 5 + chunkCoefficient Q workTapeCount) *
          blockLength time := by
  rw [catalyticBankBits_eq_grouped_internal]
  have hsum :
      booleanWidth Q time + chunkBits Q workTapeCount time ≤
        (Fintype.card Q + 5 + chunkCoefficient Q workTapeCount) *
          blockLength time := by
    calc
      booleanWidth Q time + chunkBits Q workTapeCount time ≤
          (Fintype.card Q + 5) * blockLength time +
            chunkCoefficient Q workTapeCount * blockLength time :=
        Nat.add_le_add
          (booleanWidth_le_mul_blockLength_internal Q time)
          (chunkBits_le_mul_blockLength_internal Q workTapeCount time)
      _ = (Fintype.card Q + 5 + chunkCoefficient Q workTapeCount) *
          blockLength time := by
        ring
  calc
    TreeEval.CookMertz.GroupedExtension.groupedRegisterBitBudget
        (fanIn workTapeCount) (chunkCount Q workTapeCount time)
        (fieldBits Q workTapeCount time) ≤
      (fanIn workTapeCount + 1) * 2 *
        (booleanWidth Q time + chunkBits Q workTapeCount time) :=
      LogarithmicParameters.groupedRegisterBitBudget_le_padded
        (booleanWidth Q time) (fanIn workTapeCount)
    _ ≤ (fanIn workTapeCount + 1) * 2 *
        ((Fintype.card Q + 5 + chunkCoefficient Q workTapeCount) *
          blockLength time) :=
      Nat.mul_le_mul_left _ hsum
    _ = 2 * (fanIn workTapeCount + 1) *
        (Fintype.card Q + 5 + chunkCoefficient Q workTapeCount) *
          blockLength time := by
      ring

theorem frameBits_eq_internal
    (Q : Type*) [Fintype Q] (workTapeCount time : ℕ) :
    frameBits Q workTapeCount time =
      24 * chunkBits Q workTapeCount time := by
  unfold frameBits
  rw [LogarithmicParameters.frameBitBudget_eq]
  norm_num
  rfl

theorem stackBits_le_internal
    (Q : Type*) [Fintype Q] (workTapeCount time : ℕ) :
    stackBits Q workTapeCount time ≤
      48 * chunkCoefficient Q workTapeCount * blockLength time := by
  unfold stackBits
  rw [frameBits_eq_internal]
  calc
    horizon time * (24 * chunkBits Q workTapeCount time) =
        24 * (horizon time * chunkBits Q workTapeCount time) := by
      ring
    _ ≤ 24 *
        (2 * chunkCoefficient Q workTapeCount * blockLength time) :=
      Nat.mul_le_mul_left 24
        (horizon_mul_chunkBits_le_internal Q workTapeCount time)
    _ = 48 * chunkCoefficient Q workTapeCount * blockLength time := by
      ring

theorem graphBits_le_internal
    (Q : Type*) [Fintype Q] (workTapeCount time : ℕ) :
    graphBits Q workTapeCount time ≤
      4 * fanIn workTapeCount * chunkCoefficient Q workTapeCount *
        blockLength time := by
  unfold graphBits
  calc
    4 * fanIn workTapeCount * chunkBits Q workTapeCount time ≤
        4 * fanIn workTapeCount *
          (chunkCoefficient Q workTapeCount * blockLength time) :=
      Nat.mul_le_mul_left _
        (chunkBits_le_mul_blockLength_internal Q workTapeCount time)
    _ = 4 * fanIn workTapeCount * chunkCoefficient Q workTapeCount *
        blockLength time := by
      ring

theorem horizon_le_two_mul_blockLength_internal (time : ℕ) :
    horizon time ≤ 2 * blockLength time := by
  calc
    horizon time ≤ ComplexityBridge.timeBlockCount time :=
      horizon_le_timeBlockCount_internal time
    _ ≤ ComplexityBridge.timeBlockCount time *
        ComplexityBridge.protectedBinaryLog time := by
      have hlog :=
        ComplexityBridge.protectedBinaryLog_pos time
      nlinarith
    _ ≤ 2 * blockLength time := by
      simpa only [blockLength] using
        ComplexityBridge.timeBlockCount_mul_log_le time

theorem guessBits_le_internal
    (workTapeCount time : ℕ) :
    guessBits workTapeCount time ≤
      (4 * (workTapeCount + 2) + 1) *
        blockLength time := by
  have hhorizon :
      horizon time ≤ 2 * blockLength time :=
    horizon_le_two_mul_blockLength_internal time
  have hblock : 1 ≤ blockLength time :=
    blockLength_pos_internal time
  unfold guessBits
  calc
    2 * horizon time * (workTapeCount + 2) + 1 ≤
        2 * (2 * blockLength time) * (workTapeCount + 2) +
          blockLength time := by
      exact Nat.add_le_add
        (Nat.mul_le_mul_right (workTapeCount + 2)
          (Nat.mul_le_mul_left 2 hhorizon))
        hblock
    _ = (4 * (workTapeCount + 2) + 1) *
        blockLength time := by
      ring

theorem scratchBits_le_internal
    (Q : Type*) [Fintype Q] (workTapeCount time : ℕ) :
    scratchBits Q workTapeCount time ≤
      (8 * (Fintype.card Q + 5 + chunkCoefficient Q workTapeCount + 1) +
        32) * blockLength time := by
  have hsum :
      booleanWidth Q time + chunkBits Q workTapeCount time +
          ComplexityBridge.protectedBinaryLog time ≤
        (Fintype.card Q + 5 + chunkCoefficient Q workTapeCount + 1) *
          blockLength time := by
    calc
      booleanWidth Q time + chunkBits Q workTapeCount time +
          ComplexityBridge.protectedBinaryLog time ≤
        (Fintype.card Q + 5) * blockLength time +
            chunkCoefficient Q workTapeCount * blockLength time +
          blockLength time := by
        apply Nat.add_le_add
        · exact Nat.add_le_add
            (booleanWidth_le_mul_blockLength_internal Q time)
            (chunkBits_le_mul_blockLength_internal Q workTapeCount time)
        · simpa only [blockLength] using
            ComplexityBridge.protectedBinaryLog_le_balancedBlockLength time
      _ =
          (Fintype.card Q + 5 + chunkCoefficient Q workTapeCount + 1) *
            blockLength time := by
        ring
  have hconstant : 32 ≤ 32 * blockLength time := by
    have hb : 1 ≤ blockLength time := blockLength_pos_internal time
    simpa using Nat.mul_le_mul_left 32 hb
  unfold scratchBits
  calc
    8 * (booleanWidth Q time + chunkBits Q workTapeCount time +
          ComplexityBridge.protectedBinaryLog time) + 32 ≤
        8 *
            ((Fintype.card Q + 5 + chunkCoefficient Q workTapeCount + 1) *
              blockLength time) +
          32 * blockLength time :=
      Nat.add_le_add (Nat.mul_le_mul_left 8 hsum) hconstant
    _ =
        (8 * (Fintype.card Q + 5 + chunkCoefficient Q workTapeCount + 1) +
          32) * blockLength time := by
      ring

theorem totalBits_le_internal
    (Q : Type*) [Fintype Q] (workTapeCount time : ℕ) :
    totalBits Q workTapeCount time ≤
      workspaceCoefficient Q workTapeCount * blockLength time := by
  unfold totalBits
  calc
    catalyticBankBits Q workTapeCount time +
          stackBits Q workTapeCount time +
          graphBits Q workTapeCount time +
          guessBits workTapeCount time +
          scratchBits Q workTapeCount time ≤
        2 * (fanIn workTapeCount + 1) *
              (Fintype.card Q + 5 + chunkCoefficient Q workTapeCount) *
              blockLength time +
          48 * chunkCoefficient Q workTapeCount * blockLength time +
          4 * fanIn workTapeCount * chunkCoefficient Q workTapeCount *
              blockLength time +
          (4 * (workTapeCount + 2) + 1) * blockLength time +
          (8 *
                (Fintype.card Q + 5 + chunkCoefficient Q workTapeCount + 1) +
              32) *
            blockLength time := by
      exact Nat.add_le_add
        (Nat.add_le_add
          (Nat.add_le_add
            (Nat.add_le_add
              (catalyticBankBits_le_internal Q workTapeCount time)
              (stackBits_le_internal Q workTapeCount time))
            (graphBits_le_internal Q workTapeCount time))
          (guessBits_le_internal workTapeCount time))
        (scratchBits_le_internal Q workTapeCount time)
    _ = workspaceCoefficient Q workTapeCount * blockLength time := by
      simp only [workspaceCoefficient]
      ring

theorem totalBits_isBigO_blockLength_internal
    (Q : Type*) [Fintype Q] (workTapeCount : ℕ) :
    (fun time => totalBits Q workTapeCount time) =O
      fun time => blockLength time := by
  have hpoint :
      ∀ time, totalBits Q workTapeCount time ≤
        workspaceCoefficient Q workTapeCount * blockLength time :=
    totalBits_le_internal Q workTapeCount
  exact (BigO.of_le hpoint).trans
    (BigO.const_mul_left (workspaceCoefficient Q workTapeCount)
      (BigO.refl fun time => blockLength time))

theorem totalBits_isBigO_sqrtLog_internal
    (Q : Type*) [Fintype Q] (workTapeCount : ℕ) :
    (fun time => totalBits Q workTapeCount time) =O
      ComplexityBridge.sqrtLogSpace id := by
  apply (totalBits_isBigO_blockLength_internal Q workTapeCount).trans
  simpa [blockLength, ComplexityBridge.roundedSqrtLogSpace] using
    (ComplexityBridge.roundedSqrtLogSpace_isBigO (T := id)
      (fun time => le_rfl))

theorem totalBits_le_trialEnvelope_internal
    (Q : Type*) [Fintype Q] (workTapeCount : ℕ)
    {trial trialHorizon : ℕ} (htrial : trial ≤ trialHorizon) :
    totalBits Q workTapeCount trial ≤
      trialEnvelopeBits Q workTapeCount trialHorizon := by
  calc
    totalBits Q workTapeCount trial ≤
        workspaceCoefficient Q workTapeCount * blockLength trial :=
      totalBits_le_internal Q workTapeCount trial
    _ ≤ workspaceCoefficient Q workTapeCount * blockLength trialHorizon :=
      Nat.mul_le_mul_left _
        (blockLength_mono_internal htrial)
    _ = trialEnvelopeBits Q workTapeCount trialHorizon := by
      rfl

theorem blockLength_le_trialEnvelope_internal
    (Q : Type*) [Fintype Q] (workTapeCount time : ℕ) :
    blockLength time ≤
      trialEnvelopeBits Q workTapeCount time := by
  have hcoefficient :
      1 ≤ workspaceCoefficient Q workTapeCount := by
    simp only [workspaceCoefficient]
    omega
  unfold trialEnvelopeBits
  simpa using Nat.mul_le_mul_right
    (blockLength time) hcoefficient

theorem size_le_trialEnvelope_internal
    (Q : Type*) [Fintype Q] (workTapeCount time : ℕ) :
    Nat.size time ≤
      trialEnvelopeBits Q workTapeCount time := by
  calc
    Nat.size time ≤
        ComplexityBridge.protectedBinaryLog time := by
      exact Nat.size_le_log_two_add_one time
    _ ≤ blockLength time := by
      simpa only [blockLength] using
        ComplexityBridge.protectedBinaryLog_le_balancedBlockLength time
    _ ≤ trialEnvelopeBits Q workTapeCount time :=
      blockLength_le_trialEnvelope_internal
        Q workTapeCount time

theorem totalBits_le_max_horizon_internal
    (Q : Type*) [Fintype Q] (workTapeCount inputLength haltTime : ℕ)
    {trial : ℕ} (htrial : trial ≤ max inputLength haltTime) :
    totalBits Q workTapeCount trial ≤
      trialEnvelopeBits Q workTapeCount (max inputLength haltTime) :=
  totalBits_le_trialEnvelope_internal Q workTapeCount htrial

theorem trialEnvelopeBits_isBigO_sqrtLog_internal
    (Q : Type*) [Fintype Q] (workTapeCount : ℕ) :
    (fun trialHorizon =>
      trialEnvelopeBits Q workTapeCount trialHorizon) =O
        ComplexityBridge.sqrtLogSpace id := by
  have hblock :
      (fun trialHorizon => blockLength trialHorizon) =O
        ComplexityBridge.sqrtLogSpace id := by
    simpa [blockLength, ComplexityBridge.roundedSqrtLogSpace] using
      (ComplexityBridge.roundedSqrtLogSpace_isBigO (T := id)
        (fun time => le_rfl))
  simpa only [trialEnvelopeBits] using
    BigO.const_mul_left (workspaceCoefficient Q workTapeCount) hblock

end Internal

end WorkspaceAccounting

end NeighborhoodGraph

end TimeSpaceSimulation

end Complexity
