/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/
import Complexitylib.TimeSpaceSimulation.NeighborhoodGraph.WorkspaceAccounting.Defs
import Complexitylib.TimeSpaceSimulation.NeighborhoodGraph.WorkspaceAccounting.Internal

/-!
# Verified workspace bound for the direct neighborhood route

For a fixed finite source-state type and work-tape count, the concrete
accounting budget is bounded pointwise by an explicit machine-dependent
constant times

`max 1 ⌈√(T * (log₂ T + 1))⌉`.

The theorem is total: it includes `T = 0` and `T = 1`. It also handles both
grouping branches. When `q ≤ B`, the usual four-times-payload catalytic bound
applies. When `B < q`, the chunk count is exactly one and the catalytic bank
is charged directly in terms of `q`.
-/

namespace Complexity

namespace TimeSpaceSimulation

namespace NeighborhoodGraph

namespace WorkspaceAccounting

/-- The chosen interval length is always positive. -/
theorem blockLength_pos (time : ℕ) :
    0 < blockLength time :=
  Internal.blockLength_pos_internal time

/-- Larger trial horizons use weakly larger balanced blocks. -/
theorem blockLength_mono {first second : ℕ} (h : first ≤ second) :
    blockLength first ≤ blockLength second :=
  Internal.blockLength_mono_internal h

/-- The ceiling-divided horizon is no larger than the bridge's padded block
count. -/
theorem horizon_le_timeBlockCount (time : ℕ) :
    horizon time ≤ ComplexityBridge.timeBlockCount time :=
  Internal.horizon_le_timeBlockCount_internal time

/-- The balanced interval count is at most twice the balanced block length. -/
theorem horizon_le_two_mul_blockLength (time : ℕ) :
    horizon time ≤ 2 * blockLength time :=
  Internal.horizon_le_two_mul_blockLength_internal time

/-- The compact Boolean payload is positive, even for an empty state type. -/
theorem booleanWidth_pos
    (Q : Type*) [Fintype Q] (time : ℕ) :
    0 < booleanWidth Q time :=
  Internal.booleanWidth_pos_internal Q time

/-- The direct neighborhood fan-in is positive. -/
theorem fanIn_pos (workTapeCount : ℕ) :
    0 < fanIn workTapeCount :=
  Internal.fanIn_pos_internal workTapeCount

/-- The payload is at most a machine constant times the chosen block length. -/
theorem booleanWidth_le_mul_blockLength
    (Q : Type*) [Fintype Q] (time : ℕ) :
    booleanWidth Q time ≤
      (Fintype.card Q + 5) * blockLength time :=
  Internal.booleanWidth_le_mul_blockLength_internal Q time

/-- Beyond the two finite base cases, the chosen block does not exceed time. -/
theorem blockLength_le_time {time : ℕ} (htime : 2 ≤ time) :
    blockLength time ≤ time :=
  Internal.blockLength_le_time_internal htime

/-- The grouped width is bounded by an explicit machine constant times the
protected time logarithm, including `time = 0` and `time = 1`. -/
theorem chunkBits_le_mul_log
    (Q : Type*) [Fintype Q] (workTapeCount time : ℕ) :
    chunkBits Q workTapeCount time ≤
      chunkCoefficient Q workTapeCount *
        ComplexityBridge.protectedBinaryLog time :=
  Internal.chunkBits_le_mul_log_internal Q workTapeCount time

/-- The grouped width is bounded by the same constant times the block length. -/
theorem chunkBits_le_mul_blockLength
    (Q : Type*) [Fintype Q] (workTapeCount time : ℕ) :
    chunkBits Q workTapeCount time ≤
      chunkCoefficient Q workTapeCount * blockLength time :=
  Internal.chunkBits_le_mul_blockLength_internal Q workTapeCount time

/-- Exact evaluator-frame charge: eight field scalars and eight counters cost
`24q` bits under the assigned field width. -/
theorem frameBits_eq
    (Q : Type*) [Fintype Q] (workTapeCount time : ℕ) :
    frameBits Q workTapeCount time =
      24 * chunkBits Q workTapeCount time :=
  Internal.frameBits_eq_internal Q workTapeCount time

/-- Both the ordinary logarithmic regime and the `q > B` branch have explicit
catalytic-bank bounds. In the latter branch, the chunk count is exactly one. -/
theorem catalyticBankBits_branch
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
          chunkCoefficient Q workTapeCount * blockLength time) :=
  Internal.catalyticBankBits_branch_internal Q workTapeCount time

/-- The full stack charge is square-root-logarithmic. -/
theorem stackBits_le
    (Q : Type*) [Fintype Q] (workTapeCount time : ℕ) :
    stackBits Q workTapeCount time ≤
      48 * chunkCoefficient Q workTapeCount * blockLength time :=
  Internal.stackBits_le_internal Q workTapeCount time

/-- Unconditional explicit pointwise workspace bound.

This theorem includes `time = 0`, `time = 1`, and the branch `q > B`; it has
no growth hypothesis and no hidden asymptotic side condition. -/
theorem totalBits_le
    (Q : Type*) [Fintype Q] (workTapeCount time : ℕ) :
    totalBits Q workTapeCount time ≤
      workspaceCoefficient Q workTapeCount * blockLength time :=
  Internal.totalBits_le_internal Q workTapeCount time

/-- The concrete budget is big-O of the positively rounded balance. -/
theorem totalBits_isBigO_blockLength
    (Q : Type*) [Fintype Q] (workTapeCount : ℕ) :
    (fun time => totalBits Q workTapeCount time) =O
      fun time => blockLength time :=
  Internal.totalBits_isBigO_blockLength_internal Q workTapeCount

/-- The concrete budget has the advertised `O(√(T log T))` asymptotic bound. -/
theorem totalBits_isBigO_sqrtLog
    (Q : Type*) [Fintype Q] (workTapeCount : ℕ) :
    (fun time => totalBits Q workTapeCount time) =O
      ComplexityBridge.sqrtLogSpace id :=
  Internal.totalBits_isBigO_sqrtLog_internal Q workTapeCount

/-- Every explicitly streamed candidate trial fits the envelope determined by
any upper horizon. The candidate is an ordinary natural number; no time-bound
oracle is part of this statement. -/
theorem totalBits_le_trialEnvelope
    (Q : Type*) [Fintype Q] (workTapeCount : ℕ)
    {trial trialHorizon : ℕ} (htrial : trial ≤ trialHorizon) :
    totalBits Q workTapeCount trial ≤
      trialEnvelopeBits Q workTapeCount trialHorizon :=
  Internal.totalBits_le_trialEnvelope_internal Q workTapeCount htrial

/-- The uniform trial envelope always covers its own balanced block length. -/
theorem blockLength_le_trialEnvelope
    (Q : Type*) [Fintype Q] (workTapeCount time : ℕ) :
    blockLength time ≤
      trialEnvelopeBits Q workTapeCount time :=
  Internal.blockLength_le_trialEnvelope_internal
    Q workTapeCount time

/-- The candidate's binary width fits the uniform trial envelope. -/
theorem size_le_trialEnvelope
    (Q : Type*) [Fintype Q] (workTapeCount time : ℕ) :
    Nat.size time ≤
      trialEnvelopeBits Q workTapeCount time :=
  Internal.size_le_trialEnvelope_internal
    Q workTapeCount time

/-- Uniform bound for a streamed search from the input length through the
proof-level endpoint `max inputLength haltTime`. -/
theorem totalBits_le_max_horizon
    (Q : Type*) [Fintype Q] (workTapeCount inputLength haltTime : ℕ)
    {trial : ℕ} (htrial : trial ≤ max inputLength haltTime) :
    totalBits Q workTapeCount trial ≤
      trialEnvelopeBits Q workTapeCount (max inputLength haltTime) :=
  Internal.totalBits_le_max_horizon_internal
    Q workTapeCount inputLength haltTime htrial

/-- The uniform streamed-trial envelope is itself
`O(√(H log H))` in its proof-level horizon `H`. -/
theorem trialEnvelopeBits_isBigO_sqrtLog
    (Q : Type*) [Fintype Q] (workTapeCount : ℕ) :
    (fun trialHorizon =>
      trialEnvelopeBits Q workTapeCount trialHorizon) =O
        ComplexityBridge.sqrtLogSpace id :=
  Internal.trialEnvelopeBits_isBigO_sqrtLog_internal Q workTapeCount

end WorkspaceAccounting

end NeighborhoodGraph

end TimeSpaceSimulation

end Complexity
