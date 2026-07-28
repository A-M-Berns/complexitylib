/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/
import Complexitylib.Asymptotics
import
  Complexitylib.TimeSpaceSimulation.CertifiedSearch.Asymptotics.Defs
import Complexitylib.TimeSpaceSimulation.ComplexityBridge
import
  Complexitylib.TimeSpaceSimulation.NeighborhoodGraph.WorkspaceAccounting

/-!
# Proof internals for certified-search asymptotics

This file transfers an eventual source-runtime bound through the explicit
proof-level search endpoint and the streamed-trial workspace envelope.
-/

open Asymptotics Filter

namespace Complexity

namespace TimeSpaceSimulation

namespace CertifiedSearch

namespace Asymptotics

open NeighborhoodGraph

namespace Internal

theorem binaryLog_mul_le_internal
    {factor time : ℕ} (hfactor : 0 < factor) (htime : 2 ≤ time) :
    Nat.log 2 (factor * time) ≤
      (Nat.log 2 factor + 2) * Nat.log 2 time := by
  have htimePos : 0 < time := by omega
  have hlogPos : 1 ≤ Nat.log 2 time :=
    Nat.log_pos (by omega) htime
  have hfactorLt :=
    Nat.lt_pow_succ_log_self Nat.one_lt_two factor
  have htimeLt :=
    Nat.lt_pow_succ_log_self Nat.one_lt_two time
  have hproductLt :
      factor * time <
        2 ^ ((Nat.log 2 factor + 1) +
          (Nat.log 2 time + 1)) := by
    rw [Nat.pow_add]
    calc
      factor * time <
          2 ^ (Nat.log 2 factor + 1) * time :=
        (Nat.mul_lt_mul_right htimePos).2 hfactorLt
      _ < 2 ^ (Nat.log 2 factor + 1) *
          2 ^ (Nat.log 2 time + 1) :=
        (Nat.mul_lt_mul_left (by positivity)).2 htimeLt
  have hlogLt :=
    Nat.log_lt_of_lt_pow
      (Nat.mul_pos hfactor htimePos).ne' hproductLt
  have hlog :
      Nat.log 2 (factor * time) ≤
        Nat.log 2 factor + Nat.log 2 time + 1 := by
    omega
  have hfactorLog :
      Nat.log 2 factor ≤ Nat.log 2 factor * Nat.log 2 time := by
    simpa using Nat.mul_le_mul_left (Nat.log 2 factor) hlogPos
  have htimeLog : Nat.log 2 time + 1 ≤ 2 * Nat.log 2 time := by
    omega
  calc
    Nat.log 2 (factor * time) ≤
        Nat.log 2 factor + (Nat.log 2 time + 1) := by
      omega
    _ ≤ Nat.log 2 factor * Nat.log 2 time +
          2 * Nat.log 2 time :=
      Nat.add_le_add hfactorLog htimeLog
    _ = (Nat.log 2 factor + 2) * Nat.log 2 time := by
      ring

theorem sqrt_mul_le_internal
    {factor radicand : ℕ} (hfactor : 0 < factor)
    (hradicand : 0 < radicand) :
    Nat.sqrt (factor * radicand) ≤
      2 * factor * Nat.sqrt radicand := by
  let root := Nat.sqrt radicand
  have hroot : 0 < root := by
    simpa [root] using (Nat.sqrt_pos.mpr hradicand)
  have hradicandLt :
      radicand < (root + 1) * (root + 1) := by
    simpa [root, Nat.succ_eq_add_one] using
      Nat.lt_succ_sqrt radicand
  have hrootDouble : root + 1 ≤ 2 * root := by
    omega
  have hsquare :
      (root + 1) * (root + 1) ≤
        (2 * root) * (2 * root) :=
    Nat.mul_le_mul hrootDouble hrootDouble
  have hfactorSquare : factor ≤ factor * factor := by
    calc
      factor = factor * 1 := by simp
      _ ≤ factor * factor :=
        Nat.mul_le_mul_left factor (by omega)
  have hscaledLt :
      factor * radicand <
        (2 * factor * root) * (2 * factor * root) := by
    calc
      factor * radicand <
          factor * ((root + 1) * (root + 1)) :=
        (Nat.mul_lt_mul_left hfactor).2 hradicandLt
      _ ≤ factor * ((2 * root) * (2 * root)) :=
        Nat.mul_le_mul_left factor hsquare
      _ ≤ (factor * factor) * ((2 * root) * (2 * root)) :=
        Nat.mul_le_mul_right ((2 * root) * (2 * root))
          hfactorSquare
      _ = (2 * factor * root) * (2 * factor * root) := by
        ring
  exact (Nat.sqrt_lt.mpr hscaledLt).le

theorem trialEnvelopeBits_max_le_internal
    (Q : Type*) [Fintype Q] (workTapeCount : ℕ)
    {actualTime T : ℕ → ℕ} {runtimeCoefficient threshold n : ℕ}
    (hbound : ∀ m, threshold ≤ m →
      actualTime m ≤ runtimeCoefficient * T m)
    (hT : ∀ m, m ≤ T m)
    (hn : max threshold 2 ≤ n) :
    WorkspaceAccounting.trialEnvelopeBits Q workTapeCount
        (max n (actualTime n)) ≤
      envelopeTransferCoefficient Q workTapeCount runtimeCoefficient *
        ComplexityBridge.sqrtLogSpace T n := by
  let factor := runtimeCoefficient + 1
  let logFactor := Nat.log 2 factor + 2
  let radicand := T n * Nat.log 2 (T n)
  have hnThreshold : threshold ≤ n :=
    (Nat.le_max_left threshold 2).trans hn
  have hnTwo : 2 ≤ n :=
    (Nat.le_max_right threshold 2).trans hn
  have htimeTwo : 2 ≤ T n := hnTwo.trans (hT n)
  have hfactor : 0 < factor := by
    simp [factor]
  have hactual : actualTime n ≤ runtimeCoefficient * T n :=
    hbound n hnThreshold
  have hhorizon :
      max n (actualTime n) ≤ factor * T n := by
    apply max_le
    · calc
        n ≤ T n := hT n
        _ ≤ factor * T n := by
          have hone : 1 ≤ factor := by omega
          simpa using Nat.mul_le_mul_right (T n) hone
    · calc
        actualTime n ≤ runtimeCoefficient * T n := hactual
        _ ≤ factor * T n :=
          Nat.mul_le_mul_right (T n) (by simp [factor])
  have hhorizonTwo : 2 ≤ max n (actualTime n) :=
    hnTwo.trans (Nat.le_max_left n (actualTime n))
  have hlogHorizon :
      Nat.log 2 (max n (actualTime n)) ≤
        logFactor * Nat.log 2 (T n) := by
    calc
      Nat.log 2 (max n (actualTime n)) ≤
          Nat.log 2 (factor * T n) :=
        Nat.log_mono_right hhorizon
      _ ≤ logFactor * Nat.log 2 (T n) := by
        simpa [logFactor] using
          binaryLog_mul_le_internal hfactor htimeTwo
  have hradicandPos : 0 < radicand := by
    apply Nat.mul_pos
    · omega
    · exact Nat.log_pos (by omega) htimeTwo
  have hradicandBound :
      max n (actualTime n) * Nat.log 2 (max n (actualTime n)) ≤
        (factor * logFactor) * radicand := by
    calc
      max n (actualTime n) *
            Nat.log 2 (max n (actualTime n)) ≤
          (factor * T n) *
            (logFactor * Nat.log 2 (T n)) :=
        Nat.mul_le_mul hhorizon hlogHorizon
      _ = (factor * logFactor) * radicand := by
        simp only [radicand]
        ring
  have hcombinedFactor : 0 < factor * logFactor := by
    apply Nat.mul_pos hfactor
    simp [logFactor]
  have hsqrt :
      Nat.sqrt
          (max n (actualTime n) *
            Nat.log 2 (max n (actualTime n))) ≤
        2 * (factor * logFactor) * Nat.sqrt radicand := by
    exact (Nat.sqrt_le_sqrt hradicandBound).trans
      (sqrt_mul_le_internal hcombinedFactor hradicandPos)
  have hblock :
      WorkspaceAccounting.blockLength (max n (actualTime n)) ≤
        3 * Nat.sqrt
          (max n (actualTime n) *
            Nat.log 2 (max n (actualTime n))) := by
    simpa [WorkspaceAccounting.blockLength] using
      ComplexityBridge.balancedBlockLength_le_three_mul_sqrtLog
        hhorizonTwo
  calc
    WorkspaceAccounting.trialEnvelopeBits Q workTapeCount
        (max n (actualTime n)) =
        WorkspaceAccounting.workspaceCoefficient Q workTapeCount *
          WorkspaceAccounting.blockLength
            (max n (actualTime n)) := by
      rfl
    _ ≤ WorkspaceAccounting.workspaceCoefficient Q workTapeCount *
          (3 * Nat.sqrt
            (max n (actualTime n) *
              Nat.log 2 (max n (actualTime n)))) :=
      Nat.mul_le_mul_left _ hblock
    _ ≤ WorkspaceAccounting.workspaceCoefficient Q workTapeCount *
          (3 *
            (2 * (factor * logFactor) * Nat.sqrt radicand)) :=
      Nat.mul_le_mul_left _ (Nat.mul_le_mul_left 3 hsqrt)
    _ = envelopeTransferCoefficient Q workTapeCount runtimeCoefficient *
          ComplexityBridge.sqrtLogSpace T n := by
      simp only [envelopeTransferCoefficient,
        ComplexityBridge.sqrtLogSpace, factor, logFactor, radicand]
      ring

theorem trialEnvelopeBits_max_actualTime_isBigO_internal
    (Q : Type*) [Fintype Q] (workTapeCount : ℕ)
    {actualTime T : ℕ → ℕ}
    (htime : actualTime =O T)
    (hT : ∀ n, n ≤ T n) :
    (fun n => WorkspaceAccounting.trialEnvelopeBits Q workTapeCount
      (max n (actualTime n))) =O
        ComplexityBridge.sqrtLogSpace T := by
  obtain ⟨runtimeCoefficient, threshold, hbound⟩ :=
    BigO.exists_nat_bound htime
  rw [BigO]
  apply IsBigO.of_bound
    (envelopeTransferCoefficient Q workTapeCount runtimeCoefficient)
  filter_upwards [eventually_ge_atTop (max threshold 2)] with n hn
  simp only [Real.norm_natCast]
  exact_mod_cast trialEnvelopeBits_max_le_internal Q workTapeCount
    hbound hT hn

end Internal

end Asymptotics

end CertifiedSearch

end TimeSpaceSimulation

end Complexity
