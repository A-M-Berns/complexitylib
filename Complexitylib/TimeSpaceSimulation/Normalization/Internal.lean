/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/
import Complexitylib.TimeSpaceSimulation.Normalization.Defs

/-!
# Block-respecting normalization internals

This file proves the structural and transfer facts for normalization
certificates. The operational Hopcroft--Paul--Valiant compiler is intentionally
not postulated here.
-/

namespace Complexity

namespace TimeSpaceSimulation

namespace HPVParameters

theorem time_clockConstructible_internal {timeBound blockLength : ℕ → ℕ}
    (h : HPVParameters timeBound blockLength) :
    TM.ClockConstructible timeBound :=
  h.1

theorem block_clockConstructible_internal {timeBound blockLength : ℕ → ℕ}
    (h : HPVParameters timeBound blockLength) :
    TM.ClockConstructible blockLength :=
  h.2.1

theorem input_le_time_internal {timeBound blockLength : ℕ → ℕ}
    (h : HPVParameters timeBound blockLength) (inputLength : ℕ) :
    inputLength ≤ timeBound inputLength :=
  h.2.2.1 inputLength

theorem blockLength_pos_internal {timeBound blockLength : ℕ → ℕ}
    (h : HPVParameters timeBound blockLength) (inputLength : ℕ) :
    0 < blockLength inputLength :=
  (h.2.2.2 inputLength).1

theorem binaryWidth_le_blockLength_internal
    {timeBound blockLength : ℕ → ℕ}
    (h : HPVParameters timeBound blockLength) (inputLength : ℕ) :
    (timeBound inputLength).size ≤ blockLength inputLength :=
  (h.2.2.2 inputLength).2.1

theorem blockLength_le_time_internal {timeBound blockLength : ℕ → ℕ}
    (h : HPVParameters timeBound blockLength) (inputLength : ℕ) :
    blockLength inputLength ≤ timeBound inputLength :=
  (h.2.2.2 inputLength).2.2

end HPVParameters

theorem blockRespectingDTIME_subset_DTIME_internal
    (timeBound blockLength : ℕ → ℕ) :
    BlockRespectingDTIME timeBound blockLength ⊆ DTIME timeBound := by
  rintro L ⟨workTapeCount, machine, runtime, hdecides, hruntime, _⟩
  exact ⟨workTapeCount, machine, runtime, hdecides, hruntime⟩

end TimeSpaceSimulation

namespace TM

open TimeSpaceSimulation

theorem blockRespecting_one_internal (machine : TM workTapeCount) :
    machine.BlockRespecting (fun _ => 1) := by
  intro x
  change 0 < 1 ∧
    ∀ (timeBlock : ℕ) (offset : Fin 1)
        (tape : TapeIndex workTapeCount),
      headBlock 1
          (machine.configurationAt x
            (timeBlockStart 1 timeBlock + offset.val))
          tape =
        headBlock 1
          (machine.configurationAt x (timeBlockStart 1 timeBlock))
          tape
  refine ⟨by omega, ?_⟩
  intro timeBlock offset tape
  simp

namespace LinearBlockNormalization

variable {sourceWorkTapeCount : ℕ} {source : TM sourceWorkTapeCount}
  {timeBound blockLength : ℕ → ℕ}

theorem decidesInTime_internal
    (normalization : LinearBlockNormalization source timeBound blockLength)
    {L : Language} (hdecides : source.DecidesInTime L timeBound) :
    normalization.machine.DecidesInTime L normalization.normalizedTime := by
  intro x
  obtain ⟨cfg, time, htime, hreach, hhalt, hyes, hno⟩ := hdecides x
  obtain ⟨cfg', time', htime', hreach', hhalt', hout⟩ :=
    normalization.simulatesBoundedHaltedRun x htime hreach hhalt
  refine ⟨cfg', time', htime', hreach', hhalt', ?_, ?_⟩
  · intro hx
    rw [hout]
    exact hyes hx
  · intro hx
    rw [hout]
    exact hno hx

theorem normalizedTime_bigO_internal
    (normalization : LinearBlockNormalization source timeBound blockLength)
    (hinput : ∀ inputLength, inputLength ≤ timeBound inputLength) :
    normalization.normalizedTime =O timeBound := by
  show
    (fun inputLength =>
      ((normalization.constant * (timeBound inputLength + 1) : ℕ) : ℝ))
      =O[Filter.atTop] (fun inputLength => (timeBound inputLength : ℝ))
  apply Asymptotics.IsBigO.of_bound (2 * normalization.constant)
  filter_upwards [Filter.eventually_ge_atTop 1] with inputLength hlength
  simp only [Real.norm_natCast]
  have hone : 1 ≤ timeBound inputLength :=
    le_trans hlength (hinput inputLength)
  have hnat :
      normalization.constant * (timeBound inputLength + 1) ≤
        2 * normalization.constant * timeBound inputLength := by
    calc
      normalization.constant * (timeBound inputLength + 1) ≤
          normalization.constant * (2 * timeBound inputLength) :=
        Nat.mul_le_mul_left normalization.constant (by omega)
      _ = 2 * normalization.constant * timeBound inputLength := by ring
  exact_mod_cast hnat

theorem normalizedTime_bigO_of_parameters_internal
    (normalization : LinearBlockNormalization source timeBound blockLength)
    (hparameters : HPVParameters timeBound blockLength) :
    normalization.normalizedTime =O timeBound :=
  normalization.normalizedTime_bigO_internal
    hparameters.input_le_time_internal

theorem mem_blockRespectingDTIME_internal
    (normalization : LinearBlockNormalization source timeBound blockLength)
    {L : Language} (hdecides : source.DecidesInTime L timeBound)
    (hinput : ∀ inputLength, inputLength ≤ timeBound inputLength) :
    L ∈ BlockRespectingDTIME timeBound blockLength :=
  ⟨normalization.workTapeCount, normalization.machine,
    normalization.normalizedTime,
    normalization.decidesInTime_internal hdecides,
    normalization.normalizedTime_bigO_internal hinput,
    normalization.blockRespecting⟩

theorem mem_blockRespectingDTIME_of_parameters_internal
    (normalization : LinearBlockNormalization source timeBound blockLength)
    {L : Language} (hdecides : source.DecidesInTime L timeBound)
    (hparameters : HPVParameters timeBound blockLength) :
    L ∈ BlockRespectingDTIME timeBound blockLength :=
  normalization.mem_blockRespectingDTIME_internal hdecides
    hparameters.input_le_time_internal

theorem exists_one_internal (source : TM sourceWorkTapeCount)
    (timeBound : ℕ → ℕ) :
    Nonempty
      (LinearBlockNormalization source timeBound (fun _ => 1)) := by
  refine ⟨{
    workTapeCount := sourceWorkTapeCount
    machine := source
    workTapeCount_le := by omega
    constant := 1
    constant_pos := by omega
    blockRespecting := blockRespecting_one_internal source
    simulatesBoundedHaltedRun := ?_
  }⟩
  intro x cfg time htime hreach hhalt
  exact ⟨cfg, time, by omega, hreach, hhalt, rfl⟩

end LinearBlockNormalization

end TM

namespace TimeSpaceSimulation

theorem blockRespectingDTIME_one_eq_DTIME_internal (timeBound : ℕ → ℕ) :
    BlockRespectingDTIME timeBound (fun _ => 1) = DTIME timeBound := by
  apply Set.Subset.antisymm
  · exact blockRespectingDTIME_subset_DTIME_internal timeBound (fun _ => 1)
  · rintro L ⟨workTapeCount, machine, runtime, hdecides, hruntime⟩
    exact ⟨workTapeCount, machine, runtime, hdecides, hruntime,
      TM.blockRespecting_one_internal machine⟩

end TimeSpaceSimulation

end Complexity
