/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/
import Complexitylib.Models.RandomAccessMachine.Structured.Run.Defs

/-!
# Proof internals for qualitative structured RAM execution
-/

namespace Complexity

namespace RAM

namespace Structured

namespace Internal

theorem Runs.skip_internal (store : Store) :
    Runs .skip store store :=
  ⟨0, 0, store.space, Exec.skip store⟩

theorem Runs.basic_internal (op : Basic) (store : Store) :
    Runs (.basic op) store (op.exec store) :=
  ⟨1, op.logCost store, max store.space (op.exec store).space,
    Exec.basic op store⟩

theorem Runs.seq_internal {first second : Cmd}
    {initial middle final : Store}
    (hfirst : Runs first initial middle)
    (hsecond : Runs second middle final) :
    Runs (.seq first second) initial final := by
  obtain ⟨firstSteps, firstCost, firstSpace, hfirst⟩ := hfirst
  obtain ⟨secondSteps, secondCost, secondSpace, hsecond⟩ := hsecond
  exact ⟨firstSteps + secondSteps, firstCost + secondCost,
    max firstSpace secondSpace, Exec.seq hfirst hsecond⟩

theorem Runs.ifZero_internal {test : ℕ} {onZero onNonzero : Cmd}
    {initial final : Store} (htest : initial test = 0)
    (hbranch : Runs onZero initial final) :
    Runs (.ifZero test onZero onNonzero) initial final := by
  obtain ⟨steps, cost, space, hbranch⟩ := hbranch
  exact ⟨steps + 1, bitlen (initial test) + 1 + cost,
    max initial.space space, Exec.ifZero htest hbranch⟩

theorem Runs.ifNonzero_internal {test : ℕ} {onZero onNonzero : Cmd}
    {initial final : Store} (htest : initial test ≠ 0)
    (hbranch : Runs onNonzero initial final) :
    Runs (.ifZero test onZero onNonzero) initial final := by
  obtain ⟨steps, cost, space, hbranch⟩ := hbranch
  exact ⟨steps + 2, bitlen (initial test) + 1 + cost + 1,
    max initial.space space, Exec.ifNonzero htest hbranch⟩

theorem Runs.whileZero_internal {test : ℕ} {body : Cmd}
    {store : Store} (htest : store test = 0) :
    Runs (.whileNonzero test body) store store :=
  ⟨1, bitlen (store test) + 1, store.space,
    Exec.whileZero htest⟩

theorem Runs.whileNonzero_internal {test : ℕ} {body : Cmd}
    {initial middle final : Store} (htest : initial test ≠ 0)
    (hbody : Runs body initial middle)
    (hloop : Runs (.whileNonzero test body) middle final) :
    Runs (.whileNonzero test body) initial final := by
  obtain ⟨bodySteps, bodyCost, bodySpace, hbody⟩ := hbody
  obtain ⟨loopSteps, loopCost, loopSpace, hloop⟩ := hloop
  exact ⟨bodySteps + loopSteps + 2,
    bitlen (initial test) + 1 + bodyCost + 1 + loopCost,
    max bodySpace loopSpace,
    Exec.whileNonzero htest hbody hloop⟩

end Internal

end Structured

end RAM

end Complexity
