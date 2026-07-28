/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/
import Complexitylib.Mathlib.NatBits
import Complexitylib.TreeEvaluation.CookMertz.PrimeField.Defs
import Mathlib.NumberTheory.Bertrand

/-!
# Proof internals for Cook--Mertz prime-field parameters

Bertrand's postulate supplies a prime in the interval
`(degree + 1, 2 * (degree + 1)]`. The remaining proofs identify the field
cardinality and verify that `PrimeField.units` enumerates every nonzero
residue exactly once.
-/

namespace Complexity

namespace TreeEval

namespace CookMertz

namespace PrimeField

namespace Internal

theorem choice_nonempty_internal (degree : ℕ) :
    Nonempty (Choice degree) := by
  obtain ⟨modulus, hprime, hlower, hupper⟩ :=
    Nat.exists_prime_lt_and_le_two_mul (degree + 1) (by omega)
  exact ⟨⟨modulus, hprime, by omega, hupper⟩⟩

theorem degree_lt_card_sub_one_internal {degree : ℕ}
    (choice : Choice degree) :
    degree < Fintype.card choice.Field - 1 := by
  simpa [Choice.Field, ZMod.card] using choice.degree_lt_sub_one

theorem modulus_size_le_internal {degree : ℕ}
    (choice : Choice degree) :
    choice.modulus.size ≤ Nat.log 2 (2 * (degree + 1)) + 1 := by
  exact (Nat.size_le_log_two_add_one choice.modulus).trans
    (Nat.add_le_add_right
      (Nat.log_mono_right choice.modulus_le_two_mul) 1)

variable (p : ℕ) [Fact p.Prime]

theorem coe_unitOfIndex_internal (index : Fin (p - 1)) :
    (unitOfIndex p index : ZMod p) = (index.val + 1 : ℕ) :=
  rfl

theorem units_nodup_internal : (units p).Nodup := by
  rw [units]
  apply List.Nodup.map
  · intro first second heq
    apply Fin.ext
    have hval :=
      congrArg (fun unit : (ZMod p)ˣ => (unit : ZMod p).val) heq
    simp only [coe_unitOfIndex_internal, ZMod.val_natCast] at hval
    have hfirst : first.val + 1 < p := by omega
    have hsecond : second.val + 1 < p := by omega
    rw [Nat.mod_eq_of_lt hfirst, Nat.mod_eq_of_lt hsecond] at hval
    omega
  · exact List.nodup_finRange _

theorem mem_units_internal (unit : (ZMod p)ˣ) :
    unit ∈ units p := by
  rw [units, List.mem_map]
  have hvalLt : (unit : ZMod p).val < p := ZMod.val_lt _
  have hvalNe : (unit : ZMod p).val ≠ 0 :=
    (ZMod.val_ne_zero _).mpr unit.ne_zero
  let index : Fin (p - 1) :=
    ⟨(unit : ZMod p).val - 1, by omega⟩
  refine ⟨index, List.mem_finRange _, ?_⟩
  apply Units.ext
  change ((index.val + 1 : ℕ) : ZMod p) = (unit : ZMod p)
  rw [show index.val + 1 = (unit : ZMod p).val by
    dsimp [index]
    omega]
  exact ZMod.natCast_zmod_val _

theorem units_length_internal :
    (units p).length = p - 1 := by
  simp [units]

theorem enumeratesUnits_internal :
    EnumeratesUnits (units p) :=
  ⟨units_nodup_internal p, mem_units_internal p⟩

end Internal

end PrimeField

end CookMertz

end TreeEval

end Complexity
