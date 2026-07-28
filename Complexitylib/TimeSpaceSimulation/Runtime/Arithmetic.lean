/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/
import Complexitylib.TimeSpaceSimulation.Runtime.Arithmetic.Defs
import Complexitylib.TimeSpaceSimulation.Runtime.Arithmetic.Internal

/-!
# First-order arithmetic used by the time-space simulator

The public loop theorem identifies the structured RAM modular-power loop with
the independently specified natural-residue runtime. The inverse program is
defined in `Arithmetic.Defs`; its end-to-end correctness theorem follows after
the structured execution proof.
-/

namespace Complexity

namespace TimeSpaceSimulation

namespace Runtime

open RAM Structured
open TreeEval CookMertz PrimeField

/-- The structured RAM modular-power loop is exactly the executable
natural-residue loop whenever its accumulator is canonical. -/
theorem powModLoop_eq_runtime
    {modulus base exponent accumulator : ℕ}
    (hmodulus : 0 < modulus)
    (haccumulator : accumulator < modulus) :
    RAM.Structured.RuntimeArithmetic.powModLoop
        modulus base exponent accumulator =
      PrimeField.Runtime.powLoop modulus base exponent accumulator :=
  Internal.powModLoop_eq_runtime_internal hmodulus haccumulator

/-- Starting at one, the structured RAM loop computes the executable runtime
power exactly. -/
theorem powModLoop_one_eq_runtime
    {modulus base exponent : ℕ} (hmodulus : 1 < modulus) :
    RAM.Structured.RuntimeArithmetic.powModLoop
        modulus base exponent 1 =
      PrimeField.Runtime.pow modulus base exponent :=
  Internal.powModLoop_one_eq_runtime_internal hmodulus

/-- The fixed-register inverse program computes the exact natural-residue
inverse used by the executable evaluator. -/
theorem inverseMod_runs
    (regs : RuntimeArithmetic.PowRegisters)
    (store : Store) (modulus base : ℕ)
    (hprime : modulus.Prime)
    (hmodulusValue : store regs.modulus = modulus)
    (hmodulusPred :
      store regs.modulusPred = modulus - 1)
    (hbase : store regs.base = base)
    (hone : store regs.one = 1)
    (hbaseLt : base < modulus) :
    Runs (inverseMod regs) store
      (RuntimeArithmetic.powModResultStore regs
        (PrimeField.Runtime.inverse modulus base) store) :=
  Internal.inverseMod_runs_internal regs store modulus base hprime
    hmodulusValue hmodulusPred hbase hone hbaseLt

end Runtime

end TimeSpaceSimulation

end Complexity
