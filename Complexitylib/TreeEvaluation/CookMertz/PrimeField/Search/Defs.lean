/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/
import Complexitylib.TreeEvaluation.CookMertz.PrimeField.Defs
import Mathlib.NumberTheory.Bertrand

/-!
# Executable prime-modulus search

This file defines a streamed finite search for a Cook--Mertz prime modulus.
For degree `d`, the proof-side candidate list is exactly

`d + 2, d + 3, ..., 2 * (d + 1)`.

Primality is tested by the executable decision procedure for `Nat.Prime`.
The runtime scan stores only its remaining fuel and current candidate; it
does not materialize the interval. `searchModulus` uses `2` only as a total
fallback, and Bertrand's postulate proves that branch unreachable.

## Main definitions

- `Search.candidates` -- the finite Bertrand interval
- `Search.isPrime` -- executable primality predicate
- `Search.scanPrime` -- tail-recursive consecutive-candidate scan
- `Search.firstPrime?` -- first prime found in the interval
- `Search.searchModulus` -- total executable selected modulus
-/

namespace Complexity

namespace TreeEval

namespace CookMertz

namespace PrimeField

namespace Search

/-- Finite increasing list `degree + 2, ..., 2 * (degree + 1)`. -/
def candidates (degree : ℕ) : List ℕ :=
  (List.range (degree + 1)).map (fun offset => degree + 2 + offset)

/-- Executable Boolean primality test. -/
def isPrime (value : ℕ) : Bool :=
  decide value.Prime

/-- Tail-recursively scan `fuel` consecutive candidates beginning at
`current`. -/
def scanPrime : ℕ → ℕ → Option ℕ
  | 0, _ => none
  | fuel + 1, current =>
      if isPrime current then
        some current
      else
        scanPrime fuel (current + 1)

/-- First prime in the Bertrand interval, if present.

The executable definition streams candidates instead of allocating
`candidates degree`. -/
def firstPrime? (degree : ℕ) : Option ℕ :=
  scanPrime (degree + 1) (degree + 2)

/-- Total executable modulus selection.

The fallback value is unreachable by `firstPrime?_ne_none`; retaining it in
the definition avoids any classical or proof-dependent extraction. -/
def searchModulus (degree : ℕ) : ℕ :=
  (firstPrime? degree).getD 2

end Search

end PrimeField

end CookMertz

end TreeEval

end Complexity
