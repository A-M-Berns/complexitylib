/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/
import Complexitylib.TreeEvaluation.CookMertz.GroupedExtension.Defs

/-!
# Logarithmic-chunk parameters for grouped Cook--Mertz evaluation

For a Boolean payload of width `payloadWidth` and fan-in `fanIn`, set

`q = log₂(fanIn * payloadWidth) + 1`

and split the payload into `⌈payloadWidth / q⌉` chunks. This choice makes the
number of grouped input coordinates fit inside the `2 ^ q`-point Boolean
chunk domain while keeping scalar and counter widths logarithmic.

The condition `q ≤ payloadWidth` is recorded separately as
`InLogarithmicRegime`. It is not true for arbitrary pairs of natural
parameters, so the surface module characterizes its exact positive-width
boundary instead of hiding a finite-width exception.

## Main definitions

- `chunkBits` -- the protected logarithmic chunk width `q`
- `chunkCount` -- the ceiling-divided coordinate count
- `fieldBits` -- a `2 * q`-bit charge for one field element
- `frameBitBudget` -- width of a fixed collection of scalars and counters
- `InLogarithmicRegime` -- the side condition `q ≤ payloadWidth`
- `RequiresSmallCase` -- the complementary relative-small-width branch
-/

namespace Complexity

namespace TreeEval

namespace CookMertz

namespace GroupedExtension

namespace LogarithmicParameters

/-- Protected binary-logarithmic chunk width. -/
def chunkBits (payloadWidth fanIn : ℕ) : ℕ :=
  Nat.log 2 (fanIn * payloadWidth) + 1

/-- Number of logarithmic chunks needed to cover the Boolean payload. -/
def chunkCount (payloadWidth fanIn : ℕ) : ℕ :=
  payloadWidth ⌈/⌉ chunkBits payloadWidth fanIn

/-- Bit charge for a field element from a square `q`-bit chunk domain. -/
def fieldBits (payloadWidth fanIn : ℕ) : ℕ :=
  2 * chunkBits payloadWidth fanIn

/-- Bit charge for fixed collections of field scalars and `q`-bit counters. -/
def frameBitBudget (payloadWidth fanIn scalarCount counterCount : ℕ) : ℕ :=
  scalarCount * fieldBits payloadWidth fanIn +
    counterCount * chunkBits payloadWidth fanIn

/-- Regime in which a logarithmic chunk is no wider than the payload.

For positive parameters this is equivalent to
`fanIn * payloadWidth < 2 ^ payloadWidth`. -/
def InLogarithmicRegime (payloadWidth fanIn : ℕ) : Prop :=
  chunkBits payloadWidth fanIn ≤ payloadWidth

/-- Complementary branch where the logarithmic chunk exceeds the payload. -/
def RequiresSmallCase (payloadWidth fanIn : ℕ) : Prop :=
  payloadWidth < chunkBits payloadWidth fanIn

end LogarithmicParameters

end GroupedExtension

end CookMertz

end TreeEval

end Complexity
