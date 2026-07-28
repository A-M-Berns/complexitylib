/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/
import Complexitylib.TreeEvaluation.CookMertz.GroupedExtension.TreeLift
import Complexitylib.TreeEvaluation.CookMertz.PrimeGrouped.Logarithmic.Defs
import Complexitylib.TreeEvaluation.CookMertz.PrimeGrouped.Logarithmic.Internal

/-!
# Logarithmic grouped Cook--Mertz over an executably searched prime field

For Boolean width `B` and fan-in `d`, put

`q = log₂(d * B) + 1`, `t = ⌈B / q⌉`,

and let

`D = d * t * (2 ^ q - 1)`.

The finite Bertrand scan selects a prime modulus above
`max D (2 ^ q - 1)`. The maximum makes the codebook total even at degenerate
parameters; when `B` and `d` are positive, the endpoint is exactly `D`.
The chunk codebook is the executable map obtained by decoding its bit vector
and casting the result into `ZMod`.

Every lifted Boolean node has total degree at most `D`, hence satisfies the
strict interpolation cutoff in the searched field. Cook--Mertz evaluation
therefore returns the encoding of the ordinary Boolean root value.

The selected modulus has at most `2q + 1` bits. Thus the catalytic bank is
unconditionally bounded by `3(d + 1)(B + q)`. In the `q ≤ B` branch this is
at most `6(d + 1)B`; in the explicit positive small-width branch `B < q`,
one has `t = 1` and the sharper bound `3(d + 1)q`. A zero-width payload is
the separate zero-chunk degenerate case.

Only the generic polynomial lift and its evaluator remain noncomputable
certificate objects. The prime scan, chunk encoding, field arithmetic, and
unit enumeration are executable definitions.
-/

namespace Complexity

namespace TreeEval

namespace CookMertz

namespace PrimeGrouped

namespace Logarithmic

/-- The protected logarithmic chunk width is positive for every parameter
pair. -/
theorem chunkBits_pos (payloadWidth fanIn : ℕ) :
    0 < chunkBits payloadWidth fanIn :=
  Internal.chunkBits_pos_internal payloadWidth fanIn

/-- The exact chunk alphabet has cardinality `2 ^ q` and is nonempty. -/
theorem domainSize_pos (payloadWidth fanIn : ℕ) :
    0 < domainSize payloadWidth fanIn :=
  Internal.domainSize_pos_internal payloadWidth fanIn

/-- Since `q` is protected by `+1`, the chunk alphabet has at least two
elements. -/
theorem one_lt_domainSize (payloadWidth fanIn : ℕ) :
    1 < domainSize payloadWidth fanIn :=
  Internal.one_lt_domainSize_internal payloadWidth fanIn

/-- Decoding a `q`-bit chunk produces a natural below `2 ^ q`. -/
theorem chunkCodeNat_lt {width : ℕ}
    (value : GroupedExtension.Chunk width) :
    chunkCodeNat value < 2 ^ width :=
  Internal.chunkCodeNat_lt_internal value

/-- Fixed-width binary decoding is injective on chunks. -/
theorem chunkCodeNat_injective {width : ℕ} :
    Function.Injective (@chunkCodeNat width) :=
  Internal.chunkCodeNat_injective_internal

/-- The concrete codebook is exactly binary decoding followed by the
natural cast into the searched field. -/
@[simp] theorem codebook_encode (payloadWidth fanIn : ℕ)
    (value :
      GroupedExtension.Chunk (chunkBits payloadWidth fanIn)) :
    (codebook payloadWidth fanIn).encode value =
      (chunkCodeNat value : Field payloadWidth fanIn) :=
  rfl

/-- The grouped node degree is one side of the total search endpoint. -/
theorem groupedDegree_le_endpoint (payloadWidth fanIn : ℕ) :
    groupedDegree payloadWidth fanIn ≤
      degreeEndpoint payloadWidth fanIn :=
  Internal.groupedDegree_le_endpoint_internal payloadWidth fanIn

/-- The exact codebook-capacity floor is the other side of the search
endpoint. -/
theorem codebookFloor_le_endpoint (payloadWidth fanIn : ℕ) :
    domainSize payloadWidth fanIn - 1 ≤
      degreeEndpoint payloadWidth fanIn :=
  Internal.codebookFloor_le_endpoint_internal payloadWidth fanIn

/-- For positive payload width and fan-in, the capacity floor is redundant:
the prime search runs at exactly `d * t * (2 ^ q - 1)`. -/
theorem degreeEndpoint_eq_groupedDegree
    (payloadWidth fanIn : ℕ)
    (hpayload : 0 < payloadWidth) (hfanIn : 0 < fanIn) :
    degreeEndpoint payloadWidth fanIn =
      groupedDegree payloadWidth fanIn :=
  Internal.degreeEndpoint_eq_groupedDegree_internal
    payloadWidth fanIn hpayload hfanIn

/-- The option-valued finite scan returns the modulus packaged by the
specialization. -/
theorem firstPrime?_eq_some_modulus (payloadWidth fanIn : ℕ) :
    PrimeField.Search.firstPrime?
        (degreeEndpoint payloadWidth fanIn) =
      some (fieldChoice payloadWidth fanIn).modulus := by
  simpa [fieldChoice] using
    PrimeField.firstPrime?_eq_some_searchChoice_modulus
      (degreeEndpoint payloadWidth fanIn)

/-- The exact grouped degree is strictly below the selected interpolation
cutoff. -/
theorem groupedDegree_lt_card_sub_one (payloadWidth fanIn : ℕ) :
    groupedDegree payloadWidth fanIn <
      Fintype.card (Field payloadWidth fanIn) - 1 :=
  Internal.groupedDegree_lt_card_sub_one_internal payloadWidth fanIn

/-- Every lifted node-coordinate polynomial has the sharp grouped degree
bound `d * t * (2 ^ q - 1)`. -/
theorem nodePolynomials_totalDegree_le
    (payloadWidth fanIn : ℕ)
    (combine :
      (Fin fanIn → Fin payloadWidth → Bool) →
        Fin payloadWidth → Bool)
    (outputChunk : Fin (chunkCount payloadWidth fanIn)) :
    (GroupedExtension.nodePolynomials
        (codebook payloadWidth fanIn)
        (layout payloadWidth fanIn)
        combine outputChunk).totalDegree ≤
      groupedDegree payloadWidth fanIn :=
  Internal.nodePolynomials_totalDegree_le_internal
    payloadWidth fanIn combine outputChunk

/-- Every lifted node-coordinate polynomial meets the strict selected-field
cutoff. -/
theorem nodePolynomials_totalDegree_lt_card_sub_one
    (payloadWidth fanIn : ℕ)
    (combine :
      (Fin fanIn → Fin payloadWidth → Bool) →
        Fin payloadWidth → Bool)
    (outputChunk : Fin (chunkCount payloadWidth fanIn)) :
    (GroupedExtension.nodePolynomials
        (codebook payloadWidth fanIn)
        (layout payloadWidth fanIn)
        combine outputChunk).totalDegree <
      Fintype.card (Field payloadWidth fanIn) - 1 :=
  Internal.nodePolynomials_totalDegree_lt_card_sub_one_internal
    payloadWidth fanIn combine outputChunk

/-- The complete grouped lift carries the required recursive low-degree
certificate. -/
theorem liftTree_isLowDegreePolynomial
    (payloadWidth fanIn : ℕ)
    (tree : Tree fanIn (Fin payloadWidth → Bool)) :
    IsLowDegreePolynomial
      (Fintype.card (Field payloadWidth fanIn) - 1)
      (liftTree payloadWidth fanIn tree) :=
  Internal.liftTree_isLowDegreePolynomial_internal
    payloadWidth fanIn tree

/-- Every Boolean tree becomes line-compatible after the concrete grouped
lift. -/
theorem liftTree_lineCompatible
    (payloadWidth fanIn : ℕ)
    (tree : Tree fanIn (Fin payloadWidth → Bool)) :
    LineCompatible (units payloadWidth fanIn)
      (liftTree payloadWidth fanIn tree) :=
  Internal.liftTree_lineCompatible_internal
    payloadWidth fanIn tree

/-- Grouped lifting preserves the root value after executable encoding. -/
@[simp] theorem value_liftTree
    (payloadWidth fanIn : ℕ)
    (tree : Tree fanIn (Fin payloadWidth → Bool)) :
    (liftTree payloadWidth fanIn tree).value =
      encodeValue payloadWidth fanIn tree.value :=
  Internal.value_liftTree_internal payloadWidth fanIn tree

/-- Grouped lifting preserves exact tree height. -/
@[simp] theorem height_liftTree
    (payloadWidth fanIn : ℕ)
    (tree : Tree fanIn (Fin payloadWidth → Bool)) :
    (liftTree payloadWidth fanIn tree).height = tree.height :=
  Internal.height_liftTree_internal payloadWidth fanIn tree

/-- Cook--Mertz evaluation agrees with ordinary Boolean tree evaluation,
followed by the concrete grouped field encoding. -/
theorem evaluateTree_eq_encode
    (payloadWidth fanIn : ℕ)
    (tree : Tree fanIn (Fin payloadWidth → Bool)) :
    evaluateTree payloadWidth fanIn tree =
      encodeValue payloadWidth fanIn tree.value :=
  Internal.evaluateTree_eq_encode_internal payloadWidth fanIn tree

/-- A selected prime-field residue needs at most `2q + 1` bits. -/
theorem fieldBitWidth_le (payloadWidth fanIn : ℕ) :
    fieldBitWidth payloadWidth fanIn ≤
      2 * chunkBits payloadWidth fanIn + 1 :=
  Internal.fieldBitWidth_le_internal payloadWidth fanIn

/-- Exact catalytic-bank charge before applying field-width bounds. -/
theorem catalyticRegisterBitBudget_eq (payloadWidth fanIn : ℕ) :
    catalyticRegisterBitBudget payloadWidth fanIn =
      (fanIn + 1) * chunkCount payloadWidth fanIn *
        fieldBitWidth payloadWidth fanIn :=
  Internal.catalyticRegisterBitBudget_eq_internal payloadWidth fanIn

/-- Direct bound using `t` registers of width at most `2q + 1`. -/
theorem catalyticRegisterBitBudget_le_raw (payloadWidth fanIn : ℕ) :
    catalyticRegisterBitBudget payloadWidth fanIn ≤
      (fanIn + 1) * chunkCount payloadWidth fanIn *
        (2 * chunkBits payloadWidth fanIn + 1) :=
  Internal.catalyticRegisterBitBudget_le_raw_internal
    payloadWidth fanIn

/-- Combined bound valid in both parameter regimes, including degenerate
inputs. -/
theorem catalyticRegisterBitBudget_le_padded
    (payloadWidth fanIn : ℕ) :
    catalyticRegisterBitBudget payloadWidth fanIn ≤
      3 * (fanIn + 1) *
        (payloadWidth + chunkBits payloadWidth fanIn) :=
  Internal.catalyticRegisterBitBudget_le_padded_internal
    payloadWidth fanIn

/-- In the `q ≤ B` branch, the actual searched-prime bank is at most
`6(d + 1)B`. -/
theorem catalyticRegisterBitBudget_le_logarithmic
    (payloadWidth fanIn : ℕ)
    (hregime :
      GroupedExtension.LogarithmicParameters.InLogarithmicRegime
        payloadWidth fanIn) :
    catalyticRegisterBitBudget payloadWidth fanIn ≤
      6 * (fanIn + 1) * payloadWidth :=
  Internal.catalyticRegisterBitBudget_le_logarithmic_internal
    payloadWidth fanIn hregime

/-- A positive payload in the explicit small-width branch `B < q` occupies
exactly one chunk. -/
theorem chunkCount_eq_one_of_small
    (payloadWidth fanIn : ℕ) (hpayload : 0 < payloadWidth)
    (hsmall :
      GroupedExtension.LogarithmicParameters.RequiresSmallCase
        payloadWidth fanIn) :
    chunkCount payloadWidth fanIn = 1 :=
  Internal.chunkCount_eq_one_of_small_internal
    payloadWidth fanIn hpayload hsmall

/-- A zero-width payload is the separate zero-chunk degenerate case. -/
theorem chunkCount_zero (fanIn : ℕ) :
    chunkCount 0 fanIn = 0 := by
  simp [chunkCount,
    GroupedExtension.LogarithmicParameters.chunkCount]

/-- In the positive small-width branch, the one-chunk catalytic bank costs
at most `3(d + 1)q` bits. -/
theorem catalyticRegisterBitBudget_le_small
    (payloadWidth fanIn : ℕ) (hpayload : 0 < payloadWidth)
    (hsmall :
      GroupedExtension.LogarithmicParameters.RequiresSmallCase
        payloadWidth fanIn) :
    catalyticRegisterBitBudget payloadWidth fanIn ≤
      3 * (fanIn + 1) * chunkBits payloadWidth fanIn :=
  Internal.catalyticRegisterBitBudget_le_small_internal
    payloadWidth fanIn hpayload hsmall

/-- Explicit dichotomy between the logarithmic and positive one-chunk
small-width storage bounds. -/
theorem catalyticRegisterBitBudget_branch
    (payloadWidth fanIn : ℕ) (hpayload : 0 < payloadWidth) :
    (GroupedExtension.LogarithmicParameters.InLogarithmicRegime
        payloadWidth fanIn ∧
      catalyticRegisterBitBudget payloadWidth fanIn ≤
        6 * (fanIn + 1) * payloadWidth) ∨
    (GroupedExtension.LogarithmicParameters.RequiresSmallCase
        payloadWidth fanIn ∧
      chunkCount payloadWidth fanIn = 1 ∧
      catalyticRegisterBitBudget payloadWidth fanIn ≤
        3 * (fanIn + 1) * chunkBits payloadWidth fanIn) :=
  Internal.catalyticRegisterBitBudget_branch_internal
    payloadWidth fanIn hpayload

/-- Fixed-count frames cost the ideal `(2s + c)q` plus at most one bit per
field scalar. -/
theorem frameBitBudget_le
    (payloadWidth fanIn scalarCount counterCount : ℕ) :
    frameBitBudget payloadWidth fanIn scalarCount counterCount ≤
      (2 * scalarCount + counterCount) *
          chunkBits payloadWidth fanIn +
        scalarCount :=
  Internal.frameBitBudget_le_internal
    payloadWidth fanIn scalarCount counterCount

/-- Simpler pure-logarithmic frame bound for fixed scalar and counter
counts. -/
theorem frameBitBudget_le_log
    (payloadWidth fanIn scalarCount counterCount : ℕ) :
    frameBitBudget payloadWidth fanIn scalarCount counterCount ≤
      (3 * scalarCount + counterCount) *
        chunkBits payloadWidth fanIn :=
  Internal.frameBitBudget_le_log_internal
    payloadWidth fanIn scalarCount counterCount

end Logarithmic

end PrimeGrouped

end CookMertz

end TreeEval

end Complexity
