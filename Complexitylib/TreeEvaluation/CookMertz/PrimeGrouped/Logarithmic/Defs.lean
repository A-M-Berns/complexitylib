/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/
import Complexitylib.Mathlib.NatBits
import Complexitylib.TreeEvaluation.CookMertz.GroupedExtension.LogarithmicParameters
import Complexitylib.TreeEvaluation.CookMertz.GroupedExtension.TreeLift.Defs
import Complexitylib.TreeEvaluation.CookMertz.PrimeField.Search

/-!
# Executable logarithmic prime-field parameters

For Boolean payload width `B` and fan-in `d`, this module uses the sharp
grouped parameters

`q = log₂(d * B) + 1` and `t = ⌈B / q⌉`.

The grouped interpolation degree is

`D = d * t * (2 ^ q - 1)`.

The executable prime search is run at
`max D (2 ^ q - 1)`. The second term is the exact capacity floor needed to
inject all `q`-bit chunks into the field, including the degenerate cases
`B = 0` or `d = 0`. It is redundant for positive `B` and `d`.

Chunks are encoded without a cardinality choice: `List.ofFn` materializes
their bits, `Nat.fromBits` decodes them, and the resulting natural is cast
into the searched `ZMod` field. The codebook, prime search, and unit list are
therefore executable. The polynomial tree lift remains certificate-side and
noncomputable, as in the generic grouped-extension layer.
-/

namespace Complexity

namespace TreeEval

namespace CookMertz

namespace PrimeGrouped

namespace Logarithmic

/-- Protected logarithmic chunk width `q = log₂(dB) + 1`. -/
abbrev chunkBits :=
  GroupedExtension.LogarithmicParameters.chunkBits

/-- Tight chunk count `t = ⌈B / q⌉`. -/
abbrev chunkCount :=
  GroupedExtension.LogarithmicParameters.chunkCount

/-- Cardinality of the complete `q`-bit chunk alphabet. -/
def domainSize (payloadWidth fanIn : ℕ) : ℕ :=
  2 ^ chunkBits payloadWidth fanIn

/-- Exact total-degree bound for every grouped output-coordinate
polynomial. -/
def groupedDegree (payloadWidth fanIn : ℕ) : ℕ :=
  fanIn * chunkCount payloadWidth fanIn *
    (domainSize payloadWidth fanIn - 1)

/-- Search endpoint: the grouped degree together with the codebook-capacity
floor required by degenerate parameter pairs. -/
def degreeEndpoint (payloadWidth fanIn : ℕ) : ℕ :=
  max (groupedDegree payloadWidth fanIn)
    (domainSize payloadWidth fanIn - 1)

/-- Prime-field choice produced by the finite Bertrand scan. -/
def fieldChoice (payloadWidth fanIn : ℕ) :
    PrimeField.Choice (degreeEndpoint payloadWidth fanIn) :=
  PrimeField.searchChoice (degreeEndpoint payloadWidth fanIn)

/-- Executably selected prime field. -/
abbrev Field (payloadWidth fanIn : ℕ) :=
  PrimeField.SearchField (degreeEndpoint payloadWidth fanIn)

/-- Decode a fixed-width Boolean chunk as a natural number. -/
def chunkCodeNat {width : ℕ}
    (value : GroupedExtension.Chunk width) : ℕ :=
  Nat.fromBits (List.ofFn value)

/-- Executable injection into a searched prime field, given the explicit
chunk-domain capacity inequality. -/
def zmodCodebook (degree width : ℕ)
    (hcapacity : 2 ^ width ≤ PrimeField.Search.searchModulus degree) :
    GroupedExtension.Codebook (PrimeField.SearchField degree) width where
  encode :=
    ⟨fun value => (chunkCodeNat value : PrimeField.SearchField degree), by
      intro first second heq
      apply List.ofFn_injective
      apply Nat.fromBits_inj_of_length_eq (by simp)
      apply CharP.natCast_injOn_Iio (PrimeField.SearchField degree)
        (PrimeField.Search.searchModulus degree)
      · have hlt :
            Nat.fromBits (List.ofFn first) < 2 ^ width := by
          simpa using Nat.fromBits_lt_pow_length (List.ofFn first)
        exact hlt.trans_le hcapacity
      · have hlt :
            Nat.fromBits (List.ofFn second) < 2 ^ width := by
          simpa using Nat.fromBits_lt_pow_length (List.ofFn second)
        exact hlt.trans_le hcapacity
      · exact heq⟩

/-- Executable injection of the exact logarithmic chunk alphabet into the
searched prime field. -/
def codebook (payloadWidth fanIn : ℕ) :
    GroupedExtension.Codebook (Field payloadWidth fanIn)
      (chunkBits payloadWidth fanIn) :=
  zmodCodebook
    (degreeEndpoint payloadWidth fanIn)
    (chunkBits payloadWidth fanIn) (by
      have hfloor :
          domainSize payloadWidth fanIn - 1 ≤
            degreeEndpoint payloadWidth fanIn :=
        Nat.le_max_right _ _
      have hdegree :=
        PrimeField.Search.degree_lt_searchModulus_sub_one
          (degreeEndpoint payloadWidth fanIn)
      have hpositive : 0 < domainSize payloadWidth fanIn := by
        simp [domainSize]
      unfold domainSize at hfloor hpositive
      omega)

/-- Canonical sharp layout `B` bits into `t` chunks of `q` bits. -/
theorem layout (payloadWidth fanIn : ℕ) :
    GroupedExtension.Layout payloadWidth
      (chunkBits payloadWidth fanIn)
      (chunkCount payloadWidth fanIn) :=
  GroupedExtension.LogarithmicParameters.layout payloadWidth fanIn

/-- Coordinatewise executable field encoding of a Boolean payload. -/
def encodeValue (payloadWidth fanIn : ℕ)
    (value : Fin payloadWidth → Bool) :
    Fin (chunkCount payloadWidth fanIn) → Field payloadWidth fanIn :=
  GroupedExtension.encodeVector (codebook payloadWidth fanIn) value

/-- Certificate-side grouped polynomial lift using the executable
parameters and codebook. -/
noncomputable def liftTree (payloadWidth fanIn : ℕ)
    (tree : Tree fanIn (Fin payloadWidth → Bool)) :
    Tree fanIn
      (Fin (chunkCount payloadWidth fanIn) →
        Field payloadWidth fanIn) :=
  GroupedExtension.liftTree
    (codebook payloadWidth fanIn) (layout payloadWidth fanIn) tree

/-- Executable enumeration of the nonzero elements of the selected field. -/
def units (payloadWidth fanIn : ℕ) :
    List (Field payloadWidth fanIn)ˣ :=
  PrimeField.searchUnits (degreeEndpoint payloadWidth fanIn)

/-- Cook--Mertz evaluation of the certificate-side grouped lift. -/
noncomputable def evaluateTree (payloadWidth fanIn : ℕ)
    (tree : Tree fanIn (Fin payloadWidth → Bool)) :
    Fin (chunkCount payloadWidth fanIn) → Field payloadWidth fanIn :=
  evaluate (units payloadWidth fanIn)
    (liftTree payloadWidth fanIn tree)

/-- Actual binary width of a residue in the executably selected field. -/
def fieldBitWidth (payloadWidth fanIn : ℕ) : ℕ :=
  (PrimeField.Search.searchModulus
    (degreeEndpoint payloadWidth fanIn)).size

/-- Exact charge for the `d + 1` banks of `t` field registers. -/
def catalyticRegisterBitBudget (payloadWidth fanIn : ℕ) : ℕ :=
  GroupedExtension.groupedRegisterBitBudget fanIn
    (chunkCount payloadWidth fanIn)
    (fieldBitWidth payloadWidth fanIn)

/-- Exact frame charge for a fixed number of field scalars and `q`-bit
counters. -/
def frameBitBudget (payloadWidth fanIn scalarCount counterCount : ℕ) : ℕ :=
  scalarCount * fieldBitWidth payloadWidth fanIn +
    counterCount * chunkBits payloadWidth fanIn

end Logarithmic

end PrimeGrouped

end CookMertz

end TreeEval

end Complexity
