/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/
import
  Complexitylib.TreeEvaluation.CookMertz.PrimeGrouped.Logarithmic.Decoding.Defs
import
  Complexitylib.TreeEvaluation.CookMertz.PrimeGrouped.Logarithmic.Decoding.Internal

/-!
# Executable decoding for logarithmic grouped values

Canonical residue decoding is a left inverse of the executable logarithmic
codebook. Consequently the output of grouped Cook--Mertz evaluation decodes
to the ordinary Boolean tree value exactly.
-/

namespace Complexity

namespace TreeEval

namespace CookMertz

namespace PrimeGrouped

namespace Logarithmic

namespace Decoding

/-- Every chunk code is strictly below the searched prime modulus. -/
theorem chunkCodeNat_lt_searchModulus
    (payloadWidth fanIn : ℕ)
    (value :
      GroupedExtension.Chunk (chunkBits payloadWidth fanIn)) :
    chunkCodeNat value <
      PrimeField.Search.searchModulus
        (degreeEndpoint payloadWidth fanIn) :=
  Internal.chunkCodeNat_lt_searchModulus_internal
    payloadWidth fanIn value

/-- Canonical field-residue decoding inverts the executable chunk codebook. -/
theorem decodeChunk_encode
    (payloadWidth fanIn : ℕ)
    (value :
      GroupedExtension.Chunk (chunkBits payloadWidth fanIn)) :
    decodeChunk payloadWidth fanIn
        ((codebook payloadWidth fanIn).encode value) =
      value :=
  Internal.decodeChunk_encode_internal
    payloadWidth fanIn value

/-- Coordinate decoding and row-major unpacking invert grouped encoding. -/
@[simp] theorem decodeValue_encodeValue
    (payloadWidth fanIn : ℕ)
    (value : Fin payloadWidth → Bool) :
    decodeValue payloadWidth fanIn
        (encodeValue payloadWidth fanIn value) =
      value :=
  Internal.decodeValue_encodeValue_internal
    payloadWidth fanIn value

/-- The executably decoded Cook--Mertz output is the ordinary Boolean root
value. -/
theorem decodeValue_evaluateTree
    (payloadWidth fanIn : ℕ)
    (tree :
      Tree fanIn (Fin payloadWidth → Bool)) :
    decodeValue payloadWidth fanIn
        (evaluateTree payloadWidth fanIn tree) =
      tree.value :=
  Internal.decodeValue_evaluateTree_internal
    payloadWidth fanIn tree

end Decoding

end Logarithmic

end PrimeGrouped

end CookMertz

end TreeEval

end Complexity
