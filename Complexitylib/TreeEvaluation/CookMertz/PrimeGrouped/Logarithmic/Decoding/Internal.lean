/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/
import Complexitylib.TreeEvaluation.CookMertz.BooleanExtension.Evaluation
import Complexitylib.TreeEvaluation.CookMertz.GroupedExtension
import
  Complexitylib.TreeEvaluation.CookMertz.PrimeGrouped.Logarithmic
import
  Complexitylib.TreeEvaluation.CookMertz.PrimeGrouped.Logarithmic.Decoding.Defs

/-!
# Correctness internals for executable grouped-value decoding
-/

namespace Complexity

namespace TreeEval

namespace CookMertz

namespace PrimeGrouped

namespace Logarithmic

namespace Decoding

namespace Internal

theorem chunkCodeNat_lt_searchModulus_internal
    (payloadWidth fanIn : ℕ)
    (value :
      GroupedExtension.Chunk (chunkBits payloadWidth fanIn)) :
    chunkCodeNat value <
      PrimeField.Search.searchModulus
        (degreeEndpoint payloadWidth fanIn) := by
  have hcode :=
    chunkCodeNat_lt value
  have hfloor :=
    codebookFloor_le_endpoint payloadWidth fanIn
  have hprime :=
    PrimeField.Search.degree_lt_searchModulus_sub_one
      (degreeEndpoint payloadWidth fanIn)
  unfold domainSize at hfloor
  omega

theorem decodeChunk_encode_internal
    (payloadWidth fanIn : ℕ)
    (value :
      GroupedExtension.Chunk (chunkBits payloadWidth fanIn)) :
    decodeChunk payloadWidth fanIn
        ((codebook payloadWidth fanIn).encode value) =
      value := by
  unfold decodeChunk
  rw [codebook_encode]
  rw [ZMod.val_natCast_of_lt
    (chunkCodeNat_lt_searchModulus_internal
      payloadWidth fanIn value)]
  convert
    BooleanExtension.Evaluation.assignmentOfCode_codeOfAssignment
      (Equiv.refl (Fin (chunkBits payloadWidth fanIn))) value
    using 1

theorem decodeValue_encodeValue_internal
    (payloadWidth fanIn : ℕ)
    (value : Fin payloadWidth → Bool) :
    decodeValue payloadWidth fanIn
        (encodeValue payloadWidth fanIn value) =
      value := by
  unfold decodeValue encodeValue GroupedExtension.encodeVector
  rw [show
      (fun chunk =>
        decodeChunk payloadWidth fanIn
          ((codebook payloadWidth fanIn).encode
            (GroupedExtension.Layout.pack value chunk))) =
        GroupedExtension.Layout.pack value by
      funext chunk
      exact decodeChunk_encode_internal
        payloadWidth fanIn
          (GroupedExtension.Layout.pack value chunk)]
  exact GroupedExtension.Layout.unpack_pack
    (layout payloadWidth fanIn) value

theorem decodeValue_evaluateTree_internal
    (payloadWidth fanIn : ℕ)
    (tree :
      Tree fanIn (Fin payloadWidth → Bool)) :
    decodeValue payloadWidth fanIn
        (evaluateTree payloadWidth fanIn tree) =
      tree.value := by
  rw [evaluateTree_eq_encode]
  exact decodeValue_encodeValue_internal
    payloadWidth fanIn tree.value

end Internal

end Decoding

end Logarithmic

end PrimeGrouped

end CookMertz

end TreeEval

end Complexity
