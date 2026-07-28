/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/
import
  Complexitylib.TreeEvaluation.CookMertz.BooleanExtension.Evaluation.Defs
import
  Complexitylib.TreeEvaluation.CookMertz.PrimeGrouped.Logarithmic.Defs

/-!
# Executable decoding for logarithmic grouped values

The logarithmic codebook maps a chunk to the natural decoded by
`Nat.fromBits`, then casts it into a searched prime field. Since every chunk
code is below the modulus, decoding reads the canonical residue and applies
the inverse fixed-width bit representation.

## Main definitions

- `decodeChunk` -- recover one fixed-width chunk from a field residue
- `decodeValue` -- unpack a grouped field vector into its Boolean payload
-/

namespace Complexity

namespace TreeEval

namespace CookMertz

namespace PrimeGrouped

namespace Logarithmic

namespace Decoding

/-- Decode the canonical residue of one field coordinate as a fixed-width
Boolean chunk. Values outside the codebook image are truncated to `q` bits. -/
def decodeChunk (payloadWidth fanIn : ℕ)
    (value : Field payloadWidth fanIn) :
    GroupedExtension.Chunk (chunkBits payloadWidth fanIn) :=
  BooleanExtension.Evaluation.assignmentOfCode
    (Equiv.refl (Fin (chunkBits payloadWidth fanIn))) value.val

/-- Decode all grouped field coordinates and discard the layout's trailing
padding bits. -/
def decodeValue (payloadWidth fanIn : ℕ)
    (value :
      Fin (chunkCount payloadWidth fanIn) →
        Field payloadWidth fanIn) :
    Fin payloadWidth → Bool :=
  (layout payloadWidth fanIn).unpack fun chunk =>
    decodeChunk payloadWidth fanIn (value chunk)

end Decoding

end Logarithmic

end PrimeGrouped

end CookMertz

end TreeEval

end Complexity
