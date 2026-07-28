/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/
import
  Complexitylib.TreeEvaluation.CookMertz.PrimeGrouped.Logarithmic.RuntimeBounds.Internal

/-!
# Runtime bounds for logarithmic grouped Cook--Mertz evaluation

The neighborhood simulation has Boolean payload width at least five and
fan-in at least eight. In this positive regime, its searched field modulus
fits below the square of the chunk-domain size. Consequently one natural
field residue occupies exactly the two chunk-radix digits reserved by the
runtime frame and bank codecs.
-/

namespace Complexity
namespace TreeEval
namespace CookMertz
namespace PrimeGrouped
namespace Logarithmic
namespace RuntimeBounds

/-- With a nontrivial payload and fan-in, the searched field modulus fits in
two digits of radix `2 ^ chunkBits`. -/
theorem searchModulus_lt_domainSize_sq
    (payloadWidth fanIn : ℕ)
    (hpayload : 5 ≤ payloadWidth) (hfanIn : 8 ≤ fanIn) :
    PrimeField.Search.searchModulus
        (degreeEndpoint payloadWidth fanIn) <
      domainSize payloadWidth fanIn ^ 2 :=
  Internal.searchModulus_lt_domainSize_sq_internal
    payloadWidth fanIn hpayload hfanIn

end RuntimeBounds
end Logarithmic
end PrimeGrouped
end CookMertz
end TreeEval
end Complexity
