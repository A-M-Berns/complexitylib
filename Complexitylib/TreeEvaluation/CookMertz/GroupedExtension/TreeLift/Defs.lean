/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/
import Complexitylib.TreeEvaluation.CookMertz.GroupedExtension.Defs

/-!
# Grouped polynomial lifts of Boolean trees

This file defines the structural lift from a Boolean tree to a tree over
grouped finite-field vectors. Leaves are packed and encoded coordinatewise.
Each internal Boolean node is replaced by its grouped Lagrange-extension
polynomials.

The lift is certificate-side and noncomputable because `polynomialNode` and
`nodePolynomials` are certificate-side polynomial definitions.

## Main definition

* `GroupedExtension.liftTree` -- recursively lift a Boolean tree
-/

namespace Complexity

namespace TreeEval

namespace CookMertz

namespace GroupedExtension

variable {K : Type*} [Field K] [Fintype K]
  {d b chunkBits chunkCount : ℕ}

/-- Replace Boolean leaves by their packed field encodings and Boolean node
functions by their grouped polynomial extensions. -/
noncomputable def liftTree
    (codebook : Codebook K chunkBits)
    (layout : Layout b chunkBits chunkCount) :
    Tree d (Fin b → Bool) → Tree d (Fin chunkCount → K)
  | .leaf value =>
      .leaf (encodeVector codebook value)
  | .node children combine =>
      .node
        (fun child => liftTree codebook layout (children child))
        (polynomialNode (nodePolynomials codebook layout combine))

end GroupedExtension

end CookMertz

end TreeEval

end Complexity
