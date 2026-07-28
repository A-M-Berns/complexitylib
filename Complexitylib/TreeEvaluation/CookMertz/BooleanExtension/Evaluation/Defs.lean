/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/
import Complexitylib.Mathlib.NatBits
import Complexitylib.TreeEvaluation.CookMertz.BooleanExtension.Defs
import Mathlib.Algebra.BigOperators.Group.List.Basic
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.List.OfFn
import Mathlib.Logic.Equiv.Fin.Basic

/-!
# Executable Boolean multilinear-extension evaluation

The semantic multilinear extension is represented by a full multivariate
polynomial and is noncomputable. This file defines a separate executable
evaluator which enumerates Boolean assignments by fixed-width binary codes.

`evaluate` is a tail-recursive loop over the codes below `2 ^ width`. It
generates each assignment on demand, evaluates its Lagrange-basis weight, and
adds one term to a single accumulator. In particular, the executable
definition never constructs `assignments` or the semantic polynomial;
`assignments` is retained only as a finite correctness certificate.

This Lean implementation is not yet a Turing-machine space theorem. The
eventual machine proof must implement the counter, field arithmetic, Boolean
node oracle, and coordinate traversal and charge their all-prefix workspace.

## Main definitions

- `assignmentOfCode` -- decode one fixed-width Boolean assignment
- `assignments` -- explicit certification list of all Boolean assignments
- `coordinates` -- explicit coordinate list induced by an encoding
- `basisValue` -- executable evaluation of one Boolean basis polynomial
- `sumRange` -- tail-recursive summation over a natural-number range
- `evaluate` -- executable multilinear-extension evaluator
- `evaluateNode` -- specialization to a `d`-input, `b`-bit Boolean node
-/

namespace Complexity

namespace TreeEval

namespace CookMertz

namespace BooleanExtension

namespace Evaluation

variable {σ K : Type*} {width d b : ℕ}

/-- Decode `code` as a fixed-width Boolean assignment, transported along an
explicit coordinate encoding. Codes at least `2 ^ width` are truncated by
`Nat.toBits`. -/
def assignmentOfCode (encoding : σ ≃ Fin width) (code : ℕ) : σ → Bool :=
  fun i =>
    (Nat.toBits width code).get
      (Fin.cast (Nat.length_toBits width code).symm (encoding i))

/-- Encode a Boolean assignment using the inverse coordinate order. -/
def codeOfAssignment (encoding : σ ≃ Fin width)
    (assignment : σ → Bool) : ℕ :=
  Nat.fromBits
    (List.ofFn fun i : Fin width => assignment (encoding.symm i))

/-- Explicit list of every Boolean assignment, in increasing code order.

The executable evaluator below loops over the codes directly and does not
construct this list. -/
def assignments (encoding : σ ≃ Fin width) : List (σ → Bool) :=
  (List.range (2 ^ width)).map (assignmentOfCode encoding)

/-- Explicit coordinate order induced by `encoding`. -/
def coordinates (encoding : σ ≃ Fin width) : List σ :=
  (List.finRange width).map encoding.symm

/-- Tail-recursive left-associated accumulation of `term 0` through
`term (count - 1)`. -/
def foldRange {R : Type*} [AddMonoid R] (term : ℕ → R) :
    ℕ → R → R
  | 0, accumulator => accumulator
  | count + 1, accumulator =>
      foldRange term count (term count + accumulator)

/-- Sum `term` over the natural numbers below `count` using one accumulator. -/
def sumRange {R : Type*} [AddMonoid R]
    (term : ℕ → R) (count : ℕ) : R :=
  foldRange term count 0

/-- Evaluate one Boolean-cube Lagrange basis weight from an explicit
coordinate list. -/
def basisValue [CommRing K] (encoding : σ ≃ Fin width)
    (assignment : σ → Bool) (point : σ → K) : K :=
  ((coordinates encoding).map fun i =>
    if assignment i then point i else 1 - point i).prod

/-- Evaluate a Boolean function's multilinear extension without constructing
the polynomial or the list of all assignments. -/
def evaluate [CommRing K] (encoding : σ ≃ Fin width)
    (f : (σ → Bool) → K) (point : σ → K) : K :=
  sumRange (fun code =>
    let assignment := assignmentOfCode encoding code
    f assignment * basisValue encoding assignment point) (2 ^ width)

/-- Evaluate every output coordinate of a `d`-input, `b`-bit Boolean node by
its executable multilinear extension. -/
def evaluateNode [CommRing K]
    (combine : (Fin d → Fin b → Bool) → Fin b → Bool)
    (args : Fin d → Fin b → K) : Fin b → K :=
  fun j =>
    evaluate finProdFinEquiv
      (fun assignment => bit (combine (unflatten assignment) j))
      (fun i => args i.1 i.2)

end Evaluation

end BooleanExtension

end CookMertz

end TreeEval

end Complexity
