/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/
import Complexitylib.TreeEvaluation.BoundedFanIn
import Complexitylib.TreeEvaluation.BoundedFanIn.CookMertz
import Complexitylib.TreeEvaluation.BooleanPadding
import Complexitylib.TreeEvaluation.CookMertz
import Complexitylib.TreeEvaluation.CookMertz.BooleanExtension
import Complexitylib.TreeEvaluation.CookMertz.BooleanExtension.Evaluation
import Complexitylib.TreeEvaluation.CookMertz.GroupedExtension
import Complexitylib.TreeEvaluation.CookMertz.GroupedExtension.Evaluation
import Complexitylib.TreeEvaluation.CookMertz.GroupedExtension.LogarithmicParameters
import Complexitylib.TreeEvaluation.CookMertz.GroupedExtension.Parameters
import Complexitylib.TreeEvaluation.CookMertz.GroupedExtension.TreeLift
import Complexitylib.TreeEvaluation.CookMertz.Interpolation
import Complexitylib.TreeEvaluation.CookMertz.PrimeField
import Complexitylib.TreeEvaluation.CookMertz.PrimeField.Runtime
import Complexitylib.TreeEvaluation.CookMertz.PrimeField.Runtime.CookMertz
import Complexitylib.TreeEvaluation.CookMertz.PrimeField.Search
import Complexitylib.TreeEvaluation.CookMertz.PrimeGrouped
import Complexitylib.TreeEvaluation.CookMertz.PrimeGrouped.Logarithmic
import Complexitylib.TreeEvaluation.CookMertz.PrimeGrouped.Logarithmic.Decoding
import Complexitylib.TreeEvaluation.OrderedDAG
import Complexitylib.TreeEvaluation.OrderedDAG.BooleanExtension
import Complexitylib.TreeEvaluation.OrderedDAG.CookMertz
import Complexitylib.TreeEvaluation.Workspace

/-!
# Tree evaluation

Public aggregation module for the Cook--Mertz tree evaluator and its
finite-field interpolation certificate, together with variable bounded-fan-in
trees, compact ordered computation DAGs, semantic and executable Boolean
multilinear extensions, and direct implicit-DAG evaluation over explicitly
enumerated prime fields.
-/
