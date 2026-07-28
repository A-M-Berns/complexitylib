/-
Copyright (c) 2025 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/
import Complexitylib.Models
import Complexitylib.Asymptotics
import Complexitylib.TimeConstructible
import Complexitylib.Classes
import Complexitylib.Languages
import Complexitylib.SAT
import Complexitylib.Circuits
import Complexitylib.BooleanAnalysis
import Complexitylib.DescriptiveComplexity
import Complexitylib.TreeEvaluation
import Complexitylib.TimeSpaceSimulation

/-!
# Complexitylib

The root module: importing it brings in the library's complete public
surface. Import an area module (`Complexitylib.Models`,
`Complexitylib.Classes`, …) instead to keep dependencies smaller.

## Headline theorems

Machine-checked with no `sorry` and no custom axioms — CI audits every
Complexitylib declaration for dependencies beyond `propext`,
`Classical.choice`, and `Quot.sound` (`scripts/AxiomGuard.lean`).

**Cook–Levin: SAT is NP-complete.**
- `Complexity.SAT.NPComplete_language` — `NPComplete SAT.language`
- `Complexity.SAT.language_mem_NP` — `SAT.language ∈ NP`
- `Complexity.SAT.pairLang_witness_mem_P` — the SAT verifier runs in
  polynomial time

**Universal simulation.**
- `Complexity.TM.UTMBody.utmTM_universal` — a fixed machine simulates any
  encoded machine with explicit time overhead (Arora–Barak Theorem 1.9)
- `Complexity.TM.UTMBody.utmTM_universal_padded` — the padded-encoding
  variant

**Deterministic time hierarchy.**
- `Complexity.time_hierarchy_weak` — more time decides strictly more
  languages, in a concrete clock-constructible formulation
- `Complexity.time_hierarchy_weak_ssubset`, `Complexity.DTIME_pow_ssubset`
  — strict polynomial separations such as
  `DTIME((n+1)^a) ⊂ DTIME((n+1)^(2a+5))`

**Structural containments.** `Complexity.P_subset_NP`,
`Complexity.P_subset_PSPACE`, `Complexity.P_subset_PPoly`,
`Complexity.UniformPPoly_subset_P`,
`Complexity.PAdvice_subset_PPoly`, `Complexity.PPoly_subset_PAdvice`,
`Complexity.RP_subset_NP`, `Complexity.BPP_subset_PPoly`,
`Complexity.BPP_subset_PAdvice`, and `Complexity.BPP_subset_PP`. The nonuniform
equivalence lives in `Complexitylib.Classes.PPoly.Advice`, while randomized
hardwiring and its advice corollary live in
`Complexitylib.Classes.Randomized.PPoly`; the broader time/space index is
`Complexitylib.Classes.Containments`.

**Circuit lower bounds.** Shannon's counting bound, gate-elimination
(`Circuit.card_essentialInputs_le_mul_size`), Schnorr's XOR bound
(`Complexity.sizeComplexity_xorBool_ge`), and Valiant's depth reduction
(`Complexity.Valiant.depth_reduction`).

**Barrington's theorem.** `Complexity.barrington_equivalence` identifies
logarithmic-depth Boolean formula families with polynomial-length width-`5`
permutation branching-program families.

**Cook--Mertz tree-evaluation kernel.**
- `Complexity.TreeEval.CookMertz.accumulate_eq_addAt` proves exact catalytic
  accumulator correctness and restoration of all scratch registers.
- `Complexity.TreeEval.CookMertz.evaluate_lowDegreePolynomial` derives
  correctness for coordinatewise low-degree polynomial node functions from
  the finite-field interpolation identity.
- `Complexity.TreeEval.OrderedDAG.cookMertzEvaluate_eq_value` evaluates a
  compact, structurally acyclic computation DAG directly, without constructing
  its potentially exponential semantic unrolling.
- `Complexity.TreeEval.OrderedDAG.cookMertzEvaluate_liftBoolean_eq_embed`
  evaluates an arbitrary Boolean ordered DAG through coordinatewise
  multilinear extensions when the field is larger than the node degree; the
  lifted node callback enumerates Boolean assignments on demand and stores no
  multivariate polynomial.
- `Complexity.TreeEval.OrderedDAG.cookMertzEvaluate_liftBoolean_primeField_eq_embed`
  chooses an explicit
  prime-field certificate and enumerates its nonzero residues exactly once.
- `Complexity.TreeEval.BoundedFanIn.DAG.cookMertzEvaluate_liftBoolean_pad_primeField_eq_embed`
  extends that result to Williams's variable-fan-in interface
  (`2 ≤ k ≤ d`) through padding that preserves values and dependency depth
  exactly.

**Williams time-to-space simulation (in progress).**
- `Complexity.TM.BlockRespectingOnInput` states the half-open time-block
  residence property for every named input/work/output head.
- `Complexity.TM.BlockRespectingOnInput.head_in_timeBlock` proves that every
  such head lies in its uniquely active tape block at an arbitrary time.
- `Complexity.TimeSpaceSimulation.ComputationGraph.predecessorAt_rank_lt`
  gives the implicit graph exactly `2 * (workTapeCount + 2)` Fin-indexed
  predecessor slots and proves every edge decreases time-block rank.
- `Complexity.TimeSpaceSimulation.ComputationGraph.height_unroll_computation_le`
  bounds the induced semantic tree height by the number of processed time
  blocks.
-/
