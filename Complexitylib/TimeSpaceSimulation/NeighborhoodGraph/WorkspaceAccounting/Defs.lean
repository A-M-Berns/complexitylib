/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/
import Complexitylib.TimeSpaceSimulation.ComplexityBridge.Defs
import Complexitylib.TreeEvaluation.CookMertz.GroupedExtension.LogarithmicParameters.Defs
import Complexitylib.TreeEvaluation.Workspace.Defs

/-!
# Numerical workspace accounting for the direct neighborhood route

This file assigns concrete bit charges to the abstract direct-neighborhood
evaluation. For a time horizon `time`, number of work tapes `workTapeCount`,
and finite source-state type `Q`, it uses

* `b = max 1 ⌈√(time * (log₂ time + 1))⌉`;
* `h = ⌈time / b⌉`;
* Boolean payload width `B = |Q| + 5b`;
* fan-in `d = 4(workTapeCount + 2)`; and
* chunk width `q = log₂(dB) + 1`.

The persistent catalytic bank is the exact grouped Cook--Mertz register
budget. A live evaluator frame is charged for eight field scalars and eight
`q`-bit counters. The remaining graph, streamed-guess, and arithmetic scratch
charges are explicit accounting contracts; a concrete machine implementation
must separately prove that its encodings fit these assignments.

The definitions are total at `time = 0`. No logarithmic-regime hypothesis is
built into the budget.
-/

namespace Complexity

namespace TimeSpaceSimulation

namespace NeighborhoodGraph

namespace WorkspaceAccounting

/-- Positive square-root-logarithmic interval length. -/
def blockLength (time : ℕ) : ℕ :=
  ComplexityBridge.balancedBlockLength time

/-- Number of intervals needed to cover `time` steps. -/
def horizon (time : ℕ) : ℕ :=
  time ⌈/⌉ blockLength time

/-- Boolean width of one compact neighborhood value:
the source state and five `blockLength`-bit fields. -/
def booleanWidth (Q : Type*) [Fintype Q] (time : ℕ) : ℕ :=
  Fintype.card Q + 5 * blockLength time

/-- Four predecessor roles for every named tape. -/
def fanIn (workTapeCount : ℕ) : ℕ :=
  4 * (workTapeCount + 2)

/-- Protected logarithmic grouped-coordinate width. -/
def chunkBits (Q : Type*) [Fintype Q]
    (workTapeCount time : ℕ) : ℕ :=
  TreeEval.CookMertz.GroupedExtension.LogarithmicParameters.chunkBits
    (booleanWidth Q time) (fanIn workTapeCount)

/-- Number of grouped coordinates in one compact neighborhood value. -/
def chunkCount (Q : Type*) [Fintype Q]
    (workTapeCount time : ℕ) : ℕ :=
  TreeEval.CookMertz.GroupedExtension.LogarithmicParameters.chunkCount
    (booleanWidth Q time) (fanIn workTapeCount)

/-- Assigned bit width of one grouped field element. -/
def fieldBits (Q : Type*) [Fintype Q]
    (workTapeCount time : ℕ) : ℕ :=
  TreeEval.CookMertz.GroupedExtension.LogarithmicParameters.fieldBits
    (booleanWidth Q time) (fanIn workTapeCount)

/-- Exact persistent catalytic-register charge. -/
def catalyticBankBits (Q : Type*) [Fintype Q]
    (workTapeCount time : ℕ) : ℕ :=
  TreeEval.CookMertz.Workspace.registerBitBudget
    (fanIn workTapeCount)
    (chunkCount Q workTapeCount time)
    (fieldBits Q workTapeCount time)

/-- One live evaluator frame: eight field scalars and eight `q`-bit counters. -/
def frameBits (Q : Type*) [Fintype Q]
    (workTapeCount time : ℕ) : ℕ :=
  TreeEval.CookMertz.GroupedExtension.LogarithmicParameters.frameBitBudget
    (booleanWidth Q time) (fanIn workTapeCount) 8 8

/-- Stack charge for the interval-height evaluator. -/
def stackBits (Q : Type*) [Fintype Q]
    (workTapeCount time : ℕ) : ℕ :=
  horizon time * frameBits Q workTapeCount time

/-- Local graph indices and predecessor-query state. -/
def graphBits (Q : Type*) [Fintype Q]
    (workTapeCount time : ℕ) : ℕ :=
  4 * fanIn workTapeCount * chunkBits Q workTapeCount time

/-- Packed ternary movement counter for every interval and named tape.

Each trit is charged two binary bits, and the final extra bit covers the
bit-length convention at the all-zero horizon. -/
def guessBits (workTapeCount time : ℕ) : ℕ :=
  2 * horizon time * (workTapeCount + 2) + 1

/-- Boolean payload, field-operation, counter, and fixed-control scratch. -/
def scratchBits (Q : Type*) [Fintype Q]
    (workTapeCount time : ℕ) : ℕ :=
  8 * (booleanWidth Q time + chunkBits Q workTapeCount time +
    ComplexityBridge.protectedBinaryLog time) + 32

/-- Total assigned workspace for the direct neighborhood route. -/
def totalBits (Q : Type*) [Fintype Q]
    (workTapeCount time : ℕ) : ℕ :=
  catalyticBankBits Q workTapeCount time +
    stackBits Q workTapeCount time +
    graphBits Q workTapeCount time +
    guessBits workTapeCount time +
    scratchBits Q workTapeCount time

/-- Positive machine-dependent factor dominating `dB / b`. -/
def machineFactor (Q : Type*) [Fintype Q]
    (workTapeCount : ℕ) : ℕ :=
  fanIn workTapeCount * (Fintype.card Q + 5)

/-- Machine-dependent multiplier converting `q` to the protected time log. -/
def chunkCoefficient (Q : Type*) [Fintype Q]
    (workTapeCount : ℕ) : ℕ :=
  ComplexityBridge.protectedBinaryLog
    (machineFactor Q workTapeCount) + 1

/-- Explicit coefficient in the pointwise square-root-logarithmic bound. -/
def workspaceCoefficient (Q : Type*) [Fintype Q]
    (workTapeCount : ℕ) : ℕ :=
  let states := Fintype.card Q
  let degree := fanIn workTapeCount
  let coefficient := chunkCoefficient Q workTapeCount
  2 * (degree + 1) * (states + 5 + coefficient) +
    48 * coefficient +
    4 * degree * coefficient +
    4 * (workTapeCount + 2) + 1 +
    8 * (states + 5 + coefficient + 1) + 32

/-- Uniform budget for all explicit streamed trials up to `trialHorizon`.

The simulator need not know an external running-time function: it can try
candidate times explicitly, while a correctness proof supplies a horizon
bounding the successful trial. -/
def trialEnvelopeBits (Q : Type*) [Fintype Q]
    (workTapeCount trialHorizon : ℕ) : ℕ :=
  workspaceCoefficient Q workTapeCount * blockLength trialHorizon

end WorkspaceAccounting

end NeighborhoodGraph

end TimeSpaceSimulation

end Complexity
