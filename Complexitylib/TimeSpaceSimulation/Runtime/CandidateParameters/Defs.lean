/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/
import Complexitylib.Models.RandomAccessMachine.Structured.Footprint.Defs
import Complexitylib.Models.RandomAccessMachine.Structured.Invariant.Defs
import Complexitylib.Models.RandomAccessMachine.Structured.PrimeSearch.Defs
import
  Complexitylib.TimeSpaceSimulation.Runtime.NeighborhoodProgram.Defs

/-!
# Runtime construction of one candidate's numerical parameters

This definitions layer gives one first-order structured-RAM program that
derives every numerical parameter of a neighborhood-evaluation trial from a
preserved external candidate register. The source-state count and work-tape
count are fixed when the source machine is fixed, so they occur only as
immediates in the uniform command.

The mutable allocation contains seventeen advertised outputs, seven shared
arithmetic scratch registers, and a separate eight-register prime-search
allocation. Every write has a fixed direct destination.
-/

namespace Complexity

namespace TimeSpaceSimulation

namespace Runtime

namespace CandidateParameters

open RAM Structured
open NeighborhoodGraph
open TreeEval CookMertz

/-- Protected candidate logarithm, including the total small-input guard. -/
abbrev protectedLog (candidate : ℕ) : ℕ :=
  ComplexityBridge.protectedBinaryLog candidate

/-- Radicand used to balance the interval length. -/
def radicand (candidate : ℕ) : ℕ :=
  candidate * protectedLog candidate

/-- Positive ceiling square root of the balanced radicand. -/
abbrev blockLength (candidate : ℕ) : ℕ :=
  WorkspaceAccounting.blockLength candidate

/-- Tight number of balanced intervals covering the candidate time. -/
abbrev horizon (candidate : ℕ) : ℕ :=
  WorkspaceAccounting.horizon candidate

/-- Boolean payload width of one compact neighborhood value. -/
abbrev booleanWidth (Q : Type*) [Fintype Q] (candidate : ℕ) : ℕ :=
  WorkspaceAccounting.booleanWidth Q candidate

/-- Four predecessor roles for the input, output, and every work tape. -/
abbrev fanIn (workTapeCount : ℕ) : ℕ :=
  WorkspaceAccounting.fanIn workTapeCount

/-- Protected grouped-coordinate width. -/
abbrev chunkBits (Q : Type*) [Fintype Q]
    (workTapeCount candidate : ℕ) : ℕ :=
  WorkspaceAccounting.chunkBits Q workTapeCount candidate

/-- Tight number of grouped coordinates. -/
abbrev chunkCount (Q : Type*) [Fintype Q]
    (workTapeCount candidate : ℕ) : ℕ :=
  WorkspaceAccounting.chunkCount Q workTapeCount candidate

/-- Cardinality of the complete grouped-coordinate domain. -/
def domainSize (Q : Type*) [Fintype Q]
    (workTapeCount candidate : ℕ) : ℕ :=
  PrimeGrouped.Logarithmic.domainSize
    (booleanWidth Q candidate) (fanIn workTapeCount)

/-- Exact grouped interpolation degree. -/
def groupedDegree (Q : Type*) [Fintype Q]
    (workTapeCount candidate : ℕ) : ℕ :=
  PrimeGrouped.Logarithmic.groupedDegree
    (booleanWidth Q candidate) (fanIn workTapeCount)

/-- Canonical degree endpoint, including the codebook-capacity floor. -/
def degreeEndpoint (Q : Type*) [Fintype Q]
    (workTapeCount candidate : ℕ) : ℕ :=
  PrimeGrouped.Logarithmic.degreeEndpoint
    (booleanWidth Q candidate) (fanIn workTapeCount)

/-- Assigned bit width of one field residue. -/
abbrev fieldBits (Q : Type*) [Fintype Q]
    (workTapeCount candidate : ℕ) : ℕ :=
  WorkspaceAccounting.fieldBits Q workTapeCount candidate

/-- Assigned bit width of one evaluator frame. -/
abbrev frameBits (Q : Type*) [Fintype Q]
    (workTapeCount candidate : ℕ) : ℕ :=
  WorkspaceAccounting.frameBits Q workTapeCount candidate

/-- Packed continuation-frame radix. -/
abbrev frameRadix (Q : Type*) [Fintype Q]
    (workTapeCount candidate : ℕ) : ℕ :=
  NeighborhoodProgram.frameRadix Q workTapeCount candidate

/-- Packed catalytic-bank digit radix. -/
abbrev bankRadix (Q : Type*) [Fintype Q]
    (workTapeCount candidate : ℕ) : ℕ :=
  NeighborhoodProgram.bankRadix Q workTapeCount candidate

/-- Number of residue digits in the catalytic bank. -/
abbrev bankDigitCount (Q : Type*) [Fintype Q]
    (workTapeCount candidate : ℕ) : ℕ :=
  NeighborhoodProgram.bankDigitCount Q workTapeCount candidate

/-- Canonical prime modulus for the grouped endpoint. -/
def canonicalModulus (Q : Type*) [Fintype Q]
    (workTapeCount candidate : ℕ) : ℕ :=
  PrimeField.Search.searchModulus
    (degreeEndpoint Q workTapeCount candidate)

/-- Expected values of the seventeen advertised output registers, in their
physical allocation order. -/
def expectedValues (Q : Type*) [Fintype Q]
    (workTapeCount candidate : ℕ) : Fin 17 → ℕ :=
  ![protectedLog candidate,
    radicand candidate,
    blockLength candidate,
    horizon candidate,
    booleanWidth Q candidate,
    fanIn workTapeCount,
    chunkBits Q workTapeCount candidate,
    chunkCount Q workTapeCount candidate,
    domainSize Q workTapeCount candidate,
    groupedDegree Q workTapeCount candidate,
    degreeEndpoint Q workTapeCount candidate,
    fieldBits Q workTapeCount candidate,
    frameBits Q workTapeCount candidate,
    frameRadix Q workTapeCount candidate,
    bankRadix Q workTapeCount candidate,
    bankDigitCount Q workTapeCount candidate,
    canonicalModulus Q workTapeCount candidate - 1]

/-- Thirty-two distinct mutable registers together with one external
read-only candidate register. -/
structure Registers where
  /-- Candidate supplied by the outer controller and never written here. -/
  candidate : ℕ
  /-- Mutable allocation: seventeen outputs, seven scratch registers, and
  eight prime-search registers. -/
  index : Fin 32 → ℕ
  /-- Mutable logical fields occupy distinct physical registers. -/
  injective : Function.Injective index
  /-- The external candidate does not alias any mutable destination. -/
  candidate_ne : ∀ slot, candidate ≠ index slot

namespace Registers

/-- Distinct mutable fields occupy distinct physical registers. -/
theorem index_ne (regs : Registers) {first second : Fin 32}
    (hne : first ≠ second) :
    regs.index first ≠ regs.index second :=
  fun heq => hne (regs.injective heq)

/-- Protected logarithm output. -/
abbrev protectedLog (regs : Registers) : ℕ := regs.index 0

/-- Balanced radicand output. -/
abbrev radicand (regs : Registers) : ℕ := regs.index 1

/-- Positive ceiling-square-root block length. -/
abbrev blockLength (regs : Registers) : ℕ := regs.index 2

/-- Tight interval horizon. -/
abbrev horizon (regs : Registers) : ℕ := regs.index 3

/-- Compact Boolean payload width. -/
abbrev booleanWidth (regs : Registers) : ℕ := regs.index 4

/-- Neighborhood fan-in. -/
abbrev fanIn (regs : Registers) : ℕ := regs.index 5

/-- Grouped-coordinate bit width. -/
abbrev chunkBits (regs : Registers) : ℕ := regs.index 6

/-- Number of grouped coordinates. -/
abbrev chunkCount (regs : Registers) : ℕ := regs.index 7

/-- Complete grouped-coordinate domain size. -/
abbrev domainSize (regs : Registers) : ℕ := regs.index 8

/-- Exact grouped polynomial degree. -/
abbrev groupedDegree (regs : Registers) : ℕ := regs.index 9

/-- Degree endpoint sent to canonical prime search. -/
abbrev degreeEndpoint (regs : Registers) : ℕ := regs.index 10

/-- Assigned field-residue width. -/
abbrev fieldBits (regs : Registers) : ℕ := regs.index 11

/-- Assigned evaluator-frame width. -/
abbrev frameBits (regs : Registers) : ℕ := regs.index 12

/-- Packed continuation-frame radix. -/
abbrev frameRadix (regs : Registers) : ℕ := regs.index 13

/-- Packed catalytic-bank radix. -/
abbrev bankRadix (regs : Registers) : ℕ := regs.index 14

/-- Number of digits in the catalytic bank. -/
abbrev bankDigitCount (regs : Registers) : ℕ := regs.index 15

/-- Canonical modulus predecessor. -/
abbrev modulusPred (regs : Registers) : ℕ := regs.index 16

/-- Seven-register scratch view used by logarithm, division, square-root,
and power-of-two routines. -/
def stackRegisters (regs : Registers) :
    NeighborhoodProgram.StackRegisters where
  index := fun slot => regs.index ⟨slot.val + 17, by omega⟩
  injective := by
    intro first second heq
    have hslots := regs.injective heq
    apply Fin.ext
    exact Nat.add_right_cancel (congrArg Fin.val hslots)

/-- Separate eight-register allocation used only by canonical prime search. -/
def primeRegisters (regs : Registers) :
    PrimeSearch.Registers where
  index := fun slot => regs.index ⟨slot.val + 24, by omega⟩
  injective := by
    intro first second heq
    have hslots := regs.injective heq
    apply Fin.ext
    exact Nat.add_right_cancel (congrArg Fin.val hslots)

/-- The exact finite set of mutable destinations. -/
def footprint (regs : Registers) : Finset ℕ :=
  Finset.univ.image regs.index

/-- Every mutable logical field belongs to the advertised footprint. -/
@[simp]
theorem index_mem_footprint (regs : Registers) (slot : Fin 32) :
    regs.index slot ∈ regs.footprint :=
  Finset.mem_image.mpr ⟨slot, Finset.mem_univ _, rfl⟩

/-- The external candidate cell is outside the mutable footprint. -/
@[simp]
theorem candidate_not_mem_footprint (regs : Registers) :
    regs.candidate ∉ regs.footprint := by
  intro hmem
  obtain ⟨slot, _, hslot⟩ := Finset.mem_image.mp hmem
  exact regs.candidate_ne slot hslot.symm

end Registers

/-- Source-store bit-width bound over the exact mutable footprint. -/
def ValuesWithin
    (allowed : Finset ℕ) (valueBits : ℕ) (store : Store) : Prop :=
  ∀ address, address ∈ allowed →
    bitlen (store address) ≤ valueBits

/-- Copy one direct register into another without indirect access. -/
def copy (destination source : ℕ) : Cmd :=
  Cmd.seq
    (.basic (.imm destination 0))
    (.basic (.add destination source destination))

/-- Test whether the halving word is at least two. -/
def protectedLogTest (regs : Registers) : Basic :=
  let scratch := regs.stackRegisters
  .sub scratch.test scratch.word scratch.one

/-- One protected-logarithm iteration: halve and increment. -/
def protectedLogBody (regs : Registers) (result : ℕ) : Cmd :=
  let scratch := regs.stackRegisters
  Cmd.seqList
    [NeighborhoodProgram.pop scratch,
      .basic (.add result result scratch.one),
      .basic (protectedLogTest regs)]

/-- Compute `Nat.log 2 source + 1`, including source zero and one. -/
def computeProtectedLog
    (regs : Registers) (source result : ℕ) : Cmd :=
  let scratch := regs.stackRegisters
  Cmd.seqList
    [copy scratch.word source,
      .basic (.imm scratch.base 2),
      .basic (.imm scratch.basePred 1),
      .basic (.imm scratch.one 1),
      .basic (.imm result 1),
      .basic (protectedLogTest regs),
      .whileNonzero scratch.test (protectedLogBody regs result)]

/-- Recompute whether the current square still misses the radicand. -/
def sqrtTest (regs : Registers) (source : ℕ) : Basic :=
  let scratch := regs.stackRegisters
  .sub scratch.test source scratch.quotient

/-- Increment the positive square-root candidate and refresh its square. -/
def sqrtBody (regs : Registers) (source result : ℕ) : Cmd :=
  let scratch := regs.stackRegisters
  Cmd.seqList
    [.basic (.add result result scratch.one),
      .basic (.mul scratch.quotient result result),
      .basic (sqrtTest regs source)]

/-- Compute the positive ceiling square root of a direct source register. -/
def computePositiveCeilSqrt
    (regs : Registers) (source result : ℕ) : Cmd :=
  let scratch := regs.stackRegisters
  Cmd.seqList
    [.basic (.imm scratch.one 1),
      .basic (.imm result 1),
      .basic (.imm scratch.quotient 1),
      .basic (sqrtTest regs source),
      .whileNonzero scratch.test (sqrtBody regs source result)]

/-- Compute a positive-divisor ceiling quotient via the verified packed-word
division routine. -/
def computeCeilDiv
    (regs : Registers) (dividend divisor result : ℕ) : Cmd :=
  let scratch := regs.stackRegisters
  Cmd.seqList
    [.basic (.imm scratch.one 1),
      copy scratch.word dividend,
      copy scratch.base divisor,
      .basic (.sub scratch.basePred scratch.base scratch.one),
      .basic (.add scratch.word scratch.word scratch.basePred),
      NeighborhoodProgram.pop scratch,
      copy result scratch.word]

/-- One power-of-two iteration. -/
def powTwoBody (regs : Registers) (result : ℕ) : Cmd :=
  let scratch := regs.stackRegisters
  Cmd.seq
    (.basic (.mul result result scratch.base))
    (.basic (.sub scratch.word scratch.word scratch.one))

/-- Compute `2 ^ exponent` into a direct result register. -/
def computePowTwo
    (regs : Registers) (exponent result : ℕ) : Cmd :=
  let scratch := regs.stackRegisters
  Cmd.seqList
    [.basic (.imm scratch.one 1),
      .basic (.imm scratch.base 2),
      copy scratch.word exponent,
      .basic (.imm result 1),
      .whileNonzero scratch.word (powTwoBody regs result)]

/-- Copy one of two direct sources according to a saturated comparison. -/
def computeMax
    (regs : Registers) (left right result : ℕ) : Cmd :=
  let scratch := regs.stackRegisters
  Cmd.seq
    (.basic (.sub scratch.test left right))
    (.ifZero scratch.test
      (copy result right)
      (copy result left))

/-- Compute the balanced radicand. -/
def computeRadicand (regs : Registers) : Cmd :=
  .basic (.mul regs.radicand regs.candidate regs.protectedLog)

/-- Compute the compact Boolean payload width. -/
def computeBooleanWidth (Q : Type*) [Fintype Q]
    (regs : Registers) : Cmd :=
  let scratch := regs.stackRegisters
  Cmd.seqList
    [.basic (.imm scratch.value 5),
      .basic (.mul regs.booleanWidth scratch.value regs.blockLength),
      .basic (.imm scratch.value (Fintype.card Q)),
      .basic (.add regs.booleanWidth scratch.value regs.booleanWidth)]

/-- Compute the fixed source-machine fan-in. -/
def computeFanIn (workTapeCount : ℕ) (regs : Registers) : Cmd :=
  .basic (.imm regs.fanIn (4 * (workTapeCount + 2)))

/-- Compute the grouped-coordinate logarithmic width. -/
def computeChunkBits (regs : Registers) : Cmd :=
  let scratch := regs.stackRegisters
  Cmd.seq
    (.basic (.mul scratch.value regs.fanIn regs.booleanWidth))
    (computeProtectedLog regs scratch.value regs.chunkBits)

/-- Compute the exact grouped interpolation degree. -/
def computeGroupedDegree (regs : Registers) : Cmd :=
  let scratch := regs.stackRegisters
  Cmd.seqList
    [.basic (.imm scratch.one 1),
      .basic (.sub scratch.value regs.domainSize scratch.one),
      .basic (.mul regs.groupedDegree regs.fanIn regs.chunkCount),
      .basic (.mul regs.groupedDegree
        regs.groupedDegree scratch.value)]

/-- Compute the assigned field-residue width. -/
def computeFieldBits (regs : Registers) : Cmd :=
  let scratch := regs.stackRegisters
  Cmd.seq
    (.basic (.imm scratch.value 2))
    (.basic (.mul regs.fieldBits scratch.value regs.chunkBits))

/-- Compute the assigned evaluator-frame width. -/
def computeFrameBits (regs : Registers) : Cmd :=
  let scratch := regs.stackRegisters
  Cmd.seq
    (.basic (.imm scratch.value 24))
    (.basic (.mul regs.frameBits scratch.value regs.chunkBits))

/-- Compute the number of packed catalytic-bank digits. -/
def computeBankDigitCount (regs : Registers) : Cmd :=
  let scratch := regs.stackRegisters
  Cmd.seqList
    [.basic (.imm scratch.one 1),
      .basic (.add regs.bankDigitCount regs.fanIn scratch.one),
      .basic (.mul regs.bankDigitCount
        regs.bankDigitCount regs.chunkCount)]

/-- Initialize and execute canonical prime search, then cache its predecessor. -/
def computeCanonicalModulus (regs : Registers) : Cmd :=
  let scratch := regs.stackRegisters
  let prime := regs.primeRegisters
  Cmd.seqList
    [.basic (.imm scratch.one 1),
      .basic (.imm scratch.value 2),
      .basic (.add prime.candidate regs.degreeEndpoint scratch.value),
      PrimeSearch.search prime,
      .basic (.imm scratch.one 1),
      .basic (.sub regs.modulusPred prime.candidate scratch.one)]

/-- Uniform first-order construction of all numerical trial parameters. -/
def program (Q : Type*) [Fintype Q]
    (workTapeCount : ℕ) (regs : Registers) : Cmd :=
  Cmd.seqList
    [computeProtectedLog regs regs.candidate regs.protectedLog,
      computeRadicand regs,
      computePositiveCeilSqrt regs regs.radicand regs.blockLength,
      computeCeilDiv regs regs.candidate regs.blockLength regs.horizon,
      computeBooleanWidth Q regs,
      computeFanIn workTapeCount regs,
      computeChunkBits regs,
      computeCeilDiv regs regs.booleanWidth regs.chunkBits regs.chunkCount,
      computePowTwo regs regs.chunkBits regs.domainSize,
      computeGroupedDegree regs,
      computeMax regs regs.groupedDegree
        regs.stackRegisters.value regs.degreeEndpoint,
      computeFieldBits regs,
      computeFrameBits regs,
      computePowTwo regs regs.frameBits regs.frameRadix,
      computePowTwo regs regs.fieldBits regs.bankRadix,
      computeBankDigitCount regs,
      computeCanonicalModulus regs]

/-- Exact functional postcondition of the parameter-construction program. -/
structure Post (Q : Type*) [Fintype Q]
    (workTapeCount candidate : ℕ) (regs : Registers)
    (initial final : Store) : Prop where
  /-- The external candidate register is preserved. -/
  candidate_eq : final regs.candidate = candidate
  /-- Protected logarithm output. -/
  protectedLog_eq :
    final regs.protectedLog = protectedLog candidate
  /-- Balanced radicand output. -/
  radicand_eq :
    final regs.radicand = radicand candidate
  /-- Positive balanced block length. -/
  blockLength_eq :
    final regs.blockLength = blockLength candidate
  /-- Tight ceiling-division horizon. -/
  horizon_eq :
    final regs.horizon = horizon candidate
  /-- Compact Boolean width. -/
  booleanWidth_eq :
    final regs.booleanWidth = booleanWidth Q candidate
  /-- Neighborhood fan-in. -/
  fanIn_eq :
    final regs.fanIn = fanIn workTapeCount
  /-- Protected grouped-coordinate width. -/
  chunkBits_eq :
    final regs.chunkBits = chunkBits Q workTapeCount candidate
  /-- Tight grouped-coordinate count. -/
  chunkCount_eq :
    final regs.chunkCount = chunkCount Q workTapeCount candidate
  /-- Complete grouped-coordinate domain. -/
  domainSize_eq :
    final regs.domainSize = domainSize Q workTapeCount candidate
  /-- Exact grouped interpolation degree. -/
  groupedDegree_eq :
    final regs.groupedDegree = groupedDegree Q workTapeCount candidate
  /-- Canonical degree endpoint. -/
  degreeEndpoint_eq :
    final regs.degreeEndpoint = degreeEndpoint Q workTapeCount candidate
  /-- Assigned field width. -/
  fieldBits_eq :
    final regs.fieldBits = fieldBits Q workTapeCount candidate
  /-- Assigned frame width. -/
  frameBits_eq :
    final regs.frameBits = frameBits Q workTapeCount candidate
  /-- Continuation-frame radix. -/
  frameRadix_eq :
    final regs.frameRadix = frameRadix Q workTapeCount candidate
  /-- Catalytic-bank radix. -/
  bankRadix_eq :
    final regs.bankRadix = bankRadix Q workTapeCount candidate
  /-- Catalytic-bank digit count. -/
  bankDigitCount_eq :
    final regs.bankDigitCount = bankDigitCount Q workTapeCount candidate
  /-- Canonical searched modulus. -/
  modulus_eq :
    final regs.primeRegisters.candidate =
      canonicalModulus Q workTapeCount candidate
  /-- Canonical modulus predecessor. -/
  modulusPred_eq :
    final regs.modulusPred =
      canonicalModulus Q workTapeCount candidate - 1
  /-- Every address outside the exact mutable footprint is unchanged. -/
  eq_outside : ∀ address ∉ regs.footprint,
    final address = initial address

end CandidateParameters

end Runtime

end TimeSpaceSimulation

end Complexity
