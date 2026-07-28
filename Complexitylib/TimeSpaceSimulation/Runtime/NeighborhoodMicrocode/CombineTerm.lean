/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/
import
  Complexitylib.TimeSpaceSimulation.Runtime.NeighborhoodMicrocode.CombineTerm.Defs
import
  Complexitylib.TimeSpaceSimulation.Runtime.NeighborhoodMicrocode.CombineTerm.Internal
import
  Complexitylib.TimeSpaceSimulation.Runtime.NeighborhoodMicrocode.CombineTerm.Internal.Basis

/-!
# Fixed-register assignment digits and combine-term composition

This surface exposes the uniform assignment-code digit decoder and the final
modular factor-composition layer for neighborhood combination.  The remaining
semantic kernels are now separated cleanly:

* a packed-node kernel supplies `packedAssignmentValue`;
* a tensor-basis kernel supplies `basisAssignmentValue`;
* `combineTerm` concretely multiplies them and satisfies
  `CombineTermKernelSpecAt`.
-/

namespace Complexity
namespace TimeSpaceSimulation
namespace Runtime
namespace NeighborhoodMicrocode
namespace CombineTerm

open RAM Structured
open TreeEval CookMertz

variable {controller : SearchProgram.Registers}

/-- Repeated quotient extraction agrees with division by a radix power. -/
theorem radixQuotient_eq_div_pow
    (radix word index : ℕ) :
    radixQuotient radix index word =
      word / radix ^ index :=
  Internal.radixQuotient_eq_div_pow_internal radix word index

/-- Dynamic radix-digit lookup writes exactly within its five mutable
registers. -/
theorem seekDigit_writesWithin
    (regs : DigitRegisters) :
    RAM.Structured.Footprint.CmdWritesWithin
      regs.writeFootprint (seekDigit regs) :=
  Internal.seekDigit_writesWithin_internal regs

/-- Dynamic radix-digit lookup terminates with the exact selected digit. -/
theorem seekDigit_runs
    (regs : DigitRegisters) (store : Store)
    (radix word index : ℕ)
    (hradix : 0 < radix)
    (hvalue : store regs.value = word)
    (hcursor : store regs.cursor = index)
    (hdivisor : store regs.divisor = radix) :
    ∃ final,
      Runs (seekDigit regs) store final ∧
      DigitPost regs radix word index store final :=
  Internal.seekDigit_runs_internal regs store radix word index
    hradix hvalue hcursor hdivisor

/-- Assignment lookup writes exactly within the physical digit interface. -/
theorem assignmentDigit_precise_writesWithin
    (regs : NeighborhoodTrial.Registers controller) :
    RAM.Structured.Footprint.CmdWritesWithin
      (assignmentDigitRegisters regs).writeFootprint
      (assignmentDigit regs) :=
  Internal.assignmentDigit_precise_writesWithin_internal regs

/-- Assignment lookup is confined to combine scratch. -/
theorem assignmentDigit_writesWithin
    (regs : NeighborhoodTrial.Registers controller) :
    RAM.Structured.Footprint.CmdWritesWithin
      (CombineValue.combineScratchFootprint regs)
      (assignmentDigit regs) :=
  Internal.assignmentDigit_writesWithin_internal regs

/-- Assignment lookup is confined to the shared neighborhood layout. -/
theorem assignmentDigit_layout_writesWithin
    (regs : NeighborhoodTrial.Registers controller) :
    RAM.Structured.Footprint.CmdWritesWithin
      regs.layout.footprint (assignmentDigit regs) :=
  Internal.assignmentDigit_layout_writesWithin_internal regs

/-- The concrete assignment lookup returns the exact runtime radix digit,
preserves the enclosing range interface, and preserves the neighborhood ABI. -/
theorem assignmentDigit_runs
    (regs : NeighborhoodTrial.Registers controller)
    (store : Store) (radix code index : ℕ)
    (hradix : 0 < radix)
    (hcode :
      store (CombineValue.rangeRegisters regs).remaining = code)
    (hindex : store (assignmentDigitIndex regs) = index)
    (hradixValue : store (Layout.chunkRadix regs) = radix)
    (hone :
      store (CombineValue.rangeRegisters regs).one = 1) :
    ∃ final,
      Runs (assignmentDigit regs) store final ∧
      AssignmentDigitPost regs radix code index store final ∧
      ControlDecode.PreservesABI regs store final :=
  Internal.assignmentDigit_runs_internal regs store radix code index
    hradix hcode hindex hradixValue hone

/-- The uniform tensor-basis kernel writes only the fixed combine scratch
interface. -/
theorem computationBasisKernel_writesWithin
    (workTapeCount : ℕ)
    (regs : NeighborhoodTrial.Registers controller) :
    RAM.Structured.Footprint.CmdWritesWithin
      (CombineValue.combineScratchFootprint regs)
      (computationBasisKernel workTapeCount regs) :=
  computationBasisKernel_writesWithin_internal workTapeCount regs

/-- The fixed-source tensor-basis kernel computes the exact assignment
basis value from the runtime chunk parameters and represented child bank. -/
theorem computationBasisKernel_spec
    {tm : TM workTapeCount}
    (regs : NeighborhoodTrial.Registers controller)
    (instanceData : NeighborhoodProgram.ResidueInstance tm)
    (frame : NeighborhoodScheduler.Frame tm instanceData)
    (tape : TapeIndex workTapeCount)
    (slot : NeighborhoodGraph.Slot)
    (interval : ℕ)
    (logicalBank :
      NeighborhoodExecutableEvaluation.Residue.Registers
        tm instanceData.blockLength) :
    ComputationBasisKernelSpecAt regs instanceData frame tape slot
      interval logicalBank
      (computationBasisKernel workTapeCount regs) :=
  computationBasisKernel_spec_internal regs instanceData frame tape slot
    interval logicalBank

/-- A represented scheduler state whose head is a computation frame supplies
the stable encoded-node and packed-bank context used by concrete factor
kernels. -/
theorem computationContext_of_queryState
    {tm : TM workTapeCount}
    (regs : NeighborhoodTrial.Registers controller)
    (instanceData : NeighborhoodProgram.ResidueInstance tm)
    (frame : NeighborhoodScheduler.Frame tm instanceData)
    (rest : List (NeighborhoodScheduler.Frame tm instanceData))
    (state : NeighborhoodScheduler.State tm instanceData)
    (store : Store)
    (tape : TapeIndex workTapeCount)
    (slot : NeighborhoodGraph.Slot)
    (interval : ℕ)
    (hstack : state.stack = frame :: rest)
    (hnode :
      frame.node =
        (show
          NeighborhoodEvaluator.QueryNode
            workTapeCount instanceData.horizon
          from .graph (.computation tape slot interval)))
    (hrep : Representation.QueryState regs instanceData state store) :
    ComputationContext regs instanceData tape slot interval
      state.registers store :=
  Internal.computationContext_of_queryState_internal
    regs instanceData frame rest state store tape slot interval
    hstack hnode hrep

/-- The concrete range driver's accumulator, test, countdown, and one cells
are disjoint from every field used by the encoded-node and packed-bank
representation. -/
theorem computationContext_stableUnderDriverWrites
    {tm : TM workTapeCount}
    (regs : NeighborhoodTrial.Registers controller)
    (instanceData : NeighborhoodProgram.ResidueInstance tm)
    (tape : TapeIndex workTapeCount)
    (slot : NeighborhoodGraph.Slot)
    (interval : ℕ)
    (logicalBank :
      NeighborhoodExecutableEvaluation.Residue.Registers
        tm instanceData.blockLength) :
    CombineValue.StableUnderDriverWrites
      (CombineValue.rangeRegisters regs)
      (ComputationContext regs instanceData tape slot interval
        logicalBank) :=
  Internal.computationContext_stableUnderDriverWrites_internal
    regs instanceData tape slot interval logicalBank

/-- The stable active-node context can be decoded to the exact computation
tag, tape, slot, and interval fields without changing the packed bank. -/
theorem decodeComputationNode_runs
    {tm : TM workTapeCount}
    (regs : NeighborhoodTrial.Registers controller)
    (instanceData : NeighborhoodProgram.ResidueInstance tm)
    (tape : TapeIndex workTapeCount)
    (slot : NeighborhoodGraph.Slot)
    (interval : ℕ)
    (logicalBank :
      NeighborhoodExecutableEvaluation.Residue.Registers
        tm instanceData.blockLength)
    (store : Store)
    (hfits :
      ∀ digit ∈
          FrameCodec.nodeDigits
            (show
              NeighborhoodEvaluator.QueryNode
                workTapeCount instanceData.horizon
              from .graph (.computation tape slot interval)),
        digit < Representation.digitBase instanceData)
    (hcontext :
      ComputationContext regs instanceData tape slot interval
        logicalBank store) :
    ∃ final,
      Runs (ControlDecode.decodeNode regs) store final ∧
      DecodedComputationPost regs instanceData tape slot interval
        logicalBank final :=
  Internal.decodeComputationNode_runs_internal
    regs instanceData tape slot interval logicalBank store
    hfits hcontext

/-- Dynamic catalytic-bank coordinate lookup writes only its fixed inherited
bank interface and two range-count cells. -/
theorem readResidueCoordinate_writesWithin
    (regs : NeighborhoodTrial.Registers controller) :
    RAM.Structured.Footprint.CmdWritesWithin
      (coordinateReadFootprint regs)
      (readResidueCoordinate regs) :=
  Internal.readResidueCoordinate_writesWithin_internal regs

/-- Dynamic catalytic-bank lookup returns the exact logical residue, restores
the packed word and range interface, and preserves the computation context. -/
theorem readResidueCoordinate_runs
    {tm : TM workTapeCount}
    (regs : NeighborhoodTrial.Registers controller)
    (instanceData : NeighborhoodProgram.ResidueInstance tm)
    (tape : TapeIndex workTapeCount)
    (slot : NeighborhoodGraph.Slot)
    (interval : ℕ)
    (logicalBank :
      NeighborhoodExecutableEvaluation.Residue.Registers
        tm instanceData.blockLength)
    (register :
      Fin
        (NeighborhoodExecutableEvaluation.graphFanIn workTapeCount + 1))
    (chunk :
      Fin
        (PrimeGrouped.Logarithmic.chunkCount
          (NeighborhoodExecutableEvaluation.payloadWidth
            tm instanceData.blockLength)
          (NeighborhoodExecutableEvaluation.graphFanIn workTapeCount)))
    (store : Store)
    (hcontext :
      ComputationContext regs instanceData tape slot interval
        logicalBank store)
    (hcoordinate :
      store (coordinateIndex regs) =
        NeighborhoodProgram.residueBankIndex
          tm instanceData.blockLength register chunk)
    (hone :
      store (CombineValue.rangeRegisters regs).one = 1) :
    ∃ final,
      Runs (readResidueCoordinate regs) store final ∧
      ResidueCoordinatePost regs (logicalBank register chunk)
        (NeighborhoodProgram.residueBankIndex
          tm instanceData.blockLength register chunk)
        store final ∧
      ComputationContext regs instanceData tape slot interval
        logicalBank final :=
  Internal.readResidueCoordinate_runs_internal
    regs instanceData tape slot interval logicalBank register chunk
    store hcontext hcoordinate hone

/-- Factor generation and final multiplication are confined to combine
scratch whenever both factor kernels are. -/
theorem combineTerm_writesWithin
    (regs : NeighborhoodTrial.Registers controller)
    (packedKernel basisKernel : Cmd)
    (hpacked :
      RAM.Structured.Footprint.CmdWritesWithin
        (CombineValue.combineScratchFootprint regs) packedKernel)
    (hbasis :
      RAM.Structured.Footprint.CmdWritesWithin
        (CombineValue.combineScratchFootprint regs) basisKernel) :
    RAM.Structured.Footprint.CmdWritesWithin
      (CombineValue.combineScratchFootprint regs)
      (combineTerm regs packedKernel basisKernel) :=
  Internal.combineTerm_writesWithin_internal
    regs packedKernel basisKernel hpacked hbasis

/-- Factor generation and final multiplication write within the shared
neighborhood layout. -/
theorem combineTerm_layout_writesWithin
    (regs : NeighborhoodTrial.Registers controller)
    (packedKernel basisKernel : Cmd)
    (hpacked :
      RAM.Structured.Footprint.CmdWritesWithin
        (CombineValue.combineScratchFootprint regs) packedKernel)
    (hbasis :
      RAM.Structured.Footprint.CmdWritesWithin
        (CombineValue.combineScratchFootprint regs) basisKernel) :
    RAM.Structured.Footprint.CmdWritesWithin
      regs.layout.footprint
      (combineTerm regs packedKernel basisKernel) :=
  Internal.combineTerm_layout_writesWithin_internal
    regs packedKernel basisKernel hpacked hbasis

/-- Every execution of two confined factor kernels and their final modular
multiplication preserves the neighborhood ABI. -/
theorem combineTerm_preservesABI
    (regs : NeighborhoodTrial.Registers controller)
    (packedKernel basisKernel : Cmd)
    (hpacked :
      RAM.Structured.Footprint.CmdWritesWithin
        (CombineValue.combineScratchFootprint regs) packedKernel)
    (hbasis :
      RAM.Structured.Footprint.CmdWritesWithin
        (CombineValue.combineScratchFootprint regs) basisKernel)
    {initial final : Store}
    (hrun :
      Runs (combineTerm regs packedKernel basisKernel)
        initial final) :
    ControlDecode.PreservesABI regs initial final :=
  Internal.combineTerm_preservesABI_internal
    regs packedKernel basisKernel hpacked hbasis hrun

/-- Exact packed and basis factor kernels compose into one contextual
range-term kernel by concrete runtime modular multiplication. -/
theorem combineTerm_specAt
    (regs : NeighborhoodTrial.Registers controller)
    (packedKernel basisKernel : Cmd)
    (modulus : ℕ) (packed basis : ℕ → ℕ)
    (hmodulus : 0 < modulus)
    (hpacked :
      PackedKernelSpecAt regs packedKernel modulus packed)
    (hbasis :
      BasisKernelSpecAt regs basisKernel modulus basis) :
    CombineValue.TermKernelSpecAt
      (CombineValue.rangeRegisters regs)
      (combineTerm regs packedKernel basisKernel)
      modulus
      (fun index =>
        PrimeField.Runtime.mul modulus
          (packed index) (basis index)) :=
  Internal.combineTerm_specAt_internal regs packedKernel basisKernel
    modulus packed basis hmodulus hpacked hbasis

/-- Contextual packed and basis factors compose while preserving the exact
active computation node and logical packed-bank representation. -/
theorem combineTerm_specAtContext
    {tm : TM workTapeCount}
    (regs : NeighborhoodTrial.Registers controller)
    (instanceData : NeighborhoodProgram.ResidueInstance tm)
    (tape : TapeIndex workTapeCount)
    (slot : NeighborhoodGraph.Slot)
    (interval : ℕ)
    (logicalBank :
      NeighborhoodExecutableEvaluation.Residue.Registers
        tm instanceData.blockLength)
    (packedKernel basisKernel : Cmd)
    (modulus : ℕ) (packed basis : ℕ → ℕ)
    (hmodulus : 0 < modulus)
    (hpacked :
      PackedKernelSpecAtContext regs packedKernel modulus packed
        (ComputationContext regs instanceData tape slot interval
          logicalBank))
    (hbasis :
      BasisKernelSpecAtContext regs basisKernel modulus basis
        (ComputationContext regs instanceData tape slot interval
          logicalBank)) :
    CombineValue.TermKernelSpecAtContext
      (CombineValue.rangeRegisters regs)
      (combineTerm regs packedKernel basisKernel)
      modulus
      (fun index =>
        PrimeField.Runtime.mul modulus
          (packed index) (basis index))
      (ComputationContext regs instanceData tape slot interval
        logicalBank) :=
  Internal.combineTerm_specAtContext_internal
    regs instanceData tape slot interval logicalBank
    packedKernel basisKernel modulus packed basis
    hmodulus hpacked hbasis

/-- The semantic assignment summand is exactly the modular product of its
packed-node and tensor-basis factors. -/
theorem assignmentTerm_eq_factors
    (payloadWidth fanIn : ℕ)
    (combine :
      (Fin fanIn → Fin payloadWidth → Bool) →
        Fin payloadWidth → Bool)
    (args :
      Fin fanIn →
        Fin
          (PrimeGrouped.Logarithmic.chunkCount payloadWidth fanIn) →
          ℕ)
    (outputChunk :
      Fin
        (PrimeGrouped.Logarithmic.chunkCount payloadWidth fanIn))
    (code : ℕ) :
    CombineValue.assignmentTerm payloadWidth fanIn combine args
        outputChunk code =
      PrimeField.Runtime.mul
        (NeighborhoodExecutableEvaluation.Residue.fieldModulus
          payloadWidth fanIn)
        (packedAssignmentValue payloadWidth fanIn combine
          outputChunk code)
        (basisAssignmentValue payloadWidth fanIn args code) :=
  Internal.assignmentTerm_eq_factors_internal
    payloadWidth fanIn combine args outputChunk code

/-- Exact packed-node and basis kernels close the contextual assignment-term
contract consumed by `CombineValue.rangeFold`. -/
theorem combineTerm_assignmentSpecAt
    (regs : NeighborhoodTrial.Registers controller)
    (packedKernel basisKernel : Cmd)
    (payloadWidth fanIn : ℕ)
    (combine :
      (Fin fanIn → Fin payloadWidth → Bool) →
        Fin payloadWidth → Bool)
    (args :
      Fin fanIn →
        Fin
          (PrimeGrouped.Logarithmic.chunkCount payloadWidth fanIn) →
          ℕ)
    (outputChunk :
      Fin
        (PrimeGrouped.Logarithmic.chunkCount payloadWidth fanIn))
    (hpacked :
      PackedKernelSpecAt regs packedKernel
        (NeighborhoodExecutableEvaluation.Residue.fieldModulus
          payloadWidth fanIn)
        (packedAssignmentValue payloadWidth fanIn combine outputChunk))
    (hbasis :
      BasisKernelSpecAt regs basisKernel
        (NeighborhoodExecutableEvaluation.Residue.fieldModulus
          payloadWidth fanIn)
        (basisAssignmentValue payloadWidth fanIn args)) :
    CombineValue.CombineTermKernelSpecAt
      (CombineValue.rangeRegisters regs)
      (combineTerm regs packedKernel basisKernel)
      payloadWidth fanIn combine args outputChunk :=
  Internal.combineTerm_assignmentSpecAt_internal
    regs packedKernel basisKernel payloadWidth fanIn combine args
    outputChunk hpacked hbasis

/-- Exact factor kernels compose through concrete term multiplication and the
concrete outer range fold to compute one grouped Boolean-node coordinate. -/
theorem evaluateNode_combineTerm_runs
    (regs : NeighborhoodTrial.Registers controller)
    (packedKernel basisKernel : Cmd)
    (payloadWidth fanIn : ℕ)
    (combine :
      (Fin fanIn → Fin payloadWidth → Bool) →
        Fin payloadWidth → Bool)
    (args :
      Fin fanIn →
        Fin
          (PrimeGrouped.Logarithmic.chunkCount payloadWidth fanIn) →
          ℕ)
    (outputChunk :
      Fin
        (PrimeGrouped.Logarithmic.chunkCount payloadWidth fanIn))
    (hpackedSpec :
      PackedKernelSpecAt regs packedKernel
        (NeighborhoodExecutableEvaluation.Residue.fieldModulus
          payloadWidth fanIn)
        (packedAssignmentValue payloadWidth fanIn combine outputChunk))
    (hbasisSpec :
      BasisKernelSpecAt regs basisKernel
        (NeighborhoodExecutableEvaluation.Residue.fieldModulus
          payloadWidth fanIn)
        (basisAssignmentValue payloadWidth fanIn args))
    (hpackedWrites :
      RAM.Structured.Footprint.CmdWritesWithin
        (CombineValue.combineScratchFootprint regs) packedKernel)
    (hbasisWrites :
      RAM.Structured.Footprint.CmdWritesWithin
        (CombineValue.combineScratchFootprint regs) basisKernel)
    (store : Store)
    (hmodulusValue :
      store (CombineValue.rangeRegisters regs).modulus =
        NeighborhoodExecutableEvaluation.Residue.fieldModulus
          payloadWidth fanIn)
    (hmodulusPred :
      store (CombineValue.rangeRegisters regs).modulusPred =
        NeighborhoodExecutableEvaluation.Residue.fieldModulus
            payloadWidth fanIn -
          1)
    (hcount :
      store (CombineValue.rangeRegisters regs).count =
        CombineValue.assignmentCount payloadWidth fanIn) :
    ∃ final,
      Runs
          (CombineValue.rangeFold .add
            (CombineValue.rangeRegisters regs)
            (combineTerm regs packedKernel basisKernel))
          store final ∧
        final (CombineValue.rangeRegisters regs).accumulator =
          NeighborhoodExecutableEvaluation.Residue.evaluateNode
            payloadWidth fanIn combine args outputChunk ∧
        CombineValue.RangePost .add
          (CombineValue.rangeRegisters regs)
          (NeighborhoodExecutableEvaluation.Residue.fieldModulus
            payloadWidth fanIn)
          (CombineValue.assignmentCount payloadWidth fanIn)
          (CombineValue.assignmentTerm
            payloadWidth fanIn combine args outputChunk)
          store final ∧
        ControlDecode.PreservesABI regs store final := by
  apply CombineValue.evaluateNode_rangeFold_runs
  · exact combineTerm_assignmentSpecAt regs packedKernel basisKernel
      payloadWidth fanIn combine args outputChunk
      hpackedSpec hbasisSpec
  · exact combineTerm_writesWithin regs packedKernel basisKernel
      hpackedWrites hbasisWrites
  · exact hmodulusValue
  · exact hmodulusPred
  · exact hcount

/-- Contextual factor kernels compose through the concrete modular
multiplication and outer assignment fold while preserving the exact active
computation node and packed catalytic bank. -/
theorem evaluateNode_combineTerm_runsContext
    {tm : TM workTapeCount}
    (regs : NeighborhoodTrial.Registers controller)
    (instanceData : NeighborhoodProgram.ResidueInstance tm)
    (tape : TapeIndex workTapeCount)
    (slot : NeighborhoodGraph.Slot)
    (interval : ℕ)
    (logicalBank :
      NeighborhoodExecutableEvaluation.Residue.Registers
        tm instanceData.blockLength)
    (packedKernel basisKernel : Cmd)
    (payloadWidth fanIn : ℕ)
    (combine :
      (Fin fanIn → Fin payloadWidth → Bool) →
        Fin payloadWidth → Bool)
    (args :
      Fin fanIn →
        Fin
          (PrimeGrouped.Logarithmic.chunkCount payloadWidth fanIn) →
          ℕ)
    (outputChunk :
      Fin
        (PrimeGrouped.Logarithmic.chunkCount payloadWidth fanIn))
    (hpacked :
      PackedKernelSpecAtContext regs packedKernel
        (NeighborhoodExecutableEvaluation.Residue.fieldModulus
          payloadWidth fanIn)
        (packedAssignmentValue payloadWidth fanIn combine outputChunk)
        (ComputationContext regs instanceData tape slot interval
          logicalBank))
    (hbasis :
      BasisKernelSpecAtContext regs basisKernel
        (NeighborhoodExecutableEvaluation.Residue.fieldModulus
          payloadWidth fanIn)
        (basisAssignmentValue payloadWidth fanIn args)
        (ComputationContext regs instanceData tape slot interval
          logicalBank))
    (store : Store)
    (hcontext :
      ComputationContext regs instanceData tape slot interval
        logicalBank store)
    (hmodulusValue :
      store (CombineValue.rangeRegisters regs).modulus =
        NeighborhoodExecutableEvaluation.Residue.fieldModulus
          payloadWidth fanIn)
    (hmodulusPred :
      store (CombineValue.rangeRegisters regs).modulusPred =
        NeighborhoodExecutableEvaluation.Residue.fieldModulus
            payloadWidth fanIn -
          1)
    (hcount :
      store (CombineValue.rangeRegisters regs).count =
        CombineValue.assignmentCount payloadWidth fanIn) :
    ∃ final,
      Runs
          (CombineValue.rangeFold .add
            (CombineValue.rangeRegisters regs)
            (combineTerm regs packedKernel basisKernel))
          store final ∧
      final (CombineValue.rangeRegisters regs).accumulator =
        NeighborhoodExecutableEvaluation.Residue.evaluateNode
          payloadWidth fanIn combine args outputChunk ∧
      CombineValue.RangePost .add
        (CombineValue.rangeRegisters regs)
        (NeighborhoodExecutableEvaluation.Residue.fieldModulus
          payloadWidth fanIn)
        (CombineValue.assignmentCount payloadWidth fanIn)
        (CombineValue.assignmentTerm
          payloadWidth fanIn combine args outputChunk)
        store final ∧
      ComputationContext regs instanceData tape slot interval
        logicalBank final :=
  Internal.evaluateNode_combineTerm_runsContext_internal
    regs instanceData tape slot interval logicalBank
    packedKernel basisKernel payloadWidth fanIn combine args
    outputChunk hpacked hbasis store hcontext
    hmodulusValue hmodulusPred hcount

/-- Specialized contextual outer fold for the genuine local computation
callback and the child rows represented by the catalytic bank. -/
theorem combineResidues_combineTerm_runsContext
    {tm : TM workTapeCount}
    (regs : NeighborhoodTrial.Registers controller)
    (instanceData : NeighborhoodProgram.ResidueInstance tm)
    (frame : NeighborhoodScheduler.Frame tm instanceData)
    (tape : TapeIndex workTapeCount)
    (slot : NeighborhoodGraph.Slot)
    (interval : ℕ)
    (logicalBank :
      NeighborhoodExecutableEvaluation.Residue.Registers
        tm instanceData.blockLength)
    (packedKernel basisKernel : Cmd)
    (outputChunk :
      Fin
        (PrimeGrouped.Logarithmic.chunkCount
          (NeighborhoodExecutableEvaluation.payloadWidth
            tm instanceData.blockLength)
          (NeighborhoodExecutableEvaluation.graphFanIn workTapeCount)))
    (hpacked :
      ComputationPackedKernelSpecAt regs instanceData frame tape slot
        interval logicalBank outputChunk packedKernel)
    (hbasis :
      ComputationBasisKernelSpecAt regs instanceData frame tape slot
        interval logicalBank basisKernel)
    (store : Store)
    (hcontext :
      ComputationFrameContext regs instanceData frame tape slot interval
        logicalBank store)
    (hcount :
      store (CombineValue.rangeRegisters regs).count =
        CombineValue.assignmentCount
          (NeighborhoodExecutableEvaluation.payloadWidth
            tm instanceData.blockLength)
          (NeighborhoodExecutableEvaluation.graphFanIn
            workTapeCount)) :
    ∃ final,
      Runs
          (CombineValue.rangeFold .add
            (CombineValue.rangeRegisters regs)
            (combineTerm regs packedKernel basisKernel))
          store final ∧
      final (CombineValue.rangeRegisters regs).accumulator =
        NeighborhoodExecutableEvaluation.combineResidues
          tm instanceData.x instanceData.blockLength
          instanceData.encoding instanceData.positive tape slot
          interval (computationArguments frame logicalBank)
          outputChunk ∧
      CombineValue.RangePost .add
        (CombineValue.rangeRegisters regs)
        (NeighborhoodExecutableEvaluation.Residue.fieldModulus
          (NeighborhoodExecutableEvaluation.payloadWidth
            tm instanceData.blockLength)
          (NeighborhoodExecutableEvaluation.graphFanIn workTapeCount))
        (CombineValue.assignmentCount
          (NeighborhoodExecutableEvaluation.payloadWidth
            tm instanceData.blockLength)
          (NeighborhoodExecutableEvaluation.graphFanIn workTapeCount))
        (CombineValue.assignmentTerm
          (NeighborhoodExecutableEvaluation.payloadWidth
            tm instanceData.blockLength)
          (NeighborhoodExecutableEvaluation.graphFanIn workTapeCount)
          (NeighborhoodExecutableEvaluation.booleanCombine
            tm instanceData.x instanceData.blockLength
            instanceData.encoding instanceData.positive tape slot
            interval)
          (computationArguments frame logicalBank)
          outputChunk)
        store final ∧
      ComputationFrameContext regs instanceData frame tape slot interval
        logicalBank final :=
  Internal.combineResidues_combineTerm_runsContext_internal
    regs instanceData frame tape slot interval logicalBank
    packedKernel basisKernel outputChunk hpacked hbasis
    store hcontext hcount

end CombineTerm
end NeighborhoodMicrocode
end Runtime
end TimeSpaceSimulation
end Complexity
