/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/
import
  Complexitylib.TimeSpaceSimulation.Runtime.NeighborhoodMicrocode.CombineValue.Defs
import
  Complexitylib.TimeSpaceSimulation.Runtime.NeighborhoodMicrocode.CombineValue.Internal
import Complexitylib.TreeEvaluation.CookMertz.PrimeField.Search

/-!
# Fixed-register range folds for local residue combination

This surface exposes a terminating modular sum/product loop, its exact
natural-residue semantics, its fixed write footprint, and its connection to
the executable grouped neighborhood evaluator.  The remaining lowering
boundary is explicit in `TermKernelSpec`: a caller must supply a command that
places the current range term in the fixed term register while preserving
the fold interface.
-/

namespace Complexity
namespace TimeSpaceSimulation
namespace Runtime
namespace NeighborhoodMicrocode
namespace CombineValue

open RAM Structured
open TreeEval CookMertz

variable {controller : SearchProgram.Registers}

/-- A prepared range fold terminates with the exact tail-recursive modular
fold value. -/
theorem rangeFoldFrom_runs
    (op : FoldOp) (regs : RangeRegisters)
    (termKernel : Cmd) (term : ℕ → ℕ)
    (hspec : TermKernelSpec regs termKernel term)
    (store : Store)
    (modulus count accumulator : ℕ)
    (hmodulus : 0 < modulus)
    (hremaining : store regs.remaining = count)
    (haccumulator : store regs.accumulator = accumulator)
    (hmodulusValue : store regs.modulus = modulus)
    (hmodulusPred : store regs.modulusPred = modulus - 1)
    (hone : store regs.one = 1) :
    ∃ final,
      Runs (rangeFoldFrom op regs termKernel) store final ∧
      RangeFromPost op regs modulus count accumulator term store final :=
  Internal.rangeFoldFrom_runs_internal op regs termKernel term hspec
    store modulus count accumulator hmodulus hremaining haccumulator
    hmodulusValue hmodulusPred hone

/-- A prepared range fold also accepts a term kernel whose contract assumes
the field interface already established by the fold. -/
theorem rangeFoldFrom_runsAt
    (op : FoldOp) (regs : RangeRegisters)
    (termKernel : Cmd) (term : ℕ → ℕ)
    (modulus count accumulator : ℕ)
    (hspec : TermKernelSpecAt regs termKernel modulus term)
    (store : Store)
    (hmodulus : 0 < modulus)
    (hremaining : store regs.remaining = count)
    (haccumulator : store regs.accumulator = accumulator)
    (hmodulusValue : store regs.modulus = modulus)
    (hmodulusPred : store regs.modulusPred = modulus - 1)
    (hone : store regs.one = 1) :
    ∃ final,
      Runs (rangeFoldFrom op regs termKernel) store final ∧
      RangeFromPost op regs modulus count accumulator term store final :=
  Internal.rangeFoldFrom_runsAt_internal op regs termKernel term
    modulus count accumulator hspec store hmodulus hremaining
    haccumulator hmodulusValue hmodulusPred hone

/-- A prepared range fold propagates any semantic store representation that
is insensitive to driver writes and explicitly preserved by its term
kernel. -/
theorem rangeFoldFrom_runsAtContext
    (op : FoldOp) (regs : RangeRegisters)
    (termKernel : Cmd) (term : ℕ → ℕ)
    (modulus count accumulator : ℕ)
    (context : Store → Prop)
    (hstable : StableUnderDriverWrites regs context)
    (hspec :
      TermKernelSpecAtContext regs termKernel modulus term context)
    (store : Store)
    (hmodulus : 0 < modulus)
    (hremaining : store regs.remaining = count)
    (haccumulator : store regs.accumulator = accumulator)
    (hmodulusValue : store regs.modulus = modulus)
    (hmodulusPred : store regs.modulusPred = modulus - 1)
    (hone : store regs.one = 1)
    (hcontext : context store) :
    ∃ final,
      Runs (rangeFoldFrom op regs termKernel) store final ∧
      RangeFromPost op regs modulus count accumulator term store final ∧
      context final :=
  Internal.rangeFoldFrom_runsAtContext_internal
    op regs termKernel term modulus count accumulator
    context hstable hspec store hmodulus hremaining
    haccumulator hmodulusValue hmodulusPred hone hcontext

/-- A fully initialized range fold terminates with the exact canonical
modular range value. -/
theorem rangeFold_runs
    (op : FoldOp) (regs : RangeRegisters)
    (termKernel : Cmd) (term : ℕ → ℕ)
    (hspec : TermKernelSpec regs termKernel term)
    (store : Store) (modulus count : ℕ)
    (hmodulus : 0 < modulus)
    (hmodulusValue : store regs.modulus = modulus)
    (hmodulusPred : store regs.modulusPred = modulus - 1)
    (hcount : store regs.count = count) :
    ∃ final,
      Runs (rangeFold op regs termKernel) store final ∧
      RangePost op regs modulus count term store final :=
  Internal.rangeFold_runs_internal op regs termKernel term hspec
    store modulus count hmodulus hmodulusValue hmodulusPred hcount

/-- A fully initialized fold supplies the runtime field invariants required
by a contextual modular term kernel. -/
theorem rangeFold_runsAt
    (op : FoldOp) (regs : RangeRegisters)
    (termKernel : Cmd) (term : ℕ → ℕ)
    (store : Store) (modulus count : ℕ)
    (hspec : TermKernelSpecAt regs termKernel modulus term)
    (hmodulus : 0 < modulus)
    (hmodulusValue : store regs.modulus = modulus)
    (hmodulusPred : store regs.modulusPred = modulus - 1)
    (hcount : store regs.count = count) :
    ∃ final,
      Runs (rangeFold op regs termKernel) store final ∧
      RangePost op regs modulus count term store final :=
  Internal.rangeFold_runsAt_internal op regs termKernel term store
    modulus count hspec hmodulus hmodulusValue hmodulusPred hcount

/-- A fully initialized range fold propagates a semantic store
representation through initialization, every concrete driver update, and
every context-preserving term invocation. -/
theorem rangeFold_runsAtContext
    (op : FoldOp) (regs : RangeRegisters)
    (termKernel : Cmd) (term : ℕ → ℕ)
    (store : Store) (modulus count : ℕ)
    (context : Store → Prop)
    (hstable : StableUnderDriverWrites regs context)
    (hspec :
      TermKernelSpecAtContext regs termKernel modulus term context)
    (hmodulus : 0 < modulus)
    (hmodulusValue : store regs.modulus = modulus)
    (hmodulusPred : store regs.modulusPred = modulus - 1)
    (hcount : store regs.count = count)
    (hcontext : context store) :
    ∃ final,
      Runs (rangeFold op regs termKernel) store final ∧
      RangePost op regs modulus count term store final ∧
      context final :=
  Internal.rangeFold_runsAtContext_internal
    op regs termKernel term store modulus count context
    hstable hspec hmodulus hmodulusValue hmodulusPred
    hcount hcontext

/-- Every mutable combine cell belongs to the shared neighborhood layout. -/
theorem combineScratchFootprint_subset_layout
    (regs : NeighborhoodTrial.Registers controller) :
    combineScratchFootprint regs ⊆ regs.layout.footprint :=
  Internal.combineScratchFootprint_subset_layout_internal regs

/-- The range driver and a conforming term kernel write only combine
scratch. -/
theorem rangeFold_writesWithin
    (op : FoldOp)
    (regs : NeighborhoodTrial.Registers controller)
    (termKernel : Cmd)
    (hkernel :
      RAM.Structured.Footprint.CmdWritesWithin
        (combineScratchFootprint regs) termKernel) :
    RAM.Structured.Footprint.CmdWritesWithin
      (combineScratchFootprint regs)
      (rangeFold op (rangeRegisters regs) termKernel) :=
  Internal.rangeFold_writesWithin_internal op regs termKernel hkernel

/-- The range driver and a conforming term kernel write within the shared
neighborhood layout. -/
theorem rangeFold_layout_writesWithin
    (op : FoldOp)
    (regs : NeighborhoodTrial.Registers controller)
    (termKernel : Cmd)
    (hkernel :
      RAM.Structured.Footprint.CmdWritesWithin
        (combineScratchFootprint regs) termKernel) :
    RAM.Structured.Footprint.CmdWritesWithin
      regs.layout.footprint
      (rangeFold op (rangeRegisters regs) termKernel) :=
  Internal.rangeFold_layout_writesWithin_internal
    op regs termKernel hkernel

/-- Any command confined to combine scratch preserves the active-frame and
parameter ABI. -/
theorem preservesABI_of_combineScratch
    (regs : NeighborhoodTrial.Registers controller)
    {command : Cmd}
    (hwrites :
      RAM.Structured.Footprint.CmdWritesWithin
        (combineScratchFootprint regs) command)
    {initial final : Store}
    (hrun : Runs command initial final) :
    ControlDecode.PreservesABI regs initial final :=
  Internal.preservesABI_of_combineScratch_internal regs hwrites hrun

/-- Every range-fold execution preserves the active-frame and parameter
ABI. -/
theorem rangeFold_preservesABI
    (op : FoldOp)
    (regs : NeighborhoodTrial.Registers controller)
    (termKernel : Cmd)
    (hkernel :
      RAM.Structured.Footprint.CmdWritesWithin
        (combineScratchFootprint regs) termKernel)
    {initial final : Store}
    (hrun :
      Runs (rangeFold op (rangeRegisters regs) termKernel)
        initial final) :
    ControlDecode.PreservesABI regs initial final :=
  Internal.rangeFold_preservesABI_internal
    op regs termKernel hkernel hrun

/-- The generic additive fold is exactly the executable residue sum. -/
theorem fold_add_eq_sumRange
    (modulus : ℕ) (term : ℕ → ℕ) (count : ℕ) :
    FoldOp.range .add modulus term count =
      NeighborhoodExecutableEvaluation.Residue.sumRange
        modulus term count :=
  Internal.fold_add_eq_sumRange_internal modulus term count

/-- The generic multiplicative fold is exactly the executable residue
product. -/
theorem fold_mul_eq_productRange
    (modulus : ℕ) (term : ℕ → ℕ) (count : ℕ) :
    FoldOp.range .mul modulus term count =
      NeighborhoodExecutableEvaluation.Residue.productRange
        modulus term count :=
  Internal.fold_mul_eq_productRange_internal modulus term count

/-- The pure additive range instantiated with assignment summands is exactly
the executable grouped Boolean-node evaluation. -/
theorem evaluateNode_eq_assignmentRange
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
        (PrimeGrouped.Logarithmic.chunkCount payloadWidth fanIn)) :
    NeighborhoodExecutableEvaluation.Residue.evaluateNode
        payloadWidth fanIn combine args outputChunk =
      FoldOp.range .add
        (NeighborhoodExecutableEvaluation.Residue.fieldModulus
          payloadWidth fanIn)
        (assignmentTerm payloadWidth fanIn combine args outputChunk)
        (assignmentCount payloadWidth fanIn) :=
  Internal.evaluateNode_eq_assignmentRange_internal
    payloadWidth fanIn combine args outputChunk

/-- The searched modulus used by every assignment fold is positive. -/
theorem fieldModulus_pos (payloadWidth fanIn : ℕ) :
    0 <
      NeighborhoodExecutableEvaluation.Residue.fieldModulus
        payloadWidth fanIn :=
  (PrimeField.Search.searchModulus_prime _).pos

/-- Given an exact first-order assignment-term command, the concrete
fixed-register range loop computes one coordinate of the executable grouped
Boolean-node evaluation and preserves the neighborhood ABI. -/
theorem evaluateNode_rangeFold_runs
    (regs : NeighborhoodTrial.Registers controller)
    (termKernel : Cmd)
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
    (hspec :
      CombineTermKernelSpecAt (rangeRegisters regs) termKernel
        payloadWidth fanIn combine args outputChunk)
    (hkernel :
      RAM.Structured.Footprint.CmdWritesWithin
        (combineScratchFootprint regs) termKernel)
    (store : Store)
    (hmodulusValue :
      store (rangeRegisters regs).modulus =
        NeighborhoodExecutableEvaluation.Residue.fieldModulus
          payloadWidth fanIn)
    (hmodulusPred :
      store (rangeRegisters regs).modulusPred =
        NeighborhoodExecutableEvaluation.Residue.fieldModulus
            payloadWidth fanIn -
          1)
    (hcount :
      store (rangeRegisters regs).count =
        assignmentCount payloadWidth fanIn) :
    ∃ final,
      Runs
          (rangeFold .add (rangeRegisters regs) termKernel)
          store final ∧
        final (rangeRegisters regs).accumulator =
          NeighborhoodExecutableEvaluation.Residue.evaluateNode
            payloadWidth fanIn combine args outputChunk ∧
        RangePost .add (rangeRegisters regs)
          (NeighborhoodExecutableEvaluation.Residue.fieldModulus
            payloadWidth fanIn)
          (assignmentCount payloadWidth fanIn)
          (assignmentTerm payloadWidth fanIn combine args outputChunk)
          store final ∧
        ControlDecode.PreservesABI regs store final :=
  Internal.evaluateNode_rangeFold_runs_internal
    regs termKernel payloadWidth fanIn combine args outputChunk hspec
    hkernel store (fieldModulus_pos payloadWidth fanIn)
    hmodulusValue hmodulusPred hcount

/-- One coordinate of `combineResidues` is exactly the additive assignment
range driven by this module. -/
theorem combineResidues_eq_assignmentRange
    (tm : TM workTapeCount) (x : List Bool)
    (blockLength : ℕ)
    (encoding :
      NeighborhoodExecutableEvaluation.FiniteEncoding tm blockLength)
    (hpositive : 0 < blockLength)
    (tape : TapeIndex workTapeCount)
    (slot : NeighborhoodGraph.Slot)
    (timeBlock : ℕ)
    (children :
      Fin
          (NeighborhoodExecutableEvaluation.graphFanIn workTapeCount) →
        NeighborhoodExecutableEvaluation.ResidueValue tm blockLength)
    (outputChunk :
      Fin
        (PrimeGrouped.Logarithmic.chunkCount
          (NeighborhoodExecutableEvaluation.payloadWidth tm blockLength)
          (NeighborhoodExecutableEvaluation.graphFanIn workTapeCount))) :
    NeighborhoodExecutableEvaluation.combineResidues
        tm x blockLength encoding hpositive tape slot timeBlock
        children outputChunk =
      FoldOp.range .add
        (NeighborhoodExecutableEvaluation.Residue.fieldModulus
          (NeighborhoodExecutableEvaluation.payloadWidth tm blockLength)
          (NeighborhoodExecutableEvaluation.graphFanIn workTapeCount))
        (assignmentTerm
          (NeighborhoodExecutableEvaluation.payloadWidth tm blockLength)
          (NeighborhoodExecutableEvaluation.graphFanIn workTapeCount)
          (NeighborhoodExecutableEvaluation.booleanCombine
            tm x blockLength encoding hpositive tape slot timeBlock)
          children outputChunk)
        (assignmentCount
          (NeighborhoodExecutableEvaluation.payloadWidth tm blockLength)
          (NeighborhoodExecutableEvaluation.graphFanIn workTapeCount)) := by
  simpa only [NeighborhoodExecutableEvaluation.combineResidues] using
    evaluateNode_eq_assignmentRange
      (NeighborhoodExecutableEvaluation.payloadWidth tm blockLength)
      (NeighborhoodExecutableEvaluation.graphFanIn workTapeCount)
      (NeighborhoodExecutableEvaluation.booleanCombine
        tm x blockLength encoding hpositive tape slot timeBlock)
      children outputChunk

/-- An exact assignment-term kernel closes the outer-sum layer of
`combineResidues`: the concrete range loop returns the requested residue
coordinate while preserving the neighborhood ABI. -/
theorem combineResidues_rangeFold_runs
    (regs : NeighborhoodTrial.Registers controller)
    (termKernel : Cmd)
    (tm : TM workTapeCount) (x : List Bool)
    (blockLength : ℕ)
    (encoding :
      NeighborhoodExecutableEvaluation.FiniteEncoding tm blockLength)
    (hpositive : 0 < blockLength)
    (tape : TapeIndex workTapeCount)
    (slot : NeighborhoodGraph.Slot)
    (timeBlock : ℕ)
    (children :
      Fin
          (NeighborhoodExecutableEvaluation.graphFanIn workTapeCount) →
        NeighborhoodExecutableEvaluation.ResidueValue tm blockLength)
    (outputChunk :
      Fin
        (PrimeGrouped.Logarithmic.chunkCount
          (NeighborhoodExecutableEvaluation.payloadWidth tm blockLength)
          (NeighborhoodExecutableEvaluation.graphFanIn workTapeCount)))
    (hspec :
      CombineTermKernelSpecAt (rangeRegisters regs) termKernel
        (NeighborhoodExecutableEvaluation.payloadWidth tm blockLength)
        (NeighborhoodExecutableEvaluation.graphFanIn workTapeCount)
        (NeighborhoodExecutableEvaluation.booleanCombine
          tm x blockLength encoding hpositive tape slot timeBlock)
        children outputChunk)
    (hkernel :
      RAM.Structured.Footprint.CmdWritesWithin
        (combineScratchFootprint regs) termKernel)
    (store : Store)
    (hmodulusValue :
      store (rangeRegisters regs).modulus =
        NeighborhoodExecutableEvaluation.Residue.fieldModulus
          (NeighborhoodExecutableEvaluation.payloadWidth tm blockLength)
          (NeighborhoodExecutableEvaluation.graphFanIn workTapeCount))
    (hmodulusPred :
      store (rangeRegisters regs).modulusPred =
        NeighborhoodExecutableEvaluation.Residue.fieldModulus
            (NeighborhoodExecutableEvaluation.payloadWidth tm blockLength)
            (NeighborhoodExecutableEvaluation.graphFanIn workTapeCount) -
          1)
    (hcount :
      store (rangeRegisters regs).count =
        assignmentCount
          (NeighborhoodExecutableEvaluation.payloadWidth tm blockLength)
          (NeighborhoodExecutableEvaluation.graphFanIn workTapeCount)) :
    ∃ final,
      Runs
          (rangeFold .add (rangeRegisters regs) termKernel)
          store final ∧
        final (rangeRegisters regs).accumulator =
          NeighborhoodExecutableEvaluation.combineResidues
            tm x blockLength encoding hpositive tape slot timeBlock
            children outputChunk ∧
        ControlDecode.PreservesABI regs store final := by
  obtain ⟨final, hrun, hvalue, _hpost, hpreserves⟩ :=
    evaluateNode_rangeFold_runs regs termKernel
      (NeighborhoodExecutableEvaluation.payloadWidth tm blockLength)
      (NeighborhoodExecutableEvaluation.graphFanIn workTapeCount)
      (NeighborhoodExecutableEvaluation.booleanCombine
        tm x blockLength encoding hpositive tape slot timeBlock)
      children outputChunk hspec hkernel store hmodulusValue
      hmodulusPred hcount
  refine ⟨final, hrun, ?_, hpreserves⟩
  simpa only [NeighborhoodExecutableEvaluation.combineResidues] using
    hvalue

end CombineValue
end NeighborhoodMicrocode
end Runtime
end TimeSpaceSimulation
end Complexity
