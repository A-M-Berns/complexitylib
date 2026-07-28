/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/
import
  Complexitylib.TimeSpaceSimulation.Runtime.NeighborhoodMicrocode.ResidueBankOps.Defs
import
  Complexitylib.TimeSpaceSimulation.Runtime.NeighborhoodMicrocode.ResidueBankOps.Internal

/-!
# Concrete catalytic residue-bank operations

This surface connects the shared neighborhood register layout to the verified
packed-bank primitives.  It exposes fixed-footprint commands, exact logical
residue semantics, and an all-program-point numeric invariant for streamed
whole-register scaling.
-/

namespace Complexity
namespace TimeSpaceSimulation
namespace Runtime
namespace NeighborhoodMicrocode
namespace ResidueBankOps

open RAM Structured

variable {controller : SearchProgram.Registers}

/-- Clearing the catalytic bank writes only inside the shared evaluator
layout. -/
theorem clearBank_writesWithin
    (regs : NeighborhoodTrial.Registers controller) :
    Footprint.CmdWritesWithin
      regs.layout.footprint (clearBank regs) :=
  Internal.clearBank_writesWithin_internal regs

/-- Bank initialization writes only inside the shared evaluator layout. -/
theorem initializeBank_writesWithin
    (regs : NeighborhoodTrial.Registers controller) :
    Footprint.CmdWritesWithin
      regs.layout.footprint (initializeBank regs) :=
  Internal.initializeBank_writesWithin_internal regs

/-- Active-register scaling writes only inside the shared evaluator layout. -/
theorem scaleActiveRegister_writesWithin
    (regs : NeighborhoodTrial.Registers controller) :
    Footprint.CmdWritesWithin
      regs.layout.footprint (scaleActiveRegister regs) :=
  Internal.scaleActiveRegister_writesWithin_internal regs

/-- One scaled-chunk update writes only inside the shared evaluator layout. -/
theorem addScaledActiveChunk_writesWithin
    (regs : NeighborhoodTrial.Registers controller) :
    Footprint.CmdWritesWithin
      regs.layout.footprint (addScaledActiveChunk regs) :=
  Internal.addScaledActiveChunk_writesWithin_internal regs

/-- One scaled-chunk update writes only inside its exact seventeen-register
residue-scaling view. -/
theorem addScaledActiveChunk_scaleWritesWithin
    (regs : NeighborhoodTrial.Registers controller) :
    Footprint.CmdWritesWithin
      (Layout.residueScaleRegisters regs).footprint
      (addScaledActiveChunk regs) :=
  Internal.addScaledActiveChunk_scaleWritesWithin_internal regs

/-- Bank initialization produces the all-zero logical catalytic bank while
preserving its radix. -/
theorem initializeBank_runs
    {workTapeCount : ℕ} (tm : TM workTapeCount)
    (blockLength base : ℕ)
    (regs : NeighborhoodTrial.Registers controller) (store : Store)
    (hbase :
      store
          (Layout.residueScaleRegisters regs).bank.bank.base =
        base) :
    ∃ final,
      Runs (initializeBank regs) store final ∧
      final
          (Layout.residueScaleRegisters regs).bank.bank.word =
        0 ∧
      final
          (Layout.residueScaleRegisters regs).bank.bank.one =
        1 ∧
      final
          (Layout.residueScaleRegisters regs).bank.bank.base =
        base ∧
      final
          (Layout.residueScaleRegisters regs).bank.bank.basePred =
        base - 1 ∧
      final
          (Layout.residueScaleRegisters regs).bank.bank.indexCount =
        0 ∧
      NeighborhoodProgram.RepresentsResidueBank
        tm blockLength base
          (final
            (Layout.residueScaleRegisters regs).bank.bank.word)
          (zeroRegisters tm blockLength) :=
  Internal.initializeBank_runs_internal
    tm blockLength base regs store hbase

/-- The streamed scaling command multiplies every chunk of the active
catalytic register by the preserved frame scalar. -/
theorem scaleActiveRegister_runs
    {workTapeCount : ℕ} (tm : TM workTapeCount)
    (blockLength scalar base word : ℕ)
    (original :
      NeighborhoodExecutableEvaluation.Residue.Registers
        tm blockLength)
    (register :
      Fin
        (NeighborhoodExecutableEvaluation.graphFanIn
          workTapeCount + 1))
    (regs : NeighborhoodTrial.Registers controller) (store : Store)
    (hbase : 0 < base)
    (hmodulus :
      0 < NeighborhoodExecutableEvaluation.modulus tm blockLength)
    (hmodulusBase :
      NeighborhoodExecutableEvaluation.modulus tm blockLength ≤ base)
    (hword :
      store
          (Layout.residueScaleRegisters regs).bank.bank.word =
        word)
    (hrep :
      NeighborhoodProgram.RepresentsResidueBank
        tm blockLength base word original)
    (hwordLt :
      word <
        base ^
          ((NeighborhoodExecutableEvaluation.graphFanIn
              workTapeCount + 1) *
            TreeEval.CookMertz.PrimeGrouped.Logarithmic.chunkCount
              (NeighborhoodExecutableEvaluation.payloadWidth
                tm blockLength)
              (NeighborhoodExecutableEvaluation.graphFanIn
                workTapeCount)))
    (hbaseValue :
      store
          (Layout.residueScaleRegisters regs).bank.bank.base =
        base)
    (hmodulusValue :
      store (Layout.residueScaleRegisters regs).bank.modulus =
        NeighborhoodExecutableEvaluation.modulus tm blockLength)
    (hmodulusPred :
      store (Layout.residueScaleRegisters regs).bank.modulusPred =
        NeighborhoodExecutableEvaluation.modulus tm blockLength - 1)
    (hscalar : store (Layout.scalar regs) = scalar)
    (hout : store (Layout.out regs) = register.val)
    (hchunkCount :
      store (Layout.chunkCount regs) =
        TreeEval.CookMertz.PrimeGrouped.Logarithmic.chunkCount
          (NeighborhoodExecutableEvaluation.payloadWidth tm blockLength)
          (NeighborhoodExecutableEvaluation.graphFanIn
            workTapeCount)) :
    ∃ final finalWord,
      Runs (scaleActiveRegister regs) store final ∧
      final
          (Layout.residueScaleRegisters regs).bank.bank.word =
        finalWord ∧
      NeighborhoodProgram.RepresentsResidueBank
        tm blockLength base finalWord
        (NeighborhoodExecutableEvaluation.Residue.scaleAt
          tm blockLength scalar original register) ∧
      finalWord <
        base ^
          ((NeighborhoodExecutableEvaluation.graphFanIn
              workTapeCount + 1) *
            TreeEval.CookMertz.PrimeGrouped.Logarithmic.chunkCount
              (NeighborhoodExecutableEvaluation.payloadWidth
                tm blockLength)
              (NeighborhoodExecutableEvaluation.graphFanIn
                workTapeCount)) ∧
      final
          (Layout.residueScaleRegisters regs).bank.bank.base =
        base ∧
      final
          (Layout.residueScaleRegisters regs).bank.bank.basePred =
        base - 1 ∧
      final
          (Layout.residueScaleRegisters regs).bank.bank.one =
        1 ∧
      final (Layout.residueScaleRegisters regs).bank.modulus =
        NeighborhoodExecutableEvaluation.modulus tm blockLength ∧
      final (Layout.residueScaleRegisters regs).bank.modulusPred =
        NeighborhoodExecutableEvaluation.modulus tm blockLength - 1 ∧
      final (Layout.residueScaleRegisters regs).bank.operand =
        scalar :=
  Internal.scaleActiveRegister_runs_internal
    tm blockLength scalar base word original register regs store
    hbase hmodulus hmodulusBase hword hrep hwordLt hbaseValue
    hmodulusValue hmodulusPred hscalar hout hchunkCount

/-- Whole-register scaling satisfies one numeric bound at every source and
compiled program point. -/
theorem scaleActiveRegister_invariantRuns
    {workTapeCount : ℕ} (tm : TM workTapeCount)
    (blockLength scalar base word : ℕ)
    (original :
      NeighborhoodExecutableEvaluation.Residue.Registers
        tm blockLength)
    (register :
      Fin
        (NeighborhoodExecutableEvaluation.graphFanIn
          workTapeCount + 1))
    (regs : NeighborhoodTrial.Registers controller)
    (allowed : Finset ℕ) (bound : ℕ) (store : Store)
    (hbase : 0 < base)
    (hmodulus :
      0 < NeighborhoodExecutableEvaluation.modulus tm blockLength)
    (hmodulusBase :
      NeighborhoodExecutableEvaluation.modulus tm blockLength ≤ base)
    (hword :
      store
          (Layout.residueScaleRegisters regs).bank.bank.word =
        word)
    (hrep :
      NeighborhoodProgram.RepresentsResidueBank
        tm blockLength base word original)
    (hwordLt :
      word <
        base ^
          ((NeighborhoodExecutableEvaluation.graphFanIn
              workTapeCount + 1) *
            TreeEval.CookMertz.PrimeGrouped.Logarithmic.chunkCount
              (NeighborhoodExecutableEvaluation.payloadWidth
                tm blockLength)
              (NeighborhoodExecutableEvaluation.graphFanIn
                workTapeCount)))
    (hbaseValue :
      store
          (Layout.residueScaleRegisters regs).bank.bank.base =
        base)
    (hmodulusValue :
      store (Layout.residueScaleRegisters regs).bank.modulus =
        NeighborhoodExecutableEvaluation.modulus tm blockLength)
    (hmodulusPred :
      store (Layout.residueScaleRegisters regs).bank.modulusPred =
        NeighborhoodExecutableEvaluation.modulus tm blockLength - 1)
    (hscalar : store (Layout.scalar regs) = scalar)
    (hout : store (Layout.out regs) = register.val)
    (hchunkCount :
      store (Layout.chunkCount regs) =
        TreeEval.CookMertz.PrimeGrouped.Logarithmic.chunkCount
          (NeighborhoodExecutableEvaluation.payloadWidth tm blockLength)
          (NeighborhoodExecutableEvaluation.graphFanIn
            workTapeCount))
    (hpackedBound :
      base ^
          ((NeighborhoodExecutableEvaluation.graphFanIn
              workTapeCount + 1) *
            TreeEval.CookMertz.PrimeGrouped.Logarithmic.chunkCount
              (NeighborhoodExecutableEvaluation.payloadWidth
                tm blockLength)
              (NeighborhoodExecutableEvaluation.graphFanIn
                workTapeCount)) ≤
        bound)
    (hbaseBound : base ≤ bound)
    (hdigitCountBound :
      (NeighborhoodExecutableEvaluation.graphFanIn
          workTapeCount + 1) *
          TreeEval.CookMertz.PrimeGrouped.Logarithmic.chunkCount
            (NeighborhoodExecutableEvaluation.payloadWidth
              tm blockLength)
            (NeighborhoodExecutableEvaluation.graphFanIn
              workTapeCount) ≤
        bound)
    (hscalarProductBound : base * scalar ≤ bound)
    (hindexProductBound :
      register.val *
          TreeEval.CookMertz.PrimeGrouped.Logarithmic.chunkCount
            (NeighborhoodExecutableEvaluation.payloadWidth
              tm blockLength)
            (NeighborhoodExecutableEvaluation.graphFanIn
              workTapeCount) ≤
        bound)
    (hstore :
      NeighborhoodProgram.ValuesWithin allowed bound store) :
    ∃ final finalWord steps,
      InvariantRuns
        (NeighborhoodProgram.ValuesWithin allowed bound)
        (scaleActiveRegister regs) store final steps ∧
      final
          (Layout.residueScaleRegisters regs).bank.bank.word =
        finalWord ∧
      NeighborhoodProgram.RepresentsResidueBank
        tm blockLength base finalWord
        (NeighborhoodExecutableEvaluation.Residue.scaleAt
          tm blockLength scalar original register) :=
  Internal.scaleActiveRegister_invariantRuns_internal
    tm blockLength scalar base word original register regs allowed
    bound store hbase hmodulus hmodulusBase hword hrep hwordLt
    hbaseValue hmodulusValue hmodulusPred hscalar hout hchunkCount
    hpackedBound hbaseBound hdigitCountBound hscalarProductBound
    hindexProductBound hstore

/-- One provider chunk is scaled modulo the field modulus and added at the
active row-major catalytic-bank coordinate. -/
theorem addScaledActiveChunk_runs
    {workTapeCount : ℕ} (tm : TM workTapeCount)
    (blockLength scalar base word value : ℕ)
    (original :
      NeighborhoodExecutableEvaluation.Residue.Registers
        tm blockLength)
    (register :
      Fin
        (NeighborhoodExecutableEvaluation.graphFanIn
          workTapeCount + 1))
    (chunk :
      Fin
        (TreeEval.CookMertz.PrimeGrouped.Logarithmic.chunkCount
          (NeighborhoodExecutableEvaluation.payloadWidth tm blockLength)
          (NeighborhoodExecutableEvaluation.graphFanIn
            workTapeCount)))
    (regs : NeighborhoodTrial.Registers controller) (store : Store)
    (hbase : 0 < base)
    (hmodulus :
      0 < NeighborhoodExecutableEvaluation.modulus tm blockLength)
    (hmodulusBase :
      NeighborhoodExecutableEvaluation.modulus tm blockLength ≤ base)
    (hword :
      store
          (Layout.residueScaleRegisters regs).bank.bank.word =
        word)
    (hrep :
      NeighborhoodProgram.RepresentsResidueBank
        tm blockLength base word original)
    (hbaseValue :
      store
          (Layout.residueScaleRegisters regs).bank.bank.base =
        base)
    (hmodulusValue :
      store (Layout.residueScaleRegisters regs).bank.modulus =
        NeighborhoodExecutableEvaluation.modulus tm blockLength)
    (hmodulusPred :
      store (Layout.residueScaleRegisters regs).bank.modulusPred =
        NeighborhoodExecutableEvaluation.modulus tm blockLength - 1)
    (hvalue :
      store (Layout.residueScaleRegisters regs).bank.operand = value)
    (hscalar : store (Layout.scalar regs) = scalar)
    (hout : store (Layout.out regs) = register.val)
    (hchunkCount :
      store (Layout.chunkCount regs) =
        TreeEval.CookMertz.PrimeGrouped.Logarithmic.chunkCount
          (NeighborhoodExecutableEvaluation.payloadWidth tm blockLength)
          (NeighborhoodExecutableEvaluation.graphFanIn
            workTapeCount))
    (hcursor : store (Layout.codecScratch regs) = chunk.val) :
    ∃ final,
      Runs (addScaledActiveChunk regs) store final ∧
      NeighborhoodProgram.RepresentsResidueBank
        tm blockLength base
        (final
          (Layout.residueScaleRegisters regs).bank.bank.word)
        (NeighborhoodProgram.updateResidueCoordinate
          tm blockLength original register chunk
          (NeighborhoodProgram.ResidueBankOp.add.apply
            (NeighborhoodExecutableEvaluation.modulus tm blockLength)
            (original register chunk)
            ((value * scalar) %
              NeighborhoodExecutableEvaluation.modulus
                tm blockLength))) ∧
      final
          (Layout.residueScaleRegisters regs).bank.bank.word =
        NeighborhoodProgram.replaceAt base word
          (NeighborhoodProgram.residueBankIndex
            tm blockLength register chunk)
          (NeighborhoodProgram.ResidueBankOp.add.apply
            (NeighborhoodExecutableEvaluation.modulus tm blockLength)
            (original register chunk)
            ((value * scalar) %
              NeighborhoodExecutableEvaluation.modulus
                tm blockLength)) ∧
      final
          (Layout.residueScaleRegisters regs).bank.bank.base =
        base ∧
      final (Layout.residueScaleRegisters regs).bank.modulus =
        NeighborhoodExecutableEvaluation.modulus tm blockLength ∧
      final (Layout.residueScaleRegisters regs).bank.modulusPred =
        NeighborhoodExecutableEvaluation.modulus tm blockLength - 1 :=
  Internal.addScaledActiveChunk_runs_internal
    tm blockLength scalar base word value original register chunk
    regs store hbase hmodulus hmodulusBase hword hrep hbaseValue
    hmodulusValue hmodulusPred hvalue hscalar hout hchunkCount
    hcursor

end ResidueBankOps
end NeighborhoodMicrocode
end Runtime
end TimeSpaceSimulation
end Complexity
