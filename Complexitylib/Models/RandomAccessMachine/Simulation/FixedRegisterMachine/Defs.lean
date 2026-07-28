/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/
import
  Complexitylib.Models.RandomAccessMachine.Simulation.RegisterStore.DenseOverlay.Footprint.Defs
import
  Complexitylib.Models.RandomAccessMachine.Simulation.RegisterStore.Machine.DenseInputLookup.Defs
import
  Complexitylib.Models.RandomAccessMachine.Simulation.RegisterStore.Machine.Program.Defs
import Complexitylib.Models.TuringMachine.Combinators.WorkBranch.Defs
import Complexitylib.Models.TuringMachine.Registers.RegisterOps
import Complexitylib.Models.TuringMachine.Subroutines.BinaryAddConst.Defs
import Complexitylib.Models.TuringMachine.Subroutines.BinaryCopy.Defs
import Complexitylib.Models.TuringMachine.Subroutines.BinaryLength.Defs
import Complexitylib.Models.TuringMachine.Subroutines.BinaryPred.Defs
import Complexitylib.Models.TuringMachine.Subroutines.BinaryRippleAdd.Defs
import Complexitylib.Models.TuringMachine.Subroutines.BinaryRippleSub.Defs
import Complexitylib.Models.TuringMachine.Subroutines.BinaryShiftMul.Defs
import Complexitylib.Models.TuringMachine.Subroutines.BinarySucc.Defs
import Complexitylib.Models.TuringMachine.Subroutines.ResetBinary.Defs

/-!
# Direct fixed-register RAM simulation -- definitions

This backend gives every register in one fixed program-dependent prefix its
own canonical binary work tape. Twelve additional tapes are shared by operand
loading, arithmetic, indirect-load dispatch, cleanup, and the fixed-program
controller. An indirect address
inside the prefix selects a register tape; a larger address falls back to the
immutable public-input bank.

The prefix may be much larger than the mutable footprint, but it is fixed with
the compiled program. Thus it changes only the constant number of work tapes,
not the asymptotic space bound.
-/

namespace Complexity
namespace RAM
namespace FixedRegisterMachine

open RegisterStore DenseOverlay
open DenseOverlay.FixedRegisters.Footprint

/-- One instruction contains no indirect store. -/
def InstrNoStore : Instr → Prop
  | .store _ _ => False
  | _ => True

/-- Every program-counter lookup is free of indirect stores, including the
out-of-range default halt instruction. -/
def ProgramNoStore (program : Program) : Prop :=
  ∀ (pc : ℕ), InstrNoStore ((program[pc]?).getD .halt)

/-- Every hardwired register operand of one instruction lies in the direct
work-tape prefix. Immediates and jump targets are finite-control data rather
than register addresses. -/
def InstrRegistersBelow (registerBound : ℕ) : Instr → Prop
  | .imm destination _ => destination < registerBound
  | .add destination source₀ source₁
  | .sub destination source₀ source₁
  | .mul destination source₀ source₁ =>
      destination < registerBound ∧ source₀ < registerBound ∧
        source₁ < registerBound
  | .load destination addressRegister =>
      destination < registerBound ∧ addressRegister < registerBound
  | .store addressRegister source =>
      addressRegister < registerBound ∧ source < registerBound
  | .jz source _ => source < registerBound
  | .jmp _ => True
  | .halt => True

/-- Every hardwired register operand in a program lies below one fixed bound. -/
def ProgramRegistersBelow (program : Program) (registerBound : ℕ) : Prop :=
  ∀ (pc : ℕ),
    InstrRegistersBelow registerBound ((program[pc]?).getD .halt)

/-- Hardwired register operands of one instruction. Jump targets and immediate
values are deliberately omitted because the compiler stores them in finite
control. -/
def instructionRegisters : Instr → List ℕ
  | .imm destination _ => [destination]
  | .add destination source₀ source₁
  | .sub destination source₀ source₁
  | .mul destination source₀ source₁ =>
      [destination, source₀, source₁]
  | .load destination addressRegister =>
      [destination, addressRegister]
  | .store addressRegister source =>
      [addressRegister, source]
  | .jz source _ => [source]
  | .jmp _ => []
  | .halt => []

/-- Finite list of all mutable-footprint addresses and hardwired operands that
need direct work tapes. -/
noncomputable def compilationRegisters
    (program : Program) (allowed : Finset ℕ) :
    List ℕ :=
  allowed.toList ++ program.flatMap instructionRegisters

/-- Automatically inferred exclusive bound for all direct register tapes. -/
noncomputable def compilationRegisterBound
    (program : Program) (allowed : Finset ℕ) : ℕ :=
  (compilationRegisters program allowed).foldr max 0 + 1

/-- Static hypotheses for the direct fixed-register compiler.

`writesWithin` supplies the finite mutable footprint, while `registerBound`
allocates a direct tape for every literal register and every mutable
destination. `noStore` is kept explicit even though it follows from the
write-footprint predicate, making the backend's semantic boundary auditable. -/
structure Spec (program : Program) where
  /-- Finite set of mutable direct destinations. -/
  allowed : Finset ℕ
  /-- Exclusive bound of directly allocated register tapes. -/
  registerBound : ℕ
  /-- The standard verdict/length register is mutable and directly allocated. -/
  zero_mem : 0 ∈ allowed
  /-- All writes are direct writes into the advertised footprint. -/
  writesWithin : ProgramWritesWithin program allowed
  /-- Indirect stores are absent. -/
  noStore : ProgramNoStore program
  /-- Every mutable address has a direct tape. -/
  allowed_lt : ∀ address ∈ allowed, address < registerBound
  /-- Every hardwired register operand has a direct tape. -/
  registersBelow : ProgramRegistersBelow program registerBound

/-- Twelve reusable scratch roles. The first six are exactly the multiplication
ABI; four more support countdowns, constants, equality flags, and copy
cleanup. The final two hold the bounded program counter and its dispatch copy.
Their widths are constants of the compiled program. -/
abbrev scratchCount : ℕ := 12

/-- A direct register machine has one tape per bounded register and twelve fixed
scratch tapes. -/
def workTapeCount {program : Program} (spec : Spec program) : ℕ :=
  spec.registerBound + scratchCount

/-- Tape holding one directly allocated register. -/
def registerTape {program : Program} (spec : Spec program)
    (address : ℕ) (haddress : address < spec.registerBound) :
    Fin (workTapeCount spec) :=
  Fin.castAdd scratchCount ⟨address, haddress⟩

/-- Tape holding one reusable scratch role. -/
def scratchTape {program : Program} (spec : Spec program)
    (slot : Fin scratchCount) : Fin (workTapeCount spec) :=
  Fin.natAdd spec.registerBound slot

/-- First operand or dynamic-address query. -/
def lhsTape {program : Program} (spec : Spec program) :
    Fin (workTapeCount spec) :=
  scratchTape spec 0

/-- Second operand or input-lookup countdown. -/
def rhsTape {program : Program} (spec : Spec program) :
    Fin (workTapeCount spec) :=
  scratchTape spec 1

/-- Arithmetic accumulator and lookup result. -/
def resultTape {program : Program} (spec : Spec program) :
    Fin (workTapeCount spec) :=
  scratchTape spec 2

/-- Multiplication shift tape. -/
def shiftTape {program : Program} (spec : Spec program) :
    Fin (workTapeCount spec) :=
  scratchTape spec 3

/-- First multiplication scratch tape. -/
def tmpTape {program : Program} (spec : Spec program) :
    Fin (workTapeCount spec) :=
  scratchTape spec 4

/-- Second multiplication scratch tape. -/
def dblTape {program : Program} (spec : Spec program) :
    Fin (workTapeCount spec) :=
  scratchTape spec 5

/-- Fixed-constant comparison tape. -/
def constantTape {program : Program} (spec : Spec program) :
    Fin (workTapeCount spec) :=
  scratchTape spec 6

/-- Equality flag used by indirect-load dispatch. -/
def equalTape {program : Program} (spec : Spec program) :
    Fin (workTapeCount spec) :=
  scratchTape spec 7

/-- Private counter used by dense public-input fallback. -/
def counterTape {program : Program} (spec : Spec program) :
    Fin (workTapeCount spec) :=
  scratchTape spec 8

/-- Zero scratch used by copies and fallback cleanup. -/
def copyScratchTape {program : Program} (spec : Spec program) :
    Fin (workTapeCount spec) :=
  scratchTape spec 9

/-- Canonical binary program counter. Its value is bounded by the fixed
program and hence contributes only a compiler-dependent constant. -/
def pcTape {program : Program} (spec : Spec program) :
    Fin (workTapeCount spec) :=
  scratchTape spec 10

/-- Decrementing selector used by the fixed finite dispatch tree. -/
def selectorTape {program : Program} (spec : Spec program) :
    Fin (workTapeCount spec) :=
  scratchTape spec 11

/-- The first six shared scratch tapes form the standard multiplier ABI. -/
def multiplicationABI {program : Program} (spec : Spec program) :
    TM.BinaryShiftMulABI (workTapeCount spec) where
  tape :=
    { toFun := fun slot =>
        scratchTape spec ⟨slot.val, by
          have := slot.isLt
          simp only [scratchCount]
          omega⟩
      inj' := by
        intro first second heq
        apply Fin.ext
        simpa [scratchTape, Fin.natAdd] using congrArg Fin.val heq }

/-- Finite dispatch result for an indirect address. Addresses inside the
direct prefix name a work tape; all larger addresses use the immutable-input
fallback. -/
abbrev ReadRoute (registerBound : ℕ) := Fin registerBound ⊕ Unit

/-- Route one runtime indirect address to a direct register tape or to the
immutable public-input bank. -/
def readRoute (registerBound address : ℕ) : ReadRoute registerBound :=
  if h : address < registerBound then .inl ⟨address, h⟩ else .inr ()

/-- Semantic value selected by the direct/fallback route. -/
def routedRead (input : List Bool) (snapshot : DenseOverlay.Snapshot)
    (registerBound address : ℕ) : ℕ :=
  match readRoute registerBound address with
  | .inl bounded => DenseOverlay.read input snapshot.overlay bounded.val
  | .inr _ => RAM.initRegs input address

/-- Canonical clean tape containing one natural number. -/
def natTape (value : ℕ) : Tape :=
  (Tape.init (value.bits.map Γ.ofBool)).move Dir3.right

/-- Saturate a finite-control accumulator at the direct-register bound. The
top element `bound` is the fallback sentinel. -/
def saturate (bound value : ℕ) : Fin (bound + 1) :=
  ⟨min value bound, by omega⟩

/-- Initial little-endian place value for the finite address decoder. -/
def initialPlace (bound : ℕ) : Fin (bound + 1) :=
  saturate bound 1

/-- Update the saturated decoded value after reading one little-endian bit. -/
def advanceValue (bound : ℕ) (value place : Fin (bound + 1))
    (bit : Bool) : Fin (bound + 1) :=
  saturate bound (value.val + if bit then place.val else 0)

/-- Double the saturated little-endian place value. -/
def advancePlace (bound : ℕ) (place : Fin (bound + 1)) :
    Fin (bound + 1) :=
  saturate bound (2 * place.val)

/-- Unsaturated little-endian numeric value of a Boolean list. -/
def littleEndianValue : List Bool → ℕ
  | [] => 0
  | bit :: bits =>
      (if bit then 1 else 0) + 2 * littleEndianValue bits

/-- One unsaturated arithmetic decoder step, used to specify the finite
saturated controller. -/
def decoderNatStep (state : ℕ × ℕ) (bit : Bool) : ℕ × ℕ :=
  (state.1 + if bit then state.2 else 0, 2 * state.2)

/-- One finite-control saturated decoder step. -/
def decoderStep (bound : ℕ)
    (state : Fin (bound + 1) × Fin (bound + 1)) (bit : Bool) :
    Fin (bound + 1) × Fin (bound + 1) :=
  (advanceValue bound state.1 state.2 bit,
    advancePlace bound state.2)

/-- Finite-control state obtained after scanning a little-endian bit list. -/
def decoderState (bound : ℕ) (bits : List Bool) :
    Fin (bound + 1) × Fin (bound + 1) :=
  bits.foldl (decoderStep bound)
    (saturate bound 0, initialPlace bound)

/-- Direct branch selected after finite-control address decoding. The query
head is first rewound; the selected direct register is then copied into the
shared result tape. -/
def directReadBranchTM {program : Program} (spec : Spec program)
    (address : Fin spec.registerBound) : TM (workTapeCount spec) :=
  TM.seqTM (TM.rewindWorkTM (lhsTape spec))
    (TM.binaryCopyIntoTM
      (registerTape spec address.val address.isLt)
      (resultTape spec) (copyScratchTape spec))

/-- Fallback branch selected by the saturation sentinel. The query head is
first rewound, then the immutable input bank is scanned exactly once. -/
def fallbackReadBranchTM {program : Program} (spec : Spec program) :
    TM (workTapeCount spec) :=
  TM.seqTM (TM.rewindWorkTM (lhsTape spec))
    (Machine.denseInputLookupTM
      (lhsTape spec) (counterTape spec) (resultTape spec)
      (copyScratchTape spec))

/-- Common state type of all direct-copy branches. Work-tape indices affect
transitions but not the finite state type of the composed copy routine. -/
abbrev DirectReadBranchState {program : Program} (spec : Spec program) :=
  (TM.seqTM (TM.rewindWorkTM (lhsTape spec))
    (TM.binaryCopyIntoTM
      (lhsTape spec) (resultTape spec) (copyScratchTape spec))).Q

/-- State type of the immutable-input fallback branch. -/
abbrev FallbackReadBranchState {program : Program} (spec : Spec program) :=
  (fallbackReadBranchTM spec).Q

/-- Finite-control phases of dynamic indirect-read dispatch:

* a saturated little-endian decoder;
* one selected direct-copy branch;
* the immutable-input fallback branch; or
* the common halt state. -/
abbrev ReadDispatchState {program : Program} (spec : Spec program) :=
  (Fin (spec.registerBound + 1) × Fin (spec.registerBound + 1)) ⊕
    ((Fin spec.registerBound × DirectReadBranchState spec) ⊕
      (FallbackReadBranchState spec ⊕ Unit))

@[reducible]
private def productFintype (α β : Type)
    [DecidableEq α] [DecidableEq β] [Fintype α] [Fintype β] :
    Fintype (α × β) where
  elems := (Fintype.elems : Finset α) ×ˢ (Fintype.elems : Finset β)
  complete := by
    intro pair
    rcases pair with ⟨first, second⟩
    exact Finset.mem_product.mpr
      ⟨Fintype.complete first, Fintype.complete second⟩

/-- Decode the canonical query on `lhsTape` in finite control. Values below
the fixed bound select their direct register tape. The saturation sentinel
selects an immutable-input lookup. Both branches restore the query head and
finish with the decoded value on `resultTape`.

This scanner is retained as the one-pass finite-control implementation. The
proved compiler below uses the extensionally equivalent decrementing branch
tree `readDispatchTM`, whose composition proof reuses the standard binary
subroutine contracts. -/
def readDispatchScannerTM {program : Program} (spec : Spec program) :
    TM (workTapeCount spec) :=
  let directPrototype :=
    TM.seqTM (TM.rewindWorkTM (lhsTape spec))
      (TM.binaryCopyIntoTM
        (lhsTape spec) (resultTape spec) (copyScratchTape spec))
  let fallback := fallbackReadBranchTM spec
  letI : Fintype (DirectReadBranchState spec) := directPrototype.finQ
  letI : DecidableEq (DirectReadBranchState spec) := directPrototype.decEq
  letI : Fintype (FallbackReadBranchState spec) := fallback.finQ
  letI : DecidableEq (FallbackReadBranchState spec) := fallback.decEq
  letI : Fintype
      (Fin (spec.registerBound + 1) × Fin (spec.registerBound + 1)) :=
    productFintype _ _
  letI : Fintype
      (Fin spec.registerBound × DirectReadBranchState spec) :=
    productFintype _ _
  { Q := ReadDispatchState spec
    qstart := .inl (saturate spec.registerBound 0,
      initialPlace spec.registerBound)
    qhalt := .inr (.inr (.inr ()))
    δ := fun state iHead wHeads oHead =>
      match state with
      | .inl (value, place) =>
          if wHeads (lhsTape spec) = Γ.blank then
            let nextState : ReadDispatchState spec :=
              if hvalue : value.val < spec.registerBound then
                .inr (.inl (⟨value.val, hvalue⟩,
                  (directReadBranchTM spec ⟨value.val, hvalue⟩).qstart))
              else
                .inr (.inr (.inl fallback.qstart))
            (nextState, fun i => TM.readBackWrite (wHeads i),
              TM.readBackWrite oHead, TM.idleDir iHead,
              fun i => TM.idleDir (wHeads i), TM.idleDir oHead)
          else
            let bit := wHeads (lhsTape spec) = Γ.one
            (.inl
                (advanceValue spec.registerBound value place bit,
                  advancePlace spec.registerBound place),
              fun i => TM.readBackWrite (wHeads i),
              TM.readBackWrite oHead, TM.idleDir iHead,
              fun i =>
                if i = lhsTape spec then Dir3.right
                else TM.idleDir (wHeads i),
              TM.idleDir oHead)
      | .inr (.inl (address, branchState)) =>
          let branch := directReadBranchTM spec address
          if branchState = branch.qhalt then
            (.inr (.inr (.inr ())),
              fun i => TM.readBackWrite (wHeads i),
              TM.readBackWrite oHead, TM.idleDir iHead,
              fun i => TM.idleDir (wHeads i), TM.idleDir oHead)
          else
            let (nextState, workWrites, outputWrite, inputDir, workDirs,
                outputDir) :=
              branch.δ branchState iHead wHeads oHead
            (.inr (.inl (address, nextState)), workWrites, outputWrite,
              inputDir, workDirs, outputDir)
      | .inr (.inr (.inl branchState)) =>
          if branchState = fallback.qhalt then
            (.inr (.inr (.inr ())),
              fun i => TM.readBackWrite (wHeads i),
              TM.readBackWrite oHead, TM.idleDir iHead,
              fun i => TM.idleDir (wHeads i), TM.idleDir oHead)
          else
            let (nextState, workWrites, outputWrite, inputDir, workDirs,
                outputDir) :=
              fallback.δ branchState iHead wHeads oHead
            (.inr (.inr (.inl nextState)), workWrites, outputWrite,
              inputDir, workDirs, outputDir)
      | .inr (.inr (.inr _)) =>
          TM.allIdle (.inr (.inr (.inr ()))) iHead wHeads oHead
    δ_right_of_start := by
      intro state iHead wHeads oHead
      rcases state with decoder | branch
      · rcases decoder with ⟨value, place⟩
        dsimp only
        split
        · exact ⟨TM.idleDir_right_of_start,
            fun _ => TM.idleDir_right_of_start,
            TM.idleDir_right_of_start⟩
        · refine ⟨TM.idleDir_right_of_start, ?_,
            TM.idleDir_right_of_start⟩
          intro i hstart
          by_cases hi : i = lhsTape spec
          · simp [hi]
          · simp [hi, TM.idleDir_right_of_start hstart]
      · rcases branch with direct | fallbackOrDone
        · rcases direct with ⟨address, branchState⟩
          dsimp only
          split
          · exact ⟨TM.idleDir_right_of_start,
              fun _ => TM.idleDir_right_of_start,
              TM.idleDir_right_of_start⟩
          · exact
              (directReadBranchTM spec address).δ_right_of_start
                branchState iHead wHeads oHead
        · rcases fallbackOrDone with fallbackState | done
          · dsimp only
            split
            · exact ⟨TM.idleDir_right_of_start,
                fun _ => TM.idleDir_right_of_start,
                TM.idleDir_right_of_start⟩
            · exact fallback.δ_right_of_start fallbackState iHead wHeads oHead
          · exact TM.rightOfStart_allIdle iHead wHeads oHead }

/-- Direct-copy leaf for the decrementing branch tree. Unlike the one-pass
scanner leaf, the preserved query is already parked and needs no rewind. -/
def directReadTreeBranchTM {program : Program} (spec : Spec program)
    (address : Fin spec.registerBound) : TM (workTapeCount spec) :=
  TM.binaryCopyIntoTM
    (registerTape spec address.val address.isLt)
    (resultTape spec) (copyScratchTape spec)

/-- Immutable-input leaf for the decrementing branch tree. The preserved query
remains parked throughout selector dispatch. -/
def fallbackReadTreeBranchTM {program : Program} (spec : Spec program) :
    TM (workTapeCount spec) :=
  Machine.denseInputLookupTM
    (lhsTape spec) (counterTape spec) (resultTape spec)
    (copyScratchTape spec)

/-- Fixed branch tree for dynamic reads. `remaining` direct addresses starting
at `base` are tested in order. The selector is decremented at each miss; after
all direct addresses are exhausted it is reset before the immutable-input
fallback. -/
def readDispatchTreeTM {program : Program} (spec : Spec program) :
    (remaining base : ℕ) → base + remaining = spec.registerBound →
      TM (workTapeCount spec)
  | 0, _base, _hbound =>
      TM.seqTM (TM.resetBinaryWorkTM (selectorTape spec))
        (fallbackReadTreeBranchTM spec)
  | remaining + 1, base, hbound =>
      have hbase : base < spec.registerBound := by omega
      TM.branchWorkBlankTM (selectorTape spec)
        (directReadTreeBranchTM spec ⟨base, hbase⟩)
        (TM.seqTM (TM.binaryPredTM (selectorTape spec))
          (readDispatchTreeTM spec remaining (base + 1) (by omega)))

/-- Copy the canonical runtime query to selector scratch, then use a fixed
program-dependent branch tree to choose a direct register tape or the
immutable-input fallback. The original query is preserved. -/
def readDispatchTM {program : Program} (spec : Spec program) :
    TM (workTapeCount spec) :=
  TM.seqTM
    (TM.binaryCopyIntoTM
      (lhsTape spec) (selectorTape spec) (copyScratchTape spec))
    (readDispatchTreeTM spec spec.registerBound 0 (by omega))

/-- Arithmetic operation selected by one direct three-address RAM
instruction. -/
inductive BinaryOp where
  | add
  | sub
  | mul
  deriving DecidableEq

instance : Fintype BinaryOp where
  elems := {.add, .sub, .mul}
  complete := fun op => by cases op <;> simp

/-- Replace one canonical binary work tape by a fixed natural number. -/
def setNatTM {n : ℕ} (idx : Fin n) (value : ℕ) : TM n :=
  TM.seqTM (TM.resetBinaryWorkTM idx) (TM.binaryAddConstTM idx value)

/-- Arithmetic kernel over the six shared multiplication-ABI tapes. -/
def binaryArithmeticTM {program : Program} (spec : Spec program) :
    BinaryOp → TM (workTapeCount spec)
  | .add => TM.binaryRippleAddTM
      (lhsTape spec) (rhsTape spec) (resultTape spec)
  | .sub => TM.binaryRippleSubTM
      (lhsTape spec) (rhsTape spec) (resultTape spec)
  | .mul => TM.binaryShiftMulTM (multiplicationABI spec)

/-- Copy both direct operands to scratch, evaluate one arithmetic operation,
copy the result to its direct destination, and restore the three live scratch
tapes to zero. Literal source/destination aliasing is harmless because both
sources are copied before the destination is replaced. -/
def binaryInstructionTM {program : Program} (spec : Spec program)
    (op : BinaryOp)
    (destination source₀ source₁ : ℕ)
    (hdestination : destination < spec.registerBound)
    (hsource₀ : source₀ < spec.registerBound)
    (hsource₁ : source₁ < spec.registerBound) :
    TM (workTapeCount spec) :=
  TM.seqTM
    (TM.binaryCopyIntoTM
      (registerTape spec source₀ hsource₀)
      (lhsTape spec) (copyScratchTape spec))
    (TM.seqTM
      (TM.binaryCopyIntoTM
        (registerTape spec source₁ hsource₁)
        (rhsTape spec) (copyScratchTape spec))
      (TM.seqTM
        (binaryArithmeticTM spec op)
        (TM.seqTM
          (TM.binaryCopyIntoTM
            (resultTape spec)
            (registerTape spec destination hdestination)
            (copyScratchTape spec))
          (TM.seqTM
            (TM.resetBinaryWorkTM (lhsTape spec))
            (TM.seqTM
              (TM.resetBinaryWorkTM (rhsTape spec))
              (TM.resetBinaryWorkTM (resultTape spec)))))))

/-- Direct indirect-load kernel. The address register is copied to the query
tape, finite dispatch returns the routed value, the result replaces the
destination, and all live scratch is reset. -/
def loadInstructionTM {program : Program} (spec : Spec program)
    (destination addressRegister : ℕ)
    (hdestination : destination < spec.registerBound)
    (haddressRegister : addressRegister < spec.registerBound) :
    TM (workTapeCount spec) :=
  TM.seqTM
    (TM.binaryCopyIntoTM
      (registerTape spec addressRegister haddressRegister)
      (lhsTape spec) (copyScratchTape spec))
    (TM.seqTM
      (readDispatchTM spec)
      (TM.seqTM
        (TM.binaryCopyIntoTM
          (resultTape spec)
          (registerTape spec destination hdestination)
          (copyScratchTape spec))
        (TM.seqTM
          (TM.resetBinaryWorkTM (lhsTape spec))
          (TM.resetBinaryWorkTM (resultTape spec)))))

/-- Execute a statically selected direct instruction and update the canonical
program-counter tape. The impossible indirect-store case is a no-op; semantic
theorems discharge it from `Spec.noStore`. -/
def executeInstructionTM {program : Program} (spec : Spec program)
    (instruction : Instr) : TM (workTapeCount spec) :=
  match instruction with
  | .imm destination value =>
      if hdestination : destination < spec.registerBound then
        TM.seqTM
          (setNatTM
            (registerTape spec destination hdestination) value)
          (TM.binarySuccTM (pcTape spec))
      else TM.skipTM
  | .add destination source₀ source₁ =>
      if hdestination : destination < spec.registerBound then
        if hsource₀ : source₀ < spec.registerBound then
          if hsource₁ : source₁ < spec.registerBound then
            TM.seqTM
              (binaryInstructionTM spec .add destination source₀ source₁
                hdestination hsource₀ hsource₁)
              (TM.binarySuccTM (pcTape spec))
          else TM.skipTM
        else TM.skipTM
      else TM.skipTM
  | .sub destination source₀ source₁ =>
      if hdestination : destination < spec.registerBound then
        if hsource₀ : source₀ < spec.registerBound then
          if hsource₁ : source₁ < spec.registerBound then
            TM.seqTM
              (binaryInstructionTM spec .sub destination source₀ source₁
                hdestination hsource₀ hsource₁)
              (TM.binarySuccTM (pcTape spec))
          else TM.skipTM
        else TM.skipTM
      else TM.skipTM
  | .mul destination source₀ source₁ =>
      if hdestination : destination < spec.registerBound then
        if hsource₀ : source₀ < spec.registerBound then
          if hsource₁ : source₁ < spec.registerBound then
            TM.seqTM
              (binaryInstructionTM spec .mul destination source₀ source₁
                hdestination hsource₀ hsource₁)
              (TM.binarySuccTM (pcTape spec))
          else TM.skipTM
        else TM.skipTM
      else TM.skipTM
  | .load destination addressRegister =>
      if hdestination : destination < spec.registerBound then
        if haddressRegister : addressRegister < spec.registerBound then
          TM.seqTM
            (loadInstructionTM spec destination addressRegister
              hdestination haddressRegister)
            (TM.binarySuccTM (pcTape spec))
        else TM.skipTM
      else TM.skipTM
  | .store _ _ => TM.skipTM
  | .jz source target =>
      if hsource : source < spec.registerBound then
        TM.branchWorkBlankTM
          (registerTape spec source hsource)
          (setNatTM (pcTape spec) target)
          (TM.binarySuccTM (pcTape spec))
      else TM.skipTM
  | .jmp target => setNatTM (pcTape spec) target
  | .halt => TM.skipTM

/-- Decrementing finite branch tree selected by the canonical selector tape. -/
def dispatchProgramTM {program : Program} (spec : Spec program) :
    Program → TM (workTapeCount spec)
  | [] =>
      TM.seqTM (TM.resetBinaryWorkTM (selectorTape spec))
        (executeInstructionTM spec .halt)
  | instruction :: tail =>
      TM.branchWorkBlankTM (selectorTape spec)
        (executeInstructionTM spec instruction)
        (TM.seqTM (TM.binaryPredTM (selectorTape spec))
          (dispatchProgramTM spec tail))

/-- Copy the bounded program counter into selector scratch and execute one
fixed-program instruction. -/
def programStepTM {program : Program} (spec : Spec program) :
    TM (workTapeCount spec) :=
  TM.seqTM
    (TM.binaryCopyIntoTM
      (pcTape spec) (selectorTape spec) (copyScratchTape spec))
    (dispatchProgramTM spec program)

/-- Two-state leaf that writes whether one statically selected instruction is
`halt`. -/
inductive HaltVerdictPhase where
  | write
  | done
  deriving DecidableEq

instance : Fintype HaltVerdictPhase where
  elems := {.write, .done}
  complete := fun state => by cases state <;> simp

/-- Emit one exactly when the selected instruction is `halt`, and restore the
blank-output ABI otherwise. -/
def instructionHaltVerdictTM {n : ℕ} (instruction : Instr) : TM n where
  Q := HaltVerdictPhase
  qstart := .write
  qhalt := .done
  δ := fun state iHead wHeads oHead =>
    match state with
    | .write =>
        (.done, fun i => TM.readBackWrite (wHeads i),
          if instruction = .halt then .one else .blank,
          TM.idleDir iHead, fun i => TM.idleDir (wHeads i),
          TM.idleDir oHead)
    | .done => TM.allIdle .done iHead wHeads oHead
  δ_right_of_start := by
    intro state iHead wHeads oHead
    cases state <;> exact TM.rightOfStart_allIdle iHead wHeads oHead

/-- Decrementing fixed-program dispatch for the halt test. -/
def dispatchHaltTM {program : Program} (spec : Spec program) :
    Program → TM (workTapeCount spec)
  | [] =>
      TM.seqTM (TM.resetBinaryWorkTM (selectorTape spec))
        (instructionHaltVerdictTM .halt)
  | instruction :: tail =>
      TM.branchWorkBlankTM (selectorTape spec)
        (instructionHaltVerdictTM instruction)
        (TM.seqTM (TM.binaryPredTM (selectorTape spec))
          (dispatchHaltTM spec tail))

/-- Copy the program counter into selector scratch and test the selected fixed
instruction for halting. -/
def programHaltTM {program : Program} (spec : Spec program) :
    TM (workTapeCount spec) :=
  TM.seqTM
    (TM.binaryCopyIntoTM
      (pcTape spec) (selectorTape spec) (copyScratchTape spec))
    (dispatchHaltTM spec program)

/-- Halt-aware fixed-program controller. -/
def programLoopTM {program : Program} (spec : Spec program) :
    TM (workTapeCount spec) :=
  TM.loopTM (programStepTM spec) (programHaltTM spec)

/-- Emit the direct R0 verdict, writing zero exactly for RAM value zero and
one for every nonzero value. -/
def programOutputTM {program : Program} (spec : Spec program) :
    TM (workTapeCount spec) :=
  Machine.registerVerdictTM
    (registerTape spec 0 (spec.allowed_lt 0 spec.zero_mem))

/-- Fixed-prefix initialization pass after `binaryLengthTM` has populated R0
and `rewindInputTM` has restored the public input head. At finite-control
address `i`, it writes input bit `i - 1` into direct register `i`. Once the
input ends, later bounded registers receive canonical zero. -/
def prefixInitTM {program : Program} (spec : Spec program) :
    TM (workTapeCount spec) where
  Q := Fin (spec.registerBound + 1)
  qstart := saturate spec.registerBound 1
  qhalt := saturate spec.registerBound spec.registerBound
  δ := fun state iHead wHeads oHead =>
    if hstate : state.val < spec.registerBound then
      (saturate spec.registerBound (state.val + 1),
        fun i =>
          if i = registerTape spec state.val hstate then
            if iHead = Γ.one then Γw.one else Γw.blank
          else TM.readBackWrite (wHeads i),
        TM.readBackWrite oHead,
        if iHead = Γ.zero ∨ iHead = Γ.one then
          Dir3.right
        else TM.idleDir iHead,
        fun i => TM.idleDir (wHeads i),
        TM.idleDir oHead)
    else TM.allIdle (saturate spec.registerBound spec.registerBound)
      iHead wHeads oHead
  δ_right_of_start := by
    intro state iHead wHeads oHead
    dsimp only
    split
    · refine ⟨?_, fun _ => TM.idleDir_right_of_start,
        TM.idleDir_right_of_start⟩
      split
      · intro hstart
        rcases ‹iHead = Γ.zero ∨ iHead = Γ.one› with hzero | hone
        · rw [hstart] at hzero
        · rw [hstart] at hone
      · exact TM.idleDir_right_of_start
    · exact TM.rightOfStart_allIdle iHead wHeads oHead

/-- Concrete blank-work-tape initializer for the direct representation:

1. compute the public input length into direct R0;
2. rewind the immutable input;
3. materialize input bits in direct R1 through R(`registerBound - 1`).

All remaining work tapes stay canonical zero. -/
def initializeTM {program : Program} (spec : Spec program) :
    TM (workTapeCount spec) :=
  TM.seqTM (TM.binaryLengthTM
      (registerTape spec 0
        (spec.allowed_lt 0 spec.zero_mem)))
    (TM.seqTM TM.rewindInputTM (prefixInitTM spec))

/-- Concrete initialization followed by one final rewind to the execution
boundary at input cell one. -/
def executionInitializeTM {program : Program} (spec : Spec program) :
    TM (workTapeCount spec) :=
  TM.seqTM (initializeTM spec) TM.rewindInputTM

/-- Complete direct-register compiler: initialize, execute until the selected
RAM instruction is halt, then emit the Boolean verdict from R0. -/
def programTM {program : Program} (spec : Spec program) :
    TM (workTapeCount spec) :=
  TM.seqTM (executionInitializeTM spec)
    (TM.seqTM (programLoopTM spec) (programOutputTM spec))

/-- Exact number of fixed-prefix materialization transitions. -/
def prefixInitTime {program : Program} (spec : Spec program) : ℕ :=
  spec.registerBound - 1

/-- Exact composed runtime of the concrete direct-register initializer. -/
def initializeTime {program : Program} (spec : Spec program)
    (inputLength : ℕ) : ℕ :=
  TM.binaryLengthTime inputLength + 1 +
    (inputLength + 3 + 1 + prefixInitTime spec)

/-- Sharp auxiliary-space budget of the direct-register initializer. The
input rewind and fixed-prefix materialization do not charge elapsed scan
time; the logarithmic length counter is the only growing workspace. -/
@[nolint unusedArguments]
def initializeSpace {program : Program} (_spec : Spec program)
    (inputLength : ℕ) : ℕ :=
  max (TM.binaryLengthSpace inputLength) 1

/-- Register value after the first `processed` positive addresses have been
materialized. R0 already contains the input length. -/
def prefixInitValue (input : List Bool) (address processed : ℕ) : ℕ :=
  if address = 0 then input.length
  else if address ≤ processed then RAM.initRegs input address
  else 0

/-- Canonical intermediate work image for the fixed-prefix initializer. -/
def prefixInitWork {program : Program} (spec : Spec program)
    (input : List Bool) (processed : ℕ) :
    Fin (workTapeCount spec) → Tape :=
  fun i =>
    if _h : i.val < spec.registerBound then
      natTape (prefixInitValue input i.val processed)
    else natTape 0

/-- Immutable input tape after materializing `processed` positive addresses.
The head stops at the first trailing blank. -/
def prefixInitInput (input : List Bool) (processed : ℕ) : Tape :=
  { head := min (processed + 1) (input.length + 1)
    cells := (Tape.init (input.map Γ.ofBool)).cells }

/-- Canonical initializer configuration after `processed` positive
registers. -/
def prefixInitCfg {program : Program} (spec : Spec program)
    (input : List Bool) (processed : ℕ) :
    Complexity.Cfg (workTapeCount spec) (prefixInitTM spec).Q :=
  { state := saturate spec.registerBound (processed + 1)
    input := prefixInitInput input processed
    work := prefixInitWork spec input processed
    output := natTape 0 }

/-- Boundary representation of a dense-overlay snapshot by direct register
tapes. Every scratch tape is canonical zero and every work head is parked. -/
structure Ready {program : Program} (spec : Spec program)
    (input : List Bool) (snapshot : DenseOverlay.Snapshot)
    (work : Fin (workTapeCount spec) → Tape) : Prop where
  /-- Every bounded register tape stores its decoded RAM value. -/
  register : ∀ (address : ℕ) (haddress : address < spec.registerBound),
    (work (registerTape spec address haddress)).HasBinaryNat
      (DenseOverlay.read input snapshot.overlay address)
  /-- Every reusable scratch tape is zero. -/
  scratch : ∀ slot,
    (work (scratchTape spec slot)).HasBinaryNat 0
  /-- All direct and scratch tapes are parked at a reusable boundary. -/
  parked : ∀ i, TM.Parked (work i)

/-- Canonical direct-register work image of one semantic snapshot.

This is a representation function used to state instruction boundaries. It is
not an executable initializer from the standard blank-work-tape TM start
configuration; the compiler's initialization phase must establish this image
explicitly. -/
def snapshotWork {program : Program} (spec : Spec program)
    (input : List Bool) (snapshot : DenseOverlay.Snapshot) :
    Fin (workTapeCount spec) → Tape :=
  fun i =>
    if _h : i.val < spec.registerBound then
      natTape (DenseOverlay.read input snapshot.overlay i.val)
    else natTape 0

/-- Exact parked work image at a compiled-program iteration boundary. Direct
register tapes represent the dense snapshot, the program-counter tape stores
`snapshot.pc`, and every other scratch tape is canonical zero. -/
def executionWork {program : Program} (spec : Spec program)
    (input : List Bool) (snapshot : DenseOverlay.Snapshot) :
    Fin (workTapeCount spec) → Tape :=
  Function.update (snapshotWork spec input snapshot) (pcTape spec)
    (natTape snapshot.pc)

/-- Canonical parked public-input tape used throughout compiled execution. -/
def executionInput (input : List Bool) : Tape :=
  (Tape.init (input.map Γ.ofBool)).move Dir3.right

/-- Reusable semantic boundary for a suffix of the routed-read branch tree.
The selector represents `address - base`; the preserved query still represents
the original address. -/
structure ReadTreeReady {program : Program} (spec : Spec program)
    (input : List Bool) (snapshot : DenseOverlay.Snapshot)
    (address base : ℕ) (work : Fin (workTapeCount spec) → Tape) : Prop where
  query : (work (lhsTape spec)).HasBinaryNat address
  selector :
    (work (selectorTape spec)).HasBinaryNat (address - base)
  result : (work (resultTape spec)).HasBinaryNat 0
  counter : (work (counterTape spec)).HasBinaryNat 0
  copyScratch : (work (copyScratchTape spec)).HasBinaryNat 0
  register : ∀ bounded : Fin spec.registerBound,
    (work (registerTape spec bounded.val bounded.isLt)).HasBinaryNat
      (DenseOverlay.read input snapshot.overlay bounded.val)
  parked : ∀ i, TM.Parked (work i)

/-- Pure instruction selected by the decrementing fixed-program branch tree. -/
def selectedInstruction : Program → ℕ → Instr
  | [], _ => .halt
  | instruction :: _, 0 => instruction
  | _ :: tail, selector + 1 => selectedInstruction tail selector

/-- Path-sensitive runtime of a direct/fallback read branch tree whose
selector represents `address - base`. -/
def readDispatchTreeTime {program : Program} (spec : Spec program)
    (input : List Bool) (snapshot : DenseOverlay.Snapshot) (address : ℕ) :
    (remaining base : ℕ) → ℕ
  | 0, base =>
      TM.resetBinaryWorkTime 1 (address - base).bits.length + 1 +
        Machine.denseInputLookupTime input.length address
  | remaining + 1, base =>
      if address = base then
        TM.binaryCopyTime
          (DenseOverlay.read input snapshot.overlay base) 0 + 1
      else
        (TM.binaryPredTime (address - base - 1) + 1 +
          readDispatchTreeTime spec input snapshot address remaining
            (base + 1)) + 1

/-- Runtime of the complete routed-read machine on one canonical query. -/
def readDispatchTime {program : Program} (spec : Spec program)
    (input : List Bool) (snapshot : DenseOverlay.Snapshot)
    (address : ℕ) : ℕ :=
  TM.binaryCopyTime address 0 + 1 +
    readDispatchTreeTime spec input snapshot address
      spec.registerBound 0

/-- Collapse an arbitrary RAM program counter into the finite-control halt
slot at `program.length`. Every nonhalting in-range counter is preserved
literally. -/
def controlPC (program : Program) (pc : ℕ) : Fin (program.length + 1) :=
  ⟨min pc program.length, by omega⟩

/-- Width certificate consumed by the direct compiler. Only the bounded
register tapes are data-bearing at iteration boundaries. -/
def SnapshotBound {program : Program} (spec : Spec program)
    (input : List Bool) (snapshot : DenseOverlay.Snapshot)
    (wordBits : ℕ) : Prop :=
  ∀ address, address < spec.registerBound →
    bitlen (DenseOverlay.read input snapshot.overlay address) ≤ wordBits

/-- Linear all-prefix target for one direct instruction segment. The constant
depends only on the fixed compiler ABI; runtime growth is linear in word
width. -/
def instructionSpace (wordBits : ℕ) : ℕ :=
  1000 * (wordBits + 1)

end FixedRegisterMachine
end RAM
end Complexity
