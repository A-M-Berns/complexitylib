/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/
import
  Complexitylib.TimeSpaceSimulation.Runtime.NeighborhoodMicrocode.PackedLocalConfiguration.Defs
import Complexitylib.TimeSpaceSimulation.Runtime.NeighborhoodProgram.Defs

/-!
# Semantic representation of mutable packed local configurations

`PackedLocalConfiguration.encodeAbove` is the canonical constructor for a
finite local configuration below a suspended high-order suffix. A RAM
simulator subsequently updates individual low-order digits in place, so its
loop invariant must describe arbitrary words rather than only constructor
applications.

`Represents` records exactly the two facts needed by that invariant:

* every low-order coordinate below `digitCount` is the intended
  `configurationDigit`;
* dropping the complete low-order prefix recovers the suspended suffix
  exactly.
-/

namespace Complexity
namespace TimeSpaceSimulation
namespace Runtime
namespace NeighborhoodMicrocode
namespace PackedLocalRepresentation

open NeighborhoodGraph

/-- An arbitrary natural word represents one finite local configuration
below one exact suspended high-order suffix. -/
structure Represents
    (tm : TM workTapeCount)
    (order :
      NeighborhoodExecutableEvaluation.FiniteEncoding.StateOrder tm)
    (blockLength : ℕ)
    (centers : TapeIndex workTapeCount → ℕ)
    (cfg : Cfg workTapeCount tm.Q)
    (suffix word : ℕ) : Prop where
  /-- Every represented low-order coordinate has its semantic digit. -/
  digit_eq :
    ∀ index,
      index <
          PackedLocalConfiguration.digitCount
            workTapeCount blockLength →
        PackedDigits.digit
            (PackedLocalConfiguration.radix tm) word index =
          PackedLocalConfiguration.configurationDigit
            tm order blockLength centers cfg index
  /-- Removing the complete finite prefix restores the exact suffix. -/
  suffix_eq :
    PackedDigits.drop
        (PackedLocalConfiguration.radix tm)
        (PackedLocalConfiguration.digitCount
          workTapeCount blockLength)
        word =
      suffix

end PackedLocalRepresentation
end NeighborhoodMicrocode
end Runtime
end TimeSpaceSimulation
end Complexity
