/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/
import Complexitylib.TreeEvaluation.CookMertz.GroupedExtension.Defs

/-!
# Padded one-chunk parameters for grouped Cook--Mertz evaluation

For a Boolean payload of width `payloadWidth` and fan-in `fanIn`, this file
chooses the padded width

`payloadWidth + fanIn + 1`.

One chunk contains the entire padded value, and one field element is charged
twice the padded width in bits. The extra `fanIn + 1` bits make the grouped
interpolation-domain inequality automatic for every natural fan-in.

## Main definitions

- `paddedWidth` -- the padded Boolean value width
- `chunkBits` -- the width of the unique Boolean chunk
- `chunkCount` -- the constant one-chunk coordinate count
- `fieldBits` -- the charged width of one field element
-/

namespace Complexity

namespace TreeEval

namespace CookMertz

namespace GroupedExtension

namespace Parameters

/-- Boolean payload width after reserving `fanIn + 1` padding bits. -/
def paddedWidth (payloadWidth fanIn : ℕ) : ℕ :=
  payloadWidth + fanIn + 1

/-- The unique chunk contains the complete padded Boolean value. -/
def chunkBits (payloadWidth fanIn : ℕ) : ℕ :=
  paddedWidth payloadWidth fanIn

/-- The parameter choice uses exactly one grouped field coordinate. -/
def chunkCount : ℕ :=
  1

/-- Each field element is charged twice the padded width in bits. -/
def fieldBits (payloadWidth fanIn : ℕ) : ℕ :=
  2 * paddedWidth payloadWidth fanIn

end Parameters

end GroupedExtension

end CookMertz

end TreeEval

end Complexity
