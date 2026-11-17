/-
Copyright (c) 2026 Paul Butcher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Inkproof.Demo.Seismic

namespace Inkproof.Demo.Stack

variable {α : Type}

open Inkproof.Core Inkproof.Demo.Seismic

/-- The extent of each of `cols` equal pixel columns covering samples `lo` to `hi - 1`, read from the pyramid. -/
def columns (q : Nat → Nat → Extent) (lo hi cols : Nat) : Array Extent :=
  (Array.range cols).map fun c => q (lo + (hi - lo) * c / cols) (lo + (hi - lo) * (c + 1) / cols)

theorem columns_size (q : Nat → Nat → Extent) (lo hi cols : Nat) : (columns q lo hi cols).size = cols := by
  simp [columns]

theorem getElem_columns (q : Nat → Nat → Extent) (lo hi cols c : Nat) (h : c < (columns q lo hi cols).size) :
    (columns q lo hi cols)[c] = q (lo + (hi - lo) * c / cols) (lo + (hi - lo) * (c + 1) / cols) := by
  simp [columns]

/-- The lowest and highest value of a column, absent when the station recorded nothing in it. -/
def span (e : Extent) : Option (Int × Int) :=
  match e.1.get, e.2.get with
  | some a, some b => some (a, b)
  | _, _ => none

theorem span_eq_some (e : Extent) (a b : Int) : span e = some (a, b) ↔ e.1.get = some a ∧ e.2.get = some b := by
  unfold span
  cases h1 : e.1.get <;> cases h2 : e.2.get <;> simp

/-- The pixel y of value `v` in a drawing `height` tall for values within `top` of zero. -/
def pixelY (height top : Nat) (v : Int) : Int := (height : Int) / 2 - v * height / (2 * top)

end Inkproof.Demo.Stack
