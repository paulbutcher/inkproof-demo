/-
Copyright (c) 2026 Paul Butcher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Inkproof.Demo.Draw
import Inkproof.Demo.Stack
import Inkproof.Demo.View

namespace Inkproof.Demo.Plot

open Inkproof.Core Inkproof.Scene Inkproof.Demo.Seismic Inkproof.Demo.View

/-- The envelope column of one pixel column of a station drawn in the track starting at pixel row `y0`: the highest value is the top edge. -/
def column (y0 height top : Nat) (x : Nat) (v : Int × Int) : Column where
  x := (x : Rat) + 1 / 2
  lo := y0 + Stack.pixelY height top v.2
  hi := y0 + Stack.pixelY height top v.1

theorem column_eq (y0 height top x : Nat) (v : Int × Int) :
    column y0 height top x v =
      ⟨(x : Rat) + 1 / 2, y0 + Stack.pixelY height top v.2, y0 + Stack.pixelY height top v.1⟩ := rfl

/-- The items of one station's envelope, a `gap` wherever the station recorded nothing for at least one pixel column. -/
def items (y0 height top : Nat) (g : Segmented Nat (Int × Int)) : List (Item Column) :=
  List.intercalate [Item.gap] <| g.segments.toList.map fun seg =>
    seg.points.toList.filterMap fun (x, v) => v.map fun v => Item.val (column y0 height top x v)

theorem items_eq (y0 height top : Nat) (g : Segmented Nat (Int × Int)) :
    items y0 height top g = List.intercalate [Item.gap] (g.segments.toList.map fun seg =>
      seg.points.toList.filterMap fun (x, v) => v.map fun v => Item.val (column y0 height top x v)) := rfl

/-- The stacked stations over samples `r` in `cols` pixel columns, each track `height` pixels tall. -/
def traces (paint : Paint) (qs : Array (Nat → Nat → Extent)) (r : Range) (cols height top : Nat) : DisplayList :=
  qs.zipIdx.map fun (q, i) =>
    ⟨paint.layer, paint.color, .envelope (items (i * height) height top (Stack.drawn q r.lo r.hi cols))⟩

theorem size_traces (paint : Paint) (qs : Array (Nat → Nat → Extent)) (r : Range) (cols height top : Nat) :
    (traces paint qs r cols height top).size = qs.size := by
  simp [traces]

theorem traces_getElem (paint : Paint) (qs : Array (Nat → Nat → Extent)) (r : Range) (cols height top i : Nat)
    (h : i < (traces paint qs r cols height top).size) :
    (traces paint qs r cols height top)[i] =
      ⟨paint.layer, paint.color, .envelope (items (i * height) height top
        (Stack.drawn (qs[i]'(by simpa [size_traces] using h)) r.lo r.hi cols))⟩ := by
  simp [traces]

/-- The quakes in `r` as markers in the top row of a chart `cols` columns wide. -/
def quakes (style : ScatterStyle) (qs : Array Quake) (r : Range) (cols : Nat) : DisplayList :=
  (inView r qs).map fun q =>
    ⟨style.paint.layer, style.paint.color,
      .marker style.shape ⟨((View.column r cols q.time : Nat) : Rat) + 1 / 2, style.radius⟩ style.radius⟩

theorem size_quakes (style : ScatterStyle) (qs : Array Quake) (r : Range) (cols : Nat) :
    (quakes style qs r cols).size = (inView r qs).size := by
  simp [quakes]

theorem quakes_getElem (style : ScatterStyle) (qs : Array Quake) (r : Range) (cols i : Nat)
    (h : i < (quakes style qs r cols).size) :
    (quakes style qs r cols)[i] =
      ⟨style.paint.layer, style.paint.color,
        .marker style.shape
          ⟨((View.column r cols ((inView r qs)[i]'(by simpa [size_quakes] using h)).time : Nat) : Rat) + 1 / 2,
            style.radius⟩ style.radius⟩ := by
  simp [quakes]

/-- The `src` of a chart element showing samples `r`. -/
def src (r : Range) : String := s!"{r.lo}-{r.hi}"

/-- Inverse of `src`. A proof of `parseSrc (src r) = some r` was tried and stalls at `String.splitOn` over `Nat.repr` digits, which core has no lemmas for; the round trip is tested natively instead. -/
def parseSrc (s : String) : Option Range :=
  match s.splitOn "-" with
  | [a, b] => do pure ⟨← a.toNat?, ← b.toNat?⟩
  | _ => none

theorem src_eq (r : Range) : src r = s!"{r.lo}-{r.hi}" := rfl

end Inkproof.Demo.Plot
