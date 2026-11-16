/-
Copyright (c) 2026 Paul Butcher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Inkproof.Demo.Inspect

namespace Inkproof.Demo.Series

open Inkproof.Scene Inkproof.Demo.Inspect

/-- `columns` pixel columns of `perColumn` samples each. Every column holds one tall spike, placed so that it is never the column's first sample. -/
def samples (columns perColumn : Nat) : List Pt :=
  (List.range (columns * perColumn)).map fun i =>
    let k := i % perColumn
    { x := (i : Rat) / perColumn, y := if k == perColumn / 2 then 500 else ((i * 37) % 101 : Nat) }

theorem samples_length (columns perColumn : Nat) : (samples columns perColumn).length = columns * perColumn := by
  simp [samples]

/-- The `x,y` coordinate of each point `d` keeps from `xs`, each y flipped into a drawing `height` pixels tall for values up to `top`. -/
def coords (d : Decimation) (xs : List Pt) (height top : Nat) : List String :=
  (d.apply xs).map fun p =>
    s!"{(Rat.floor p.x)},{(height : Int) - Rat.floor (p.y * height / top)}"

theorem coords_length (d : Decimation) (xs : List Pt) (height top : Nat) :
    (coords d xs height top).length = (d.apply xs).length := by
  simp [coords]

/-- The `points` attribute of an SVG polyline drawing `coords`. -/
def points (d : Decimation) (xs : List Pt) (height top : Nat) : String :=
  " ".intercalate (coords d xs height top)

theorem points_toList (d : Decimation) (xs : List Pt) (height top : Nat) :
    (points d xs height top).toList = [' '].intercalate ((coords d xs height top).map String.toList) := by
  simp [points]

end Inkproof.Demo.Series
