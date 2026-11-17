/-
Copyright (c) 2026 Paul Butcher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Inkproof.Demo.Draw
import Inkproof.Demo.Stack
import Inkproof.Demo.View

namespace Inkproof.Demo.Plot

open Inkproof.Core Inkproof.Scene Inkproof.Demo.Seismic Inkproof.Demo.View

/-- The projection of a track starting at pixel row `y0`: pixel column `x` is centred at `x + 1/2`, and the highest value is the top edge. -/
def projection (y0 height top : Nat) : Projection Nat Int where
  x := fun x => (x : Rat) + 1 / 2
  y := fun v => y0 + Stack.pixelY height top v

theorem projection_x (y0 height top : Nat) (x : Nat) : (projection y0 height top).x x = (x : Rat) + 1 / 2 := rfl

theorem projection_y (y0 height top : Nat) (v : Int) :
    (projection y0 height top).y v = y0 + Stack.pixelY height top v := rfl

/-- The stacked stations over samples `r` in `cols` pixel columns, each track `height` pixels tall, a gap wherever a station recorded nothing for at least one pixel column. -/
def traces (paint : Paint) (qs : Array (Nat → Nat → Extent)) (r : Range) (cols height top : Nat) : DisplayList :=
  qs.zipIdx.flatMap fun (q, i) =>
    compileEnvelope paint (projection (i * height) height top) ((Stack.columns q r.lo r.hi cols).map Stack.span)

theorem mem_traces (paint : Paint) (qs : Array (Nat → Nat → Extent)) (r : Range) (cols height top : Nat)
    (c : Command) :
    c ∈ traces paint qs r cols height top ↔
      ∃ q i, (q, i) ∈ qs.zipIdx ∧
        c ∈ compileEnvelope paint (projection (i * height) height top)
          ((Stack.columns q r.lo r.hi cols).map Stack.span) := by
  simp [traces]

/-- The pixel columns of `cols` across the samples `r`, the sample `t` falling in column `(bins r cols).col t`. -/
def bins (r : Range) (cols : Nat) : Binning Nat := Binning.ofNat r.lo r.hi (max cols 1) (by omega)

theorem bins_columns (r : Range) (cols : Nat) : (bins r cols).columns = max cols 1 := rfl

/-- The quakes in `r` as markers in the top row of a chart `cols` columns wide. -/
def quakes (style : ScatterStyle) (qs : Array Quake) (r : Range) (cols : Nat) : DisplayList :=
  (inView r qs).map fun q =>
    ⟨style.paint.layer, style.paint.color,
      .marker style.shape ⟨(((bins r cols).col q.time : Nat) : Rat) + 1 / 2, style.radius⟩ style.radius⟩

theorem size_quakes (style : ScatterStyle) (qs : Array Quake) (r : Range) (cols : Nat) :
    (quakes style qs r cols).size = (inView r qs).size := by
  simp [quakes]

theorem quakes_getElem (style : ScatterStyle) (qs : Array Quake) (r : Range) (cols i : Nat)
    (h : i < (quakes style qs r cols).size) :
    (quakes style qs r cols)[i] =
      ⟨style.paint.layer, style.paint.color,
        .marker style.shape
          ⟨(((bins r cols).col ((inView r qs)[i]'(by simpa [size_quakes] using h)).time : Nat) : Rat) + 1 / 2,
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
