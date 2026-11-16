/-
Copyright (c) 2026 Paul Butcher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Inkproof.Demo.View

namespace Inkproof.Demo.Bound

/-- The name of the Scale theorem whose bound `pixelError` evaluates. -/
def theoremName : String := "Inkproof.Scale.Affine.rebase_apply_float_error"

/-- The bound of `theoremName` on the pixel position of sample `t` in a chart `cols` pixels wide showing `r`, in pixels: the map is `a * t + d` with `a = cols / width` and `d = -a * lo`, rebased at the view's start, and the proved error is at most `(|a * (t - lo)| + |a * lo| + |d|) / 2 ^ 50`. -/
def pixelError (r : View.Range) (cols t : Nat) : Rat :=
  let a : Rat := (cols : Rat) / r.width
  let w : Rat := r.lo
  let d : Rat := -(a * w)
  ((a * (t - w)).abs + (a * w).abs + d.abs) / 2 ^ 50

theorem pixelError_eq (r : View.Range) (cols t : Nat) :
    pixelError r cols t =
      ((((cols : Rat) / r.width) * ((t : Rat) - r.lo)).abs + (((cols : Rat) / r.width) * r.lo).abs +
        (-(((cols : Rat) / r.width) * r.lo)).abs) / 2 ^ 50 := rfl

/-- The bound in millionths of a pixel, rounded up. -/
def micro (q : Rat) : Nat := (q * 1000000).ceil.toNat

theorem micro_eq (q : Rat) : micro q = (q * 1000000).ceil.toNat := rfl

end Inkproof.Demo.Bound
