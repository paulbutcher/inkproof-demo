/-
Copyright (c) 2026 Paul Butcher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Inkproof.Scale.Proofs.FloatBound
import Inkproof.Demo.View

namespace Inkproof.Demo.Bound

/-- The name of the Scale theorem whose bound `pixelError` evaluates. -/
def theoremName : String := "Inkproof.Scale.Affine.rebase_apply_float_error"

/-- The bound of `theoremName` on the pixel position of sample `t` in a chart `cols` pixels wide showing `r`, in pixels: the map is `a * t + d` with `a = cols / width` and `d = -a * lo`, rebased at the view's start. -/
def pixelError (r : View.Range) (cols t : Nat) : Rat :=
  let a : Rat := (cols : Rat) / r.width
  Inkproof.Scale.Affine.rebaseErrorBound 50 a r.lo t (-(a * r.lo))

theorem pixelError_eq (r : View.Range) (cols t : Nat) :
    pixelError r cols t =
      Inkproof.Scale.Affine.rebaseErrorBound 50 ((cols : Rat) / r.width) r.lo t (-(((cols : Rat) / r.width) * r.lo)) := rfl

/-- The bound in millionths of a pixel, rounded up. -/
def micro (q : Rat) : Nat := (q * 1000000).ceil.toNat

theorem micro_eq (q : Rat) : micro q = (q * 1000000).ceil.toNat := rfl

end Inkproof.Demo.Bound
