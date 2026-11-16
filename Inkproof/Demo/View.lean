/-
Copyright (c) 2026 Paul Butcher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Inkproof.Viewport
import Inkproof.Demo.Seismic

namespace Inkproof.Demo.View

/-- The samples `lo` to `hi - 1` of a recording `n` samples long. -/
structure Range where
  lo : Nat
  hi : Nat
  deriving DecidableEq

def Range.width (r : Range) : Nat := r.hi - r.lo

theorem Range.width_eq (r : Range) : r.width = r.hi - r.lo := rfl

/-- Whether `r` is a non-empty range inside a recording of `n` samples. -/
def Range.Valid (n : Nat) (r : Range) : Prop := r.lo < r.hi ∧ r.hi ≤ n

/-- The samples a viewport interval shows, clamped to a recording of `n > 0` samples and never empty. -/
def Range.ofInterval (n : Nat) (a : Inkproof.Viewport.Interval Rat) : Range :=
  let lo := min (n - 1) a.start.floor.toNat
  ⟨lo, min n (max (lo + 1) (a.start + a.span).ceil.toNat)⟩

theorem Range.ofInterval_lo (n : Nat) (a : Inkproof.Viewport.Interval Rat) :
    (Range.ofInterval n a).lo = min (n - 1) a.start.floor.toNat := rfl

theorem Range.ofInterval_hi (n : Nat) (a : Inkproof.Viewport.Interval Rat) :
    (Range.ofInterval n a).hi =
      min n (max ((Range.ofInterval n a).lo + 1) (a.start + a.span).ceil.toNat) := rfl

theorem Range.ofInterval_valid (n : Nat) (hn : 0 < n) (a : Inkproof.Viewport.Interval Rat) :
    (Range.ofInterval n a).Valid n := by
  simp only [Range.Valid, Range.ofInterval]
  omega

/-- The pixel column, of `cols`, in which sample `t` falls. -/
def column (r : Range) (cols t : Nat) : Nat := (t - r.lo) * cols / r.width

theorem column_eq (r : Range) (cols t : Nat) : column r cols t = (t - r.lo) * cols / (r.hi - r.lo) := rfl

theorem column_lt (r : Range) (cols t : Nat) (hc : 0 < cols) (h : r.lo ≤ t) (ht : t < r.hi) : column r cols t < cols := by
  unfold column
  apply Nat.div_lt_of_lt_mul
  have : t - r.lo < r.width := by unfold Range.width; omega
  exact Nat.mul_lt_mul_of_pos_right this hc

/-- The quakes whose time lies inside `r`. -/
def inView (r : Range) (qs : Array Seismic.Quake) : Array Seismic.Quake :=
  qs.filter fun q => r.lo ≤ q.time && q.time < r.hi

theorem mem_inView (r : Range) (qs : Array Seismic.Quake) (q : Seismic.Quake) :
    q ∈ inView r qs ↔ q ∈ qs ∧ r.lo ≤ q.time ∧ q.time < r.hi := by
  simp [inView, Array.mem_filter]

end Inkproof.Demo.View
