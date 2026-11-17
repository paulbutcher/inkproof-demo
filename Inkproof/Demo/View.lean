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
  ⟨(a.indexRange n).1, (a.indexRange n).2⟩

theorem Range.ofInterval_eq (n : Nat) (a : Inkproof.Viewport.Interval Rat) :
    (Range.ofInterval n a).lo = (a.indexRange n).1 ∧ (Range.ofInterval n a).hi = (a.indexRange n).2 :=
  ⟨rfl, rfl⟩

/-- The quakes whose time lies inside `r`. -/
def inView (r : Range) (qs : Array Seismic.Quake) : Array Seismic.Quake :=
  qs.filter fun q => r.lo ≤ q.time && q.time < r.hi

theorem mem_inView (r : Range) (qs : Array Seismic.Quake) (q : Seismic.Quake) :
    q ∈ inView r qs ↔ q ∈ qs ∧ r.lo ≤ q.time ∧ q.time < r.hi := by
  simp [inView, Array.mem_filter]

end Inkproof.Demo.View
