/-
Copyright (c) 2026 Paul Butcher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Inkproof.Core
import Inkproof.Scene

namespace Inkproof.Demo.Seismic

open Inkproof.Core Inkproof.Scene

/-- A recording station: `outages` are the half-open sample ranges in which it recorded nothing. -/
structure Station where
  seed : Nat
  outages : List (Nat × Nat)

def Station.down (s : Station) (i : Nat) : Bool :=
  s.outages.any fun (a, b) => a ≤ i && i < b

/-- A pseudo-random trace, absent exactly while the station is down. -/
def Station.sample (s : Station) (i : Nat) : Option Int :=
  if s.down i then none else some (Int.ofNat ((i * 7919 + s.seed * 104729) % 2001) - 1000)

theorem Station.sample_eq_none_iff (s : Station) (i : Nat) : s.sample i = none ↔ s.down i = true := by
  unfold sample
  split <;> simp_all

def Station.samples (s : Station) (n : Nat) : Array (Option Int) :=
  (Array.range n).map s.sample

/-- The lowest and highest value of a run of samples; both are absent when the run holds none. -/
abbrev Extent := Minimum Int × Maximum Int

def extent : Option Int → Extent
  | none => (⟨none⟩, ⟨none⟩)
  | some v => (⟨some v⟩, ⟨some v⟩)

/-- The precomputed tile pyramid of a station: node `j` of level `k` is the extent of samples `j * 2^k` to `(j + 1) * 2^k - 1`. -/
def Station.pyramid (s : Station) (n : Nat) : Pyramid Extent :=
  Pyramid.ofMeasure 2 (by omega) extent (s.samples n)

/-- Whether a minimum summarises a run with no samples at all, which the chart draws as a gap. -/
def isGap (m : Minimum Int) : Bool := m.get.isNone

/-- An earthquake in the catalogue, at a sample index. -/
structure Quake where
  time : Nat
  magnitude : Nat

def catalogue (qs : Array Quake) : Series Nat Nat :=
  Series.ofUnsorted (qs.map fun q => (q.time, some q.magnitude))

/-- The overlay of earthquakes, one marker each. -/
def markers (style : ScatterStyle) (proj : Projection Nat Nat) (qs : Array Quake) : DisplayList :=
  compileScatter style proj (catalogue qs)

/-- The marker `style` draws for a quake. -/
def markerOf (style : ScatterStyle) (proj : Projection Nat Nat) (q : Quake) : Command where
  layer := style.paint.layer
  color := style.paint.color
  shape := Shape.marker style.shape { x := proj.x q.time, y := proj.y q.magnitude } style.radius

end Inkproof.Demo.Seismic
