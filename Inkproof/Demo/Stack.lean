/-
Copyright (c) 2026 Paul Butcher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Inkproof.Core.Proofs.Segmented
import Inkproof.Core.Proofs.Series
import Inkproof.Demo.Seismic

namespace Inkproof.Demo.Stack

variable {α : Type}

open Inkproof.Core Inkproof.Demo.Seismic

/-- The extent of each of `cols` equal pixel columns covering samples `lo` to `hi - 1`, read from the pyramid. -/
def columns (p : Pyramid Extent) (lo hi cols : Nat) : Array Extent :=
  (Array.range cols).map fun c => p.query (lo + (hi - lo) * c / cols) (lo + (hi - lo) * (c + 1) / cols)

theorem columns_size (p : Pyramid Extent) (lo hi cols : Nat) : (columns p lo hi cols).size = cols := by
  simp [columns]

theorem getElem_columns (p : Pyramid Extent) (lo hi cols c : Nat) (h : c < (columns p lo hi cols).size) :
    (columns p lo hi cols)[c] = p.query (lo + (hi - lo) * c / cols) (lo + (hi - lo) * (c + 1) / cols) := by
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

/-- The corners of a run of columns, each with its pixel x: along the highest values, then back along the lowest. -/
def outlinePoints (height top : Nat) (run : List ((Int × Int) × Nat)) : List (Nat × Int) :=
  (run.map fun ((_, b), x) => (x, pixelY height top b)) ++ (run.reverse.map fun ((a, _), x) => (x, pixelY height top a))

theorem mem_outlinePoints (height top : Nat) (run : List ((Int × Int) × Nat)) (q : Nat × Int) :
    q ∈ outlinePoints height top run ↔
      ∃ a b x, ((a, b), x) ∈ run ∧ (q = (x, pixelY height top b) ∨ q = (x, pixelY height top a)) := by
  simp only [outlinePoints, List.mem_append, List.mem_map, List.mem_reverse]
  constructor
  · rintro (⟨⟨⟨a, b⟩, x⟩, h, rfl⟩ | ⟨⟨⟨a, b⟩, x⟩, h, rfl⟩)
    · exact ⟨a, b, x, h, Or.inl rfl⟩
    · exact ⟨a, b, x, h, Or.inr rfl⟩
  · rintro ⟨a, b, x, h, rfl | rfl⟩
    · exact Or.inl ⟨((a, b), x), h, rfl⟩
    · exact Or.inr ⟨((a, b), x), h, rfl⟩

theorem length_outlinePoints (height top : Nat) (run : List ((Int × Int) × Nat)) :
    (outlinePoints height top run).length = 2 * run.length := by
  simp [outlinePoints]; omega

def outline (height top : Nat) (run : List ((Int × Int) × Nat)) : String :=
  " ".intercalate ((outlinePoints height top run).map fun (x, y) => s!"{x},{y}")

theorem outline_eq (height top : Nat) (run : List ((Int × Int) × Nat)) :
    outline height top run = " ".intercalate ((outlinePoints height top run).map fun (x, y) => s!"{x},{y}") := rfl

/-- The columns in which the station recorded something, each with its pixel x. -/
def present (p : Pyramid Extent) (lo hi cols : Nat) : Array (Nat × Option (Int × Int)) :=
  ((columns p lo hi cols).zipIdx.filterMap fun (e, x) => (span e).map fun s => (x, some s))

theorem mem_present (p : Pyramid Extent) (lo hi cols x : Nat) (s : Int × Int) :
    (x, some s) ∈ (present p lo hi cols).toList ↔
      ∃ h : x < (columns p lo hi cols).size, span (columns p lo hi cols)[x] = some s := by
  simp only [present, Array.toList_filterMap, List.mem_filterMap, Array.toList_zipIdx, List.mem_zipIdx_iff_getElem?]
  constructor
  · rintro ⟨⟨e, y⟩, h, h2⟩
    simp only [Option.map_eq_some_iff, Prod.mk.injEq, Option.some.injEq] at h2
    obtain ⟨t, ht, rfl, rfl⟩ := h2
    have hx := (List.getElem?_eq_some_iff.mp h)
    obtain ⟨hl, he⟩ := hx
    simp at hl
    exact ⟨hl, by simp at he; rw [he]; exact ht⟩
  · rintro ⟨h, hs⟩
    refine ⟨((columns p lo hi cols)[x], x), ?_, by simp [hs]⟩
    simp [h]

/-- The recorded columns divided wherever pixel columns were skipped, so an outage is always a break. -/
def drawn (p : Pyramid Extent) (lo hi cols : Nat) : Segmented Nat (Int × Int) :=
  Segmented.splitWhere (Series.ofUnsorted (present p lo hi cols)) fun a b => a + 1 < b

theorem mem_breaks_drawn (p : Pyramid Extent) (lo hi cols b : Nat) :
    b ∈ (drawn p lo hi cols).breaks ↔
      ∃ h : 0 < b ∧ b < (Series.ofUnsorted (present p lo hi cols)).size,
        (Series.ofUnsorted (present p lo hi cols)).xs[b - 1]'(by unfold Series.size at h; omega) + 1 <
          (Series.ofUnsorted (present p lo hi cols)).xs[b]'h.2 := by
  simp only [drawn]
  rw [Segmented.mem_breaks_splitWhere]
  simp

/-- No recorded column is lost and none is added. -/
theorem drawn_points_perm (p : Pyramid Extent) (lo hi cols : Nat) :
    (drawn p lo hi cols).series.points.toList.Perm (present p lo hi cols).toList :=
  Series.ofUnsorted_perm

/-- One outline for each stretch of a station's view in which it recorded something; outages leave gaps between them. -/
def traces (p : Pyramid Extent) (lo hi cols height top : Nat) : List String :=
  (drawn p lo hi cols).segments.toList.map fun seg =>
    outline height top (seg.points.toList.filterMap fun (x, v) => v.map (·, x))

theorem getElem_traces (p : Pyramid Extent) (lo hi cols height top i : Nat) (h : i < (traces p lo hi cols height top).length) :
    (traces p lo hi cols height top)[i] =
      outline height top (((drawn p lo hi cols).segments.toList[i]'(by simpa [traces] using h)).points.toList.filterMap
        fun (x, v) => v.map (·, x)) := by
  simp [traces]

theorem length_traces (p : Pyramid Extent) (lo hi cols height top : Nat) :
    (traces p lo hi cols height top).length = (drawn p lo hi cols).numSegments := by
  simp [traces, Segmented.segments]

end Inkproof.Demo.Stack
