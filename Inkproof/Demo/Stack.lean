/-
Copyright (c) 2026 Paul Butcher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Inkproof.Demo.Seismic

namespace Inkproof.Demo.Stack

variable {α : Type}

open Inkproof.Core Inkproof.Demo.Seismic

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

/-- The largest magnitude among the columns' values, at least 1: the `top` that fits every drawn value in the track. -/
def peak (cs : Array Extent) : Nat :=
  max 1 (cs.foldl (fun m e => match span e with | some (a, b) => max m (max a.natAbs b.natAbs) | none => m) 0)

theorem one_le_peak (cs : Array Extent) : 1 ≤ peak cs := Nat.le_max_left _ _

theorem le_peak (cs : Array Extent) (e : Extent) (he : e ∈ cs) (a b : Int) (h : span e = some (a, b)) :
    a.natAbs ≤ peak cs ∧ b.natAbs ≤ peak cs := by
  unfold peak
  rw [← Array.foldl_toList]
  have key : ∀ (l : List Extent) (m : Nat), m ≤ l.foldl (fun m e => match span e with | some (a, b) => max m (max a.natAbs b.natAbs) | none => m) m ∧
      ∀ e ∈ l, ∀ a b, span e = some (a, b) → a.natAbs ≤ l.foldl (fun m e => match span e with | some (a, b) => max m (max a.natAbs b.natAbs) | none => m) m ∧ b.natAbs ≤ l.foldl (fun m e => match span e with | some (a, b) => max m (max a.natAbs b.natAbs) | none => m) m := by
    intro l
    induction l with
    | nil => intro m; simp
    | cons x xs ih =>
      intro m
      simp only [List.foldl_cons]
      have hm : m ≤ (match span x with | some (a, b) => max m (max a.natAbs b.natAbs) | none => m) := by
        cases span x with
        | none => exact Nat.le_refl _
        | some p => exact Nat.le_max_left _ _
      refine ⟨Nat.le_trans hm (ih _).1, ?_⟩
      intro e he a b h
      rcases List.mem_cons.mp he with rfl | he
      · rw [h] at hm ⊢
        simp only at hm ⊢
        have := (ih (max m (max a.natAbs b.natAbs))).1
        exact ⟨Nat.le_trans (Nat.le_trans (Nat.le_max_left _ _) (Nat.le_max_right _ _)) this, Nat.le_trans (Nat.le_trans (Nat.le_max_right _ _) (Nat.le_max_right _ _)) this⟩
      · exact (ih _).2 e he a b h
  have := (key cs.toList 0).2 e (Array.mem_toList_iff.mpr he) a b h
  exact ⟨Nat.le_trans this.1 (Nat.le_max_right _ _), Nat.le_trans this.2 (Nat.le_max_right _ _)⟩

end Inkproof.Demo.Stack
