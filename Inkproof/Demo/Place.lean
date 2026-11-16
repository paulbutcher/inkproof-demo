/-
Copyright (c) 2026 Paul Butcher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Inkproof.Demo.MiniSeed

namespace Inkproof.Demo.Place

open Inkproof.Demo.MiniSeed

/-- The index of a record's first sample on a grid of `rate` samples per second that starts at `tenthMs` of day `day`. -/
def startIndex (rate day : Nat) (r : Record) : Nat :=
  ((r.day - day) * 864000000 + r.tenthMs) * rate / 10000

/-- `a` with the samples `l` written from index `i` on; samples past the end are dropped. -/
def put (a : Array (Option Int)) (i : Nat) : List Int → Array (Option Int)
  | [] => a
  | v :: vs => put (a.setIfInBounds i (some v)) (i + 1) vs

/-- The samples of one day on a grid of `rate` samples per second: each record's samples at its start time, and `none` where no record covers. -/
def place (rate day : Nat) (rs : Array Record) : Array (Option Int) :=
  rs.foldl (init := Array.replicate (86400 * rate) none) fun acc r =>
    put acc (startIndex rate day r) r.samples.toList

theorem startIndex_same_day (rate day : Nat) (r : Record) (h : r.day = day) :
    startIndex rate day r = r.tenthMs * rate / 10000 := by
  simp [startIndex, h]

theorem place_empty (rate day : Nat) : place rate day #[] = Array.replicate (86400 * rate) none := rfl

theorem put_size (l : List Int) : ∀ (a : Array (Option Int)) (i : Nat), (put a i l).size = a.size := by
  induction l with
  | nil => intro a i; rfl
  | cons v vs ih => intro a i; simp [put, ih]

theorem put_getElem?_of_lt (l : List Int) : ∀ (a : Array (Option Int)) (i j : Nat), j < i ∨ i + l.length ≤ j →
    (put a i l)[j]? = a[j]? := by
  induction l with
  | nil => intro a i j _; rfl
  | cons v vs ih =>
    intro a i j h
    simp only [put]
    simp only [List.length_cons] at h
    rw [ih _ _ _ (by omega), Array.getElem?_setIfInBounds_ne (by omega)]

theorem put_getElem?_of_get (l : List Int) : ∀ (a : Array (Option Int)) (i j : Nat) (v : Int),
    i ≤ j → j < a.size → l[j - i]? = some v → (put a i l)[j]? = some (some v) := by
  induction l with
  | nil => intro a i j v _ _ h; simp at h
  | cons x xs ih =>
    intro a i j v h1 h2 h3
    simp only [put]
    by_cases hij : i = j
    · subst hij
      simp at h3
      subst h3
      rw [put_getElem?_of_lt xs _ _ _ (by omega)]
      simp [h2]
    · apply ih _ _ _ _ (by omega) (by simpa using h2)
      have : j - i = (j - (i + 1)) + 1 := by omega
      rwa [this, List.getElem?_cons_succ] at h3

/-- Whether record `r` writes index `j`. -/
def covers (rate day : Nat) (r : Record) (j : Nat) : Prop :=
  startIndex rate day r ≤ j ∧ j < startIndex rate day r + r.samples.size

private def step (rate day : Nat) (acc : Array (Option Int)) (r : Record) : Array (Option Int) :=
  put acc (startIndex rate day r) r.samples.toList

private theorem fold_getElem?_of_uncovered (rate day : Nat) (j : Nat) : ∀ (l : List Record) (a : Array (Option Int)),
    (∀ r ∈ l, ¬ covers rate day r j) → (l.foldl (step rate day) a)[j]? = a[j]? := by
  intro l
  induction l with
  | nil => intro a _; rfl
  | cons x xs ih =>
    intro a h
    simp only [List.foldl_cons]
    rw [ih _ (fun r hr => h r (List.mem_cons_of_mem _ hr))]
    apply put_getElem?_of_lt
    have := h x List.mem_cons_self
    simp only [covers, Array.length_toList] at this ⊢
    omega

/-- Where no record covers an index, the grid is still `none`. -/
theorem place_getElem?_of_uncovered (rate day : Nat) (rs : Array Record) (j : Nat)
    (h : ∀ r ∈ rs, ¬ covers rate day r j) :
    (place rate day rs)[j]? = (Array.replicate (86400 * rate) (none : Option Int))[j]? := by
  unfold place
  rw [← Array.foldl_toList]
  exact fold_getElem?_of_uncovered rate day j rs.toList _ (fun r hr => h r (by simpa using hr))

private theorem fold_getElem?_of_last (rate day : Nat) (j : Nat) (r : Record) (v : Int) (post : List Record) :
    ∀ (a : Array (Option Int)), j < a.size → (∀ q ∈ post, ¬ covers rate day q j) →
    r.samples.toList[j - startIndex rate day r]? = some v → startIndex rate day r ≤ j →
    ((r :: post).foldl (step rate day) a)[j]? = some (some v) := by
  intro a hj hpost hv hs
  simp only [List.foldl_cons]
  rw [fold_getElem?_of_uncovered rate day j post _ hpost]
  exact put_getElem?_of_get _ _ _ _ _ hs hj hv

/-- A record's sample lands on the grid unless a later record covers the same index. -/
theorem place_getElem?_of_last (rate day : Nat) (pre post : List Record) (r : Record) (j : Nat) (v : Int)
    (hj : j < 86400 * rate) (hpost : ∀ q ∈ post, ¬ covers rate day q j)
    (hs : startIndex rate day r ≤ j) (hv : r.samples.toList[j - startIndex rate day r]? = some v) :
    (place rate day (pre ++ r :: post).toArray)[j]? = some (some v) := by
  unfold place
  rw [← Array.foldl_toList, List.toList_toArray, List.foldl_append]
  have hsz : j < (pre.foldl (step rate day) (Array.replicate (86400 * rate) none)).size := by
    have : ∀ (l : List Record) (a : Array (Option Int)), (l.foldl (step rate day) a).size = a.size := by
      intro l
      induction l with
      | nil => intro a; rfl
      | cons x xs ih => intro a; simp only [List.foldl_cons]; rw [ih, step, put_size]
    rw [this]; simpa using hj
  exact fold_getElem?_of_last rate day j r v post _ hsz hpost hv hs

theorem place_size (rate day : Nat) (rs : Array Record) : (place rate day rs).size = 86400 * rate := by
  unfold place
  rw [← Array.foldl_toList, ← Array.size_replicate (n := 86400 * rate) (v := (none : Option Int))]
  suffices h : ∀ (l : List Record) (a : Array (Option Int)),
      (l.foldl (fun acc r => put acc (startIndex rate day r) r.samples.toList) a).size = a.size by
    simpa using h rs.toList (Array.replicate (86400 * rate) none)
  intro l
  induction l with
  | nil => intro a; rfl
  | cons x xs ih => intro a; simp only [List.foldl_cons]; rw [ih, put_size]

end Inkproof.Demo.Place
