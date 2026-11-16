/-
Copyright (c) 2026 Paul Butcher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Inkproof.Scene
import Inkproof.Demo.TheoremIndex

namespace Inkproof.Demo.Inspect

open Inkproof.Scene

/-- How a chart thins a series down to its pixel columns. -/
inductive Decimation
  | guaranteed
  | naive
  deriving DecidableEq

def Decimation.toggle : Decimation → Decimation
  | .guaranteed => .naive
  | .naive => .guaranteed

theorem Decimation.toggle_guaranteed : Decimation.guaranteed.toggle = .naive := rfl

theorem Decimation.toggle_naive : Decimation.naive.toggle = .guaranteed := rfl

theorem Decimation.toggle_toggle (d : Decimation) : d.toggle.toggle = d := by cases d <;> rfl

/-- Keeps the first sample of each pixel column, dropping whatever else the column held. -/
def keepFirst (prev : Option Int) : List Pt → List Pt
  | [] => []
  | p :: rest =>
    if prev == some p.x.floor then keepFirst prev rest else p :: keepFirst (some p.x.floor) rest

theorem keepFirst_nil (prev : Option Int) : keepFirst prev [] = [] := rfl

theorem keepFirst_cons_same {prev : Option Int} {p : Pt} (rest : List Pt) (h : prev = some p.x.floor) :
    keepFirst prev (p :: rest) = keepFirst prev rest := by
  simp [keepFirst, h]

theorem keepFirst_cons_new {prev : Option Int} {p : Pt} (rest : List Pt) (h : prev ≠ some p.x.floor) :
    keepFirst prev (p :: rest) = p :: keepFirst (some p.x.floor) rest := by
  simp [keepFirst, h]

theorem keepFirst_sublist (prev : Option Int) (xs : List Pt) : (keepFirst prev xs).Sublist xs := by
  induction xs generalizing prev with
  | nil => simp [keepFirst]
  | cons p rest ih =>
    unfold keepFirst
    split
    · exact (ih prev).cons _
    · exact (ih _).cons_cons _

def Decimation.apply : Decimation → List Pt → List Pt
  | .guaranteed, xs => reducePoints xs
  | .naive, xs => keepFirst none xs

theorem Decimation.apply_guaranteed (xs : List Pt) : Decimation.guaranteed.apply xs = reducePoints xs := rfl

theorem Decimation.apply_naive (xs : List Pt) : Decimation.naive.apply xs = keepFirst none xs := rfl

/-- The samples that fall in pixel column `c`. -/
def column (xs : List Pt) (c : Int) : List Pt := xs.filter fun p => p.x.floor == c

theorem mem_column {xs : List Pt} {c : Int} {p : Pt} : p ∈ column xs c ↔ p ∈ xs ∧ p.x.floor = c := by
  simp [column]

/-- The lowest `y` among the samples, computed by a plain fold. -/
def lowest : List Pt → Option Rat
  | [] => none
  | p :: rest => some (rest.foldl (fun m q => if q.y < m then q.y else m) p.y)

def highest : List Pt → Option Rat
  | [] => none
  | p :: rest => some (rest.foldl (fun m q => if m < q.y then q.y else m) p.y)

private theorem foldl_low (rest : List Pt) (m : Rat) :
    ∃ r, rest.foldl (fun m q => if q.y < m then q.y else m) m = r ∧ r ≤ m ∧ (r = m ∨ ∃ q ∈ rest, q.y = r) ∧
      ∀ q ∈ rest, r ≤ q.y := by
  induction rest generalizing m with
  | nil => exact ⟨m, rfl, Rat.le_refl, Or.inl rfl, by simp⟩
  | cons q rest ih =>
    simp only [List.foldl_cons]
    by_cases h : q.y < m
    · obtain ⟨r, hr, h1, h2, h3⟩ := ih q.y
      simp only [h, ite_true]
      refine ⟨r, hr, Rat.le_trans h1 (Rat.le_of_lt h), ?_, ?_⟩
      · rcases h2 with h2 | ⟨q', hq', h2⟩
        · exact Or.inr ⟨q, by simp, h2.symm⟩
        · exact Or.inr ⟨q', by simp [hq'], h2⟩
      · intro q' hq'
        rcases List.mem_cons.mp hq' with rfl | hq'
        · exact h1
        · exact h3 q' hq'
    · obtain ⟨r, hr, h1, h2, h3⟩ := ih m
      simp only [h, ite_false]
      refine ⟨r, hr, h1, ?_, ?_⟩
      · rcases h2 with h2 | ⟨q', hq', h2⟩
        · exact Or.inl h2
        · exact Or.inr ⟨q', by simp [hq'], h2⟩
      · intro q' hq'
        rcases List.mem_cons.mp hq' with rfl | hq'
        · exact Rat.le_trans h1 (Rat.not_lt.mp h)
        · exact h3 q' hq'

theorem lowest_spec {xs : List Pt} (h : xs ≠ []) :
    ∃ m, lowest xs = some m ∧ (∃ p ∈ xs, p.y = m) ∧ ∀ p ∈ xs, m ≤ p.y := by
  obtain ⟨p, rest, rfl⟩ : ∃ p rest, xs = p :: rest := by cases xs <;> simp_all
  obtain ⟨r, hr, h1, h2, h3⟩ := foldl_low rest p.y
  refine ⟨r, by simp [lowest, hr], ?_, ?_⟩
  · rcases h2 with h2 | ⟨q, hq, h2⟩
    · exact ⟨p, by simp, h2.symm⟩
    · exact ⟨q, by simp [hq], h2⟩
  · intro q hq
    rcases List.mem_cons.mp hq with rfl | hq
    · exact h1
    · exact h3 q hq

theorem lowest_nil : lowest [] = none := rfl

private theorem foldl_high (rest : List Pt) (m : Rat) :
    ∃ r, rest.foldl (fun m q => if m < q.y then q.y else m) m = r ∧ m ≤ r ∧ (r = m ∨ ∃ q ∈ rest, q.y = r) ∧
      ∀ q ∈ rest, q.y ≤ r := by
  induction rest generalizing m with
  | nil => exact ⟨m, rfl, Rat.le_refl, Or.inl rfl, by simp⟩
  | cons q rest ih =>
    simp only [List.foldl_cons]
    by_cases h : m < q.y
    · obtain ⟨r, hr, h1, h2, h3⟩ := ih q.y
      simp only [h, ite_true]
      refine ⟨r, hr, Rat.le_trans (Rat.le_of_lt h) h1, ?_, ?_⟩
      · rcases h2 with h2 | ⟨q', hq', h2⟩
        · exact Or.inr ⟨q, by simp, h2.symm⟩
        · exact Or.inr ⟨q', by simp [hq'], h2⟩
      · intro q' hq'
        rcases List.mem_cons.mp hq' with rfl | hq'
        · exact h1
        · exact h3 q' hq'
    · obtain ⟨r, hr, h1, h2, h3⟩ := ih m
      simp only [h, ite_false]
      refine ⟨r, hr, h1, ?_, ?_⟩
      · rcases h2 with h2 | ⟨q', hq', h2⟩
        · exact Or.inl h2
        · exact Or.inr ⟨q', by simp [hq'], h2⟩
      · intro q' hq'
        rcases List.mem_cons.mp hq' with rfl | hq'
        · exact Rat.not_lt.mp h |> fun h' => Rat.le_trans h' h1
        · exact h3 q' hq'

theorem highest_spec {xs : List Pt} (h : xs ≠ []) :
    ∃ m, highest xs = some m ∧ (∃ p ∈ xs, p.y = m) ∧ ∀ p ∈ xs, p.y ≤ m := by
  obtain ⟨p, rest, rfl⟩ : ∃ p rest, xs = p :: rest := by cases xs <;> simp_all
  obtain ⟨r, hr, h1, h2, h3⟩ := foldl_high rest p.y
  refine ⟨r, by simp [highest, hr], ?_, ?_⟩
  · rcases h2 with h2 | ⟨q, hq, h2⟩
    · exact ⟨p, by simp, h2.symm⟩
    · exact ⟨q, by simp [hq], h2⟩
  · intro q hq
    rcases List.mem_cons.mp hq with rfl | hq
    · exact h1
    · exact h3 q hq

theorem highest_nil : highest [] = none := rfl

/-- What the inspector shows for one pixel column. `lowest` and `highest` are computed from the raw samples alone;
`drawnLowest` and `drawnHighest` are the extremes of what the guaranteed reduction draws there. -/
structure Reading where
  column : Int
  raw : List Pt
  lowest : Option Rat
  highest : Option Rat
  drawnLowest : Option Rat
  drawnHighest : Option Rat
  naiveHighest : Option Rat

def inspect (xs : List Pt) (c : Int) : Reading :=
  let raw := column xs c
  let drawn := reducePoints raw
  { column := c, raw, lowest := lowest raw, highest := highest raw,
    drawnLowest := lowest drawn, drawnHighest := highest drawn,
    naiveHighest := highest (keepFirst none raw) }

theorem inspect_raw (xs : List Pt) (c : Int) : (inspect xs c).raw = column xs c := rfl

theorem inspect_lowest (xs : List Pt) (c : Int) : (inspect xs c).lowest = lowest (column xs c) := rfl

theorem inspect_highest (xs : List Pt) (c : Int) : (inspect xs c).highest = highest (column xs c) := rfl

/-- The independent extremes match the ones the guaranteed reduction draws. -/
def Reading.agrees (r : Reading) : Bool := r.lowest == r.drawnLowest && r.highest == r.drawnHighest

theorem Reading.agrees_iff (r : Reading) :
    r.agrees = true ↔ r.lowest = r.drawnLowest ∧ r.highest = r.drawnHighest := by
  simp [Reading.agrees]

/-- The first sample of each column is all naive decimation draws, so a column's peak is lost whenever it is not the first sample. -/
def Reading.naiveLoses (r : Reading) : Bool := r.naiveHighest != r.highest

theorem Reading.naiveLoses_iff (r : Reading) : r.naiveLoses = true ↔ r.naiveHighest ≠ r.highest := by
  simp [Reading.naiveLoses]

/-- The theorem that guarantees the reduction, in plain English; `Inkproof.Scene.reducePoints_covers`. -/
def guaranteeName : String := "Inkproof.Scene.reducePoints_covers"

def guaranteeText : String :=
  "Decimating a series to the first, lowest, highest and last sample of each pixel column lights exactly the same pixels as drawing every sample: no pixel is lost and none is added."

/-- The formal statement of the guarantee as released, if the library declares it. -/
def guaranteeStatement (lib : Library) : Option String :=
  (lib.theorems.find? (·.name == guaranteeName)).map (·.statement)

theorem guaranteeStatement_of_find {lib : Library} {t : _} (h : lib.theorems.find? (·.name == guaranteeName) = some t) :
    guaranteeStatement lib = some t.statement := by
  simp [guaranteeStatement, h]

theorem guaranteeStatement_of_none {lib : Library} (h : lib.theorems.find? (·.name == guaranteeName) = none) :
    guaranteeStatement lib = none := by
  simp [guaranteeStatement, h]

def showRat (q : Rat) : String := s!"{q}"

def showOpt : Option Rat → String
  | none => "none"
  | some q => showRat q

def Reading.html (r : Reading) (statement : Option String) : String :=
  s!"<section class=\"inspector\"><h3>Pixel column {r.column}</h3>" ++
  s!"<p>{r.raw.length} raw samples: {escapeHtml (", ".intercalate (r.raw.map fun p => showRat p.y))}</p>" ++
  s!"<p>Minimum {showOpt r.lowest}, maximum {showOpt r.highest} (computed from the raw samples)</p>" ++
  s!"<p>{escapeHtml guaranteeText}</p>" ++
  s!"<pre>{escapeHtml (guaranteeName ++ " : " ++ statement.getD "not found in the released API.lock")}</pre></section>"

end Inkproof.Demo.Inspect
