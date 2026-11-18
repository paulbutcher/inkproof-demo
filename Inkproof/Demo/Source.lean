/-
Copyright (c) 2026 Paul Butcher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Lean.Data.Json

namespace Inkproof.Demo.Source

/-- The line that opens a chart's source: `-- chart: <name>`. -/
def beginName (line : String) : Option String :=
  if line.startsWith "-- chart: " then some (line.drop 10).toString else none

theorem beginName_eq (line : String) :
    beginName line = if line.startsWith "-- chart: " then some (line.drop 10).toString else none := rfl

/-- The line that closes a chart's source. -/
def endMarker : String := "-- end chart"

/-- The marked regions of a file, each as its name and the lines between the markers; a region left open at the end of the file is dropped. `cur` is the region being read, with its lines reversed. -/
def go : Option (String × List String) → List String → List (String × List String)
  | _, [] => []
  | none, l :: ls =>
    match beginName l with
    | some n => go (some (n, [])) ls
    | none => go none ls
  | some (n, acc), l :: ls =>
    if l == endMarker then (n, acc.reverse) :: go none ls else go (some (n, l :: acc)) ls

def regions (lines : List String) : List (String × List String) := go none lines

theorem regions_nil : regions [] = [] := rfl

/-- A region opens at a marker line, takes lines up to the closing marker, and the rest of the file is read afresh. -/
theorem regions_open (n : String) (l : String) (ls : List String) (h : beginName l = some n) :
    regions (l :: ls) = go (some (n, [])) ls := by simp [regions, go, h]

theorem go_mem : ∀ (ls : List String) (cur : Option (String × List String)) (n : String) (b : List String),
    (n, b) ∈ go cur ls → ∀ x ∈ b, x ∈ ls ∨ ∃ n' acc, cur = some (n', acc) ∧ x ∈ acc := by
  intro ls
  induction ls with
  | nil => intro cur n b h; simp [go] at h
  | cons l ls ih =>
    intro cur n b h x hx
    match cur with
    | none =>
      simp only [go] at h
      split at h
      · rcases ih _ _ _ h x hx with h | ⟨n', acc, e, hx⟩
        · exact Or.inl (List.mem_cons_of_mem _ h)
        · simp at e; obtain ⟨-, rfl⟩ := e; simp at hx
      · rcases ih _ _ _ h x hx with h | ⟨n', acc, e, hx⟩
        · exact Or.inl (List.mem_cons_of_mem _ h)
        · simp at e
    | some (n0, acc) =>
      simp only [go] at h
      split at h
      · rcases List.mem_cons.1 h with e | h
        · obtain ⟨-, rfl⟩ := Prod.mk.inj e
          exact Or.inr ⟨n0, acc, rfl, by simpa using hx⟩
        · rcases ih _ _ _ h x hx with h | ⟨n', acc', e, hx⟩
          · exact Or.inl (List.mem_cons_of_mem _ h)
          · simp at e
      · rcases ih _ _ _ h x hx with h | ⟨n', acc', e, hx⟩
        · exact Or.inl (List.mem_cons_of_mem _ h)
        · simp at e; obtain ⟨-, rfl⟩ := e
          rcases List.mem_cons.1 hx with rfl | hx
          · exact Or.inl (List.mem_cons_self ..)
          · exact Or.inr ⟨n0, acc, rfl, hx⟩

/-- Every line of a chart's source is a line of the file it came from, so the text shown is the text compiled. -/
theorem regions_mem (lines : List String) (n : String) (b : List String) (h : (n, b) ∈ regions lines) :
    ∀ x ∈ b, x ∈ lines := by
  intro x hx
  rcases go_mem lines none n b h x hx with h | ⟨_, _, e, _⟩
  · exact h
  · simp at e

/-- The number of lines a chart's source takes, not counting blank lines. -/
def length (b : List String) : Nat := (b.filter fun l => l.any (!·.isWhitespace)).length

theorem length_eq (b : List String) : length b = (b.filter fun l => l.any (!·.isWhitespace)).length := rfl

/-- The charts' sources in a file, as the JSON the page reads. -/
def toJson (text : String) : String :=
  Lean.Json.compress (Lean.Json.arr ((regions (text.splitOn "\n")).map fun (n, b) =>
    Lean.Json.mkObj [("name", Lean.toJson n), ("source", Lean.toJson ("\n".intercalate b))]).toArray)

theorem toJson_eq (text : String) : toJson text =
    Lean.Json.compress (Lean.Json.arr ((regions (text.splitOn "\n")).map fun (n, b) =>
      Lean.Json.mkObj [("name", Lean.toJson n), ("source", Lean.toJson ("\n".intercalate b))]).toArray) := rfl

/-- Reads what `toJson` writes, as name and source; `none` if it is not that. No theorem that `parse (toJson t)` returns `regions`: Lean's `Json.parse` has no round-trip lemma and an attempt by unfolding the parser did not close; the browser test checks the sources appear. -/
def parse (s : String) : Option (List (String × String)) := do
  let j ← (Lean.Json.parse s).toOption
  let items ← (j.getArr?).toOption
  items.toList.mapM fun i => do
    pure (← (i.getObjValAs? String "name").toOption, ← (i.getObjValAs? String "source").toOption)

end Inkproof.Demo.Source
