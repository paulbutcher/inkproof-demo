/-
Copyright (c) 2026 Paul Butcher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Lean.Data.Json
import Inkproof.Demo.Seismic

namespace Inkproof.Demo.Catalogue

/-- Where a tile set's sample 0 is: day `day` (from 1) of `year`, at `rate` samples per second. -/
structure Origin where
  year : Nat
  day : Nat
  rate : Nat
  deriving Repr, BEq

def Origin.toJson (o : Origin) : String :=
  s!"\{\"year\":{o.year},\"day\":{o.day},\"rate\":{o.rate}}"

def Origin.parse (s : String) : Option Origin := do
  let j ← (Lean.Json.parse s).toOption
  pure ⟨← (j.getObjValAs? Nat "year").toOption, ← (j.getObjValAs? Nat "day").toOption,
    ← (j.getObjValAs? Nat "rate").toOption⟩

/-- Days from 1970-01-01 to a proleptic Gregorian date, by the standard civil-calendar algorithm. -/
def daysFromCivil (y m d : Int) : Int :=
  let y := if m ≤ 2 then y - 1 else y
  let era := y / 400
  let yoe := y - era * 400
  let mp := (m + 9) % 12
  let doy := (153 * mp + 2) / 5 + d - 1
  let doe := yoe * 365 + yoe / 4 - yoe / 100 + doy
  era * 146097 + doe - 719468

/-- A decimal such as `5.6` in tenths, rounded down; `none` if it is not a non-negative decimal. -/
def tenths (s : String) : Option Nat :=
  match s.splitOn "." with
  | [w] => (· * 10) <$> w.toNat?
  | [w, f] => do
    let t := (f.take 1).toNat?.getD 0
    if f.isEmpty then none else pure ((← w.toNat?) * 10 + t)
  | _ => none

/-- The sample index of an ISO 8601 UTC time such as `2025-03-02T14:05:11.123Z` on the grid of `o`; `none` if the time is malformed or precedes the grid. -/
def sampleOf (o : Origin) (time : String) : Option Nat := do
  let [date, clock] := time.splitOn "T" | none
  let [y, m, d] := date.splitOn "-" | none
  let [hh, mm, ss] := ((clock.splitOn "Z").headD "").splitOn ":" | none
  let secs := (← hh.toNat?) * 3600 + (← mm.toNat?) * 60 + (← (ss.splitOn ".").head?.bind String.toNat?)
  let day := daysFromCivil (← y.toInt?) (← m.toInt?) (← d.toInt?)
  let start := daysFromCivil o.year 1 1 + o.day - 1
  let since := (day - start) * 86400 + secs
  if since < 0 then none else pure (since.toNat * o.rate)

/-- The quakes of a USGS CSV with a `time` and a `mag` column; a row that is malformed or outside the recording is dropped. `none` if the header lacks either column. -/
def parseCsv (o : Origin) (csv : String) : Option (Array Seismic.Quake) := do
  let lines := (csv.splitOn "\n").filter (!·.isEmpty)
  let header ← lines.head?
  let cols := header.splitOn ","
  let t ← cols.findIdx? (· == "time")
  let m ← cols.findIdx? (· == "mag")
  pure (lines.tail.toArray.filterMap fun l =>
    let f := l.splitOn ","
    do pure ⟨← sampleOf o (← f[t]?), ← tenths (← f[m]?)⟩)

/-- Quakes as the JSON the browser reads: an array of `[sample, tenths of a magnitude]`. -/
def toJson (qs : Array Seismic.Quake) : String :=
  "[" ++ ",".intercalate (qs.toList.map fun q => s!"[{q.time},{q.magnitude}]") ++ "]"

def parseJson (s : String) : Option (Array Seismic.Quake) := do
  let j ← (Lean.Json.parse s).toOption
  let a ← (Lean.fromJson? (α := Array (Nat × Nat)) j).toOption
  pure (a.map fun (t, m) => ⟨t, m⟩)

theorem toJson_eq (qs : Array Seismic.Quake) :
    toJson qs = "[" ++ ",".intercalate (qs.toList.map fun q => s!"[{q.time},{q.magnitude}]") ++ "]" := rfl

theorem Origin.toJson_eq (o : Origin) :
    o.toJson = s!"\{\"year\":{o.year},\"day\":{o.day},\"rate\":{o.rate}}" := rfl

theorem daysFromCivil_epoch : daysFromCivil 1970 1 1 = 0 := by decide

theorem daysFromCivil_next_day (y m d : Int) :
    daysFromCivil y m (d + 1) = daysFromCivil y m d + 1 := by
  unfold daysFromCivil
  simp only []
  omega

theorem toJson_empty : toJson #[] = "[]" := rfl

-- tenths, sampleOf and parseCsv split and parse strings; core has no lemmas relating
-- String.splitOn or String.toNat? to their results, so a proof was out of reach and
-- the native tests check them on examples and on rows outside the recording.

end Inkproof.Demo.Catalogue
