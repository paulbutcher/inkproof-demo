/-
Copyright (c) 2026 Paul Butcher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Inkproof.Demo.Catalogue
import Inkproof.Demo.Manifest

open Inkproof.Demo

/-- The numbers of the day files a station's `s0/raw` holds, in order. -/
def rawDays (station : System.FilePath) : IO (Array Nat) := do
  let names := (← (station / "s0/raw").readDir).map (·.fileName)
  let days := names.filterMap fun n =>
    if n.startsWith "d" && n.endsWith ".bin" then ((n.drop 1).dropEnd 4).toNat? else none
  return days.qsort (· < ·)

def readJson (file : System.FilePath) : IO Lean.Json := do
  IO.ofExcept (Lean.Json.parse (← IO.FS.readFile file))

def main (args : List String) : IO UInt32 := do
  let site :: stations := args | IO.eprintln "usage: build-manifest <site dir> <station tile dir>..."; return 1
  if stations.isEmpty then IO.eprintln "no station directories"; return 1
  let mut sizes : Array (Array Nat) := #[]
  let mut days : Array (Array Nat) := #[]
  let mut first : Option Nat := none
  let mut firstLevel : Option Nat := none
  let mut rate : Option Nat := none
  for dir in stations do
    let mf ← readJson (dir ++ "/manifest.json")
    let some o := Catalogue.Origin.parse (← IO.FS.readFile (dir ++ "/recording.json"))
      | IO.eprintln s!"{dir}/recording.json is not a recording"; return 1
    let some level := (mf.getObjValAs? Nat "firstLevel").toOption | IO.eprintln s!"{dir}/manifest.json has no firstLevel"; return 1
    let some ss := (mf.getObjValAs? (Array (Array Nat)) "stations").toOption | IO.eprintln s!"{dir}/manifest.json has no stations"; return 1
    let some s0 := ss[0]? | IO.eprintln s!"{dir}/manifest.json holds no station"; return 1
    if (first.any (· != o.day)) || (firstLevel.any (· != level)) || (rate.any (· != o.rate)) then
      IO.eprintln "the stations do not share a first day, rate and first level"; return 1
    first := some o.day
    firstLevel := some level
    rate := some o.rate
    sizes := sizes.push s0
    days := days.push (← rawDays dir)
  let (some f, some level, some r) := (first, firstLevel, rate) | return 1
  IO.FS.createDirAll site
  IO.FS.writeFile (site ++ "/manifest.json") (Manifest.toJson ⟨level, sizes, r * 86400, f, days⟩)
  return 0
