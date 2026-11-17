/-
Copyright (c) 2026 Paul Butcher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Inkproof.Demo.Catalogue

open Inkproof.Demo

def main (args : List String) : IO UInt32 := do
  let [csv, tiles] := args | IO.eprintln "usage: build-catalogue <USGS catalogue csv> <tile directory>"; return 1
  let some o := Catalogue.Origin.parse (← IO.FS.readFile (tiles ++ "/recording.json"))
    | IO.eprintln s!"{tiles}/recording.json is not a recording description"; return 1
  let some qs := Catalogue.parseCsv o (← IO.FS.readFile csv)
    | IO.eprintln s!"{csv} has no time and mag columns"; return 1
  IO.FS.writeFile (tiles ++ "/catalogue.json") (Catalogue.toJson qs)
  IO.println s!"{qs.size} quakes"
  return 0
