/-
Copyright (c) 2026 Paul Butcher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Inkproof.Demo.Place
import Inkproof.Demo.Tiles

open Inkproof.Demo Inkproof.Core

/-- The samples of one station and channel directory of day files named `<date>.mseed`, a day after another from the first. -/
def loadStation (dir : System.FilePath) : IO (Array (Option Int)) := do
  let files := (← dir.readDir).map (·.path) |>.qsort (·.toString < ·.toString)
  let mut out : Array (Option Int) := #[]
  let mut day0 := 0
  for f in files, i in List.range files.size do
    let rs ← IO.ofExcept (MiniSeed.decodeFile (← IO.FS.readBinFile f))
    let some r := rs[0]? | continue
    if i == 0 then day0 := r.day
    let rate := (Int.toNat r.factor)
    out := out ++ Place.place rate r.day rs
  return out

def main (args : List String) : IO UInt32 := do
  let [data, dir] := args | IO.eprintln "usage: build-real-tiles <mseed station dir> <output dir>"; return 1
  let raw ← loadStation data
  let top := raw.foldl (fun m v => max m (v.getD 0).natAbs) 0
  let d : Int := (top + 32766) / 32767
  let d := max d 1
  let samples := raw.map (·.map fun v => v / d)
  let p := Pyramid.ofMeasure 2 (by omega) Seismic.extent samples
  for (path, bytes) in Tiles.stationTiles 0 p do
    let file : System.FilePath := dir / path
    if let some parent := file.parent then IO.FS.createDirAll parent
    IO.FS.writeBinFile file bytes
  IO.FS.writeFile (dir / "manifest.json") (Tiles.manifest #[p])
  IO.println s!"{samples.size} samples, {(samples.filter (·.isNone)).size} in gaps, counts divided by {d}"
  return 0
