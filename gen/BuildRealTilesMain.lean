/-
Copyright (c) 2026 Paul Butcher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Inkproof.Demo.Place
import Inkproof.Demo.Tiles

open Inkproof.Demo Inkproof.Core

/-- Leaves per chunk, a power of two so a chunk's nodes line up with the whole pyramid's. -/
def chunkLog : Nat := 20

/-- The level at which chunks are joined: its nodes are the leaves of the pyramid above. -/
def joinLevel : Nat := 12

def dayFiles (dir : System.FilePath) : IO (Array System.FilePath) := do
  let files := (← dir.readDir).map (·.path) |>.filter (·.extension == some "mseed")
  return files.qsort (·.toString < ·.toString)

/-- Calls `f` on each day's samples, in order, with `none` for each day that has no file. -/
def forDays (dir : System.FilePath) (f : Array (Option Int) → IO Unit) : IO Unit := do
  let mut next : Option Nat := none
  for file in ← dayFiles dir do
    let rs ← IO.ofExcept (MiniSeed.decodeFile (← IO.FS.readBinFile file))
    let some r := rs[0]? | continue
    let rate := Int.toNat r.factor
    if let some n := next then
      if r.day > n then f (Array.replicate ((r.day - n) * 86400 * rate) none)
    f (Place.place rate r.day rs)
    next := some (r.day + 1)

def writeTiles (out : System.FilePath) (k : Nat) (first : Nat) (level : Array Seismic.Extent) : IO Unit := do
  IO.FS.createDirAll (out / s!"s0/l{k}")
  for j in List.range (Tiles.tileCount level) do
    IO.FS.writeBinFile (out / Tiles.tilePath 0 k (first + j)) (Tiles.tileBytes level j)

def main (args : List String) : IO UInt32 := do
  let [data, out] := args | IO.eprintln "usage: build-real-tiles <mseed station dir> <output dir>"; return 1
  let top ← IO.mkRef 0
  forDays data fun day => top.modify (day.foldl (fun m v => max m (v.getD 0).natAbs))
  let d : Int := max (((← top.get) + 32766) / 32767) 1
  let chunk := 2 ^ chunkLog
  let buf ← IO.mkRef (#[] : Array (Option Int))
  let joined ← IO.mkRef (#[] : Array Seismic.Extent)
  let chunks ← IO.mkRef 0
  let total ← IO.mkRef 0
  let gaps ← IO.mkRef 0
  let flush (xs : Array (Option Int)) : IO Unit := do
    let n ← chunks.get
    chunks.set (n + 1)
    let levels := Tiles.chunkLevels joinLevel (xs.map (·.map (· / d)))
    for (level, k) in levels.toList.zipIdx do
      writeTiles out k (n * 2 ^ (chunkLog - k) / Tiles.tileSize) level
    joined.modify (· ++ levels.back?.getD #[])
  forDays data fun day => do
    total.modify (· + day.size)
    gaps.modify (· + (day.filter (·.isNone)).size)
    buf.modify (· ++ day)
    while (← buf.get).size ≥ chunk do
      let b ← buf.get
      buf.set (b.extract chunk b.size)
      flush (b.extract 0 chunk)
  if (← buf.get).size > 0 then flush (← buf.get)
  let upper := Pyramid.build 2 (by omega) (← joined.get)
  for (level, k) in upper.levels.toList.zipIdx do
    if k > 0 then writeTiles out (joinLevel + k) 0 level
  let n ← total.get
  let low := (List.range (joinLevel + 1)).map fun k => (n + 2 ^ k - 1) / 2 ^ k
  let high := (upper.levels.toList.drop 1).map (·.size)
  IO.FS.writeFile (out ++ "/manifest.json") (Tiles.manifestOfSizes #[(low ++ high).toArray])
  IO.println s!"{n} samples, {← gaps.get} in gaps, counts divided by {d}"
  return 0
