/-
Copyright (c) 2026 Paul Butcher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Inkproof.Demo.Catalogue
import Inkproof.Demo.Manifest
import Inkproof.Demo.Tiles

open Inkproof.Demo

/-- The stations whose tiles are written. -/
def stations : Array Seismic.Station :=
  #[⟨1, [(900, 1300)]⟩, ⟨2, [(2000, 2600)]⟩, ⟨3, []⟩, ⟨4, [(300, 500), (3000, 3500)]⟩]

/-- The catalogue of the synthetic recording: a sample index and a magnitude in tenths. -/
def quakes : Array Seismic.Quake := #[⟨100, 30⟩, ⟨1000, 50⟩, ⟨2048, 40⟩, ⟨2049, 60⟩, ⟨3700, 70⟩]

def main (args : List String) : IO UInt32 := do
  let [dir] := args | IO.eprintln "usage: build-tiles <output dir>"; return 1
  let samples := 4096
  let ps := stations.map (·.pyramid samples)
  for (p, s) in ps.toList.zipIdx do
    for (path, bytes) in Tiles.stationTiles s p do
      let file : System.FilePath := dir / path
      if let some parent := file.parent then IO.FS.createDirAll parent
      IO.FS.writeBinFile file bytes
  for (st, s) in stations.toList.zipIdx do
    IO.FS.createDirAll (dir / s!"s{s}/raw")
    IO.FS.writeBinFile (dir / Tiles.rawPath s 0) (Tiles.rawBytes (st.samples samples))
  let manifest : Manifest := ⟨0, ps.map (·.levels.map (·.size)), samples, 0, ps.map fun _ => #[0]⟩
  IO.FS.writeFile (dir / "manifest.json") manifest.toJson
  IO.FS.writeFile (dir / "catalogue.json") (Catalogue.toJson quakes)
  return 0
