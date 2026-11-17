/-
Copyright (c) 2026 Paul Butcher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Inkproof.Demo.Catalogue
import Inkproof.Demo.Tiles

open Inkproof.Demo

/-- The stations whose tiles are written. -/
def stations : Array Seismic.Station :=
  #[⟨1, [(900, 1300)]⟩, ⟨2, [(2000, 2600)]⟩, ⟨3, []⟩, ⟨4, [(300, 500), (3000, 3500)]⟩]

/-- The catalogue of the synthetic recording: a sample index and a magnitude in tenths. -/
def quakes : Array Seismic.Quake := #[⟨100, 30⟩, ⟨1000, 50⟩, ⟨2048, 40⟩, ⟨2049, 60⟩, ⟨3700, 70⟩]

def main (args : List String) : IO UInt32 := do
  let [dir] := args | IO.eprintln "usage: build-tiles <output dir>"; return 1
  let ps := stations.map (·.pyramid 4096)
  for (p, s) in ps.toList.zipIdx do
    for (path, bytes) in Tiles.stationTiles s p do
      let file : System.FilePath := dir / path
      if let some parent := file.parent then IO.FS.createDirAll parent
      IO.FS.writeBinFile file bytes
  IO.FS.writeFile (dir / "manifest.json") (Tiles.manifest ps)
  IO.FS.writeFile (dir / "catalogue.json") (Catalogue.toJson quakes)
  return 0
