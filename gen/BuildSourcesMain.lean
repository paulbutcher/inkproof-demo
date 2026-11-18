/-
Copyright (c) 2026 Paul Butcher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Inkproof.Demo.Source

/-- Usage: `build-sources <Lean file> <output file>`: writes the sources of the file's marked charts as JSON. -/
def main (args : List String) : IO UInt32 := do
  let [file, out] := args | IO.eprintln "usage: build-sources <Lean file> <output file>"; return 1
  let json := Inkproof.Demo.Source.toJson (← IO.FS.readFile file)
  if (Inkproof.Demo.Source.parse json).all (·.isEmpty) then IO.eprintln s!"{file} has no marked chart"; return 1
  IO.FS.writeFile out json
  return 0
