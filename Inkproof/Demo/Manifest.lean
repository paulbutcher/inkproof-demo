/-
Copyright (c) 2026 Paul Butcher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Lean.Data.Json
import Inkproof.Demo.Tiles

namespace Inkproof.Demo

/-- What the browser learns about a tile set before it reads any tile: the first level written and, per station, the node count of each level from there; and the raw sample files, which hold `rawSpan` samples each, file `d` starting at sample `(d - rawFirst) * rawSpan`, with the numbers of the files each station has. -/
structure Manifest where
  firstLevel : Nat
  stations : Array (Array Nat)
  rawSpan : Nat
  rawFirst : Nat
  rawDays : Array (Array Nat)
  deriving Repr, BEq

namespace Manifest

/-- Reads the JSON that the tile build writes; `none` if it is not that. A statement about this needs a JSON parser the demo does not have, so it is tested instead. -/
def parse (s : String) : Option Manifest := do
  let j ← (Lean.Json.parse s).toOption
  let firstLevel ← (j.getObjValAs? Nat "firstLevel").toOption
  let stations ← (j.getObjValAs? (Array (Array Nat)) "stations").toOption
  let rawSpan ← (j.getObjValAs? Nat "rawSpan").toOption
  let rawFirst ← (j.getObjValAs? Nat "rawFirst").toOption
  let rawDays ← (j.getObjValAs? (Array (Array Nat)) "rawDays").toOption
  if rawSpan = 0 then none else
  pure ⟨firstLevel, stations, rawSpan, rawFirst, rawDays⟩

/-- The JSON `parse` reads. A statement about this needs a JSON parser the demo does not have, so a round trip is tested instead. -/
def toJson (m : Manifest) : String :=
  Lean.Json.compress (Lean.Json.mkObj [("tileSize", Lean.toJson Tiles.tileSize), ("firstLevel", Lean.toJson m.firstLevel),
    ("stations", Lean.toJson m.stations), ("rawSpan", Lean.toJson m.rawSpan), ("rawFirst", Lean.toJson m.rawFirst),
    ("rawDays", Lean.toJson m.rawDays)])

/-- The coarsest level written for a station. -/
def top (m : Manifest) (s : Nat) : Nat := m.firstLevel + ((m.stations.getD s #[]).size - 1)

/-- The number of samples a station's tiles cover, rounded up to a whole node of the first level. -/
def samples (m : Manifest) (s : Nat) : Nat := (m.stations.getD s #[]).getD 0 0 * 2 ^ m.firstLevel

theorem top_eq (m : Manifest) (s : Nat) : m.top s = m.firstLevel + ((m.stations.getD s #[]).size - 1) := rfl

theorem samples_eq (m : Manifest) (s : Nat) :
    m.samples s = (m.stations.getD s #[]).getD 0 0 * 2 ^ m.firstLevel := rfl

end Manifest

end Inkproof.Demo
