/-
Copyright (c) 2026 Paul Butcher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Inkproof.Demo.Tiles

namespace Inkproof.Demo.Loaded

open Inkproof.Core Inkproof.Demo.Seismic Inkproof.Demo.Tiles

/-- The extent a decoded tile node stands for; a gap stands for no samples and bytes that are not a node stand for nothing. -/
def nodeExtent : Option (Option (Int × Int)) → Option Extent
  | some (some (a, b)) => some (⟨some a⟩, ⟨some b⟩)
  | some none => some (⟨none⟩, ⟨none⟩)
  | none => none

theorem nodeExtent_span (a b : Int) :
    (nodeExtent (some (some (a, b)))).map Stack.span = some (some (a, b)) := rfl

theorem nodeExtent_gap : (nodeExtent (some none)).map Stack.span = some none := rfl

theorem nodeExtent_invalid : nodeExtent none = none := rfl

/-- The extent of node `i` of a fetched tile file, read from its four bytes. -/
def fileNode (bs : ByteArray) (i : Nat) : Option Extent :=
  nodeExtent (decodeNode ((List.range 4).filterMap fun d => bs[4 * i + d]?))

/-- The nodes of a fetched tile file; `none` unless the file is whole nodes, every one valid. Linear in the file's size. -/
def tileNodes (bs : ByteArray) : Option (Array Extent) :=
  if bs.size % 4 = 0 then
    let ns := (Array.range (bs.size / 4)).filterMap (fileNode bs)
    if ns.size = bs.size / 4 then some ns else none
  else none

theorem tileNodes_ragged (bs : ByteArray) (h : bs.size % 4 ≠ 0) : tileNodes bs = none := by
  simp [tileNodes, h]

theorem tileNodes_eq (bs : ByteArray) (ns : Array Extent) (h : tileNodes bs = some ns) :
    ns = (Array.range (bs.size / 4)).filterMap (fileNode bs) ∧ ns.size = bs.size / 4 := by
  unfold tileNodes at h
  by_cases h4 : bs.size % 4 = 0
  · simp only [h4, ↓reduceIte] at h
    by_cases hs : (Array.filterMap (fileNode bs) (Array.range (bs.size / 4))).size = bs.size / 4
    · simp only [hs, ↓reduceIte] at h
      cases h
      exact ⟨rfl, hs⟩
    · simp only [hs, ↓reduceIte] at h
      cases h
  · simp only [h4, ↓reduceIte] at h
    cases h

/-- A fetched tile file as the nodes it holds, or why it is not a tile file. -/
def decodeTile (bs : ByteArray) : Except String (Array Extent) :=
  match tileNodes bs with
  | some ns => .ok ns
  | none => .error "not a whole number of valid tile nodes"

theorem decodeTile_eq (bs : ByteArray) (ns : Array Extent) :
    decodeTile bs = .ok ns ↔ tileNodes bs = some ns := by
  unfold decodeTile
  cases tileNodes bs <;> simp

end Inkproof.Demo.Loaded
