/-
Copyright (c) 2026 Paul Butcher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Inkproof.Demo.TileRead

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

/-- The extent of samples `lo` to `hi - 1` read from the nodes of one level: the merge of every node that overlaps them. -/
def levelQuery (level : Nat) (node : Nat → Extent) (lo hi : Nat) : Extent :=
  Aggregate.fold node (Array.range' (TileRead.nodeRange level lo hi).1
    ((TileRead.nodeRange level lo hi).2 - (TileRead.nodeRange level lo hi).1))

theorem levelQuery_eq (level : Nat) (node : Nat → Extent) (lo hi : Nat) :
    levelQuery level node lo hi = Aggregate.fold node (Array.range' (lo / 2 ^ level)
      ((hi + 2 ^ level - 1) / 2 ^ level - lo / 2 ^ level)) := rfl

/-- The node `n` of a level cut into tiles of `tileSize` nodes, given the nodes of each tile; past the end of a tile there are no samples, as at the end of a level. -/
def nodeOf (tile : Nat → Array Extent) (n : Nat) : Extent :=
  (tile (n / tileSize)).getD (n % tileSize) (⟨none⟩, ⟨none⟩)

theorem nodeOf_eq (tile : Nat → Array Extent) (n : Nat) :
    nodeOf tile n = (tile (n / tileSize)).getD (n % tileSize) (⟨none⟩, ⟨none⟩) := rfl

end Inkproof.Demo.Loaded
