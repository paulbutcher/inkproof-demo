/-
Copyright (c) 2026 Paul Butcher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Inkproof.Demo.Tiles

namespace Inkproof.Demo.TileRead

open Inkproof.Demo.Tiles

/-- The level whose nodes are the widest that still fit in a pixel column of a view of `span` samples over `cols` columns. -/
def levelFor (span cols : Nat) : Nat := Nat.log2 (max 1 (span / cols))

theorem pow_levelFor_le (span cols : Nat) : 2 ^ levelFor span cols ≤ max 1 (span / cols) :=
  Nat.log2_self_le (by omega)

theorem lt_pow_levelFor (span cols : Nat) : max 1 (span / cols) < 2 ^ (levelFor span cols + 1) :=
  Nat.lt_log2_self

/-- The level to read: `levelFor`, but never coarser than the pyramid's top `top`. -/
def readLevel (top span cols : Nat) : Nat := min top (levelFor span cols)

theorem readLevel_eq_of_le {top span cols : Nat} (h : levelFor span cols ≤ top) :
    readLevel top span cols = levelFor span cols := by
  unfold readLevel; omega

theorem readLevel_eq_top_of_le {top span cols : Nat} (h : top ≤ levelFor span cols) :
    readLevel top span cols = top := by
  unfold readLevel; omega

/-- The nodes of `level` that overlap samples `lo` to `hi - 1`, as a half-open range of node indices. -/
def nodeRange (level lo hi : Nat) : Nat × Nat := (lo / 2 ^ level, (hi + 2 ^ level - 1) / 2 ^ level)

theorem nodeRange_covers (level lo hi i : Nat) (h : lo ≤ i) (h' : i < hi) :
    (nodeRange level lo hi).1 ≤ i / 2 ^ level ∧ i / 2 ^ level < (nodeRange level lo hi).2 := by
  have hp : 0 < 2 ^ level := Nat.two_pow_pos level
  unfold nodeRange
  dsimp only
  constructor
  · exact Nat.div_le_div_right h
  · rw [Nat.div_lt_iff_lt_mul hp]
    have : hi ≤ (hi + 2 ^ level - 1) / 2 ^ level * 2 ^ level := by
      have := Nat.div_add_mod' (hi + 2 ^ level - 1) (2 ^ level)
      have := Nat.mod_lt (hi + 2 ^ level - 1) hp
      omega
    omega

/-- The tile files of a level holding nodes `a` to `b - 1`, as a half-open range of tile indices. -/
def tileRange (a b : Nat) : Nat × Nat := (a / tileSize, (b + tileSize - 1) / tileSize)

theorem tileRange_covers (a b j : Nat) (h : a ≤ j) (h' : j < b) :
    (tileRange a b).1 ≤ j / tileSize ∧ j / tileSize < (tileRange a b).2 := by
  have hp : 0 < tileSize := by unfold tileSize; omega
  unfold tileRange
  dsimp only
  constructor
  · exact Nat.div_le_div_right h
  · rw [Nat.div_lt_iff_lt_mul hp]
    have := Nat.div_add_mod' (b + tileSize - 1) tileSize
    have := Nat.mod_lt (b + tileSize - 1) hp
    omega

/-- The nodes of one tile file; `none` for a node that is not four bytes, which a well formed file never holds. -/
def decodeTile (bs : ByteArray) : List (Option (Option (Int × Int))) :=
  (List.range (bs.size / 4)).map fun i => decodeNode ((bs.toList.drop (4 * i)).take 4)

theorem length_decodeTile (bs : ByteArray) : (decodeTile bs).length = bs.size / 4 := by
  simp [decodeTile]

theorem getElem_decodeTile (bs : ByteArray) (i : Nat) (h : i < (decodeTile bs).length) :
    (decodeTile bs)[i] = decodeNode ((bs.toList.drop (4 * i)).take 4) := by
  simp [decodeTile]

end Inkproof.Demo.TileRead
