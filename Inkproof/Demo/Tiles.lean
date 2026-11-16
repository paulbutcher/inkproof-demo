/-
Copyright (c) 2026 Paul Butcher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Inkproof.Demo.Stack

namespace Inkproof.Demo.Tiles

open Inkproof.Core Inkproof.Demo.Seismic

/-- The 16-bit word that stands for a node with no samples; no sample takes this value. -/
def gapWord : Int := -32768

def encodeWord (v : Int) : Nat := (v % 65536).toNat

def decodeWord (w : Nat) : Int := if w < 32768 then (w : Int) else (w : Int) - 65536

theorem decodeWord_encodeWord (v : Int) (h : -32768 ≤ v) (h' : v < 32768) : decodeWord (encodeWord v) = v := by
  unfold decodeWord encodeWord
  split <;> omega

theorem toNat_bytes (w : Nat) (hw : w < 65536) : (w % 256).toUInt8.toNat + 256 * (w / 256).toUInt8.toNat = w := by
  simp [Nat.toUInt8]
  omega

/-- A node as two little-endian 16-bit words, lowest then highest; a gap is the gap word twice. -/
def encodeNode (e : Extent) : List UInt8 :=
  let (a, b) := (Stack.span e).getD (gapWord, gapWord)
  [(encodeWord a % 256).toUInt8, (encodeWord a / 256).toUInt8, (encodeWord b % 256).toUInt8, (encodeWord b / 256).toUInt8]

/-- The node `encodeNode` wrote, `some none` for a gap, and `none` for bytes that are not a node. -/
def decodeNode (bs : List UInt8) : Option (Option (Int × Int)) :=
  match bs with
  | [a0, a1, b0, b1] =>
    let a := decodeWord (a0.toNat + 256 * a1.toNat)
    let b := decodeWord (b0.toNat + 256 * b1.toNat)
    some (if a = gapWord then none else some (a, b))
  | _ => none

theorem decodeNode_encodeNode (e : Extent) (a b : Int) (h : Stack.span e = some (a, b))
    (ha : -32767 ≤ a) (ha' : a < 32768) (hb : -32768 ≤ b) (hb' : b < 32768) :
    decodeNode (encodeNode e) = some (some (a, b)) := by
  have e1 := toNat_bytes
  have hw : ∀ v : Int, -32768 ≤ v → v < 32768 → encodeWord v < 65536 := by
    intro v h1 h2; unfold encodeWord; omega
  simp only [encodeNode, decodeNode, h, Option.getD_some, e1 _ (hw a (by omega) ha'), e1 _ (hw b hb hb'),
    decodeWord_encodeWord a (by omega) ha', decodeWord_encodeWord b hb hb']
  have : a ≠ gapWord := by unfold gapWord; omega
  simp [this]

theorem decodeNode_gap (e : Extent) (h : Stack.span e = none) : decodeNode (encodeNode e) = some none := by
  have : ∀ w : Nat, w = encodeWord gapWord → w < 65536 := by
    intro w hw; subst hw; simp [encodeWord, gapWord]
  simp only [encodeNode, decodeNode, h, Option.getD_none]
  have e1 := toNat_bytes
  rw [e1 _ (this _ rfl), decodeWord_encodeWord gapWord (by simp [gapWord]) (by simp [gapWord])]
  simp

/-- Nodes per tile file. -/
def tileSize : Nat := 256

/-- The nodes of `level` held by tile `j`, as bytes. -/
def tileBytes (level : Array Extent) (j : Nat) : ByteArray :=
  ⟨((level.extract (j * tileSize) ((j + 1) * tileSize)).toList.flatMap encodeNode).toArray⟩

theorem encodeNode_length (e : Extent) : (encodeNode e).length = 4 := by
  simp [encodeNode]

def tileCount (level : Array Extent) : Nat := (level.size + tileSize - 1) / tileSize

theorem tileCount_mul (level : Array Extent) : level.size ≤ tileCount level * tileSize := by
  unfold tileCount tileSize; omega

theorem tileBytes_size (level : Array Extent) (j : Nat) :
    (tileBytes level j).size = 4 * (min ((j + 1) * tileSize) level.size - j * tileSize) := by
  unfold tileBytes
  have h : ∀ l : List Extent, (l.flatMap encodeNode).length = 4 * l.length := by
    intro l
    induction l with
    | nil => simp
    | cons x xs ih => simp [encodeNode_length, ih]; omega
  simp [ByteArray.size, h]
  omega

/-- The path of tile `j` of level `k` of station `s`. -/
def tilePath (s k j : Nat) : String := s!"s{s}/l{k}/t{j}.bin"

/-- Every tile of a station's pyramid with its path. -/
def stationTiles (s : Nat) (p : Pyramid Extent) : Array (String × ByteArray) :=
  (p.levels.toList.zipIdx.flatMap fun (level, k) =>
    (List.range (tileCount level)).map fun j => (tilePath s k j, tileBytes level j)).toArray

theorem tilePath_eq (s k j : Nat) : tilePath s k j = s!"s{s}/l{k}/t{j}.bin" := rfl

theorem stationTiles_size (s : Nat) (p : Pyramid Extent) :
    (stationTiles s p).size = (p.levels.toList.map tileCount).sum := by
  unfold stationTiles
  simp only [List.size_toArray, List.length_flatMap, List.length_map, List.length_range]
  generalize p.levels.toList = ls
  suffices ∀ n, ((ls.zipIdx n).map fun x => tileCount x.1).sum = (ls.map tileCount).sum by
    simpa using this 0
  intro n
  induction ls generalizing n with
  | nil => simp
  | cons x xs ih => simp [List.zipIdx_cons, ih]

/-- A description of the tile set for the browser: station count, then per station the node count of each level. No theorem: the string is JSON built by concatenation, and a statement about it needs a JSON parser the demo does not have. -/
def manifest (ps : Array (Pyramid Extent)) : String :=
  s!"\{\"tileSize\":{tileSize},\"stations\":[" ++
    ",".intercalate (ps.toList.map fun p =>
      "[" ++ ",".intercalate (p.levels.toList.map fun l => toString l.size) ++ "]") ++ "]}"

end Inkproof.Demo.Tiles
