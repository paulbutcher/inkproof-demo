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

/-- Levels `0` to `j` of the pyramid over `xs`, so a long recording can be built in chunks and joined at level `j`. -/
def chunkLevels (j : Nat) (xs : Array (Option Int)) : Array (Array Extent) :=
  (Pyramid.ofMeasure 2 (by omega) Seismic.extent xs).levels.extract 0 (j + 1)

theorem chunkLevels_eq (j : Nat) (xs : Array (Option Int)) :
    chunkLevels j xs = (Pyramid.ofMeasure 2 (by omega) Seismic.extent xs).levels.extract 0 (j + 1) := rfl

/-- A sample as one little-endian 16-bit word, the gap word for a sample not recorded. -/
def rawSample (x : Option Int) : List UInt8 :=
  let w := encodeWord (x.getD gapWord)
  [(w % 256).toUInt8, (w / 256).toUInt8]

def rawBytes (xs : Array (Option Int)) : ByteArray :=
  ⟨(xs.toList.flatMap rawSample).toArray⟩

theorem rawBytes_data (xs : Array (Option Int)) : (rawBytes xs).data.toList = xs.toList.flatMap rawSample := by
  simp [rawBytes]

theorem rawSample_decode (x : Option Int) (h : ∀ v, x = some v → -32767 ≤ v ∧ v < 32768) :
    (match rawSample x with
      | [lo, hi] => some (decodeWord (lo.toNat + 256 * hi.toNat))
      | _ => none) = some (x.getD gapWord) := by
  have hw : ∀ v : Int, -32768 ≤ v → v < 32768 → encodeWord v < 65536 := by
    intro v h1 h2; unfold encodeWord; omega
  cases x with
  | none =>
    simp only [rawSample, Option.getD_none]
    rw [toNat_bytes _ (hw _ (by simp [gapWord]) (by simp [gapWord])),
      decodeWord_encodeWord _ (by simp [gapWord]) (by simp [gapWord])]
  | some v =>
    have := h v rfl
    simp only [rawSample, Option.getD_some]
    rw [toNat_bytes _ (hw _ (by omega) (by omega)), decodeWord_encodeWord _ (by omega) (by omega)]

theorem rawBytes_size (xs : Array (Option Int)) : (rawBytes xs).size = 2 * xs.size := by
  unfold rawBytes
  have h : ∀ l : List (Option Int), (l.flatMap rawSample).length = 2 * l.length := by
    intro l
    induction l with
    | nil => simp
    | cons x xs ih => simp [rawSample, ih]; omega
  simp [ByteArray.size, h]

/-- The path of the raw samples of day `d` of station `s`. A format string with no computation, so there is no theorem to state. -/
def rawPath (s d : Nat) : String := s!"s{s}/raw/d{d}.bin"

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

/-- A description of the tile set for the browser: the first level written (finer ones are read from the raw samples), then per station the node count of each level from there. No theorem: the string is JSON built by concatenation, and a statement about it needs a JSON parser the demo does not have. -/
def manifestOfSizes (firstLevel : Nat) (sizes : Array (Array Nat)) : String :=
  s!"\{\"tileSize\":{tileSize},\"firstLevel\":{firstLevel},\"stations\":[" ++
    ",".intercalate (sizes.toList.map fun ls => "[" ++ ",".intercalate (ls.toList.map toString) ++ "]") ++ "]}"

def manifest (ps : Array (Pyramid Extent)) : String :=
  manifestOfSizes 0 (ps.map fun p => p.levels.map (·.size))

end Inkproof.Demo.Tiles
