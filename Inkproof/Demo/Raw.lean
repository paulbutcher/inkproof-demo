/-
Copyright (c) 2026 Paul Butcher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Inkproof.Demo.Loaded

namespace Inkproof.Demo.Raw

open Inkproof.Demo.Seismic Inkproof.Demo.Tiles

/-- A run of leaves in a raw file (Web's `RawRange` is in a module that imports Lasm, which this one must not): `len` bytes at `start` of `path`, the leaves from sample `first`. -/
structure Piece where
  path : String
  first : Nat
  start : Nat
  len : Nat
  deriving Repr, BEq

/-- Station `s`'s raw file `d`, which holds the `span` samples from sample `(d - first0) * span`, as far as it overlaps samples `lo` to `hi - 1`. -/
def piece (s span first0 lo hi d : Nat) : Option Piece :=
  let a := (d - first0) * span
  let from_ := max lo a
  let to := min hi (a + span)
  if from_ < to then some ⟨rawPath s d, from_, 2 * (from_ - a), 2 * (to - from_)⟩ else none

/-- The pieces of the raw files `days` that hold samples `lo` to `hi - 1`; a sample in no file is a gap. -/
def pieces (s span first0 : Nat) (days : Array Nat) (lo hi : Nat) : Array Piece :=
  days.filterMap (piece s span first0 lo hi)

theorem mem_pieces (s span first0 : Nat) (days : Array Nat) (lo hi : Nat) (p : Piece) :
    p ∈ pieces s span first0 days lo hi ↔ ∃ d ∈ days, piece s span first0 lo hi d = some p := by
  simp [pieces, Array.mem_filterMap]

theorem piece_spec (s span first0 lo hi d : Nat) (p : Piece) (h : piece s span first0 lo hi d = some p) :
    p.path = rawPath s d ∧ lo ≤ p.first ∧ p.first + p.len / 2 ≤ hi ∧ p.len % 2 = 0 ∧
      p.first ≥ (d - first0) * span ∧ p.first + p.len / 2 ≤ (d - first0) * span + span ∧
      p.start = 2 * (p.first - (d - first0) * span) ∧ 0 < p.len := by
  unfold piece at h
  dsimp only at h
  split at h
  · cases h
    refine ⟨rfl, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> dsimp only <;> omega
  · cases h

theorem piece_covers (s span first0 lo hi d i : Nat) (h1 : lo ≤ i) (h2 : i < hi)
    (h3 : (d - first0) * span ≤ i) (h4 : i < (d - first0) * span + span) :
    ∃ p, piece s span first0 lo hi d = some p ∧ p.first ≤ i ∧ i < p.first + p.len / 2 := by
  unfold piece
  dsimp only
  split
  · exact ⟨_, rfl, by dsimp only; omega, by dsimp only; omega⟩
  · omega

/-- The extent of the sample a raw word stands for. -/
def wordExtent (w : Nat) : Extent :=
  let v := decodeWord w
  if v = gapWord then (⟨none⟩, ⟨none⟩) else extent (some v)

theorem wordExtent_encodeWord (v : Int) (h : -32768 < v) (h' : v < 32768) :
    wordExtent (encodeWord v) = extent (some v) := by
  have := decodeWord_encodeWord v (by omega) h'
  unfold wordExtent
  have hne : v ≠ gapWord := by unfold gapWord; omega
  simp [this, hne]

theorem wordExtent_gap : wordExtent (encodeWord gapWord) = (⟨none⟩, ⟨none⟩) := by
  have := decodeWord_encodeWord gapWord (by decide) (by decide)
  unfold wordExtent
  rw [this]
  simp

/-- The leaves of a raw file's bytes, a sample to each little-endian 16-bit word; an error if the bytes are not whole words. -/
def decodeLeaves (bs : ByteArray) : Except String (Array Extent) :=
  if bs.size % 2 = 0 then
    .ok ((Array.range (bs.size / 2)).map fun i => wordExtent ((bs.data.getD (2 * i) 0).toNat + 256 * (bs.data.getD (2 * i + 1) 0).toNat))
  else .error s!"{bs.size} bytes is not a whole number of samples"

theorem decodeLeaves_ragged (bs : ByteArray) (h : bs.size % 2 ≠ 0) : ∃ e, decodeLeaves bs = .error e := by
  simp [decodeLeaves, h]

theorem size_decodeLeaves (bs : ByteArray) (a : Array Extent) (h : decodeLeaves bs = .ok a) : a.size = bs.size / 2 := by
  unfold decodeLeaves at h
  split at h
  · cases h; simp
  · cases h

theorem getElem_decodeLeaves (bs : ByteArray) (a : Array Extent) (h : decodeLeaves bs = .ok a) (i : Nat)
    (hi : i < a.size) :
    a[i] = wordExtent ((bs.data.getD (2 * i) 0).toNat + 256 * (bs.data.getD (2 * i + 1) 0).toNat) := by
  unfold decodeLeaves at h
  split at h
  · cases h; simp
  · cases h

end Inkproof.Demo.Raw
