/-
Copyright (c) 2026 Paul Butcher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

namespace Inkproof.Demo.MiniSeed

/-- The low `bits` bits of `v` read as a two's complement number. -/
def signExtend (bits v : Nat) : Int :=
  if v % 2 ^ bits < 2 ^ (bits - 1) then ((v % 2 ^ bits : Nat) : Int) else ((v % 2 ^ bits : Nat) : Int) - 2 ^ bits

theorem signExtend_of_lt (bits v : Nat) (h : v < 2 ^ (bits - 1)) (hb : 1 ≤ bits) : signExtend bits v = v := by
  have h1 : 2 ^ (bits - 1) < 2 ^ bits := Nat.pow_lt_pow_right (by omega) (by omega)
  have : v % 2 ^ bits = v := Nat.mod_eq_of_lt (by omega)
  simp [signExtend, this, h]

theorem signExtend_of_ge (bits v : Nat) (h : 2 ^ (bits - 1) ≤ v % 2 ^ bits) :
    signExtend bits v = ((v % 2 ^ bits : Nat) : Int) - 2 ^ bits := by
  simp [signExtend, Nat.not_lt.mpr h]

/-- The `bits`-wide field of `w` whose lowest bit is bit `shift`. -/
def field (w shift bits : Nat) : Nat := (w >>> shift) % 2 ^ bits

theorem field_lt (w shift bits : Nat) : field w shift bits < 2 ^ bits :=
  Nat.mod_lt _ (Nat.two_pow_pos bits)

/-- The differences packed in one data word of a Steim frame, in order, given the word's two-bit
code `c` in the frame's first word. `none` is a reserved code. Steim1 and Steim2 differ in
how a word's payload is divided. -/
def unpack (steim2 : Bool) (c w : Nat) : Option (List Int) :=
  let parts (n bits : Nat) (top : Nat) : List Int :=
    (List.range n).map fun i => signExtend bits (field w (top - bits * (i + 1)) bits)
  if c == 1 then some (parts 4 8 32)
  else if !steim2 then
    if c == 2 then some (parts 2 16 32) else if c == 3 then some (parts 1 32 32) else none
  else
    let d := field w 30 2
    if c == 2 then
      if d == 1 then some (parts 1 30 30) else if d == 2 then some (parts 2 15 30)
      else if d == 3 then some (parts 3 10 30) else none
    else if c == 3 then
      if d == 0 then some (parts 5 6 30) else if d == 1 then some (parts 6 5 30)
      else if d == 2 then some (parts 7 4 28) else none
    else none

theorem unpack_steim1_32 (w : Nat) : unpack false 3 w = some [signExtend 32 (field w 0 32)] := by
  simp [unpack]

theorem unpack_steim1_8 (w : Nat) : unpack false 1 w =
    some ((List.range 4).map fun i => signExtend 8 (field w (32 - 8 * (i + 1)) 8)) := by
  simp [unpack]

theorem unpack_steim1_16 (w : Nat) : unpack false 2 w =
    some ((List.range 2).map fun i => signExtend 16 (field w (32 - 16 * (i + 1)) 16)) := by
  simp [unpack]

theorem unpack_steim1_zero (w : Nat) : unpack false 0 w = none := by
  simp [unpack]

theorem unpack_steim2_8 (w : Nat) : unpack true 1 w =
    some ((List.range 4).map fun i => signExtend 8 (field w (32 - 8 * (i + 1)) 8)) := by
  simp [unpack]

theorem unpack_steim2_30 (w : Nat) (h : field w 30 2 = 1) : unpack true 2 w = some [signExtend 30 (field w 0 30)] := by
  simp [unpack, h]

theorem unpack_steim2_2x15 (w : Nat) (h : field w 30 2 = 2) : unpack true 2 w =
    some ((List.range 2).map fun i => signExtend 15 (field w (30 - 15 * (i + 1)) 15)) := by
  simp [unpack, h]

theorem unpack_steim2_3x10 (w : Nat) (h : field w 30 2 = 3) : unpack true 2 w =
    some ((List.range 3).map fun i => signExtend 10 (field w (30 - 10 * (i + 1)) 10)) := by
  simp [unpack, h]

theorem unpack_steim2_5x6 (w : Nat) (h : field w 30 2 = 0) : unpack true 3 w =
    some ((List.range 5).map fun i => signExtend 6 (field w (30 - 6 * (i + 1)) 6)) := by
  simp [unpack, h]

theorem unpack_steim2_6x5 (w : Nat) (h : field w 30 2 = 1) : unpack true 3 w =
    some ((List.range 6).map fun i => signExtend 5 (field w (30 - 5 * (i + 1)) 5)) := by
  simp [unpack, h]

theorem unpack_steim2_7x4 (w : Nat) (h : field w 30 2 = 2) : unpack true 3 w =
    some ((List.range 7).map fun i => signExtend 4 (field w (28 - 4 * (i + 1)) 4)) := by
  simp [unpack, h]

/-- Bytes `i` to `i + n` of `b` as a number, big-endian unless `little`. -/
def uint (b : ByteArray) (little : Bool) (i n : Nat) : Except String Nat := do
  if i + n > b.size then throw s!"read of {n} bytes at {i} runs past the end of the {b.size}-byte record"
  let bytes := (List.range n).map fun k => (b.data[i + k]?.getD 0).toNat
  return (if little then bytes.reverse else bytes).foldl (fun acc x => acc * 256 + x) 0

theorem uint_of_gt (b : ByteArray) (little : Bool) (i n : Nat) (h : b.size < i + n) :
    uint b little i n = .error s!"read of {n} bytes at {i} runs past the end of the {b.size}-byte record" := by
  have : i + n > b.size := h
  simp [uint, this]
  rfl

theorem uint_of_le (b : ByteArray) (little : Bool) (i n : Nat) (h : i + n ≤ b.size) :
    uint b little i n = .ok ((if little then ((List.range n).map fun k => (b.data[i + k]?.getD 0).toNat).reverse
      else (List.range n).map fun k => (b.data[i + k]?.getD 0).toNat).foldl (fun acc x => acc * 256 + x) 0) := by
  simp [uint, Nat.not_lt.mpr h]
  rfl

/-- The first `n` samples, starting from `x0`, whose successive differences are `diffs` (the first is unused, as `x0` is the first sample). -/
def integrate (x0 : Int) (diffs : Array Int) (n : Nat) : Array Int :=
  ((List.range n).foldl (fun (p : Int × Array Int) i =>
    let x := if i > 0 then p.1 + diffs[i]?.getD 0 else p.1
    (x, p.2.push x)) (x0, #[])).2

theorem integrate_size (x0 : Int) (diffs : Array Int) (n : Nat) : (integrate x0 diffs n).size = n := by
  have : ∀ (l : List Nat) (p : Int × Array Int),
      ((l.foldl (fun (p : Int × Array Int) i =>
        let x := if i > 0 then p.1 + diffs[i]?.getD 0 else p.1
        (x, p.2.push x)) p).2).size = p.2.size + l.length := by
    intro l
    induction l with
    | nil => intro p; simp
    | cons a t ih => intro p; simp only [List.foldl_cons, ih, Array.size_push, List.length_cons]; omega
  simp [integrate, this]

/-- The samples of the Steim frames in `b` from `start`, `n` of them, `frames` frames long. -/
def steim (steim2 little : Bool) (b : ByteArray) (start frames n : Nat) : Except String (Array Int) := do
  let mut diffs : Array Int := #[]
  let mut x0 : Int := 0
  for f in List.range frames do
    let base := start + 64 * f
    let nibbles ← uint b little base 4
    for k in List.range 15 do
      let i := k + 1
      let w ← uint b little (base + 4 * i) 4
      if f == 0 && i == 1 then x0 := signExtend 32 w
      else if f == 0 && i == 2 then pure ()
      else
        match unpack steim2 (field nibbles (30 - 2 * i) 2) w with
        | some ds => diffs := diffs ++ ds.toArray
        | none => if field nibbles (30 - 2 * i) 2 != 0 then throw s!"reserved Steim code in word {i} of frame {f}"
  if diffs.size < n then throw s!"{diffs.size} differences for {n} samples"
  return integrate x0 diffs n

theorem steim_no_samples (steim2 little : Bool) (b : ByteArray) (start : Nat) :
    steim steim2 little b start 0 0 = .ok #[] := by
  simp [steim]
  rfl

theorem steim_size (steim2 little : Bool) (b : ByteArray) (start frames n : Nat) (r : Array Int)
    (h : steim steim2 little b start frames n = .ok r) : r.size = n := by
  unfold steim at h
  simp only [Bind.bind, Except.bind] at h
  split at h <;> try simp at h
  split at h <;> try simp at h
  have h' := Except.ok.inj h
  rw [← h']
  exact integrate_size _ _ _

/-- One data record: its start time in units of 0.1 ms since the start of the year `year`
(day `day`, from 1), the sample rate as a factor and multiplier, and the samples. -/
structure Record where
  year : Nat
  day : Nat
  tenthMs : Nat
  factor : Int
  multiplier : Int
  samples : Array Int
  deriving Repr

/-- Whether the fixed header is little-endian, judged by which byte order makes the year plausible. -/
def isLittle (b : ByteArray) : Except String Bool := do
  let beYear ← uint b false 20 2
  return !(1900 ≤ beYear && beYear ≤ 2200)

theorem isLittle_eq (b : ByteArray) (h : 22 ≤ b.size) :
    isLittle b = .ok (!(1900 ≤ (b.data[20]?.getD 0).toNat * 256 + (b.data[21]?.getD 0).toNat &&
      (b.data[20]?.getD 0).toNat * 256 + (b.data[21]?.getD 0).toNat ≤ 2200)) := by
  rw [isLittle, uint_of_le b false 20 2 (by omega)]
  simp [List.range_succ, Bind.bind, Except.bind, Pure.pure, Except.pure]

/-- The record at the start of `b`, with Steim1 or Steim2 data. -/
def decodeRecord (b : ByteArray) : Except String Record := do
  let little ← isLittle b
  let year ← uint b little 20 2
  let day ← uint b little 22 2
  let hour ← uint b little 24 1
  let min ← uint b little 25 1
  let sec ← uint b little 26 1
  let frac ← uint b little 28 2
  let n ← uint b little 30 2
  let factor ← uint b little 32 2
  let mult ← uint b little 34 2
  let dataOffset ← uint b little 44 2
  let blk ← uint b little 46 2
  let kind ← uint b little blk 2
  if kind != 1000 then throw s!"first blockette is {kind}, not 1000"
  let encoding ← uint b false (blk + 4) 1
  let order ← uint b false (blk + 5) 1
  let lengthExp ← uint b false (blk + 6) 1
  let length := 2 ^ lengthExp
  if encoding != 10 && encoding != 11 then throw s!"unsupported encoding {encoding}"
  if (order == 0) != little then throw "byte order of the header and of blockette 1000 disagree"
  if length > b.size then throw s!"record length {length} exceeds the {b.size} bytes given"
  let samples ← steim (encoding == 11) little (b.extract 0 length) dataOffset ((length - dataOffset) / 64) n
  return { year, day, tenthMs := ((hour * 60 + min) * 60 + sec) * 10000 + frac, factor := signExtend 16 factor,
           multiplier := signExtend 16 mult, samples }

/-- All the records in a file, which must be whole records one after another. -/
def decodeFile (b : ByteArray) : Except String (Array Record) := do
  let mut out := #[]
  let mut pos := 0
  for _ in List.range b.size do
    if pos < b.size then
      let rest := b.extract pos b.size
      let little ← isLittle rest
      let blk ← uint rest little 46 2
      let lenExp ← uint rest false (blk + 6) 1
      out := out.push (← decodeRecord rest)
      pos := pos + 2 ^ lenExp
  return out

theorem decodeFile_empty : decodeFile ByteArray.empty = .ok #[] := by
  simp [decodeFile]
  rfl


-- `decodeRecord` and `decodeFile` have no general theorem: a proof that the samples number the header's
-- count needs the guard branches (each a `throw` bound in `Except`) discharged one by one, and
-- `decodeFile` also needs an induction on the record offsets; neither closed within a few tries.
-- The real-record tests check them instead.

end Inkproof.Demo.MiniSeed
