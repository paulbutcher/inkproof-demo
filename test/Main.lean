/-
Copyright (c) 2026 Paul Butcher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Inkproof.Demo
import Inkproof.Demo.Place
import Inkproof.Viewport
import Inkproof.Viewport.Proofs
import Inkproof.Scene
import Inkproof.Float
import Inkproof.Gpu
import Inkproof.Core.Proofs
import InkproofTools.Test.Harness
import InkproofTools.Test.Platform

open InkproofTools.Test Inkproof.Demo

private def lib : Library where
  repo := "inkproof-x"
  tag := "v1.2.3"
  apiLock := "def X.f : Nat\ntheorem X.f_eq : ∀ n : Nat, X.f n = n\ntheorem X.G.mono : a < b → a ≤ b\nfield X.G.h : Nat\ntheorem X.G.h_pos : 0 < X.G.h"
  sources := #[("Other.lean", "theorem f_eq : True := trivial"),
    ("X.lean", "namespace X\n\ntheorem f_eq : True := trivial\n"),
    ("X/G.lean", "namespace X.G\ntheorem Y.mono : True := trivial\n@[simp] protected theorem mono : True := trivial")]

/-! Theorems for the pure functions whose definitions unfold directly. `escapeHtml`, `lineCount`, `locate`, `declarationLine` and `Library.theorems` go through `String.foldl`, `String.splitOn`, `Array.qsort` and `Array.filterMap`, whose lemmas are too thin to close proofs about them here, so those behaviours are tested below instead. `tcbHtml` and `codeFiles` on non-empty input are string concatenations and folds over those same functions, so they are tested too. -/

theorem ofInterval_valid (n : Nat) (hn : 0 < n) (a : Inkproof.Viewport.Interval Rat) :
    (View.Range.ofInterval n a).Valid n :=
  Inkproof.Viewport.Interval.indexRange_lt_le a n hn

theorem sourceUrl_unlocated (l : Library) (n : String) (h : locate l.sources n = none) :
    sourceUrl l n = githubUrl l.repo l.tag := by simp [sourceUrl, h]

theorem sourceUrl_declared (l : Library) (n path : String) (k : Nat) (h : locate l.sources n = some (path, some k)) :
    sourceUrl l n = s!"{githubUrl l.repo l.tag}/{path}#L{k}" := by simp [sourceUrl, h]

theorem sourceUrl_module (l : Library) (n path : String) (h : locate l.sources n = some (path, none)) :
    sourceUrl l n = s!"{githubUrl l.repo l.tag}/{path}" := by simp [sourceUrl, h]

theorem codeFiles_empty : codeFiles #[] = #[] := by simp [codeFiles]

theorem template_matches (path : String) :
    CodeKind.template.matches "inkproof-gpu" path = (path == "Inkproof/Gpu/Js.lean") := by
  simp [CodeKind.matches]

theorem generated_matches (repo path : String) :
    CodeKind.generated.matches repo path = (path.startsWith "generated/" || path.startsWith "gpu-js/") := rfl

theorem shim_matches (repo path : String) :
    CodeKind.shim.matches repo path = (path.startsWith "shim/" && path.endsWith ".js") := rfl

theorem label_template : CodeKind.template.label = "Generator template" := rfl
theorem label_generated : CodeKind.generated.label = "Generated output" := rfl
theorem label_shim : CodeKind.shim.label = "Hand-written JavaScript shim" := rfl

theorem TheoremEntry.html_eq (e : TheoremEntry) :
    e.html = s!"<li><a href=\"{escapeHtml e.url}\"><code>{escapeHtml e.name}</code></a>" ++ s!"<pre>{escapeHtml e.statement}</pre></li>" := by
  rfl

theorem Library.html_eq (l : Library) :
    l.html = s!"<section id=\"{l.repo}\"><h2>{l.repo} {l.tag} ({l.theorems.size} theorems)</h2><ul>" ++
      "".intercalate (l.theorems.toList.map (·.html)) ++ "</ul></section>" := rfl

theorem theoremPage_eq (libs : Array Library) (code : Array CodeFile) :
    theoremPage libs code =
      "<!doctype html><html lang=\"en\"><head><meta charset=\"utf-8\"><title>Inkproof theorems</title></head><body><h1>Theorems and trusted computing base</h1>" ++
      tcbHtml code ++ "".intercalate (libs.toList.map (·.html)) ++ "</body></html>\n" := rfl

/-- Theorems are exactly the `theorem` lines of the lock file, and each is linked to its tagged source. -/
private def indexTest : Except String Unit := do
  let es := lib.theorems
  check (es.map (·.name) == #["X.f_eq", "X.G.mono", "X.G.h_pos"]) s!"names {es.map (·.name)}"
  let urls := es.map (·.url)
  let base := "https://github.com/paulbutcher/inkproof-x/blob/v1.2.3"
  check (urls[0]? == some s!"{base}/X.lean#L3") s!"prefers the namespace's module: {urls[0]?}"
  check (urls[1]? == some s!"{base}/X/G.lean#L3") s!"unqualified declaration: {urls[1]?}"
  check (urls[2]? == some s!"{base}/X/G.lean") s!"no declaration, namespace module: {urls[2]?}"

private def htmlTest : Except String Unit := do
  let page := theoremPage #[lib] #[]
  for e in lib.theorems do
    check (page.contains e.name) s!"page names {e.name}"
    check ((page.splitOn e.url).length > 1) s!"page links {e.url}"
  let nasty := "a<b & \"c\" >d"
  check ((escapeHtml nasty).all fun c => c != '<' && c != '>' && c != '"') "escapes markup"
  check ((escapeHtml "plain text 1.0").length == 14) "leaves plain text alone"

private def tcbTest : Except String Unit := do
  let files := #[("inkproof-gpu", "Inkproof/Gpu/Js.lean", "a\nb\nc\n"),
    ("inkproof-web", "shim/el/index.js", "x\ny"), ("inkproof-web", "Inkproof/Web.lean", "z\n"),
    ("inkproof-gpu", "generated/gpu.js", "g\n")]
  let code := codeFiles files
  let count (k : CodeKind) := (code.filter (·.kind == k)).foldl (· + ·.lines) 0
  check (count .template == 3) "template lines"
  check (count .shim == 2) "shim lines without a trailing newline"
  check (count .generated == 1) "generated lines"
  check (code.size == 3) "other files are not counted"
  let html := tcbHtml code
  for r in tcbRows do
    check ((html.splitOn (escapeHtml r.component)).length > 1) s!"row for {r.component}"
  for k in [CodeKind.template, .generated, .shim] do
    check ((html.splitOn k.label).length > 1) s!"row for {k.label}"

namespace Robot

open Inkproof.Viewport

/-- `n` charts that share an x axis, all linked. -/
def home (c : ViewConfig Float) (n : Nat) : Linked Float n :=
  { x := ⟨c.x.home⟩, y := fun _ => c.y.home }

theorem home_view (c : ViewConfig Float) (n : Nat) (i : Fin n) :
    (home c n).view i = View.home c := by simp [home, Linked.view, View.home]

inductive Action (n : Nat) where
  | input (i : Fin n) (inp : Input Float)
  | toggle (i : Fin n)

private def key (k : Nat) : Key :=
  match k % 6 with
  | 0 => .zoomIn | 1 => .zoomOut | 2 => .left | 3 => .right | 4 => .up | _ => .down

/-- Inputs of every kind, including factors that are zero and boxes that are empty or inverted. -/
def action (n : Nat) (hn : 0 < n) (s : Rng) : Action n × Rng :=
  let (k, s) := Rng.below s 10
  let (i, s) := Rng.below s n
  let (a, s) := Rng.below s 801
  let (b, s) := Rng.below s 401
  let (c, s) := Rng.below s 801
  let (d, s) := Rng.below s 401
  let i : Fin n := ⟨i % n, Nat.mod_lt _ hn⟩
  let a := a.toFloat
  let b := b.toFloat
  let c := c.toFloat
  let d := d.toFloat
  (match k with
   | 0 | 1 => .input i (.wheel a b (c / 200))
   | 2 => .input i (.pinch a b (c / 200) (d / 100))
   | 3 | 4 => .input i (.drag (a - 400) (b - 200))
   | 5 => .input i (.key (key (c.toUInt64.toNat)))
   | 6 => .input i (.box a b c d)
   | 7 => .toggle i
   | 8 => .input i (.set (a - 400) (c - 400) (b - 200) (d - 200))
   | _ => .input i .reset, s)

private def within (c : Interval.Config Float) (a : Interval Float) : Bool :=
  c.minSpan ≤ a.span && a.span ≤ c.maxSpan

/-- The first broken property after `a` takes `r` to `r'`: a limit, a link, a cursor, or a chart
other than the one acted on moving, or unlinking one changing what it shows. -/
def violation {n : Nat} (c : ViewConfig Float) (r r' : Linked Float n) (a : Action n) : Option String :=
  let views := List.finRange n
  let limits := views.any fun j => !(within c.x (r'.view j).x && within c.y (r'.view j).y)
  let linkedX := views.filter r'.isLinked |>.map fun j => (r'.view j).x
  let desynced := linkedX.any fun x => x != r'.x.scale
  let moved := match a with
    | .input i _ => views.any fun j => j != i && (r'.view j).y != (r.view j).y
    | .toggle i => views.any fun j => (r'.view j).y != (r.view j).y ||
        (j != i && (r'.view j).x != (r.view j).x) || (!r'.isLinked i && r'.view i != r.view i)
  let drift := match a with
    | .input i (.wheel px py _) | .input i (.pinch px py _ _) =>
      let before := View.cursor c (r.view i) px py
      let after := View.cursor c (r'.view i) px py
      !(Inkproof.Float.Float.near before.1 after.1 && Inkproof.Float.Float.near before.2 after.2)
    | _ => false
  if limits then some "zoom limit violated"
  else if desynced then some "linked charts disagree on x"
  else if drift then some "cursor moved under a zoom"
  else if moved then some "an action moved a chart it did not address"
  else none

/-- Run `steps` random actions on `n` charts from `seed`; the first violation, with its step. A rig
with no charts is reported, since it would check nothing. -/
def run (c : ViewConfig Float) (n : Nat) (seed steps : Nat) : Option String :=
  if hn : 0 < n then
    let rec go : Nat → Rng → Linked Float n → Option String
      | 0, _, _ => none
      | k + 1, s, r =>
        let (a, s) := action n hn s
        let r' := match a with
          | .input i inp => r.step c i inp
          | .toggle i => if r.isLinked i then r.unlink i else r.relink i
        match violation c r r' a with
        | some e => some s!"step {steps - k}: {e}"
        | none => go k s r'
    go steps ⟨seed.toUInt64⟩ (home c n)
  else some "no charts to check"

end Robot

private def robotConfig : Inkproof.Viewport.ViewConfig Float :=
  let axis : Inkproof.Viewport.Interval.Config Float :=
    { length := 800, minSpan := 0.5, maxSpan := 1000, home := ⟨0, 100⟩, keyZoom := 1.25, keyPan := 0.1 }
  ⟨axis, { axis with length := 400 }⟩

def robotTest : Except String Unit := do
  for seed in [1:101] do
    if let some e := Robot.run robotConfig 4 seed 1000 then
      check false s!"seed {seed}: {e}"

/-- A column of flat samples with one spike that is not the first sample: naive decimation draws the first sample and
loses the spike, the guaranteed reduction keeps it, and switching back restores it. -/
private def spikeSeries : List Inkproof.Scene.Pt :=
  [⟨0, 1⟩, ⟨1/4, 1⟩, ⟨1/2, 50⟩, ⟨3/4, 1⟩, ⟨1, 1⟩, ⟨5/4, 2⟩]

private def peak (xs : List Inkproof.Scene.Pt) : Option Rat := Inspect.highest xs

private def decimationTest : Except String Unit := do
  let d := Inspect.Decimation.naive
  check (peak (d.apply spikeSeries) == some 1) "naive decimation loses the spike"
  check (peak (d.toggle.apply spikeSeries) == some 50) "guaranteed decimation keeps the spike"
  check (peak (d.toggle.toggle.apply spikeSeries) == some 1) "toggling twice is the naive view again"
  for seed in [1:201] do
    let (n, s) := Rng.below ⟨seed.toUInt64⟩ 31
    let (xs, _) := (List.range (n + 1)).foldl (fun (acc, s) i =>
      let (v, s) := Rng.below s 101
      let (j, s) := Rng.below s 4
      (acc ++ [(⟨(i : Rat) / 4 + j / 16, v⟩ : Inkproof.Scene.Pt)], s)) (([] : List Inkproof.Scene.Pt), s)
    let kept := Inspect.Decimation.guaranteed.apply xs
    for c in List.range ((n + 1) / 4 + 1) do
      let r := Inspect.inspect xs c
      check r.agrees s!"seed {seed} column {c}: raw {r.lowest} {r.highest}, drawn {r.drawnLowest} {r.drawnHighest}"
      check (r.raw.all fun p => p.x.floor == c) s!"seed {seed} column {c}: raw samples lie in the column"
      check (match r.naiveHighest, r.highest with | some a, some b => a ≤ b | _, _ => true)
        s!"seed {seed} column {c}: naive never exceeds the true peak"
    check (kept.all fun p => xs.any fun q => q.y == p.y) s!"seed {seed}: guaranteed decimation draws no value that is not a sample's"

private def inspectorTest : Except String Unit := do
  let r := Inspect.inspect spikeSeries 0
  check (r.raw.length == 4) "raw samples of the column"
  check (r.lowest == some 1 && r.highest == some 50) "independent extremes"
  check r.naiveLoses "naive decimation loses this column's peak"
  check (!(Inspect.inspect (spikeSeries.take 1) 0).naiveLoses) "a one-sample column loses nothing"
  let statement := "∀ (l : List Pt), True"
  let l : Library := { lib with apiLock := s!"theorem {Inspect.guaranteeName} : {statement}" }
  check (Inspect.guaranteeStatement l == some statement) "statement comes from the lock file"
  check (Inspect.guaranteeStatement lib == none) "absent theorem is not invented"
  let html := r.html (Inspect.guaranteeStatement l)
  check ((html.splitOn Inspect.guaranteeText).length > 1) "page gives the plain-English statement"
  check ((html.splitOn "∀ (l : List Pt)").length > 1) "page gives the formal statement"

theorem Seismic.isGap_fold (xs : Array (Option Int)) :
    Seismic.isGap (Inkproof.Core.Aggregate.fold (fun x => (Seismic.extent x).1) xs) = true ↔ ∀ x ∈ xs, x = none := by
  simp only [Seismic.isGap, Option.isNone_iff_eq_none]
  rw [Inkproof.Core.Minimum.fold_get_eq_none]
  refine forall_congr' fun x => imp_congr_right fun _ => ?_
  cases x <;> simp [Seismic.extent]

/-- Every catalogued earthquake has its marker, wherever the view is. -/
theorem marker_of_quake (style : Inkproof.Scene.ScatterStyle) (proj : Inkproof.Scene.Projection Nat Nat) (qs : Array Seismic.Quake) (q : Seismic.Quake)
    (h : q ∈ qs) : Seismic.markerOf style proj q ∈ Seismic.markers style proj qs := by
  have hp : (q.time, some q.magnitude) ∈ (Seismic.catalogue qs).points.toList := by
    refine (Inkproof.Core.Series.ofUnsorted_perm).mem_iff.2 ?_
    simp only [Array.toList_map, List.mem_map]
    exact ⟨q, by simpa using h, rfl⟩
  refine (Inkproof.Scene.mem_compileScatter style proj (Seismic.catalogue qs) _).2 ⟨q.time, q.magnitude, ?_, rfl⟩
  simpa using hp


theorem Seismic.size_samples (s : Seismic.Station) (n : Nat) : (s.samples n).size = n := by
  simp [Seismic.Station.samples]

theorem Seismic.getElem_samples (s : Seismic.Station) (n i : Nat) (h : i < (s.samples n).size) :
    (s.samples n)[i] = s.sample i := by
  simp [Seismic.Station.samples]

/-- A pyramid query summarises exactly the samples of its range. -/
theorem Seismic.pyramid_query (s : Seismic.Station) (n lo hi : Nat) :
    (s.pyramid n).query lo hi = Inkproof.Core.Aggregate.fold Seismic.extent ((s.samples n).extract lo hi) :=
  Inkproof.Core.Pyramid.query_ofMeasure 2 (by omega) Seismic.extent (s.samples n) lo hi

theorem Seismic.down_iff (s : Seismic.Station) (i : Nat) :
    s.down i = true ↔ ∃ o ∈ s.outages, o.1 ≤ i ∧ i < o.2 := by
  simp [Seismic.Station.down]

theorem Seismic.extent_get (x : Option Int) : (Seismic.extent x).1.get = x ∧ (Seismic.extent x).2.get = x := by
  cases x <;> simp [Seismic.extent]

theorem Seismic.catalogue_points (qs : Array Seismic.Quake) :
    (Seismic.catalogue qs).points.toList.Perm (qs.map fun q => (q.time, some q.magnitude)).toList :=
  Inkproof.Core.Series.ofUnsorted_perm

private def columnsOf (p : Inkproof.Core.Pyramid Seismic.Extent) (lo hi cols : Nat) : Array Seismic.Extent :=
  Inkproof.Core.Pyramid.columns Tiles.tileSize (by decide) 2 p.levels.size (p.tile Tiles.tileSize) lo hi cols

private def envelopeItems (qs : Array (Inkproof.Core.Pyramid Seismic.Extent)) (n cols : Nat) :
    List (Inkproof.Scene.Item Inkproof.Scene.Column) :=
  (Plot.traces ⟨0, ⟨0, 0, 0, 255⟩⟩ (qs.map (columnsOf · 0 n cols)) 200 (qs.map fun _ => 1000)).toList.flatMap fun c =>
    match c.shape with | .envelope is => is | _ => []

private def stackTest : Except String Unit := do
  let st : Seismic.Station := { seed := 3, outages := [(10, 20), (40, 45)] }
  let n := 60
  let runs (items : List (Inkproof.Scene.Item Inkproof.Scene.Column)) := (items.filter fun | .gap => true | _ => false).length + 1
  let items := envelopeItems #[st.pyramid n] n n
  check (runs items == 3) s!"two outages split the trace into three, got {runs items}"
  let up := (List.range n).filter fun i => !st.down i
  check ((items.filter fun | .val _ => true | _ => false).length == up.length) "every recorded column is drawn, no outage column is"
  let coarse := envelopeItems #[st.pyramid n] n 6
  check (runs coarse == 2) s!"only the column wholly inside an outage is a gap, got {runs coarse} runs"

private def tilesTest : Except String Unit := do
  let st : Seismic.Station := { seed := 5, outages := [(300, 700), (1500, 1600)] }
  let p := st.pyramid 2048
  for (level, k) in p.levels.toList.zipIdx do
    let nodes := (List.range (p.numTiles Tiles.tileSize k)).flatMap fun j =>
      let bs := (Tiles.tileBytes p k j).toList
      (List.range (bs.length / 4)).map fun i => (Tiles.decodeNode (bs.drop (4 * i) |>.take 4)).getD none
    check (nodes == level.toList.map Stack.span) s!"level {k}: tiles decode to the pyramid's nodes"
  check ((Tiles.stationTiles 0 p).size == ((List.range p.levels.size).map fun k => p.numTiles Tiles.tileSize k).sum) "one file per tile"

private def loadedTest : Except String Unit := do
  let st : Seismic.Station := { seed := 5, outages := [(300, 700), (1500, 1600)] }
  let p := st.pyramid 2048
  for k in [0, 3, 6] do
    for j in [0:p.numTiles Tiles.tileSize k] do
      check ((Loaded.decodeTile (Tiles.tileBytes p k j)).toOption == some (p.tile Tiles.tileSize k j))
        s!"level {k}, tile {j}: a tile file reads back as the pyramid's nodes"
  check (Loaded.decodeTile (ByteArray.mk #[1, 2, 3])).toOption.isNone "a ragged tile file is refused"
  let tiles := fun k t => (Loaded.decodeTile (Tiles.tileBytes p k t)).toOption.getD #[]
  for (lo, hi, cols) in [(0, 2048, 64), (5, 1700, 40), (290, 1610, 7)] do
    let got := Inkproof.Core.Pyramid.columnsFrom Tiles.tileSize (by decide) 2 p.levels.size tiles 0 lo hi cols
    check (got.map Stack.span == (columnsOf p lo hi cols).map Stack.span) s!"samples {lo} to {hi}: columns read from tile files cover the pyramid's"

private def manifestTest : Except String Unit := do
  let m : Manifest := ⟨4, #[#[10, 5, 3], #[8, 4]], 1000, 60, #[#[60, 62], #[61]]⟩
  check (Manifest.parse m.toJson == some m) "a manifest reads back as written"
  check (m.top 0 == 6 && m.top 1 == 5) "top level"
  check (m.samples 0 == 160 && m.samples 1 == 128) "samples cover the first level's nodes"
  check (Manifest.parse "{\"tileSize\":256}" == none) "a manifest with no stations is refused"
  check (Manifest.parse "not json" == none) "text that is not JSON is refused"
  check (Manifest.parse (Manifest.toJson { m with rawSpan := 0 }) == none) "a raw file of no samples is refused"

private def rawTest' : Except String Unit := do
  let st : Seismic.Station := { seed := 5, outages := [(30, 70)] }
  let span := 50
  let xs := st.samples 200
  let days := #[7, 8, 10]
  -- file d holds samples (d - 7) * 50 onward; day 9 is missing and so a gap.
  let leaves (lo hi : Nat) : Array Seismic.Extent := Id.run do
    let mut out := Array.replicate (hi - lo) (⟨none⟩, ⟨none⟩)
    for pc in Raw.pieces 0 span 7 days lo hi do
      let a := pc.first - pc.start / 2
      let file := Tiles.rawBytes (xs.extract a (a + span))
      let some ls := (Raw.decodeLeaves (file.extract pc.start (pc.start + pc.len))).toOption | return #[]
      for (l, i) in ls.zipIdx do out := out.set! (pc.first + i - lo) l
    return out
  for (lo, hi) in [(0, 200), (45, 120), (60, 61), (149, 151)] do
    let got := leaves lo hi
    check (got.size == hi - lo) s!"{lo} to {hi}: the pieces' bytes are those of the samples they name"
    for i in [0:hi - lo] do
      let t := lo + i
      let expect := if 100 ≤ t ∧ t < 150 then Seismic.extent none else Seismic.extent (xs.getD t none)
      check ((got[i]?.map Stack.span) == some (Stack.span expect)) s!"{lo} to {hi}: sample {t}"
  check ((Raw.decodeLeaves (ByteArray.mk #[1, 2, 3])).toOption.isNone) "a ragged raw file is refused"

private def catalogueTest : Except String Unit := do
  let o : Catalogue.Origin := ⟨2025, 60, 20⟩
  check (Catalogue.Origin.parse o.toJson == some o) "origin round trip"
  -- 2025-03-01 is day 60 of 2025, the origin; 2025-03-02 is one day on.
  check (Catalogue.sampleOf o "2025-03-01T00:00:00.000Z" == some 0) "origin time is sample 0"
  check (Catalogue.sampleOf o "2025-03-02T01:02:03.456Z" == some ((86400 + 3723) * 20)) "a day and 1:02:03 on"
  check (Catalogue.sampleOf o "2025-02-28T23:59:59.000Z" == none) "before the recording is dropped"
  check (Catalogue.sampleOf ⟨2024, 366, 20⟩ "2025-01-01T00:00:10.000Z" == some (86410 * 20)) "the year rolls over"
  check (Catalogue.sampleOf o "garbage" == none) "malformed time is refused"
  check (Catalogue.tenths "5.67" == some 56 && Catalogue.tenths "6" == some 60 && Catalogue.tenths "x" == none) "magnitudes in tenths"
  let csv := "time,latitude,longitude,depth,mag,magType\n2025-03-01T00:00:01.000Z,1,2,3,5.6,mww\n2025-02-01T00:00:00.000Z,1,2,3,6.0,mww\nbad,1,2,3,6.0,mww\n2025-03-03T00:00:00.000Z,1,2,3,7.1,mww\n"
  let some qs := Catalogue.parseCsv o csv | throw "csv is not read"
  check (qs.map (fun q => (q.time, q.magnitude)) == #[(20, 56), (2 * 86400 * 20, 71)]) s!"rows in and out of the recording: {qs.map (·.time)}"
  check (Catalogue.parseCsv o "a,b\n1,2").isNone "csv without time and mag is refused"
  check ((Catalogue.parseJson (Catalogue.toJson qs)).map (·.map fun q => (q.time, q.magnitude)) == some (qs.map fun q => (q.time, q.magnitude))) "catalogue json round trip"
  check (Catalogue.parseJson "{}").isNone "non-array json is refused"

private def drawTest : Except String Unit := do
  let style : Inkproof.Scene.ScatterStyle := ⟨⟨1, ⟨200, 30, 30, 255⟩⟩, .circle, 4⟩
  let proj : Inkproof.Scene.Projection Nat Nat := ⟨fun t => (t : Rat) / 10, fun m => 100 - (m : Rat) * 5⟩
  for seed in [1:51] do
    let (n, s) := Rng.below ⟨seed.toUInt64⟩ 21
    let (qs, _) := (List.range n).foldl (fun (acc, s) i =>
      let (m, s) := Rng.below s 10
      (acc.push ⟨i * 7 + 3, m⟩, s)) ((#[] : Array Seismic.Quake), s)
    let cmds := (Inkproof.Gpu.frame (Inkproof.Gpu.tessellate ⟨0, 0⟩) {} true 400 200 (Seismic.markers style proj qs) ⟨255, 255, 255, 255⟩).2
    let draws := cmds.filter (·.op == 5)
    check (draws.length == n) s!"seed {seed}: {draws.length} draws for {n} quakes"

private def plotTest : Except String Unit := do
  let st : Seismic.Station := { seed := 3, outages := [(10, 20), (40, 45)] }
  let p := st.pyramid 60
  for (lo, hi) in [(0, 60), (5, 30), (12, 18), (30, 60)] do
    let r : View.Range := ⟨lo, hi⟩
    check ((Plot.parseSrc (Plot.src r)).map (fun r => (r.lo, r.hi)) == some (lo, hi)) s!"{lo}-{hi}: src round trip"
    let gaps (items : List (Inkproof.Scene.Item Inkproof.Scene.Column)) := (items.filter fun | .gap => true | _ => false).length
    let spans := (columnsOf p lo hi 60).map Stack.span
    let cmds := Plot.traces ⟨0, ⟨0, 0, 0, 255⟩⟩ #[columnsOf p lo hi 60] 100 #[1000]
    let items := cmds.toList.flatMap fun c => match c.shape with | .envelope is => is | _ => []
    let present := (spans.filter (·.isSome)).size
    check ((items.filter fun | .val _ => true | _ => false).length == present) s!"{lo}-{hi}: every present column is drawn"
    let runs := (List.range spans.size).filter fun i => (spans[i]?.bind id).isSome && !((i > 0 && (spans[i - 1]?.bind id).isSome))
    check (gaps items + 1 == runs.length || runs.isEmpty) s!"{lo}-{hi}: one gap between runs"
  check (Plot.parseSrc "7" == none && Plot.parseSrc "a-3" == none) "malformed src is rejected"

private def boundTest : Except String Unit := do
  let n := 3000000000
  for (lo, hi) in [(0, n), (n / 2, n / 2 + 1000), (n - 2, n)] do
    let r : View.Range := ⟨lo, hi⟩
    let b := Bound.pixelError r 400 n
    check (b ≤ 1 / 2) s!"{lo}-{hi}: bound {Bound.micro b} millionths is within half a pixel"
  let r : View.Range := ⟨n - 2, n⟩
  check (Bound.pixelError r 400 n > Bound.pixelError ⟨0, n⟩ 400 n) "deeper zoom has a larger bound"

open Inkproof.Demo.MiniSeed in
private def be (n k : Nat) : List UInt8 := (List.range k).reverse.map fun i => (n / 256 ^ i % 256).toUInt8

open Inkproof.Demo.MiniSeed in
/-- A 512-byte Steim1 record of `xs` (at most 26 samples) with every difference in a 16-bit half-word. -/
private def steim1Record (xs : List Int) : ByteArray :=
  let diffs := 0 :: (xs.zip (0 :: xs)).tail.map fun (a, b) => a - b
  let pairs := (List.range ((diffs.length + 1) / 2)).map fun i =>
    (diffs.drop (2 * i)).take 2 ++ [0] |>.take 2
  let word (d : List Int) : Nat := d.foldl (fun acc v => acc * 65536 + (v % 65536).toNat) 0
  let x0 : Int := xs.headD 0
  let xn : Int := xs.getLastD 0
  let nibbles := (List.range pairs.length).foldl (fun acc k => acc + 2 * 2 ^ (30 - 2 * (k + 3))) 0
  let header := be 1 6 ++ [0x44, 0x20] ++ List.replicate 12 0x20 ++ be 2025 2 ++ be 60 2 ++ [0, 0, 0, 0] ++ be 0 2 ++
    be xs.length 2 ++ be 100 2 ++ be 1 2 ++ [0, 0, 0, 0] ++ be 0 4 ++ be 64 2 ++ be 48 2 ++ be 1000 2 ++ be 0 2 ++ [10, 1, 9, 0] ++ List.replicate 8 0
  let frame := be nibbles 4 ++ be (x0 % 4294967296).toNat 4 ++ be (xn % 4294967296).toNat 4 ++ (pairs.flatMap fun p => be (word p) 4)
  ⟨((header ++ frame ++ List.replicate 512 0).take 512).toArray⟩

open Inkproof.Demo.MiniSeed in
private def miniSeedTest (real : ByteArray) : Except String Unit := do
  match decodeFile real with
  | .error e => check false s!"real excerpt decodes: {e}"
  | .ok rs =>
    check (rs.size == real.size / 512) s!"one record per 512 bytes: {rs.size}"
    for (r, i) in rs.toList.zipIdx do
      let lastWord := (real.extract (512 * i + 64 + 8) (512 * i + 64 + 12)).data.foldl (fun a x => a * 256 + x.toNat) 0
      check (r.samples.back? == some (signExtend 32 lastWord)) s!"record {i} ends at the frame's reverse integration constant"
    let times := rs.map fun r => r.tenthMs + 10000 * r.samples.size / 100
    check ((rs.toList.zip rs.toList.tail).all fun (a, b) => a.tenthMs + 100 * a.samples.size == b.tenthMs)
      s!"records are contiguous at 100 Hz: {times}"
  let xs : List Int := [100, 105, 90, -20, -20, 7000, -20000, -5000, 0, 1]
  match decodeFile (steim1Record xs) with
  | .error e => check false s!"steim1 record decodes: {e}"
  | .ok rs => check (rs[0]?.map (·.samples.toList) == some xs) s!"steim1 round trip: {rs.map (·.samples)}"
  check (match decodeFile ⟨(steim1Record xs).data.extract 0 100⟩ with | .error _ => true | .ok _ => false) "truncated record is an error"

open Inkproof.Demo in
private def placeTest : Except String Unit := do
  let rec' (t : Nat) (xs : List Int) : MiniSeed.Record := ⟨2025, 60, t, 100, 1, xs.toArray⟩
  -- the second record starts at sample 53, leaving a gap after the first
  let a := rec' 0 [1, 2, 3]
  let b := { rec' 0 [4, 5] with tenthMs := 5300 }
  let out := Place.place 100 60 #[a, b]
  check (out.size == 8640000) "a day of 100 Hz samples"
  check (out[0]? == some (some 1) && out[2]? == some (some 3)) "first record at its start"
  check (out[3]? == some none && out[52]? == some none) "no record, no sample"
  check (out[53]? == some (some 4) && out[54]? == some (some 5)) "second record at its start time"
  check ((out.filter (·.isSome)).size == 5) "nothing else is filled"

private def chunkedTest : Except String Unit := do
  let xs : Array (Option Int) := (Array.range 45).map fun i => if i % 11 == 4 then none else some ((i * 37 % 19 : Nat) : Int)
  let bytes (l : Array Seismic.Extent) := l.toList.flatMap Tiles.encodeNode
  let whole := (Inkproof.Core.Pyramid.ofMeasure 2 (by omega) Seismic.extent xs).levels
  let chunks := (List.range 6).map fun c => (Inkproof.Core.Pyramid.ofMeasure 2 (by omega) Seismic.extent (xs.extract (c * 8) (c * 8 + 8))).levels.extract 0 3
  for k in List.range 3 do
    let joined := chunks.foldl (fun acc ls => acc ++ (ls[k]?.getD #[])) #[]
    check (bytes joined == bytes (whole[k]?.getD #[])) s!"chunks joined at level {k}"
  let joined := chunks.foldl (fun acc ls => acc ++ (ls.back?.getD #[])) #[]
  let upper := (Inkproof.Core.Pyramid.build 2 (by omega) joined).levels
  for k in List.range upper.size do
    check (bytes (upper[k]?.getD #[]) == bytes (whole[k + 2]?.getD #[])) s!"upper level {k} above the join"

private def rawTest : Except String Unit := do
  let xs : Array (Option Int) := #[some 5, none, some (-32767), some 32767, some 0]
  let bs := (Tiles.rawBytes xs).data.toList
  let back := (List.range xs.size).map fun i =>
    let v := Tiles.decodeWord ((bs.getD (2 * i) 0).toNat + 256 * (bs.getD (2 * i + 1) 0).toNat)
    if v == Tiles.gapWord then none else some v
  check (back == xs.toList) "raw samples round trip, a gap as the gap word"

def main (args : List String) : IO UInt32 := do
  let real ← IO.FS.readBinFile "fixtures/IU.ANMO.00.HHZ.excerpt.mseed"
  runTests [⟨"theorem index", indexTest⟩, ⟨"page", htmlTest⟩, ⟨"tcb", tcbTest⟩, ⟨"input robot", robotTest⟩,
    ⟨"decimation", decimationTest⟩, ⟨"inspector", inspectorTest⟩, ⟨"stack", stackTest⟩, ⟨"tiles", tilesTest⟩, ⟨"loaded tiles", loadedTest⟩, ⟨"manifest", manifestTest⟩, ⟨"raw files", rawTest'⟩, ⟨"catalogue", catalogueTest⟩, ⟨"draw", drawTest⟩, ⟨"plot", plotTest⟩, ⟨"bound", boundTest⟩, ⟨"miniSEED", miniSeedTest real⟩, ⟨"place", placeTest⟩, ⟨"chunked build", chunkedTest⟩, ⟨"raw samples", rawTest⟩,
    platformTest (args.contains "--expect-wasm")]
