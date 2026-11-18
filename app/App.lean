/-
Copyright (c) 2026 Paul Butcher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Lasm.UI
import Lasm.JS.Web.Fetch
import Inkproof.Demo
import Inkproof.Web.Host.Chart
import Inkproof.Web.Host.Tiles

open Lasm.UI Inkproof.Web.Host Inkproof.Demo Inkproof.Demo.Inspect Inkproof.Demo.View Inkproof.Viewport

def chartCols : Nat := 400
def trackHeight : Nat := 100

def axisConfig (sampleCount : Nat) : Interval.Config Rat :=
  { length := chartCols, minSpan := 2, maxSpan := sampleCount, home := ⟨0, sampleCount⟩, keyZoom := 2, keyPan := 1 / 4 }

def viewConfig (sampleCount : Nat) : ViewConfig Rat := ⟨axisConfig sampleCount, axisConfig sampleCount⟩

/-- Until the tile manifest arrives the recording's length is unknown, so nothing is drawn. -/
structure Model where
  mode : Decimation := .guaranteed
  column : Int := 0
  manifest : Option Manifest := none
  failure : Option String := none
  view : View Rat := ⟨⟨0, 0⟩, ⟨0, 0⟩⟩
  robot : String := ""
  sources : List (String × String) := []

def Model.sampleCount (m : Model) : Nat := (m.manifest.map (·.samples 0)).getD 0

inductive Msg
  | manifest (result : Except Http.Error String)
  | toggle
  | pick (column : Int)
  | zoomIn
  | zoomOut
  | panLeft
  | panRight
  | robot (seed : Nat)
  | sources (result : Except Http.Error String)

def series : List Inkproof.Scene.Pt := Series.samples 200 20

def manifestUrl : String := "tiles/manifest.json"

def sourcesUrl : String := "chart-sources.json"

def catalogueUrl : String := "tiles/catalogue.json"

/-- Seeds the robot runs in the page, one per message so the page stays responsive between them. -/
def robotSeeds : Nat := 20

def update : Msg → Model → Model × Cmd Msg
  | .manifest (.ok body), m =>
    match Manifest.parse body with
    | some mf =>
      let cfg := axisConfig (mf.samples 0)
      ({ m with manifest := some mf, view := ⟨cfg.home, cfg.home⟩ }, .none)
    | none =>
      ({ m with failure := some s!"{manifestUrl} is not a tile manifest" },
        .io fun _ => log .warn "manifest is not a tile manifest" [("url", manifestUrl)])
  | .manifest (.error e), m =>
    ({ m with failure := some s!"{manifestUrl}: {e}" },
      .io fun _ => log .warn "manifest fetch failed" [("url", manifestUrl), ("error", toString e)])
  | .sources (.ok body), m =>
    match Source.parse body with
    | some l => ({ m with sources := l }, .none)
    | none => (m, .io fun _ => log .warn "chart sources are malformed" [("url", sourcesUrl)])
  | .sources (.error e), m =>
    (m, .io fun _ => log .warn "chart sources fetch failed" [("url", sourcesUrl), ("error", toString e)])
  | .toggle, m => ({ m with mode := m.mode.toggle }, .none)
  | .pick c, m => ({ m with column := c }, .none)
  | .zoomIn, m => ({ m with view := View.step (viewConfig m.sampleCount) m.view (.key .zoomIn) }, .none)
  | .zoomOut, m => ({ m with view := View.step (viewConfig m.sampleCount) m.view (.key .zoomOut) }, .none)
  | .panLeft, m => ({ m with view := View.step (viewConfig m.sampleCount) m.view (.key .left) }, .none)
  | .panRight, m => ({ m with view := View.step (viewConfig m.sampleCount) m.view (.key .right) }, .none)
  | .robot seed, m =>
    if seed > robotSeeds then ({ m with robot := s!"robot: {robotSeeds} runs, no violations" }, .none)
    else match Robot.runSeed seed with
      | some e =>
        ({ m with robot := s!"robot: {e}" }, .io fun _ => log .warn "robot found a violation" [("violation", e)])
      | none => ({ m with robot := s!"robot: running, seed {seed}" }, Cmd.delay 0 (.robot (seed + 1)))

def modeName : Decimation → String
  | .guaranteed => "guaranteed"
  | .naive => "naive"

/-- Enough for every tile one chart view reads from four stations, so linked charts and the next pan or zoom find them. -/
def tileCacheCapacity : Nat := 512

def tracePaint : Inkproof.Scene.Paint := ⟨0, ⟨70, 130, 180, 255⟩⟩

def quakeStyle : Inkproof.Scene.ScatterStyle := ⟨⟨1, ⟨220, 20, 60, 255⟩⟩, .circle, 4⟩

-- chart: Seismic stack
/-- The extent of each of `chartCols` pixel columns of samples `r` of station `s`, from its tiles, with the finest zooms read from its raw day files by byte range. -/
def stationColumns (cache : TileCache Seismic.Extent) (mf : Manifest) (s : Nat) (r : Range) : Lasm.JS.Async (Array Seismic.Extent) :=
  queryColumnsFrom Tiles.tileSize (by decide) 2 (mf.top s + 1) mf.firstLevel
    (fun k t => s!"tiles/{Tiles.tilePath s k t}") Loaded.decodeTile
    (fun lo hi => (Raw.pieces s mf.rawSpan mf.rawFirst (mf.rawDays.getD s #[]) lo hi).map fun p =>
      { url := s!"tiles/{p.path}", first := p.first, start := p.start, len := p.len })
    Raw.decodeLeaves r.lo r.hi chartCols (some cache)

/-- One track of extents per station and a marker for each quake in view. -/
def stackItems (columns : Nat → Lasm.JS.Async (Array Seismic.Extent)) (quakes : Lasm.JS.Async (Array Seismic.Quake))
    (stations : Nat) (r : Range) : Lasm.JS.Async Inkproof.Scene.DisplayList := do
  let cols ← (Array.range stations).mapM columns
  return Plot.traces tracePaint cols trackHeight (cols.map Stack.peak) ++ Plot.quakes quakeStyle (← quakes) r chartCols
-- end chart

def loadManifest (ref : IO.Ref (Option Manifest)) : Lasm.JS.Async Manifest := do
  if let some mf := (← ref.get) then return mf
  let resp ← try Lasm.JS.Web.fetch (.usvString manifestUrl) catch e =>
    log .warn "manifest fetch failed" [("url", manifestUrl), ("error", toString e)]
    throw e
  unless ← resp.ok do
    log .warn "manifest fetch failed" [("url", manifestUrl), ("status", toString (← resp.status))]
    throw (IO.userError s!"{manifestUrl} not available")
  let some mf := Manifest.parse (← resp.text) | do
    log .warn "manifest is not a tile manifest" [("url", manifestUrl)]
    throw (IO.userError s!"{manifestUrl} is malformed")
  ref.set (some mf)
  return mf

def loadCatalogue (ref : IO.Ref (Option (Array Seismic.Quake))) : Lasm.JS.Async (Array Seismic.Quake) := do
  if let some qs := (← ref.get) then return qs
  let resp ← try Lasm.JS.Web.fetch (.usvString catalogueUrl) catch e =>
    log .warn "catalogue fetch failed" [("url", catalogueUrl), ("error", toString e)]
    throw e
  unless ← resp.ok do
    log .warn "catalogue fetch failed" [("url", catalogueUrl), ("status", toString (← resp.status))]
    throw (IO.userError s!"{catalogueUrl} not available")
  let some qs := Catalogue.parseJson (← resp.text) | do
    log .warn "catalogue is malformed" [("url", catalogueUrl)]
    throw (IO.userError s!"{catalogueUrl} is malformed")
  ref.set (some qs)
  return qs

def sceneOf (cache : TileCache Seismic.Extent) (manifest : IO.Ref (Option Manifest)) (catalogue : IO.Ref (Option (Array Seismic.Quake))) (src : String) : Lasm.JS.Async Scene := do
  let some r := Plot.parseSrc src | throw (IO.userError s!"not a sample range: {src}")
  let mf ← loadManifest manifest
  let stations := mf.stations.size
  let labels ← IO.mkRef (#[] : Array Label)
  -- A failure is already logged; an empty track would read as an outage and no catalogue as a quiet period, so say what happened.
  let columns s := try stationColumns cache mf s r catch _ => do
    labels.modify (·.push { text := s!"station {s + 1}: tiles failed to load", x := 8, y := 14 + Float.ofNat (s * trackHeight), color := "#b00020" })
    pure (Array.replicate chartCols (⟨none⟩, ⟨none⟩))
  let quakes := try loadCatalogue catalogue catch _ => do
    labels.modify (·.push { text := "catalogue failed to load", x := 8, y := Float.ofNat (trackHeight * stations) - 6, color := "#b00020" })
    pure #[]
  let list ← stackItems columns quakes stations r
  return { commands := Draw.bytes chartCols (trackHeight * stations) list, labels := ← labels.get }

def linkedCharts : Nat := 8

def deepest : Nat := 3000000000

def stacked (stations : Nat) (r : Range) (i : Nat) : Html Msg :=
  node "inkproof-chart" [attr "id" (if i == 0 then "stack" else s!"stack-{i}"), attr "class" "linked",
    attr "src" (Plot.src r), attr "style" s!"width:{chartCols}px;height:{trackHeight * stations}px"] []

def errorBound (r : Range) : String :=
  s!"Placement error at most {Bound.micro (Bound.pixelError r chartCols deepest)} millionths of a pixel anywhere in a {deepest} sample recording, by {Bound.theoremName}, provided every intermediate product and sum stays in the normal floating-point range (its NormalRange hypotheses)"

-- chart: Decimated line
def lineChart (mode : Decimation) : Html Msg :=
  Svg.svg [attr "id" "chart", attr "viewBox" "0 0 200 100", attr "width" "800", attr "height" "400"]
    [Svg.polyline [attr "fill" "none", attr "stroke" "steelblue", attr "points" (Series.points mode series 100 500)] []]
-- end chart

def sourcePanel (m : Model) : Html Msg :=
  div [attr "id" "sources"] (m.sources.map fun (name, text) =>
    details [attr "class" "source"] [summary [] [.text s!"Source of {name}"], pre [] [.text text]])

def view (m : Model) : Html Msg :=
  let reading := inspect series m.column
  let sampleCount := m.sampleCount
  let stations := (m.manifest.map (·.stations.size)).getD 0
  main_ [] [
    p [attr "id" "status"] [.text (m.failure.getD (if m.manifest.isSome then "" else "Loading tiles"))],
    div [] [
      button [onClick .zoomIn, attr "id" "zoom-in"] [.text "Zoom in"],
      button [onClick .zoomOut, attr "id" "zoom-out"] [.text "Zoom out"],
      button [onClick .panLeft, attr "id" "pan-left"] [.text "Left"],
      button [onClick .panRight, attr "id" "pan-right"] [.text "Right"],
      span [attr "id" "range"] [.text s!"samples {(Range.ofInterval sampleCount m.view.x).lo} to {(Range.ofInterval sampleCount m.view.x).hi}"]],
    div [attr "id" "charts"] (if m.manifest.isSome then (List.range linkedCharts).map (stacked stations (Range.ofInterval sampleCount m.view.x)) else []),
    p [attr "id" "error-bound"] [.text (errorBound (Range.ofInterval sampleCount m.view.x))],
    div [] [
      button [onClick (.robot 1), attr "id" "robot-run"] [.text "Run input robot"],
      span [attr "id" "robot"] [.text m.robot]],
    button [onClick .toggle, attr "id" "toggle"] [.text s!"Decimation: {modeName m.mode}"],
    lineChart m.mode,
    sourcePanel m,
    input [attr "id" "column", attr "type" "number", value (toString m.column),
      onInput fun s => .pick (s.toInt?.getD 0)],
    div [attr "id" "inspector", prop "innerHTML" (.str (reading.html (some guaranteeText)))] []]

def main : IO Unit := do
  let manifest ← IO.mkRef none
  let catalogue ← IO.mkRef none
  let cache ← TileCache.new tileCacheCapacity
  register "inkproof-chart" (sceneOf cache manifest catalogue)
  let app : App Unit Model Msg := App.element (fun _ => ({}, Cmd.batch [Http.get manifestUrl .manifest, Http.get sourcesUrl .sources])) update view
  App.run app
