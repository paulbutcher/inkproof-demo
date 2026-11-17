/-
Copyright (c) 2026 Paul Butcher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Lasm.UI
import Lasm.JS.Web.Fetch
import Inkproof.Demo
import Inkproof.Web.Host.Chart

open Lasm.UI Inkproof.Web.Host Inkproof.Demo Inkproof.Demo.Inspect Inkproof.Demo.View Inkproof.Viewport

def sampleCount : Nat := 4096
def chartCols : Nat := 400
def trackHeight : Nat := 100
def chartHeight : Nat := 200

def axisConfig : Interval.Config Rat :=
  { length := chartCols, minSpan := 2, maxSpan := sampleCount, home := ⟨0, sampleCount⟩, keyZoom := 2, keyPan := 1 / 4 }

def viewConfig : ViewConfig Rat := ⟨axisConfig, axisConfig⟩

structure Model where
  mode : Decimation := .guaranteed
  column : Int := 0
  view : View Rat := ⟨axisConfig.home, axisConfig.home⟩

inductive Msg
  | toggle
  | pick (column : Int)
  | zoomIn
  | zoomOut
  | panLeft
  | panRight

def stations : Array Seismic.Station :=
  #[⟨1, [(900, 1300)]⟩, ⟨2, [(2000, 2600)]⟩, ⟨3, []⟩, ⟨4, [(300, 500), (3000, 3500)]⟩]

def quakes : Array Seismic.Quake := #[⟨100, 3⟩, ⟨1000, 5⟩, ⟨2048, 4⟩, ⟨2049, 6⟩, ⟨3700, 7⟩]

def series : List Inkproof.Scene.Pt := Series.samples 200 20

def update : Msg → Model → Model
  | .toggle, m => { m with mode := m.mode.toggle }
  | .pick c, m => { m with column := c }
  | .zoomIn, m => { m with view := View.step viewConfig m.view (.key .zoomIn) }
  | .zoomOut, m => { m with view := View.step viewConfig m.view (.key .zoomOut) }
  | .panLeft, m => { m with view := View.step viewConfig m.view (.key .left) }
  | .panRight, m => { m with view := View.step viewConfig m.view (.key .right) }

def modeName : Decimation → String
  | .guaranteed => "guaranteed"
  | .naive => "naive"

def tracePaint : Inkproof.Scene.Paint := ⟨0, ⟨70, 130, 180, 255⟩⟩

def quakeStyle : Inkproof.Scene.ScatterStyle := ⟨⟨1, ⟨220, 20, 60, 255⟩⟩, .circle, 4⟩

def topLevel : Nat := 12

abbrev TileCache := IO.Ref (Std.HashMap (Nat × Nat × Nat) (Array Seismic.Extent))

def loadTile (cache : TileCache) (s k j : Nat) : Lasm.JS.Async (Array Seismic.Extent) := do
  let key := (s, k, j)
  if let some t := (← cache.get)[key]? then return t
  let url := Tiles.tilePath s k j
  let resp ← try Lasm.JS.Web.fetch (.usvString s!"tiles/{url}") catch e =>
    log .warn "tile fetch failed" [("tile", url), ("error", toString e)]
    throw e
  unless ← resp.ok do
    log .warn "tile fetch failed" [("tile", url), ("status", toString (← resp.status))]
    throw (IO.userError s!"tile {url} not available")
  let some t := Loaded.tileNodes (← resp.bytes) | do
    log .warn "tile is not a whole number of valid nodes" [("tile", url)]
    throw (IO.userError s!"tile {url} is malformed")
  cache.modify (·.insert key t)
  return t

def stationQuery (cache : TileCache) (s : Nat) (r : Range) : Lasm.JS.Async (Nat → Nat → Seismic.Extent) := do
  let k := TileRead.readLevel topLevel (r.hi - r.lo) chartCols
  let (a, b) := TileRead.nodeRange k r.lo r.hi
  let (j0, j1) := TileRead.tileRange a b
  let mut tiles : Array (Array Seismic.Extent) := #[]
  for j in [j0:j1] do
    tiles := tiles.push (← loadTile cache s k j)
  return Loaded.levelQuery k (Loaded.nodeOf fun j => tiles.getD (j - j0) #[])

def sceneOf (cache : TileCache) (src : String) : Lasm.JS.Async Scene := do
  let some r := Plot.parseSrc src | throw (IO.userError s!"not a sample range: {src}")
  let mut qs := #[]
  let mut labels : Array Label := #[]
  for s in [0:stations.size] do
    try
      qs := qs.push (← stationQuery cache s r)
    catch _ =>
      -- The failure is already logged; an empty track would read as an outage, so say what happened.
      qs := qs.push fun _ _ => (⟨none⟩, ⟨none⟩)
      labels := labels.push { text := s!"station {s + 1}: tiles failed to load", x := 8, y := 14 + Float.ofNat (s * chartHeight / stations.size), color := "#b00020" }
  let list := Plot.traces tracePaint qs r chartCols trackHeight 1000 ++ Plot.quakes quakeStyle quakes r chartCols
  return { commands := Draw.bytes 0xffffffff chartCols (trackHeight * stations.size) list, labels }

def linkedCharts : Nat := 8

def deepest : Nat := 3000000000

def stacked (r : Range) (i : Nat) : Html Msg :=
  node "inkproof-chart" [attr "id" (if i == 0 then "stack" else s!"stack-{i}"), attr "class" "linked",
    attr "src" (Plot.src r), attr "style" s!"width:{chartCols}px;height:{chartHeight}px"] []

def errorBound (r : Range) : String :=
  s!"Placement error at most {Bound.micro (Bound.pixelError r chartCols deepest)} millionths of a pixel anywhere in a {deepest} sample recording, by {Bound.theoremName}, provided every intermediate product and sum stays in the normal floating-point range (its NormalRange hypotheses)"

def view (m : Model) : Html Msg :=
  let reading := inspect series m.column
  main_ [] [
    div [] [
      button [onClick .zoomIn, attr "id" "zoom-in"] [.text "Zoom in"],
      button [onClick .zoomOut, attr "id" "zoom-out"] [.text "Zoom out"],
      button [onClick .panLeft, attr "id" "pan-left"] [.text "Left"],
      button [onClick .panRight, attr "id" "pan-right"] [.text "Right"],
      span [attr "id" "range"] [.text s!"samples {(Range.ofInterval sampleCount m.view.x).lo} to {(Range.ofInterval sampleCount m.view.x).hi}"]],
    div [attr "id" "charts"] ((List.range linkedCharts).map (stacked (Range.ofInterval sampleCount m.view.x))),
    p [attr "id" "error-bound"] [.text (errorBound (Range.ofInterval sampleCount m.view.x))],
    button [onClick .toggle, attr "id" "toggle"] [.text s!"Decimation: {modeName m.mode}"],
    Svg.svg [attr "id" "chart", attr "viewBox" "0 0 200 100", attr "width" "800", attr "height" "400"]
      [Svg.polyline [attr "fill" "none", attr "stroke" "steelblue",
        attr "points" (Series.points m.mode series 100 500)] []],
    input [attr "id" "column", attr "type" "number", value (toString m.column),
      onInput fun s => .pick (s.toInt?.getD 0)],
    div [attr "id" "inspector", prop "innerHTML" (.str (reading.html (some guaranteeText)))] []]

def main : IO Unit := do
  let cache ← IO.mkRef {}
  register "inkproof-chart" (sceneOf cache)
  let app : App Unit Model Msg := App.sandbox {} update view
  App.run app
