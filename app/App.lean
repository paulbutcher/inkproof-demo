/-
Copyright (c) 2026 Paul Butcher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Lasm.UI
import Inkproof.Demo

open Lasm.UI Inkproof.Demo Inkproof.Demo.Inspect

structure Model where
  mode : Decimation := .guaranteed
  column : Int := 0

inductive Msg
  | toggle
  | pick (column : Int)

def series : List Inkproof.Scene.Pt := Series.samples 200 20

def update : Msg → Model → Model
  | .toggle, m => { m with mode := m.mode.toggle }
  | .pick c, m => { m with column := c }

def modeName : Decimation → String
  | .guaranteed => "guaranteed"
  | .naive => "naive"

def view (m : Model) : Html Msg :=
  let reading := inspect series m.column
  main_ [] [
    button [onClick .toggle, attr "id" "toggle"] [.text s!"Decimation: {modeName m.mode}"],
    Svg.svg [attr "id" "chart", attr "viewBox" "0 0 200 100", attr "width" "800", attr "height" "400"]
      [Svg.polyline [attr "fill" "none", attr "stroke" "steelblue",
        attr "points" (Series.points m.mode series 100 500)] []],
    input [attr "id" "column", attr "type" "number", value (toString m.column),
      onInput fun s => .pick (s.toInt?.getD 0)],
    div [attr "id" "inspector", prop "innerHTML" (.str (reading.html (some guaranteeText)))] []]

def main : IO Unit := do
  let app : App Unit Model Msg := App.sandbox {} update view
  App.run app
