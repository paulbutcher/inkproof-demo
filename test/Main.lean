/-
Copyright (c) 2026 Paul Butcher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Inkproof.Demo
import Inkproof.Viewport
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

/-! Theorems for the pure functions whose definitions unfold directly. `escapeHtml`, `lineCount`, `locate`, `declares`, `parseTheorem` on theorem lines and `Library.theorems` go through `String.foldl`, `String.splitOn`, `Array.qsort` and `Array.filterMap`, whose lemmas are too thin to close proofs about them here, so those behaviours are tested below instead. `tcbHtml` and `codeFiles` on non-empty input are string concatenations and folds over those same functions, so they are tested too. -/

theorem parseTheorem_other (line : String) (h : line.startsWith "theorem " = false) :
    parseTheorem line = none := by simp [parseTheorem, h]

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

private def robotConfig : Inkproof.Viewport.ViewConfig Float :=
  let axis : Inkproof.Viewport.Interval.Config Float :=
    { length := 800, minSpan := 0.5, maxSpan := 1000, home := ⟨0, 100⟩, keyZoom := 1.25, keyPan := 0.1 }
  ⟨axis, { axis with length := 400 }⟩

def robotTest : Except String Unit := do
  for seed in [1:101] do
    if let some e := Robot.run robotConfig 4 seed 1000 then
      check false s!"seed {seed}: {e}"

def main (args : List String) : IO UInt32 :=
  runTests [⟨"theorem index", indexTest⟩, ⟨"page", htmlTest⟩, ⟨"tcb", tcbTest⟩, ⟨"input robot", robotTest⟩,
    platformTest (args.contains "--expect-wasm")]
