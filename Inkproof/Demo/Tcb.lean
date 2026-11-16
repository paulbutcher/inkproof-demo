/-
Copyright (c) 2026 Paul Butcher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Inkproof.Demo.TheoremIndex

namespace Inkproof.Demo

structure TcbRow where
  component : String
  why : String
  mitigation : String

def tcbRows : List TcbRow := [
  ⟨"Generated JS decoder and interpreter", "JavaScript, outside Lean", "Generated from one Lean definition; templates reviewed; round-trip tests"⟩,
  ⟨"Generated GLSL shaders", "Run on the GPU", "Generated from proved shader-language expressions; printer tested"⟩,
  ⟨"Code generator templates", "Their output is trusted", "Few templates; reviewed; any template bug is systematic, so tests catch it"⟩,
  ⟨"Lasm browser bindings", "The Lean glue reaches browser APIs through them", "Part of Lasm, pinned with it; any fallback JavaScript shim is listed below with its line count"⟩,
  ⟨"Lean compiler and runtime", "Compiles proved source", "Differential tests between native and Lasm builds"⟩,
  ⟨"Lasm compiler, runtime, Emscripten", "Compiles Lean to Wasm", "Same differential tests; pin versions"⟩,
  ⟨"Browser, GPU driver", "Execute WebGL calls and shaders", "Visual checks on a device matrix; known driver issues documented"⟩,
  ⟨"Float-order axiom", "Lean floats are opaque to proofs", "One reviewed axiom; wrapper type excluding NaN and -0.0; tested on each platform's floats"⟩,
  ⟨"Float rounding model", "Lean floats are opaque to proofs", "One reviewed axiom, in the IEEE 754 round-to-nearest form for binary64; tested on each platform's floats"⟩,
  ⟨"Host text measurement", "Used by label layout", "Stated as a hypothesis of the theorem"⟩,
  ⟨"Time-zone data", "External data", "Versioned and stated as an input"⟩]

inductive CodeKind where
  | template
  | generated
  | shim
  deriving DecidableEq

def CodeKind.label : CodeKind → String
  | .template => "Generator template"
  | .generated => "Generated output"
  | .shim => "Hand-written JavaScript shim"

/-- Whether a file of a library counts towards a kind of trusted code. -/
def CodeKind.matches (kind : CodeKind) (repo path : String) : Bool :=
  match kind with
  | .template => repo == "inkproof-gpu" && path == "Inkproof/Gpu/Js.lean"
  | .generated => path.startsWith "generated/" || path.startsWith "gpu-js/"
  | .shim => path.startsWith "shim/" && path.endsWith ".js"

structure CodeFile where
  kind : CodeKind
  repo : String
  path : String
  lines : Nat

def lineCount (text : String) : Nat :=
  (text.splitOn "\n").length - (if text.endsWith "\n" then 1 else 0)

/-- The trusted-code files among `files` (repository, path, contents), with their line counts. -/
def codeFiles (files : Array (String × String × String)) : Array CodeFile :=
  files.flatMap fun (repo, path, text) =>
    #[CodeKind.template, .generated, .shim].filterMap fun kind =>
      if kind.matches repo path then some { kind, repo, path, lines := lineCount text } else none

def tcbHtml (files : Array CodeFile) : String :=
  let row (r : TcbRow) :=
    s!"<tr><td>{escapeHtml r.component}</td><td>{escapeHtml r.why}</td><td>{escapeHtml r.mitigation}</td></tr>"
  let kinds := #[CodeKind.template, .generated, .shim]
  let total (k : CodeKind) := (files.filter (·.kind == k)).foldl (· + ·.lines) 0
  let countRow (k : CodeKind) :=
    let detail := ", ".intercalate ((files.filter (·.kind == k)).toList.map fun f => s!"{f.repo}/{f.path}: {f.lines}")
    s!"<tr><td>{k.label}</td><td>{total k}</td><td>{escapeHtml detail}</td></tr>"
  "<section id=\"tcb\"><h2>Trusted computing base</h2><table><thead><tr><th>Component</th><th>Why trusted</th><th>Mitigation</th></tr></thead><tbody>" ++
  "".intercalate (tcbRows.map row) ++
  "</tbody></table><h3>Lines of trusted code</h3><table><thead><tr><th>Kind</th><th>Lines</th><th>Files</th></tr></thead><tbody>" ++
  "".intercalate (kinds.toList.map countRow) ++ "</tbody></table></section>"

end Inkproof.Demo
