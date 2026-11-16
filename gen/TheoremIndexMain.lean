/-
Copyright (c) 2026 Paul Butcher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Inkproof.Demo
import Lean.Data.Json

open Lean System

/-- Every `.lean`, `.js`, `.glsl` file under `dir`, as (path relative to `dir`, contents). -/
def readFiles (dir : FilePath) : IO (Array (String × String)) := do
  let mut out := #[]
  for f in ← dir.walkDir fun p => pure (p.fileName != some ".lake" && p.fileName != some "test") do
    if f.extension.any (["lean", "js", "glsl"].contains ·) && !(← f.isDir) then
      let rel := (f.toString.drop (dir.toString.length + 1)).toString
      out := out.push (rel, ← IO.FS.readFile f)
  return out

/-- The pinned tag of each package in a lake manifest, by repository name. -/
def pinnedTags (manifest : FilePath) : IO (Array (String × String)) := do
  let json ← IO.ofExcept (Json.parse (← IO.FS.readFile manifest))
  let pkgs ← IO.ofExcept (json.getObjVal? "packages" >>= Json.getArr?)
  pkgs.filterMapM fun p => do
    let name ← IO.ofExcept (p.getObjValAs? String "name")
    let tag ← IO.ofExcept (p.getObjValAs? String "inputRev")
    return if name.startsWith "«inkproof-" then
      some (((name.drop 1).dropEnd 1).toString, tag) else none

/-- Usage: `theorem-index <project dir> <output file>`; the project's packages are read from `<project dir>/.lake/packages`. -/
def main (args : List String) : IO UInt32 := do
  let [project, out] := args | IO.eprintln "usage: theorem-index <project dir> <output file>"; return 1
  let mut libs := #[]
  let mut files := #[]
  for (repo, tag) in ← pinnedTags (FilePath.mk project / "lake-manifest.json") do
    let dir := FilePath.mk project / ".lake" / "packages" / repo
    let sources ← readFiles dir
    libs := libs.push
      { repo, tag, apiLock := ← IO.FS.readFile (dir / "API.lock"), sources := sources.filter (·.1.endsWith ".lean") :
        Inkproof.Demo.Library }
    files := files ++ sources.map fun (path, text) => (repo, path, text)
  IO.FS.writeFile out (Inkproof.Demo.theoremPage libs (Inkproof.Demo.codeFiles files))
  return 0
