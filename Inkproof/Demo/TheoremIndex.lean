/-
Copyright (c) 2026 Paul Butcher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import InkproofTools.ApiLock.Reader

namespace Inkproof.Demo

/-- A released library: its repository name, release tag, `API.lock` text and Lean sources as (path, contents). -/
structure Library where
  repo : String
  tag : String
  apiLock : String
  sources : Array (String × String)

structure TheoremEntry where
  library : String
  name : String
  statement : String
  url : String

/-- The namespaces open after a source line, given those open before it. -/
private def namespacesAfter (line : String) (open_ : List String) : List String :=
  match line.trimAscii.toString.splitOn " " with
  | ["namespace", n] => open_ ++ n.splitOn "."
  | ["end", n] => open_.take (open_.length - (n.splitOn ".").length)
  | _ => open_

/-- The 1-based line of the source text that declares theorem `name`, tracking the namespaces it is read inside. -/
def declarationLine (text name : String) : Option Nat :=
  let step := fun (st : List String × Option Nat × Nat) line =>
    let (ns, found, i) := st
    (namespacesAfter line ns, found <|> if InkproofTools.ApiLock.declaresInSourceAt line name ns then some i else none, i + 1)
  ((text.splitOn "\n").foldl step ([], none, 1)).2.1

/-- The file declaring theorem `name`, with the 1-based line, preferring the module named by its namespaces. A theorem with no declaration of its own, such as a structure field or an instance, gets the module its namespaces name, if there is one. -/
def locate (sources : Array (String × String)) (name : String) : Option (String × Option Nat) :=
  let parts := name.splitOn "."
  let prefixes := ((List.range parts.length).map fun k => "/".intercalate (parts.take k) ++ ".lean").reverse
  let rank (path : String) : Nat := (prefixes.findIdx? (· == path)).getD prefixes.length
  let ordered := sources.qsort fun a b => rank a.1 < rank b.1
  let declared := ordered.findSome? fun (path, text) => (declarationLine text name).map fun i => (path, some i)
  declared <|> (ordered[0]?.bind fun (path, _) => if rank path < prefixes.length then some (path, none) else none)

def githubUrl (repo tag : String) : String :=
  s!"https://github.com/paulbutcher/{repo}/blob/{tag}"

/-- A link to the source of theorem `name`: its declaration when found, otherwise the library at its tag. -/
def sourceUrl (lib : Library) (name : String) : String :=
  match locate lib.sources name with
  | some (path, some line) => s!"{githubUrl lib.repo lib.tag}/{path}#L{line}"
  | some (path, none) => s!"{githubUrl lib.repo lib.tag}/{path}"
  | none => githubUrl lib.repo lib.tag

/-- Every theorem in the library's `API.lock`, in file order. -/
def Library.theorems (lib : Library) : Array TheoremEntry :=
  (lib.apiLock.splitOn "\n").toArray.filterMap fun line =>
    (InkproofTools.ApiLock.parseTheorem line).map fun thm =>
      { library := lib.repo, name := thm.name, statement := thm.statement, url := sourceUrl lib thm.name }

def escapeHtml (s : String) : String :=
  s.foldl (fun acc c => acc ++ match c with
    | '&' => "&amp;" | '<' => "&lt;" | '>' => "&gt;" | '"' => "&quot;" | c => c.toString) ""

def TheoremEntry.html (e : TheoremEntry) : String :=
  s!"<li><a href=\"{escapeHtml e.url}\"><code>{escapeHtml e.name}</code></a>" ++
  s!"<pre>{escapeHtml e.statement}</pre></li>"

def Library.html (lib : Library) : String :=
  let es := lib.theorems
  s!"<section id=\"{lib.repo}\"><h2>{lib.repo} {lib.tag} ({es.size} theorems)</h2><ul>" ++
  "".intercalate (es.toList.map (·.html)) ++ "</ul></section>"

end Inkproof.Demo
