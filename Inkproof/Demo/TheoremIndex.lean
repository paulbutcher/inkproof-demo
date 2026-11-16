/-
Copyright (c) 2026 Paul Butcher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

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

/-- The name and statement of an `API.lock` line that declares a theorem. -/
def parseTheorem (line : String) : Option (String × String) :=
  if line.startsWith "theorem " then
    match (line.drop 8).toString.splitOn " : " with
    | name :: rest@(_ :: _) => some (name, " : ".intercalate rest)
    | _ => none
  else none

/-- Whether `line` declares theorem `name`, written in full or relative to its namespaces. -/
def declares (name : String) (line : String) : Bool :=
  match line.splitOn "theorem " with
  | _ :: rest@(_ :: _) =>
    let token := (" ".intercalate rest).takeWhile fun c => !c.isWhitespace && c != ':'
    token == name || name.endsWith ("." ++ token)
  | _ => false

/-- The file declaring theorem `name`, with the 1-based line, preferring the module named by its namespaces. A theorem with no declaration of its own, such as a structure field or an instance, gets the module its namespaces name, if there is one. -/
def locate (sources : Array (String × String)) (name : String) : Option (String × Option Nat) :=
  let parts := name.splitOn "."
  let prefixes := ((List.range parts.length).map fun k => "/".intercalate (parts.take k) ++ ".lean").reverse
  let rank (path : String) : Nat := (prefixes.findIdx? (· == path)).getD prefixes.length
  let ordered := sources.qsort fun a b => rank a.1 < rank b.1
  let declared := ordered.findSome? fun (path, text) =>
    ((text.splitOn "\n").findIdx? (declares name)).map fun i => (path, some (i + 1))
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
    (parseTheorem line).map fun (name, statement) =>
      { library := lib.repo, name, statement, url := sourceUrl lib name }

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
