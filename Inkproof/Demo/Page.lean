/-
Copyright (c) 2026 Paul Butcher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Inkproof.Demo.Tcb

namespace Inkproof.Demo

def theoremPage (libs : Array Library) (code : Array CodeFile) : String :=
  "<!doctype html><html lang=\"en\"><head><meta charset=\"utf-8\"><title>Inkproof theorems</title></head><body><h1>Theorems and trusted computing base</h1>" ++
  tcbHtml code ++ "".intercalate (libs.toList.map (·.html)) ++ "</body></html>\n"

end Inkproof.Demo
