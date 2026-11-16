/-
Copyright (c) 2026 Paul Butcher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Lake
open Lake DSL

package «inkproof-demo-test» where
  leanOptions := #[
    ⟨`autoImplicit, false⟩,
    ⟨`relaxedAutoImplicit, false⟩,
    ⟨`warningAsError, true⟩
  ]

require «inkproof-demo» from ".."
require «inkproof-tools» from git "https://github.com/paulbutcher/inkproof-tools" @ "v0.2.1"

@[default_target]
lean_exe tests where
  root := `Main

@[test_driver]
script test do
  let driver ← IO.Process.spawn
    { cmd := "lake", args := #["exe", "inkproof-test-driver"], cwd := __dir__ }
  let code ← driver.wait
  if code != 0 then return code
  let app := __dir__ / ".." / "app"
  unless ← (app / "node_modules" / "playwright").pathExists do
    IO.eprintln "::warning::Browser tests skipped: run `npm ci` in app/"
    return 0
  for (name, cmd, args) in #[("build", "npx", #["vite", "build"]), ("browser", "node", #["--test", "browser.test.mjs"])] do
    IO.println s!"== {name}"
    let child ← IO.Process.spawn { cmd, args, cwd := app, env := #[("LASM_EDITOR", some "0")] }
    let code ← child.wait
    if code != 0 then return code
  return 0
