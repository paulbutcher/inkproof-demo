/-
Copyright (c) 2026 Paul Butcher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Lake
open Lake DSL

package «inkproof-demo» where
  leanOptions := #[
    ⟨`autoImplicit, false⟩,
    ⟨`relaxedAutoImplicit, false⟩,
    ⟨`warningAsError, true⟩
  ]

require «inkproof-web» from git "https://github.com/paulbutcher/inkproof-web" @ "v0.4.1"
require «inkproof-export» from git "https://github.com/paulbutcher/inkproof-export" @ "v0.3.0"
require «inkproof-viewport» from git "https://github.com/paulbutcher/inkproof-viewport" @ "v0.4.0"
require «inkproof-scene» from git "https://github.com/paulbutcher/inkproof-scene" @ "v0.6.0"
require «inkproof-gpu» from git "https://github.com/paulbutcher/inkproof-gpu" @ "v0.5.0"

@[default_target]
lean_lib InkproofDemo where
  roots := #[`Inkproof.Demo]

@[test_driver]
script tests do
  let child ← IO.Process.spawn
    { cmd := "lake", args := #["test"], cwd := __dir__ / "test" }
  child.wait

lean_exe «theorem-index» where
  root := `TheoremIndexMain
  srcDir := "gen"

lean_exe «build-tiles» where
  root := `BuildTilesMain
  srcDir := "gen"
