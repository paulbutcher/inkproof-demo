# Inkproof.Demo design

## Theorem index and trusted computing base

`Inkproof.Demo.TheoremIndex`, `Tcb` and `Page` are native modules that do not import Lasm. `lake exe theorem-index <project dir> <output.html>` reads each pinned library's `API.lock` and sources from `<project dir>/.lake/packages`, so the page always describes the releases the demo is built against. A theorem links to its declaration at the library's tag, or to the module its namespaces name when it has no declaration of its own (a structure field, an instance). Line counts of generator templates, generated output and hand-written JavaScript shims are measured from the same sources.

## Decimation toggle and pixel inspector

`Inkproof.Demo.Inspect` is a native module that does not import Lasm. `Decimation` selects between the library's guaranteed reduction (`reducePoints`) and naive decimation, which keeps the first sample of each pixel column and drops the rest; the toggle is `Decimation.toggle`. `inspect` gives, for one pixel column, the raw samples, their lowest and highest values computed by a plain fold that shares nothing with the library's reduction, and the extremes of what the guaranteed reduction draws, so the two can be compared. The plain-English statement of `Inkproof.Scene.reducePoints_covers` is shown beside its formal statement, read from the pinned release's `API.lock`. That the drawn extremes equal the raw ones is tested over generated series rather than proved: it needs `reduceRun_spec` lifted through `groupByKey`.

## Browser app

`app/` is the Lasm browser build: `App.lean` is a Lasm.UI app over the native modules, drawing the series (`Inkproof.Demo.Series`) as an SVG polyline under the chosen `Decimation`, with the toggle and the inspector panel (`Reading.html`) beside it. Its `package.json` takes the Gpu interpreter and the custom-element shim from the pinned `inkproof-web` package under `.lake/packages`, so `lake build` must run before `npm ci`. `lake test` builds it with Vite and runs `app/browser.test.mjs` in headless Chromium when `app/node_modules` exists. Tests check that naive decimation draws fewer points and a higher lowest peak than the guaranteed mode, that toggling back restores the same points, and that the inspector shows the raw sample count, the maximum and the guarantee. The WebGL chart elements of the full demo are not in it yet.
