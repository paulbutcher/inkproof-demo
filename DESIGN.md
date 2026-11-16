# Inkproof.Demo design

## Theorem index and trusted computing base

`Inkproof.Demo.TheoremIndex`, `Tcb` and `Page` are native modules that do not import Lasm. `lake exe theorem-index <project dir> <output.html>` reads each pinned library's `API.lock` and sources from `<project dir>/.lake/packages`, so the page always describes the releases the demo is built against. A theorem links to its declaration at the library's tag, or to the module its namespaces name when it has no declaration of its own (a structure field, an instance). Line counts of generator templates, generated output and hand-written JavaScript shims are measured from the same sources.

## Decimation toggle and pixel inspector

`Inkproof.Demo.Inspect` is a native module that does not import Lasm. `Decimation` selects between the library's guaranteed reduction (`reducePoints`) and naive decimation, which keeps the first sample of each pixel column and drops the rest; the toggle is `Decimation.toggle`. `inspect` gives, for one pixel column, the raw samples, their lowest and highest values computed by a plain fold that shares nothing with the library's reduction, and the extremes of what the guaranteed reduction draws, so the two can be compared. The plain-English statement of `Inkproof.Scene.reducePoints_covers` is shown beside its formal statement, read from the pinned release's `API.lock`. That the drawn extremes equal the raw ones is tested over generated series rather than proved: it needs `reduceRun_spec` lifted through `groupByKey`.

## Browser app

`app/` is the Lasm browser build: `App.lean` is a Lasm.UI app over the native modules, drawing the series (`Inkproof.Demo.Series`) as an SVG polyline under the chosen `Decimation`, with the toggle and the inspector panel (`Reading.html`) beside it. Its `package.json` takes the Gpu interpreter and the custom-element shim from the pinned `inkproof-web` package under `.lake/packages`, so `lake build` must run before `npm ci`. `lake test` builds it with Vite and runs `app/browser.test.mjs` in headless Chromium when `app/node_modules` exists. Tests check that naive decimation draws fewer points and a higher lowest peak than the guaranteed mode, that toggling back restores the same points, and that the inspector shows the raw sample count, the maximum and the guarantee. The WebGL chart elements of the full demo are not in it yet.

## Drawing

`Inkproof.Demo.Draw` is a native module that does not import Lasm. `frame` turns a Scene display list into the wire commands a Web chart element runs: clear, build and use the renderer's program, then Gpu's `compile` over one tile whose grid is device pixels from the top left, with Gpu's `tessellate` for the vertex words. `bytes` is its encoding, the `commands` of a Web `Scene`. Tested that every quake marker is one draw and that a frame survives the wire.

## Seismic model

`Inkproof.Demo.Seismic` is a native module that does not import Lasm. A `Station` is a pseudo-random trace that is absent during its outages; samples become `Extent` (minimum and maximum) leaves of a Core `Pyramid`, so a tile node is the extent of the samples under it and a range with no samples is a gap (`isGap`). The earthquake catalogue is a Core `Series` drawn with Scene's `compileScatter`, which gives every catalogued quake a marker whatever the view. The theorems that need Core's proof modules (`isGap_fold`, `marker_of_quake`) live in `test/Main.lean`, so the browser build does not link them. `Inkproof.Demo.Stack` turns a station's pyramid and a view into pixel-column extents (`columns`) and then into one outline per stretch of recorded samples (`traces`); a column wholly inside an outage is absent and ends a run, so no outline spans a gap (`runs_mem`). `Inkproof.Demo.View` turns Viewport's interval, which does the zooming and panning, into the visible sample `Range` clamped to the recording (`ofInterval_valid`), and puts each quake in view in a pixel column inside the chart (`column_lt`). The browser app draws four stations stacked as SVG outlines, one per recorded stretch, with a marker for each quake in view, and buttons to zoom and pan. The tiled static site, the WebGL chart elements and linking of several charts are not built yet.

## Tiles

`Inkproof.Demo.Tiles` is a native module that does not import Lasm. Each level of a station's pyramid is cut into files of `tileSize` nodes, `s<station>/l<level>/t<n>.bin`, and a node is two little-endian 16-bit words, lowest then highest, with the gap word twice for a node with no samples (`decodeNode_encodeNode`, `decodeNode_gap`). `lake exe build-tiles <dir>` writes the files and a `manifest.json` of level sizes; `lake test` writes them to `app/web/public/tiles` before the Vite build, so the static site carries them. The stations are listed in `gen/BuildTilesMain.lean` and again in `app/App.lean`.
