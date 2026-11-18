# Inkproof.Demo

Part of Inkproof. Released under the Apache 2.0 license; see `LICENSE`.

An application, not a library: a browser demo of seismic recordings and earthquakes charted with the Inkproof libraries. Nothing depends on it, so there is nothing to require; clone it and follow the steps below. It uses `inkproof-web`, `inkproof-export` and `inkproof-core` at release tags.

## What it does

The public modules under `Inkproof/Demo/`, by job:

- Decode miniSEED recordings (Steim 1 and 2, either byte order): `MiniSeed.decodeFile`, `MiniSeed.decodeRecord`.
- Lay decoded records out on a regular sample grid with gaps: `Place.place`.
- Cut a station into tile files and a manifest, using Core's pyramid: `Tiles.stationTiles`, `Tiles.tileBytes`, `Tiles.manifest`, `Tiles.encodeNode`, `Tiles.rawBytes`.
- Decode fetched tile and raw sample files into min/max extents, and find the raw day files a sample range needs: `Loaded.decodeTile`, `Raw.decodeLeaves`, `Raw.pieces`, `Manifest.parse`, `Manifest.toJson`.
- Parse and write the earthquake catalogue (USGS CSV to `catalogue.json`): `Catalogue.parseCsv`, `Catalogue.toJson`, `Catalogue.parseJson`.
- Turn extents and quakes into chart items for a view range: `Plot.traces`, `Stack.peak`, `Plot.quakes`, `Plot.bins`, `Plot.src`, `Seismic.markers`, `View.inView`.
- Draw a display list to GPU commands or raw pixels: `Draw.frame`, `Draw.tile`, `Draw.bytes`.
- Compute the guaranteed pixel error bound shown in the app: `Bound.pixelError`.
- Compare guaranteed and naive decimation and read a pixel column: `Inspect.inspect`, `Inspect.Decimation.apply`, `Series.points`.
- Drive random pan and zoom against the linked-view invariants: `Robot.run`.
- List the proved guarantees and the trusted computing base for the page: `Library.html`, `Library.theorems`, `Inspect.guaranteeStatement`, `TcbRow`.
- Find the file and line declaring a proved theorem in the library sources: `locate`, `declarationLine`.
- Choose how the code panel labels a file: `CodeKind.ofNat`, `CodeKind.matches`.

## Data

The demo charts public seismic recordings and earthquakes. Fetching is a separate step from building, and nothing here runs it for you.

1. Fetch: `node scripts/fetch.mjs [--data <dir>] [--quarter] [--days <n>]`. The data directory defaults to the git-ignored `data/`. By default it fetches one station for one week (`scripts/selection.json`); `--quarter` fetches the pinned four stations for the 90 days from 2025-03-01, about 3 GB of miniSEED. Days already on disk are skipped, so rerun it to resume an interrupted fetch. Only Node 24 is needed.
2. Build tiles: `lake exe build-real-tiles <miniSEED station dir> <output dir>` cuts one station's day files into tiles. Peak memory is about 560 MiB for one day, 580 MiB for a week and 0.9 to 1.2 GiB for each of the four stations over the 90 days (peak resident size), because it works in chunks of 2^20 samples and not the whole recording; it stops growing between a week and 20 days. A station takes two to eleven minutes and about 3 GB of tiles.
3. Describe the tile set: `lake exe build-manifest <site dir> <station tile dir>...` writes the site's `manifest.json` from the stations' manifests and raw day files; link each station's `s0` as `<site dir>/s<i>`.
4. Build the catalogue: `lake exe build-catalogue <data>/catalogue/<range>.csv <output dir>` writes `catalogue.json` next to the tiles, placing each quake on the tiles' sample grid from the `recording.json` that step 2 wrote. It holds the catalogue (a few thousand rows) in memory and nothing else.
4. Serve: the static site from local disk.

## Looking at the quarter

With the quarter fetched and the four stations' tiles built (steps 1 and 2 above, `--quarter`), build `data/site` with step 3 and 4 (`recording.json` is copied from the first station's tile directory), then `cd app && npx vite build`, replace `dist/tiles` with a link to `data/site` and run `npx vite preview`. In the page:

- Four stacked station traces with the earthquake markers along the top: zoom in and out and pan with the buttons, from the whole quarter down to individual samples. Each track is scaled to the largest value in view.
- Station outages are blank stretches in a track, for instance ANMO on days 81 to 83 (zoom to 2025-03-22).
- A tile that fails to load is labelled in red on the chart and logged at warn.
- The placement error bound is shown under the charts, with the theorem that proves it and its normal-range condition.
- `INKPROOF_SITE=../data/site node --test quarter.test.mjs` in `app/` checks that every catalogued quake has a marker at three zooms after a jump to it, and that each station's outages are gaps, against the real tiles.

## Building the browser app

Run Lasm with `LASM_EDITOR=0`, as in `LASM_EDITOR=0 npx lasm build` from `app/`, or it applies an elan override that breaks the build. Install the packages first with `npm ci` in `app/`, `test/` and the repository root.

## Attribution

Waveforms are from the Global Seismographic Network (network IU, https://doi.org/10.7914/SN/IU), distributed by the EarthScope Data Services (https://service.earthscope.org). The earthquake catalogue is the USGS ComCat (https://earthquake.usgs.gov/fdsnws/event/1/).
