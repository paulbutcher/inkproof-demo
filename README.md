# Inkproof.Demo

Part of Inkproof. Released under the Apache 2.0 license; see `LICENSE`.

An application, not a library: a browser demo of seismic recordings and earthquakes charted with the Inkproof libraries. Nothing depends on it, so there is nothing to require; clone it and follow the steps below. It uses `inkproof-web`, `inkproof-export` and `inkproof-core` at release tags.

## What it does

The public modules under `Inkproof/Demo/`, by job:

- Decode miniSEED recordings (Steim 1 and 2, either byte order): `MiniSeed.decodeFile`, `MiniSeed.decodeRecord`.
- Lay decoded records out on a regular sample grid with gaps: `Place.place`.
- Cut a station into tile files and a manifest, using Core's pyramid: `Tiles.stationTiles`, `Tiles.tileBytes`, `Tiles.manifest`, `Tiles.encodeNode`, `Tiles.rawBytes`.
- Read tiles back into min/max extents for a pixel range: `TileRead.levelFor`, `TileRead.nodeRange`, `Loaded.tileNodes`, `Loaded.levelQuery`, `Manifest.parse`.
- Parse and write the earthquake catalogue (USGS CSV to `catalogue.json`): `Catalogue.parseCsv`, `Catalogue.toJson`, `Catalogue.parseJson`.
- Turn extents and quakes into chart items for a view range: `Plot.traces`, `Plot.quakes`, `Plot.bins`, `Plot.src`, `Seismic.markers`, `View.inView`.
- Draw a display list to GPU commands or raw pixels: `Draw.frame`, `Draw.tile`, `Draw.bytes`.
- Compute the guaranteed pixel error bound shown in the app: `Bound.pixelError`.
- Compare guaranteed and naive decimation and read a pixel column: `Inspect.inspect`, `Inspect.Decimation.apply`, `Series.points`.
- Drive random pan and zoom against the linked-view invariants: `Robot.run`.
- List the proved guarantees and the trusted computing base for the page: `Library.html`, `Library.theorems`, `Inspect.guaranteeStatement`, `TcbRow`.
- Choose how the code panel labels a file: `CodeKind.ofNat`, `CodeKind.matches`.

## Data

The demo charts public seismic recordings and earthquakes. Fetching is a separate step from building, and nothing here runs it for you.

1. Fetch: `node scripts/fetch.mjs [--data <dir>] [--full-year] [--days <n>]`. The data directory defaults to the git-ignored `data/`. By default it fetches one station for one week (`scripts/selection.json`); `--full-year` fetches the pinned year, which is large. Days already on disk are skipped, so rerun it to resume an interrupted fetch. Only Node 24 is needed.
2. Build tiles: `lake exe build-real-tiles <miniSEED station dir> <output dir>` cuts one station's day files into tiles. Peak memory is about 560 MiB for one day and 580 MiB for a week of ANMO (measured with `getrusage`), because it works in chunks of 2^20 samples and not the whole recording; it does not grow with the range.
3. Build the catalogue: `lake exe build-catalogue <data>/catalogue/<range>.csv <output dir>` writes `catalogue.json` next to the tiles, placing each quake on the tiles' sample grid from the `recording.json` that step 2 wrote. It holds the catalogue (a few thousand rows) in memory and nothing else.
4. Serve: the static site from local disk.

## Building the browser app

Run Lasm with `LASM_EDITOR=0`, as in `LASM_EDITOR=0 npx lasm build` from `app/`, or it applies an elan override that breaks the build. Install the packages first with `npm ci` in `app/`, `test/` and the repository root.

## Attribution

Waveforms are from the Global Seismographic Network (network IU, https://doi.org/10.7914/SN/IU), distributed by the EarthScope Data Services (https://service.earthscope.org). The earthquake catalogue is the USGS ComCat (https://earthquake.usgs.gov/fdsnws/event/1/).
