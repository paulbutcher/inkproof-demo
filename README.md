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
- Drive random pan and zoom against the linked-view invariants, natively and in the page: `Robot.run`, `Robot.runSeed`.
- Read the marked chart sources out of the app's Lean file for the page's source panel: `Source.regions`, `Source.toJson`, `Source.parse`.
- List the proved guarantees and the trusted computing base for the page: `Library.html`, `Library.theorems`, `Inspect.guaranteeStatement`, `TcbRow`.
- Find the file and line declaring a proved theorem in the library sources: `locate`, `declarationLine`.
- Choose how the code panel labels a file: `CodeKind.ofNat`, `CodeKind.matches`.

## Build and run

Needs git, Node 24 or later, [elan](https://github.com/leanprover/elan) (it installs the toolchain in `lean-toolchain`), a browser with WebGL and network access. Run from the repository root. Times are from an 18-core machine.

The slice, one station for one week (0.3 GB of disk, about ten minutes, about 580 MiB peak memory):

```sh
git clone https://github.com/paulbutcher/inkproof-demo.git && cd inkproof-demo
lake build
npm ci && (cd app && npm ci)
node scripts/fetch.mjs                    # resumes if interrupted
lake exe build-real-tiles data/mseed/IU.ANMO.00.HHZ data/tiles/IU.ANMO.00.HHZ
mkdir -p data/site && ln -s ../tiles/IU.ANMO.00.HHZ/s0 data/site/s0
lake exe build-manifest data/site data/tiles/IU.ANMO.00.HHZ
cp data/tiles/IU.ANMO.00.HHZ/recording.json data/site/
lake exe build-catalogue data/catalogue/2025-03-01_7.csv data/site
mkdir -p app/web/public && lake exe build-sources app/App.lean app/web/public/chart-sources.json
cd app && LASM_EDITOR=0 npx vite build    # LASM_EDITOR=0 stops an elan override breaking Lasm
rm -rf dist/tiles && ln -s ../../data/site dist/tiles && npx vite preview
```

Open http://localhost:4173/: one trace with a few earthquake markers.

The quarter, four stations for 90 days, needs 15 GB of disk (3 GB of miniSEED, 12 GB of tiles). After the slice's `lake build`, `npm ci` and `build-sources`, from the root:

```sh
rm -rf data/tiles data/site && node scripts/fetch.mjs --quarter    # about ten minutes
for s in ANMO COLA KONO MAJO; do lake exe build-real-tiles data/mseed/IU.$s.00.HHZ data/tiles/IU.$s.00.HHZ; done
mkdir data/site && i=0 && for s in ANMO COLA KONO MAJO; do ln -s ../tiles/IU.$s.00.HHZ/s0 data/site/s$i; i=$((i+1)); done
lake exe build-manifest data/site data/tiles/IU.{ANMO,COLA,KONO,MAJO}.00.HHZ
cp data/tiles/IU.ANMO.00.HHZ/recording.json data/site/ && lake exe build-catalogue data/catalogue/2025-03-01_90.csv data/site
cd app && LASM_EDITOR=0 npx vite build && rm -rf dist/tiles && ln -s ../../data/site dist/tiles && npx vite preview
```

Each station's tiles take two to eleven minutes and peak at 0.9 to 1.2 GiB resident, since they are cut in chunks of 2^20 samples; memory stops growing past about 20 days.

## Looking at the quarter

In the page:

- Four stacked station traces with the earthquake markers along the top: zoom in and out and pan with the buttons, from the whole quarter down to individual samples. Each track is scaled to the largest value in view.
- Station outages are blank stretches in a track, for instance ANMO on days 81 to 83 (zoom to 2025-03-22).
- A tile that fails to load is labelled in red on the chart and logged at warn.
- The placement error bound is shown under the charts, with the theorem that proves it and its normal-range condition.
- `INKPROOF_SITE=../data/site node --test quarter.test.mjs` in `app/` checks that every catalogued quake has a marker at three zooms after a jump to it, and that each station's outages are gaps, against the real tiles.

## Attribution

Waveforms are from the Global Seismographic Network (network IU, https://doi.org/10.7914/SN/IU), distributed by the EarthScope Data Services (https://service.earthscope.org). The earthquake catalogue is the USGS ComCat (https://earthquake.usgs.gov/fdsnws/event/1/).
