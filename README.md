# Inkproof.Demo

Part of Inkproof. Released under the Apache 2.0 license; see `LICENSE`.

## Data

The demo charts public seismic recordings and earthquakes. Fetching is a separate step from building, and nothing here runs it for you.

1. Fetch: `node scripts/fetch.mjs [--data <dir>] [--full-year] [--days <n>]`. The data directory defaults to the git-ignored `data/`. By default it fetches one station for one week (`scripts/selection.json`); `--full-year` fetches the pinned year, which is large. Days already on disk are skipped, so rerun it to resume an interrupted fetch. Only Node 24 is needed.
2. Build tiles: `lake exe build-real-tiles <miniSEED station dir> <output dir>` cuts one station's day files into tiles. Peak memory is about 560 MiB for one day and 580 MiB for a week of ANMO (measured with `getrusage`), because it works in chunks of 2^20 samples and not the whole recording; it does not grow with the range.
3. Serve: the static site from local disk.

## Building the browser app

Run Lasm with `LASM_EDITOR=0`, as in `LASM_EDITOR=0 npx lasm build` from `app/`, or it applies an elan override that breaks the build. Install the packages first with `npm ci` in `app/`, `test/` and the repository root.

## Attribution

Waveforms are from the Global Seismographic Network (network IU, https://doi.org/10.7914/SN/IU), distributed by the EarthScope Data Services (https://service.earthscope.org). The earthquake catalogue is the USGS ComCat (https://earthquake.usgs.gov/fdsnws/event/1/).
