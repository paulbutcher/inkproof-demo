# Inkproof.Demo

Part of Inkproof. Released under the Apache 2.0 license; see `LICENSE`.

## Data

The demo charts public seismic recordings and earthquakes. Fetching is a separate step from building, and nothing here runs it for you.

1. Fetch: `node scripts/fetch.mjs [--data <dir>] [--full-year] [--days <n>]`. The data directory defaults to the git-ignored `data/`. By default it fetches one station for one week (`scripts/selection.json`); `--full-year` fetches the pinned year, which is large. Days already on disk are skipped, so rerun it to resume an interrupted fetch. Only Node 24 is needed.
2. Build tiles: from the local miniSEED and catalogue files to tiles (in progress).
3. Serve: the static site from local disk.

## Attribution

Waveforms are from the Global Seismographic Network (network IU, https://doi.org/10.7914/SN/IU), distributed by the EarthScope Data Services (https://service.earthscope.org). The earthquake catalogue is the USGS ComCat (https://earthquake.usgs.gov/fdsnws/event/1/).
