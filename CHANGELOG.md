# Changelog

## v0.5.0

- Each station's track is scaled to the largest value in view.
- The tests compare floats with inkproof-float's Float.near.
- The tiles above level 12 of a real recording are written correctly.
- The input robot runs in the browser app under Lasm, one seed at a time, and is checked in the browser tests.

## v0.4.0

- Tiles are read with Web's queryColumnsFrom and TileCache, and the finest zooms from raw day files by byte range.
- The four-station quarter is pinned.

## v0.3.0

- The chart's commands come from Gpu's frame.
- The visible sample range comes from Viewport's Interval.indexRange.
- Tiles are fetched with Web's Host.fetchTile.
- The theorem page and inspector read API.lock with inkproof-tools' reader.

## v0.2.0

- Tiles are cut with Core's pyramid.
- The README lists what the demo does.
- The tests use inkproof-tools' Rng in place of the demo's own generator.

## v0.1.0

Browser app with the naive-decimation toggle and the pixel inspector.
