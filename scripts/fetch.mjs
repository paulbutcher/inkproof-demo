// Copyright (c) 2026 Paul Butcher. All rights reserved.
// Released under Apache 2.0 license as described in the file LICENSE.
//
// Fetches miniSEED (EarthScope) and the earthquake catalogue (USGS ComCat) into a
// data directory. One dataselect request per station, channel and day; days already
// on disk are skipped, so an interrupted fetch resumes. Usage:
//   node scripts/fetch.mjs [--data <dir>] [--full-year] [--days <n>]
import { readFile, writeFile, mkdir, rename, stat } from "node:fs/promises";
import { dirname, join, resolve } from "node:path";
import { fileURLToPath } from "node:url";

const here = dirname(fileURLToPath(import.meta.url));
const args = process.argv.slice(2);
const opt = (name) => { const i = args.indexOf(name); return i < 0 ? undefined : args[i + 1]; };
const dataDir = resolve(opt("--data") ?? join(here, "..", "data"));
const selection = JSON.parse(await readFile(join(here, "selection.json"), "utf8"));
const range = args.includes("--full-year") ? selection.year : selection.slice;
const days = Number(opt("--days") ?? range.days);
const concurrency = 2;
const retries = 5;

const DATASELECT = "https://service.earthscope.org/fdsnws/dataselect/1/query";
const EVENTS = "https://earthquake.usgs.gov/fdsnws/event/1/query";

const dayString = (start, offset) => {
  const d = new Date(`${start}T00:00:00Z`);
  d.setUTCDate(d.getUTCDate() + offset);
  return d.toISOString().slice(0, 10);
};

const exists = (path) => stat(path).then(() => true, () => false);

const sleep = (ms) => new Promise((r) => setTimeout(r, ms));

// null means the service has no data for the request (HTTP 204 or 404).
const get = async (url) => {
  for (let attempt = 0; ; attempt++) {
    try {
      const res = await fetch(url);
      if (res.status === 204 || res.status === 404) return null;
      if (res.ok) return new Uint8Array(await res.arrayBuffer());
      throw new Error(`HTTP ${res.status}`);
    } catch (e) {
      if (attempt >= retries) throw new Error(`${url}: ${e.message}`);
      await sleep(1000 * 2 ** attempt);
    }
  }
};

const save = async (path, bytes) => {
  await mkdir(dirname(path), { recursive: true });
  await writeFile(`${path}.part`, bytes);
  await rename(`${path}.part`, path);
};

const jobs = [];
for (const s of selection.stations) {
  const id = `${s.net}.${s.sta}.${s.loc}.${s.cha}`;
  for (let i = 0; i < days; i++) {
    const day = dayString(range.start, i);
    const next = dayString(range.start, i + 1);
    const path = join(dataDir, "mseed", id, `${day}.mseed`);
    const query = new URLSearchParams({
      net: s.net, sta: s.sta, loc: s.loc, cha: s.cha,
      starttime: `${day}T00:00:00`, endtime: `${next}T00:00:00`, nodata: "404",
    });
    jobs.push({ path, url: `${DATASELECT}?${query}`, label: `${id} ${day}` });
  }
}

let fetched = 0, skipped = 0, empty = 0;
const queue = [...jobs];
const worker = async () => {
  for (let job; (job = queue.shift());) {
    if (await exists(job.path) || await exists(`${job.path}.empty`)) { skipped++; continue; }
    const bytes = await get(job.url);
    if (bytes === null) { await save(`${job.path}.empty`, ""); empty++; console.log(`${job.label}: no data`); }
    else { await save(job.path, bytes); fetched++; console.log(`${job.label}: ${bytes.length} bytes`); }
  }
};
await Promise.all(Array.from({ length: concurrency }, worker));

const catalogue = join(dataDir, "catalogue", `${range.start}_${days}.csv`);
if (!(await exists(catalogue))) {
  const query = new URLSearchParams({
    format: "csv", orderby: "time-asc",
    starttime: `${range.start}T00:00:00`, endtime: `${dayString(range.start, days)}T00:00:00`,
    minmagnitude: String(selection.catalogue.minMagnitude),
  });
  const bytes = await get(`${EVENTS}?${query}`);
  await save(catalogue, bytes ?? "");
  console.log(`catalogue: ${bytes?.length ?? 0} bytes`);
}
console.log(`done: ${fetched} fetched, ${skipped} already present, ${empty} without data`);
