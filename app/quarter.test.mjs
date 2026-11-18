// Copyright (c) 2026 Paul Butcher. All rights reserved.
// Released under Apache 2.0 license as described in the file LICENSE.
// Browser tests of the built demo against a real tile set (the pinned quarter), served from the directory named by INKPROOF_SITE. Skipped when it is not set.
import { test, before, after } from 'node:test';
import assert from 'node:assert/strict';
import { chromium } from 'playwright';
import { preview } from 'vite';
import { readFileSync, openSync, readSync, closeSync, statSync, existsSync } from 'node:fs';
import { join, resolve } from 'node:path';

const site = process.env.INKPROOF_SITE && resolve(process.env.INKPROOF_SITE);
const skip = !site;
const cols = 400;
const total = 90 * 8640000;
const daySamples = 8640000;
// Sample 0 is the start of the first recorded day, so a day number d starts at (d - first) * daySamples.
const manifest = skip ? null : JSON.parse(readFileSync(join(site, 'manifest.json')));
const first = skip ? 0 : JSON.parse(readFileSync(join(site, 'recording.json'))).day;
const quakes = skip ? [] : JSON.parse(readFileSync(join(site, 'catalogue.json')));

let server, browser, base;

before(async () => {
  if (skip) return;
  server = await preview({ root: 'web', build: { outDir: '../dist' }, preview: { port: 0, host: '127.0.0.1' } });
  base = server.resolvedUrls.local[0];
  browser = await chromium.launch();
});

after(async () => {
  await browser?.close();
  await server?.close();
});

const serve = async page => {
  await page.route('**/tiles/**', route => {
    const file = join(site, new URL(route.request().url()).pathname.replace(/^.*\/tiles\//, ''));
    if (!existsSync(file) || !statSync(file).isFile()) return route.fulfill({ status: 404 });
    const size = statSync(file).size;
    const m = /bytes=(\d+)-(\d*)/.exec(route.request().headers().range ?? '');
    if (!m) return route.fulfill({ status: 200, body: readFileSync(file) });
    const lo = Number(m[1]), hi = m[2] === '' ? size - 1 : Math.min(Number(m[2]), size - 1);
    const body = Buffer.alloc(hi - lo + 1);
    const fd = openSync(file, 'r');
    readSync(fd, body, 0, body.length, lo);
    closeSync(fd);
    return route.fulfill({ status: 206, body, headers: { 'content-range': `bytes ${lo}-${hi}/${size}` } });
  });
};

const open = async () => {
  const page = await browser.newPage();
  page.warnings = [];
  page.on('console', m => { if (m.text().includes('[inkproof warn]')) page.warnings.push(m.text()); });
  await serve(page);
  await page.addInitScript(() => {
    window.draws = 0;
    document.addEventListener('inkproof-draw', () => { window.draws += 1; });
  });
  await page.goto(base);
  await page.waitForFunction(() => window.draws > 0, null, { timeout: 120000 });
  return page;
};

// Shows samples lo to hi in the first chart and waits for it to draw.
const show = async (page, lo, hi) => {
  const draws = await page.evaluate(() => window.draws);
  await page.evaluate(([lo, hi]) => document.querySelector('#stack').setAttribute('src', `${lo}-${hi}`), [lo, hi]);
  await page.waitForFunction(d => window.draws > d, draws, { timeout: 120000 });
  assert.deepEqual(page.warnings, [], `drawing ${lo} to ${hi} logged warnings`);
};

const colourAt = (page, x, y) => page.evaluate(([x, y]) => {
  const c = document.querySelector('#stack').shadowRoot.querySelector('canvas');
  const [r, g, b] = c.getContext('2d').getImageData(Math.floor((x + 0.5) * c.width / 400), Math.floor((y + 0.5) * c.height / 400), 1, 1).data;
  return { r, g, b };
}, [x, y]);
// Whether chart column x of track s has no drawn pixel below the row of quake markers: a quiet recording draws a trace thinner than a pixel, so the whole column is read.
const blank = (page, x, s) => page.evaluate(([x, s]) => {
  const c = document.querySelector('#stack').shadowRoot.querySelector('canvas');
  const px = Math.floor((x + 0.5) * c.width / 400), scale = c.height / 400, top = Math.floor((s * 100 + 10) * scale), h = Math.floor(90 * scale);
  const d = c.getContext('2d').getImageData(px, top, 1, h).data;
  for (let i = 0; i < d.length; i += 4) if (d[i] < 250 || d[i + 1] < 250 || d[i + 2] < 250) return false;
  return true;
}, [x, s]);
const isRed = c => c.r > 150 && c.g < 100 && c.b < 100;

// Each station's runs of consecutive missing day numbers.
const outages = s => {
  const have = new Set(manifest.rawDays[s]);
  const last = Math.max(...manifest.rawDays.map(r => Math.max(...r)));
  const runs = [];
  for (let d = first; d <= last; d++) {
    if (have.has(d)) continue;
    if (runs.length && runs[runs.length - 1].at(-1) === d - 1) runs[runs.length - 1].push(d); else runs.push([d]);
  }
  return runs;
};

test('every catalogued quake has a marker at every zoom, after a jump to it', { skip, timeout: 1800000 }, async () => {
  const page = await open();
  assert.ok(quakes.length > 0);
  // The whole quarter shows every quake; the deeper zooms are each visited for a spread of them, since a draw reads tiles over the network.
  for (const [width, step] of [[total, 1], [daySamples, 10], [6000, 10]]) {
    for (const [t] of quakes.filter((_, i) => i % step === 0)) {
      const lo = Math.min(total - width, Math.max(0, t - Math.floor(width / 3)));
      await show(page, lo, lo + width);
      const x = Math.floor((t - lo) * cols / width);
      let red = false;
      for (const dx of [-1, 0, 1]) red ||= isRed(await colourAt(page, Math.min(cols - 1, Math.max(0, x + dx)), 4));
      assert.ok(red, `quake at ${t} in ${lo} to ${lo + width}`);
    }
  }
  await page.close();
});

test('a station outage is a gap and is never bridged', { skip, timeout: 600000 }, async () => {
  const page = await open();
  let checked = 0;
  for (let s = 0; s < manifest.rawDays.length; s++) {
    for (const run of outages(s)) {
      // One day of recording on each side of the outage, so it covers the middle of the view.
      const days = run.length + 2;
      const lo = (run[0] - 1 - first) * daySamples;
      await show(page, lo, lo + days * daySamples);
      // Only the first station records continuously; the others hold a few percent of each day, so a column beside their outage may be a gap too.
      if (s === 0) assert.ok(!await blank(page, 2, s), `station ${s}: the day before days ${run} is drawn`);
      for (let x = Math.ceil(cols / days) + 6; x < Math.floor(cols * (days - 1) / days) - 5; x += 5) {
        assert.ok(await blank(page, x, s), `station ${s}: column ${x} inside the outage of days ${run} is empty`);
      }
      checked++;
    }
  }
  assert.ok(checked > 0, 'the quarter has an outage');
  await page.close();
});
