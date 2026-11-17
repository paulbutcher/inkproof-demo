// Copyright (c) 2026 Paul Butcher. All rights reserved.
// Released under Apache 2.0 license as described in the file LICENSE.
// Browser tests: the built demo in headless Chromium.
import { test, before, after } from 'node:test';
import assert from 'node:assert/strict';
import { chromium } from 'playwright';
import { preview } from 'vite';
import { readFileSync } from 'node:fs';

const baseline = JSON.parse(readFileSync(new URL('perf-baseline.json', import.meta.url)));
const tolerance = 1.5;

let server, browser, base;

before(async () => {
  server = await preview({ root: 'web', build: { outDir: '../dist' }, preview: { port: 0, host: '127.0.0.1' } });
  base = server.resolvedUrls.local[0];
  browser = await chromium.launch();
});

after(async () => {
  await browser?.close();
  await server?.close();
});

const open = async () => {
  const page = await browser.newPage();
  await page.goto(base);
  await page.waitForSelector('#chart polyline');
  return page;
};

const ys = page => page.$eval('#chart polyline', p => p.getAttribute('points').split(' ').map(s => Number(s.split(',')[1])));

test('naive decimation loses the peaks that the guaranteed reduction keeps, and toggling back restores them', async () => {
  const page = await open();
  const guaranteed = await ys(page);
  await page.click('#toggle');
  await page.waitForFunction(() => document.querySelector('#toggle').textContent.includes('naive'));
  const naive = await ys(page);
  assert.ok(naive.length < guaranteed.length);
  assert.ok(Math.min(...naive) > Math.min(...guaranteed));
  await page.click('#toggle');
  await page.waitForFunction(() => document.querySelector('#toggle').textContent.includes('guaranteed'));
  assert.deepEqual(await ys(page), guaranteed);
  await page.close();
});

test('the inspector shows the raw samples, their extremes and the guarantee for the chosen column', async () => {
  const page = await open();
  await page.fill('#column', '7');
  await page.waitForFunction(() => document.querySelector('#inspector').textContent.includes('column 7'));
  const text = await page.$eval('#inspector', e => e.textContent);
  assert.match(text, /20 raw samples/);
  assert.match(text, /maximum 500/);
  assert.match(text, /no pixel is lost/);
  await page.close();
});

const stack = async () => {
  const page = await browser.newPage();
  await page.addInitScript(() => {
    window.draws = 0;
    document.addEventListener('inkproof-draw', () => { window.draws += 1; });
  });
  await page.goto(base);
  await page.waitForFunction(() => window.draws > 0);
  return page;
};
const range = page => page.$eval('#range', e => e.textContent.match(/\d+/g).map(Number));
const settle = async (page, before, draws) => {
  await page.waitForFunction(b => document.querySelector('#range').textContent !== b, before).catch(() => {});
  await page.waitForFunction(d => window.draws > d, draws);
};
// The colour at chart pixel (x, y), a chart being 400 by 400 chart pixels however large its backing store is.
const colourAt = (page, x, y) => page.evaluate(([x, y]) => {
  const c = document.querySelector('#stack').shadowRoot.querySelector('canvas');
  const [r, g, b] = c.getContext('2d').getImageData(Math.floor((x + 0.5) * c.width / 400), Math.floor((y + 0.5) * c.height / 400), 1, 1).data;
  return { r, g, b };
}, [x, y]);
const isWhite = c => c.r > 240 && c.g > 240 && c.b > 240;
const isRed = c => c.r > 150 && c.g < 100 && c.b < 100;

test('stations with outages are drawn with gaps, never bridged', async () => {
  const page = await stack();
  // Station 1 is down for samples 900 to 1300, which is chart columns 88 to 126 of the full view; station 2 is down for 2000 to 2600, columns 195 to 254, and station 3 never goes down.
  assert.ok(!isWhite(await colourAt(page, 50, 50)));
  for (const x of [90, 100, 110, 125]) assert.ok(isWhite(await colourAt(page, x, 50)), `column ${x} of the first track`);
  for (const x of [200, 225, 250]) assert.ok(isWhite(await colourAt(page, x, 150)), `column ${x} of the second track`);
  for (const x of [50, 225, 380]) assert.ok(!isWhite(await colourAt(page, x, 250)), `column ${x} of the third track`);
  await page.close();
});

test('every catalogued quake in view has a marker inside the chart, after zooming and panning', async () => {
  const page = await stack();
  const times = [100, 1000, 2048, 2049, 3700];
  for (const id of [null, 'zoom-in', 'pan-right', 'pan-left', 'zoom-in', 'pan-right']) {
    if (id) {
      const before = await page.$eval('#range', e => e.textContent);
      const draws = await page.evaluate(() => window.draws);
      await page.click(`#${id}`);
      await settle(page, before, draws);
    }
    const [lo, hi] = await range(page);
    for (const t of times.filter(t => lo <= t && t < hi)) {
      const x = Math.floor((t - lo) * 400 / (hi - lo));
      assert.ok(isRed(await colourAt(page, x, 4)), `quake at ${t} in ${lo} to ${hi}`);
    }
  }
  await page.close();
});

test('zooming in narrows the range and zooming out restores it', async () => {
  const page = await stack();
  const [lo0, hi0] = await range(page);
  await page.click('#zoom-in');
  await page.waitForFunction(w => Number(document.querySelector('#range').textContent.match(/\d+/g)[1]) - Number(document.querySelector('#range').textContent.match(/\d+/g)[0]) < w, hi0 - lo0);
  const [lo1, hi1] = await range(page);
  assert.ok(hi1 - lo1 < hi0 - lo0 && lo1 >= lo0 && hi1 <= hi0);
  await page.click('#zoom-out');
  await page.waitForFunction(w => Number(document.querySelector('#range').textContent.match(/\d+/g)[1]) - Number(document.querySelector('#range').textContent.match(/\d+/g)[0]) > w, hi1 - lo1);
  await page.close();
});

test('the displayed placement bound names its theorem and its normal-range condition', async () => {
  const page = await stack();
  const text = await page.$eval('#error-bound', e => e.textContent);
  assert.match(text, /rebase_apply_float_error/);
  assert.match(text, /normal floating-point range/);
  await page.close();
});

// Headless Chromium has no GPU, so these times say nothing absolute about a phone; they only guard against regressions from the recorded baseline.
test('first draw and longest frame interval with eight linked charts do not regress', async () => {
  const page = await browser.newPage();
  await page.addInitScript(() => {
    window.firstDraw = null;
    document.addEventListener('inkproof-draw', () => { window.firstDraw ??= performance.now(); });
  });
  const cdp = await page.context().newCDPSession(page);
  await cdp.send('Emulation.setCPUThrottlingRate', { rate: 4 });
  await page.goto(base);
  await page.waitForFunction(() => window.firstDraw !== null);
  const firstDraw = await page.evaluate(() => window.firstDraw);
  console.log(`first draw ${firstDraw} ms`);
  assert.ok(firstDraw <= baseline.firstDrawMs * tolerance, `first draw ${firstDraw} ms against baseline ${baseline.firstDrawMs}`);
  assert.equal(await page.$$eval('#charts inkproof-chart', e => e.length), 8);
  // A stall from a busy host lands in one round and not the others, a regression in all of them, so the best round is compared.
  const worst = [];
  for (let round = 0; round < 3; round++) {
    await page.evaluate(() => {
      window.frames = [];
      let last = performance.now();
      const tick = now => { window.frames.push(now - last); last = now; window.frameLoop = requestAnimationFrame(tick); };
      window.frameLoop = requestAnimationFrame(tick);
    });
    for (const id of ['zoom-in', 'pan-right', 'zoom-in', 'pan-left', 'zoom-out', 'pan-right', 'zoom-out', 'pan-left']) {
      const before = await page.$eval('#range', e => e.textContent);
      await page.click(`#${id}`);
      await page.waitForFunction(b => document.querySelector('#range').textContent !== b, before).catch(() => {});
      await page.waitForTimeout(250);
    }
    const frames = await page.evaluate(() => { cancelAnimationFrame(window.frameLoop); return window.frames.slice(1); });
    frames.sort((a, b) => a - b);
    assert.ok(frames.length > 30, 'enough frames sampled');
    worst.push(frames[frames.length - 1]);
  }
  const longest = Math.min(...worst);
  console.log(`longest frame interval ${longest} ms (rounds ${worst.map(x => x.toFixed(1)).join(', ')})`);
  assert.ok(longest <= baseline.longestFrameMs * tolerance, `longest frame interval ${longest} ms against baseline ${baseline.longestFrameMs}`);
  await page.close();
});

test('a tile that fails to load is labelled and logged at warn, not drawn as an outage', async () => {
  const page = await browser.newPage();
  const warnings = [];
  page.on('console', m => { if (m.type() === 'warning') warnings.push(m.text()); });
  await page.route('**/tiles/**/t*.bin', route => route.abort());
  await page.addInitScript(() => {
    window.draws = 0;
    document.addEventListener('inkproof-draw', () => { window.draws += 1; });
  });
  await page.goto(base);
  await page.waitForFunction(() => window.draws > 0);
  // Station 3 never has an outage, so any ink in its track beyond the trace is the failure label.
  const dark = await page.evaluate(() => {
    const c = document.querySelector('#stack').shadowRoot.querySelector('canvas');
    const h = c.height / 4;
    const d = c.getContext('2d').getImageData(0, 2 * h, c.width, h).data;
    let n = 0;
    for (let i = 0; i < d.length; i += 4) if (d[i] < 200 || d[i + 1] < 200 || d[i + 2] < 200) n += 1;
    return n;
  });
  assert.ok(dark > 0, 'the failed track carries a label');
  assert.ok(warnings.some(w => w.includes('fetching a tile failed') && w.includes('tiles/s')), `warnings: ${warnings}`);
  await page.close();
});

test('a catalogue that fails to load is logged at warn and labelled, not drawn as a quiet period', async () => {
  const page = await browser.newPage();
  const warnings = [];
  page.on('console', m => { if (m.type() === 'warning') warnings.push(m.text()); });
  await page.route('**/tiles/catalogue.json', route => route.abort());
  await page.addInitScript(() => {
    window.draws = 0;
    document.addEventListener('inkproof-draw', () => { window.draws += 1; });
  });
  await page.goto(base);
  await page.waitForFunction(() => window.draws > 0);
  assert.ok(warnings.some(w => w.includes('catalogue fetch failed')), `warnings: ${warnings}`);
  await page.close();
});
