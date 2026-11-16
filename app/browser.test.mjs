// Copyright (c) 2026 Paul Butcher. All rights reserved.
// Released under Apache 2.0 license as described in the file LICENSE.
// Browser tests: the built demo in headless Chromium.
import { test, before, after } from 'node:test';
import assert from 'node:assert/strict';
import { chromium } from 'playwright';
import { preview } from 'vite';

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
  await page.goto(base);
  await page.waitForSelector('#stack .trace');
  return page;
};
const range = page => page.$eval('#range', e => e.textContent.match(/\d+/g).map(Number));
const settle = (page, before) => page.waitForFunction(b => document.querySelector('#range').textContent !== b, before);

test('stations with outages are drawn as separate traces, never bridged', async () => {
  const page = await stack();
  const traces = await page.$$eval('#stack .trace', ps => ps.map(p => p.getAttribute('transform')));
  const perStation = {};
  for (const t of traces) perStation[t] = (perStation[t] ?? 0) + 1;
  assert.deepEqual(Object.values(perStation).sort(), [1, 2, 2, 3]);
  await page.close();
});

test('every catalogued quake in view has a marker inside the chart, after zooming and panning', async () => {
  const page = await stack();
  assert.equal((await page.$$('#stack .quake')).length, 5);
  for (const id of ['zoom-in', 'pan-right', 'pan-left', 'zoom-in', 'pan-right']) {
    const before = await page.$eval('#range', e => e.textContent);
    await page.click(`#${id}`);
    await settle(page, before).catch(() => {});
    const [lo, hi] = await range(page);
    const expected = [100, 1000, 2048, 2049, 3700].filter(t => lo <= t && t < hi).length;
    const xs = await page.$$eval('#stack .quake', cs => cs.map(c => Number(c.getAttribute('cx'))));
    assert.equal(xs.length, expected);
    assert.ok(xs.every(x => x >= 0 && x < 400));
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
