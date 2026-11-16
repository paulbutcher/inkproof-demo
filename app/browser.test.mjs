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
