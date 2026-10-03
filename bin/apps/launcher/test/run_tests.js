#!/usr/bin/env node
// run_tests.js -- zero-dependency site-integrity suite for the launcher.
//
// The Pages site is a PROJECT page (sean-galloway.github.io/RTLDesignSherpa/),
// so absolute root URLs like href="/" resolve to the github.io domain root
// (a 404), not the site root. These tests pin that failure class: no app
// html may reference "/" absolutely, and launcher tiles must point at
// directories that exist in the staged site.
//
// Usage: node bin/apps/launcher/test/run_tests.js
'use strict';

var fs = require('fs');
var path = require('path');

var root = path.join(__dirname, '..');
var appsRoot = path.join(root, '..');

var tests = [];
var n = 0;
var failed = 0;

function test(name, fn) { tests.push({ name: name, fn: fn }); }

var APP_INDEXES = ['ddr_drills', 'fifo_depth', 'launcher'].map(function (d) {
  return path.join(appsRoot, d, 'index.html');
});

test('no absolute root URLs in app html', function () {
  APP_INDEXES.forEach(function (f) {
    var html = fs.readFileSync(f, 'utf8');
    var m = html.match(/(?:href|src)="\/"/g);
    if (m) {
      throw new Error(path.basename(path.dirname(f)) + '/index.html has ' +
        m.length + ' absolute root URL(s): ' + m.join(' '));
    }
  });
});

test('launcher tiles point at existing app directories', function () {
  // The workflow stages repo dirs under these names (its cp lines); the
  // tile hrefs must match that staging map and the target must exist.
  var STAGED = { 'ddr_drills/': 'ddr_drills', 'fifo/': 'fifo_depth' };
  var apps = require(path.join(root, 'js', 'apps.js'));
  apps.forEach(function (a) {
    var repoDir = STAGED[a.href];
    if (!repoDir) {
      throw new Error('tile ' + a.id + ' -> ' + a.href +
        ' is not in the staging map (check the workflow cp lines)');
    }
    if (!fs.existsSync(path.join(appsRoot, repoDir, 'index.html'))) {
      throw new Error('staged target ' + repoDir + ' has no index.html');
    }
  });
});

tests.forEach(function (t) {
  n += 1;
  try {
    t.fn();
    console.log('ok ' + n + ' - ' + t.name);
  } catch (e) {
    failed += 1;
    console.log('not ok ' + n + ' - ' + t.name + ' :: ' + e.message);
  }
});

console.log('# ' + (n - failed) + '/' + n + ' passed, ' + failed + ' failed');
process.exit(failed === 0 ? 0 : 1);
