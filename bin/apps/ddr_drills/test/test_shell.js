// test_shell.js -- app.js shell: tab switching must NOT re-mount a mode
// section (an in-progress drill question survives a detour to the Timing
// Reference / Commands tabs), while a technology-pack change MUST re-mount.
//
// app.js is browser-only, so this suite builds a minimal fake DOM, registers
// counting stub mode modules onto DDRD, requires js/app.js (which boots
// immediately: readyState is 'complete'), then drives tab clicks and a pack
// change through the shell's real event listeners.
//
// Registered LAST in TEST_ORDER: it mutates globalThis.window/document and
// deletes its stub modes in a finally block, so earlier suites are unaffected.
var SUITES = (typeof window !== 'undefined' ? window : globalThis).DDRD_TEST_SUITES ||
             ((typeof window !== 'undefined' ? window : globalThis).DDRD_TEST_SUITES = []);

(function () {
  'use strict';

  var DDRD = globalThis.DDRD;
  var MODE_IDS = ['quiz', 'timing', 'scenario', 'sandbox', 'timingref',
                  'commands'];

  // -- minimal fake DOM -------------------------------------------------------

  function makeEl(tag) {
    var el = {
      tagName: tag,
      children: [],
      listeners: {},
      className: '',
      textContent: '',
      value: '',
      hidden: false,
      disabled: false,
      title: ''
    };
    var classes = {};
    el.classList = {
      add: function (c) { classes[c] = true; },
      remove: function (c) { delete classes[c]; },
      toggle: function (c, force) {
        if (force === undefined) { force = !classes[c]; }
        if (force) { classes[c] = true; } else { delete classes[c]; }
        return force;
      },
      contains: function (c) { return !!classes[c]; }
    };
    el.setAttribute = function (k, v) { el['attr:' + k] = v; };
    el.getAttribute = function (k) { return el['attr:' + k]; };
    el.addEventListener = function (ev, fn) {
      (el.listeners[ev] = el.listeners[ev] || []).push(fn);
    };
    el.appendChild = function (c) { el.children.push(c); return c; };
    el.querySelectorAll = function () { return []; };
    el.fire = function (ev) {
      (el.listeners[ev] || []).forEach(function (fn) { fn(); });
    };
    Object.defineProperty(el, 'innerHTML', {
      get: function () { return el._html || ''; },
      set: function (v) {
        el._html = v;
        if (v === '') { el.children = []; }
      }
    });
    return el;
  }

  var byId = {};
  MODE_IDS.forEach(function (m) { byId['mode-' + m] = makeEl('section'); });
  byId['pack-picker'] = makeEl('select');
  byId['pack-citation'] = makeEl('p');

  var tabs = MODE_IDS.map(function (m) {
    var t = makeEl('button');
    t.setAttribute('data-mode', m);
    return t;
  });

  var fakeDocument = {
    readyState: 'complete',
    getElementById: function (id) { return byId[id] || null; },
    querySelectorAll: function (sel) {
      return sel === '.mode-tab' ? tabs : [];
    },
    createElement: function (tag) { return makeEl(tag); },
    addEventListener: function () {}
  };

  var fakeWindow = {
    DDRD: DDRD,
    document: fakeDocument,
    location: { hash: '' },
    addEventListener: function () {}
  };

  // -- stub mode modules with mount/unmount counters ---------------------------

  var mounts = {};
  var unmounts = {};
  MODE_IDS.forEach(function (m) {
    mounts[m] = 0;
    unmounts[m] = 0;
    DDRD[m + 'Mode'] = {
      mount: function (el, pack) {
        mounts[m]++;
        // A question-scoped marker: proves the section's live DOM persists
        // across tab switches.
        var marker = makeEl('div');
        marker.textContent = 'question-of-' + pack.id;
        el.appendChild(marker);
      },
      unmount: function () { unmounts[m]++; }
    };
  });

  function tab(mode) {
    for (var i = 0; i < tabs.length; i++) {
      if (tabs[i].getAttribute('data-mode') === mode) { return tabs[i]; }
    }
    return null;
  }

  function clickTab(mode) { tab(mode).fire('click'); }

  function markerText(mode) {
    var kids = byId['mode-' + mode].children;
    return kids.length ? kids[0].textContent : '';
  }

  // Boot the real shell against the fake DOM.
  globalThis.window = fakeWindow;
  globalThis.document = fakeDocument;
  require(require('path').join(__dirname, '..', 'js', 'app.js'));

  SUITES.push({
    name: 'shell: tab switches preserve mounted modes; pack change remounts',
    run: function (t) {
      try {
        t.eq(mounts.quiz, 1, 'boot mounts the default quiz mode once');
        t.eq(byId['mode-quiz'].hidden, false, 'quiz section visible at boot');
        t.eq(byId['mode-timing'].hidden, true,
             'timing section hidden at boot');

        clickTab('timing');
        t.eq(mounts.timing, 1, 'timing mounts on first visit');
        t.eq(fakeWindow.location.hash, '#/timing/hbm4',
             'hash routing follows tab clicks');
        t.eq(byId['mode-quiz'].hidden, true,
             'quiz section hidden after switching away');

        clickTab('timingref');
        t.eq(mounts.timingref, 1, 'timing reference mounts on first visit');
        t.eq(mounts.timing, 1,
             'timing NOT re-mounted when leaving for the reference tab');
        t.eq(unmounts.timing, 0, 'timing NOT unmounted on reference visit');

        clickTab('commands');
        t.eq(mounts.commands, 1, 'commands reference mounts on first visit');
        t.eq(mounts.timing, 1,
             'second reference detour still leaves timing mounted');

        clickTab('timing');
        t.eq(mounts.timing, 1,
             'returning to the timing drill re-mounts nothing');
        t.eq(unmounts.timing, 0, 'timing still not unmounted');
        t.eq(markerText('timing'), 'question-of-hbm4',
             'the in-progress timing question DOM is untouched');

        clickTab('scenario');
        clickTab('sandbox');
        clickTab('quiz');
        t.eq(mounts.scenario + mounts.sandbox + mounts.quiz, 3,
             'round-robin visits every mode exactly once');
        t.eq(markerText('quiz'), 'question-of-hbm4',
             'quiz question DOM also survives tab detours');

        byId['pack-picker'].value = 'ddr4';
        byId['pack-picker'].fire('change');
        t.eq(mounts.quiz, 2,
             'pack change re-mounts the active mode (quiz)');
        t.eq(unmounts.quiz, 1, 'pack change unmounts the stale quiz mount');
        t.eq(markerText('quiz'), 'question-of-ddr4',
             'active drill shows the new pack immediately');
        t.eq(mounts.timing, 1,
             'inactive modes stay stale until visited (lazy re-mount)');
        t.eq(markerText('timing'), 'question-of-hbm4',
             'stale section keeps its old-pack content until revisited');

        clickTab('timing');
        t.eq(mounts.timing, 2, 'visiting timing after pack change remounts');
        t.eq(unmounts.timing, 1, 'stale timing mount is unmounted first');
        t.eq(markerText('timing'), 'question-of-ddr4',
             're-mounted timing drill shows the new pack');
        t.eq(fakeWindow.location.hash, '#/timing/ddr4',
             'hash reflects pack change');
      } finally {
        MODE_IDS.forEach(function (m) { delete DDRD[m + 'Mode']; });
        delete globalThis.window;
        delete globalThis.document;
      }
    }
  });
})();
