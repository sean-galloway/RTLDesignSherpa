// app.js -- shell: pack picker, mode tabs, hash routing (#/mode/pack).
// Browser-only (DOM); not require()d by the node harness. Mode modules
// register themselves as DDRD.<name>Mode with { mount(el, pack), unmount() }.
//
// Mount policy: each mode's <section> is mounted at most once per pack and
// stays in the document (hidden) when its tab is not active, so switching to
// a reference tab and back never disturbs an in-progress drill question. A
// section is re-mounted only when the technology pack changes.
(function () {
  'use strict';

  var DDRD = window.DDRD;
  if (!DDRD) { return; }

  var MODE_IDS = ['quiz', 'timing', 'scenario', 'sandbox', 'timingref',
                  'commands'];
  var current = { mode: null, packId: null };
  // mode -> packId currently mounted in that mode's <section>.
  var mountedPack = {};

  function packs() { return DDRD.listPacks(); }

  function parseHash() {
    var h = (window.location.hash || '').replace(/^#\/?/, '');
    var parts = h.split('/');
    return { mode: parts[0] || '', packId: parts[1] || '' };
  }

  function writeHash(mode, packId) {
    var h = '#/' + mode + '/' + packId;
    if (window.location.hash !== h) { window.location.hash = h; }
  }

  function modeModule(mode) {
    return DDRD[mode + 'Mode'] || null;
  }

  function populatePicker(selectedId) {
    var sel = document.getElementById('pack-picker');
    sel.innerHTML = '';
    packs().forEach(function (p) {
      var opt = document.createElement('option');
      opt.value = p.id;
      opt.textContent = p.name + ' (' + p.jedec.doc + ')';
      sel.appendChild(opt);
    });
    if (selectedId && DDRD.getPack(selectedId)) {
      sel.value = selectedId;
    }
    return sel.value;
  }

  function refreshTabs() {
    var tabs = document.querySelectorAll('.mode-tab');
    tabs.forEach(function (tab) {
      var mode = tab.getAttribute('data-mode');
      tab.disabled = !modeModule(mode);
      tab.classList.toggle('active', mode === current.mode);
      tab.title = tab.disabled ? 'Lands in a later build step' : '';
    });
  }

  function showContainer(mode) {
    MODE_IDS.forEach(function (m) {
      var sec = document.getElementById('mode-' + m);
      if (sec) { sec.hidden = (m !== mode); }
    });
  }

  function mountCurrent() {
    var mod = modeModule(current.mode);
    var pack = DDRD.getPack(current.packId);
    if (!mod || !pack) { return; }
    var el = document.getElementById('mode-' + current.mode);
    // Re-mount only when this section was never mounted for the current
    // pack; otherwise keep the live section (preserving any in-progress
    // question) and just toggle visibility.
    if (mountedPack[current.mode] !== pack.id) {
      // Unmount only when replacing a previous mount (stale pack), never
      // on the first mount of a section.
      if (Object.prototype.hasOwnProperty.call(mountedPack, current.mode) &&
          mod.unmount) {
        mod.unmount();
      }
      el.innerHTML = '';
      mod.mount(el, pack);
      mountedPack[current.mode] = pack.id;
    }
    showContainer(current.mode);
    refreshTabs();
    updateFooter(pack);
  }

  function updateFooter(pack) {
    var el = document.getElementById('pack-citation');
    if (el && pack) {
      el.textContent = pack.name + ' content paraphrased from JEDEC ' +
                       pack.jedec.doc + '. ' + pack.jedec.note;
    }
  }

  function route() {
    var h = parseHash();
    var packIds = packs().map(function (p) { return p.id; });

    var packId = packIds.indexOf(h.packId) !== -1 ? h.packId
               : (packIds.indexOf(current.packId) !== -1 ? current.packId
               : packIds[0]);
    var mode = MODE_IDS.indexOf(h.mode) !== -1 && modeModule(h.mode)
             ? h.mode
             : (current.mode && modeModule(current.mode) ? current.mode
             : 'quiz');

    var changed = (mode !== current.mode) || (packId !== current.packId);
    current.mode = mode;
    current.packId = packId;
    populatePicker(packId);
    writeHash(mode, packId);
    if (changed) { mountCurrent(); }
  }

  function boot() {
    var sel = document.getElementById('pack-picker');
    sel.addEventListener('change', function () {
      current.packId = sel.value;
      writeHash(current.mode, current.packId);
      mountCurrent();
    });
    document.querySelectorAll('.mode-tab').forEach(function (tab) {
      tab.addEventListener('click', function () {
        var mode = tab.getAttribute('data-mode');
        if (modeModule(mode)) {
          current.mode = mode;
          writeHash(mode, current.packId);
          mountCurrent();
        }
      });
    });
    window.addEventListener('hashchange', route);
    route();
  }

  if (document.readyState === 'loading') {
    document.addEventListener('DOMContentLoaded', boot);
  } else {
    boot();
  }
})();
