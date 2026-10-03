// reference.js -- reference tabs: every timing parameter and every command
// of the selected pack, with meanings.
//
// Pure layer (node-tested, registered on DDRD):
//   groupParamsByChapter(timingParams) -> [{chapter, params:[...]}] in
//     first-seen chapter order, params in pack order.
//
// UI layer (browser only):
//   DDRD.buildTimingReference(container, pack) -- the chapter-grouped
//     timing table. Shared: the Timing Drill's mid-question panel and the
//     Timing Reference tab render from this one function.
//   DDRD.timingrefMode = { mount, unmount } -- Timing Reference tab.
//   DDRD.commandsMode  = { mount, unmount } -- Commands tab: one row per
//     pack.commandDocs entry (command, name, brief description).
var DDRD = (typeof window !== 'undefined' ? window : globalThis).DDRD ||
           ((typeof window !== 'undefined' ? window : globalThis).DDRD = {});

(function (DDRD) {
  'use strict';

  // -- pure layer ------------------------------------------------------------

  function groupParamsByChapter(timingParams) {
    var chapters = [];
    var byChapter = {};
    timingParams.forEach(function (p) {
      if (!byChapter[p.chapter]) {
        byChapter[p.chapter] = [];
        chapters.push(p.chapter);
      }
      byChapter[p.chapter].push(p);
    });
    return chapters.map(function (ch) {
      return { chapter: ch, params: byChapter[ch] };
    });
  }

  DDRD.groupParamsByChapter = groupParamsByChapter;

  // -- UI layer (browser only) ------------------------------------------------

  if (typeof window === 'undefined' || !window.document) {
    return;
  }

  function el(tag, cls, text) {
    var e = document.createElement(tag);
    if (cls) { e.className = cls; }
    if (text !== undefined) { e.textContent = text; }
    return e;
  }

  // Chapter-grouped timing table: Symbol / Definition / Applies between.
  function buildTimingReference(container, pack) {
    groupParamsByChapter(pack.timingParams).forEach(function (group) {
      container.appendChild(el('h3', 'timing-ref-chapter', group.chapter));
      var table = el('table', 'timing-ref-table');
      var head = el('tr', 'timing-ref-head');
      ['Symbol', 'Definition', 'Applies between'].forEach(function (h) {
        head.appendChild(el('th', null, h));
      });
      table.appendChild(head);
      group.params.forEach(function (p) {
        var row = el('tr');
        row.appendChild(el('td', 'timing-ref-symbol', p.symbol));
        row.appendChild(el('td', null, p.definition));
        row.appendChild(el('td', 'timing-ref-applies', p.appliesTo.map(
          function (r) {
            return r.from + ' -> ' + r.to + ' (' + r.scope + ')';
          }).join('; ')));
        table.appendChild(row);
      });
      container.appendChild(table);
    });
  }

  DDRD.buildTimingReference = buildTimingReference;

  // -- Timing Reference tab ---------------------------------------------------

  var timingrefState = null;

  DDRD.timingrefMode = {
    mount: function (elRoot, pack) {
      timingrefState = {};
      elRoot.appendChild(el('p', 'ref-intro',
        'Every timing parameter of the ' + pack.name + ' pack (' +
        pack.jedec.doc + '), grouped by chapter. "Applies between" lists ' +
        'the command transitions the parameter constrains and the bank ' +
        'scope it fires on.'));
      var body = el('div', 'timing-reference');
      buildTimingReference(body, pack);
      elRoot.appendChild(body);
    },
    unmount: function () { timingrefState = null; }
  };

  // -- Commands tab -----------------------------------------------------------

  var commandsState = null;

  DDRD.commandsMode = {
    mount: function (elRoot, pack) {
      commandsState = {};
      elRoot.appendChild(el('p', 'ref-intro',
        'The ' + pack.name + ' command set (' + pack.jedec.doc + '). The ' +
        'drill engine emits the first six (ACT, PRE, RD, WR, RDA, WRA); ' +
        'the rest round out what a real controller issues.'));
      var body = el('div', 'timing-reference');
      var table = el('table', 'timing-ref-table');
      var head = el('tr', 'timing-ref-head');
      ['Command', 'Name', 'What it does'].forEach(function (h) {
        head.appendChild(el('th', null, h));
      });
      table.appendChild(head);
      (pack.commandDocs || []).forEach(function (c) {
        var row = el('tr');
        row.appendChild(el('td', 'timing-ref-symbol', c.cmd));
        row.appendChild(el('td', 'cmd-ref-name', c.name));
        row.appendChild(el('td', null, c.description));
        table.appendChild(row);
      });
      body.appendChild(table);
      elRoot.appendChild(body);
    },
    unmount: function () { commandsState = null; }
  };
})(DDRD);
