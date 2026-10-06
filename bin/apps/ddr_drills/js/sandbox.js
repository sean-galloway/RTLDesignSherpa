// sandbox.js -- Mode 4: the live scheduling sandbox.
// Browser-only. The learner edits the initial bank state, builds a request
// stream in two AXI-style columns -- Reads (AR channel) and Writes (AW
// channel) -- merged lockstep reads-first into the arrival order the
// scheduler sees, picks a policy (open-page / close-page / FR-FCFS) and
// whether ACT pipelining is allowed, and the annotated schedule with
// per-command reasons recomputes on every change.
// Each column's builder carries a flow-control dropdown: '---' adds a
// normal request (id/bank/row/col, plus SID when the topology has stacks),
// IDLE adds a command-bubble marker, FENCE a drain marker. Both bound
// reordering; only IDLE emits a visible bubble. The id is an AXI-style
// transaction ID: same-id requests keep their relative order under
// FR-FCFS, different ids reorder freely.
// Turnaround annotation labels come from the pack's
// scenarioTweaks.turnaround so the text matches the technology.
// Registers as DDRD.sandboxMode = { mount, unmount }.
var DDRD = (typeof window !== 'undefined' ? window : globalThis).DDRD ||
           ((typeof window !== 'undefined' ? window : globalThis).DDRD = {});

(function (DDRD) {
  'use strict';

  if (typeof window === 'undefined' || !window.document) {
    return;
  }

  var st = null; // per-mount state

  function el(tag, cls, text) {
    var e = document.createElement(tag);
    if (cls) { e.className = cls; }
    if (text !== undefined) { e.textContent = text; }
    return e;
  }

  function select(cls, options, current, onChange) {
    var s = el('select', cls);
    options.forEach(function (o) {
      var opt = el('option', null, o.label);
      opt.value = o.value;
      s.appendChild(opt);
    });
    s.value = String(current);
    s.addEventListener('change', function () { onChange(s.value); });
    return s;
  }

  function rangeOptions(n, prefix) {
    var out = [];
    for (var i = 0; i < n; i++) {
      out.push({ value: String(i), label: prefix + i });
    }
    return out;
  }

  // -- control renderers ------------------------------------------------------

  function renderBankEditor() {
    var topo = st.pack.topology;
    // Same grouped-column presentation as the bank-state drill; the group
    // header names the group, so the cell name is just the bank. Grouped
    // wraps get the flex modifier so the G* boxes hug their content like
    // the drill's do, instead of the .sand-banks grid stretching each one
    // to a fraction of the page width.
    var grouped = DDRD.renderBankGroups(topo, function (bank) {
      var cell = el('label', 'sand-bankcell');
      cell.appendChild(el('span', 'sand-bankname', 'B' + bank));
      var opts = [{ value: '-1', label: 'idle' }]
        .concat(rangeOptions(topo.rows, 'open R'));
      cell.appendChild(select('sand-banksel', opts,
        st.bankState[bank].openRow === null ? '-1'
                                            : String(st.bankState[bank].openRow),
        function (v) {
          st.bankState[bank].openRow = (v === '-1') ? null : parseInt(v, 10);
          recompute();
        }));
      return cell;
    }, topo.hasBankGroups ? 'sand-banks sand-banks-grouped' : 'sand-banks');
    st.bankEl.replaceWith(grouped);
    st.bankEl = grouped;
  }

  // Lockstep merge of the two column lists into scheduler-arrival order:
  // read entry i and write entry i arrive together, reads first. Markers
  // occupy a slot in their column exactly like a request does. Removal
  // targets the column entry that produced a merged position.
  function mergedEntries() {
    var out = [];
    var n = Math.max(st.rdList.length, st.wrList.length);
    for (var i = 0; i < n; i++) {
      if (i < st.rdList.length) {
        out.push({ col: 'rd', idx: i, item: st.rdList[i] });
      }
      if (i < st.wrList.length) {
        out.push({ col: 'wr', idx: i, item: st.wrList[i] });
      }
    }
    return out;
  }

  function currentReqs() {
    return mergedEntries().map(function (e) { return e.item; });
  }

  function renderReqList() {
    st.reqListEl.innerHTML = '';
    var entries = mergedEntries();
    if (entries.length === 0) {
      st.reqListEl.appendChild(el('p', 'sand-hint',
        'No requests yet - add some below.'));
      return;
    }
    entries.forEach(function (e, i) {
      var row = el('div', 'sand-reqrow');
      row.appendChild(el('span', 'sand-reqtext',
        (i + 1) + '. ' + DDRD.format_stream_item(e.item)));
      var rm = el('button', 'sand-reqrm', 'remove');
      rm.type = 'button';
      rm.addEventListener('click', function () {
        st[e.col + 'List'].splice(e.idx, 1);
        renderReqList();
        recompute();
      });
      row.appendChild(rm);
      st.reqListEl.appendChild(row);
    });
  }

  // Grey out the address/id selects when the flow dropdown says this add
  // is a marker, not a request.
  function updateColumnForm(col) {
    var isMarker = st.builder[col].flow.value !== 'req';
    ['id', 'bank', 'row', 'col', 'sid'].forEach(function (k) {
      var s = st.builder[col][k];
      if (s) { s.disabled = isMarker; }
    });
  }

  function addEntry(col) {
    var topo = st.pack.topology;
    var flow = st.builder[col].flow.value;
    var item;
    if (flow === 'idle') {
      item = DDRD.make_idle();
    } else if (flow === 'fence') {
      item = DDRD.make_fence();
    } else {
      item = DDRD.make_req(
        col === 'rd' ? 'RD' : 'WR',
        parseInt(st.builder[col].bank.value, 10),
        parseInt(st.builder[col].row.value, 10),
        parseInt(st.builder[col].col.value, 10),
        topo.sids > 0 ? parseInt(st.builder[col].sid.value, 10) : null,
        parseInt(st.builder[col].id.value, 10));
    }
    st[col + 'List'].push(item);
    renderReqList();
    recompute();
  }

  function buildColumn(col, title) {
    var topo = st.pack.topology;
    var wrap = el('div', 'sand-col');
    wrap.appendChild(el('div', 'sand-colhead', title));
    var b = el('div', 'sand-builder');
    st.builder[col] = {};
    st.builder[col].flow = select('sand-sel', [
      { value: 'req', label: '---' },
      { value: 'idle', label: 'IDLE' },
      { value: 'fence', label: 'FENCE' }
    ], 'req', function () { updateColumnForm(col); });
    st.builder[col].id = select('sand-sel', rangeOptions(4, 'ID'),
                                '0', function () {});
    st.builder[col].bank = select('sand-sel', rangeOptions(topo.banks, 'B'),
                                  '0', function () {});
    st.builder[col].row = select('sand-sel', rangeOptions(topo.rows, 'R'),
                                 '0', function () {});
    st.builder[col].col = select('sand-sel', rangeOptions(topo.cols, 'C'),
                                 '0', function () {});
    if (topo.sids > 0) {
      st.builder[col].sid = select('sand-sel', rangeOptions(topo.sids, 'S'),
                                   '0', function () {});
    }
    b.appendChild(st.builder[col].flow);
    b.appendChild(st.builder[col].id);
    b.appendChild(st.builder[col].bank);
    b.appendChild(st.builder[col].row);
    b.appendChild(st.builder[col].col);
    if (topo.sids > 0) {
      b.appendChild(st.builder[col].sid);
    }
    var add = el('button', 'sand-add',
                 col === 'rd' ? 'Add read' : 'Add write');
    add.type = 'button';
    add.addEventListener('click', function () { addEntry(col); });
    b.appendChild(add);
    wrap.appendChild(b);
    return wrap;
  }

  // -- schedule output --------------------------------------------------------

  function recompute() {
    st.outEl.innerHTML = '';
    var reqs = currentReqs();
    if (reqs.length === 0) {
      st.outEl.appendChild(el('p', 'sand-hint',
        'Add requests to see the schedule.'));
      return;
    }
    st.pipeCb.disabled = (st.policy === 'close');
    var tweaks = st.pack.scenarioTweaks || {};
    var opts = {
      turnaround: tweaks.turnaround,
      pipelining: st.pipeCb.checked
    };
    var result = DDRD.schedule_with_policy(
      st.policy, reqs, st.bankState, st.pack.topology, opts);

    if (result.reordered) {
      st.outEl.appendChild(el('p', 'sand-reorder',
        'FR-FCFS served order: ' +
        result.reordered.map(DDRD.format_stream_item).join(' ; ')));
    }
    var sched = el('div', 'sand-sched');
    result.cmds.forEach(function (cmd, i) {
      var line = el('div', cmd.annotation ? 'sand-cmd sand-ann' : 'sand-cmd');
      line.textContent = DDRD.format_cmd(cmd);
      if (result.reasons[i]) {
        line.appendChild(el('span', 'sand-reason', '  ' + result.reasons[i]));
      }
      sched.appendChild(line);
    });
    st.outEl.appendChild(sched);

    var openBanks = result.bankState.filter(function (e) {
      return e.openRow !== null;
    }).length;
    st.outEl.appendChild(el('p', 'sand-endstate',
      'End state: ' + openBanks + ' bank' + (openBanks === 1 ? '' : 's') +
      ' left open, ' + result.cmds.filter(function (c) {
        return !c.annotation;
      }).length + ' commands issued.'));
  }


  // -- mount ------------------------------------------------------------------

  function mount(elRoot, pack) {
    var topo = pack.topology;
    st = {
      pack: pack,
      bankState: DDRD.make_bank_state(topo),
      rdList: [],
      wrList: [],
      policy: (pack.scenarioTweaks &&
               pack.scenarioTweaks.defaultPolicy) || 'open',
      builder: {}
    };

    elRoot.appendChild(DDRD.assumptionsNote(topo));
    elRoot.appendChild(el('div', 'sand-subhead', 'Initial bank state'));
    st.bankEl = el('div', 'sand-banks');
    elRoot.appendChild(st.bankEl);
    renderBankEditor();

    elRoot.appendChild(el('div', 'sand-subhead', 'Requests'));
    // Two AXI-style entry columns, merged lockstep reads-first into the
    // single arrival stream listed (and scheduled) below.
    st.builder = {};
    var cols = el('div', 'sand-cols');
    cols.appendChild(buildColumn('rd', 'Reads (AR channel)'));
    cols.appendChild(buildColumn('wr', 'Writes (AW channel)'));
    elRoot.appendChild(cols);
    st.reqListEl = el('div', 'sand-reqlist');
    elRoot.appendChild(st.reqListEl);
    var clearRow = el('div', 'sand-clearrow');
    var clear = el('button', 'sand-clear', 'Clear all');
    clear.type = 'button';
    clear.addEventListener('click', function () {
      st.rdList = [];
      st.wrList = [];
      renderReqList();
      recompute();
    });
    clearRow.appendChild(clear);
    elRoot.appendChild(clearRow);

    elRoot.appendChild(el('div', 'sand-subhead', 'Scheduling options'));
    var optRow = el('div', 'sand-options');
    [['open', 'open-page'], ['close', 'close-page'], ['frfcfs', 'FR-FCFS']]
      .forEach(function (pair) {
        var lab = el('label', 'sand-policy');
        var rb = document.createElement('input');
        rb.type = 'radio';
        rb.name = 'sand-policy';
        rb.checked = (st.policy === pair[0]);
        rb.addEventListener('change', function () {
          st.policy = pair[0];
          recompute();
        });
        lab.appendChild(rb);
        lab.appendChild(document.createTextNode(' ' + pair[1]));
        optRow.appendChild(lab);
      });
    var pipeLab = el('label', 'sand-policy');
    st.pipeCb = document.createElement('input');
    st.pipeCb.type = 'checkbox';
    st.pipeCb.checked = true;
    st.pipeCb.addEventListener('change', recompute);
    pipeLab.appendChild(st.pipeCb);
    pipeLab.appendChild(document.createTextNode(
      ' allow ACT pipelining (when all requests share an op, hit distinct ' +
      'banks, and miss no open page)'));
    optRow.appendChild(pipeLab);
    elRoot.appendChild(optRow);

    elRoot.appendChild(el('div', 'sand-subhead', 'Schedule'));
    st.outEl = el('div', 'sand-output');
    elRoot.appendChild(st.outEl);

    renderReqList();
    recompute();
  }

  function unmount() { st = null; }

  DDRD.sandboxMode = { mount: mount, unmount: unmount };
})(DDRD);
