// sandbox.js -- Mode 4: the live scheduling sandbox.
// Browser-only. The learner edits the initial bank state, builds a request
// list (op/bank/row/col, plus SID when the topology has stacks), picks a
// policy (open-page / close-page / FR-FCFS) and whether ACT pipelining is
// allowed, and the annotated schedule with per-command reasons recomputes
// on every change. Turnaround annotation labels come from the pack's
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
    // header names the group, so the cell name is just the bank.
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
    }, 'sand-banks');
    st.bankEl.replaceWith(grouped);
    st.bankEl = grouped;
  }

  function renderReqList() {
    st.reqListEl.innerHTML = '';
    if (st.reqs.length === 0) {
      st.reqListEl.appendChild(el('p', 'sand-hint',
        'No requests yet - add some below.'));
      return;
    }
    st.reqs.forEach(function (req, i) {
      var row = el('div', 'sand-reqrow');
      row.appendChild(el('span', 'sand-reqtext',
        (i + 1) + '. ' + DDRD.format_req(req)));
      var rm = el('button', 'sand-reqrm', 'remove');
      rm.type = 'button';
      rm.addEventListener('click', function () {
        st.reqs = st.reqs.filter(function (_, j) { return j !== i; });
        renderReqList();
        recompute();
      });
      row.appendChild(rm);
      st.reqListEl.appendChild(row);
    });
  }

  function addRequest() {
    var topo = st.pack.topology;
    var req = DDRD.make_req(
      st.builder.op.value,
      parseInt(st.builder.bank.value, 10),
      parseInt(st.builder.row.value, 10),
      parseInt(st.builder.col.value, 10),
      topo.sids > 0 ? parseInt(st.builder.sid.value, 10) : null);
    st.reqs.push(req);
    renderReqList();
    recompute();
  }

  // -- schedule output --------------------------------------------------------

  function recompute() {
    st.outEl.innerHTML = '';
    if (st.reqs.length === 0) {
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
      st.policy, st.reqs, st.bankState, st.pack.topology, opts);

    if (result.reordered) {
      st.outEl.appendChild(el('p', 'sand-reorder',
        'FR-FCFS served order: ' +
        result.reordered.map(DDRD.format_req).join(' ; ')));
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
      reqs: [],
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
    st.reqListEl = el('div', 'sand-reqlist');
    elRoot.appendChild(st.reqListEl);

    var buildRow = el('div', 'sand-builder');
    st.builder.op = select('sand-sel', [
      { value: 'RD', label: 'RD' }, { value: 'WR', label: 'WR' }
    ], 'RD', function () {});
    st.builder.bank = select('sand-sel', rangeOptions(topo.banks, 'B'),
                             '0', function () {});
    st.builder.row = select('sand-sel', rangeOptions(topo.rows, 'R'),
                            '0', function () {});
    st.builder.col = select('sand-sel', rangeOptions(topo.cols, 'C'),
                            '0', function () {});
    buildRow.appendChild(st.builder.op);
    buildRow.appendChild(st.builder.bank);
    buildRow.appendChild(st.builder.row);
    buildRow.appendChild(st.builder.col);
    if (topo.sids > 0) {
      st.builder.sid = select('sand-sel', rangeOptions(topo.sids, 'S'),
                              '0', function () {});
      buildRow.appendChild(st.builder.sid);
    }
    var add = el('button', 'sand-add', 'Add request');
    add.type = 'button';
    add.addEventListener('click', addRequest);
    buildRow.appendChild(add);
    var clear = el('button', 'sand-clear', 'Clear all');
    clear.type = 'button';
    clear.addEventListener('click', function () {
      st.reqs = [];
      renderReqList();
      recompute();
    });
    buildRow.appendChild(clear);
    elRoot.appendChild(buildRow);

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
