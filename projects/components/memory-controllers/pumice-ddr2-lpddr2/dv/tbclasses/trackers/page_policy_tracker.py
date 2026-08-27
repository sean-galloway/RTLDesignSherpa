# SPDX-License-Identifier: MIT
# SPDX-FileCopyrightText: 2026 sean galloway
#
# Module: PagePolicyTracker
# Purpose: Passive monitor for the Axis-2 paging engine (pumice_page_policy)
#          and its two sub-predictors, so a run's paging DECISIONS can be
#          followed and grepped out of a unified tracker log.

"""
Passive tracker for the `pumice_page_policy` FUB (PUMICE-006 Axis 2).

Replaces the retired `page_predictor` tracker (that FUB was deleted with
the HAPPY_HYBRID retirement, 2026-08-25). The engine this watches owns
every runtime paging decision:

## Signals → events table

| Signal observed                     | Event emitted   | Notes                                   |
|-------------------------------------|-----------------|-----------------------------------------|
| `policy_mode_i` change              | `MODE_<n>`      | 0 build-dflt,1 sopen,2 sclose,3 fixed,   |
|                                     |                 | 4 adapt_time,5 adapt_access,6/7 rbl      |
| `ap_close_o[b]` 0→1                 | `AP_SET`        | bank b will auto-precharge its column    |
| `ap_close_o[b]` 1→0                 | `AP_CLR`        | bank b released back to open-page        |
| `timeout_pre_req_o` 0→1             | `TMO_REQ`       | idle-timeout close requested (bank)      |
| `stat_page_hit_o` increment         | `PAGE_HIT`      | column op to an already-open row         |
| `stat_page_miss_o` increment        | `PAGE_MISS`     | ACT to a bank a conflict PRE had closed  |
| `stat_page_empty_o` increment       | `PAGE_EMPTY`    | ACT to a simply-closed bank              |
| `u_rbl.low_locality_o[b]` 0→1/1→0   | `RBL_LOWLOC` /  | modes 6/7 verdict latched at ACT time    |
|                                     | `RBL_CLR`       |                                          |
| `u_row_pred.close_pred_o[b]` edges  | `ACC_CLOSE` /   | mode 5 per-row predictor verdict         |
|                                     | `ACC_OPEN`      |                                          |

The two sub-predictor taps are OPTIONAL: they are read through the child
instances (`u_rbl`, `u_row_pred`) and silently skipped when the tracker
is scoped at a level where those handles do not resolve.

## Grep examples

```
grep '| pgpol   |' run.md                 # every paging event
grep '| pgpol   | PAGE_MISS' run.md       # just the row-conflict misses
grep '| pgpol   | .* | b3 ' run.md        # everything paging did to bank 3
grep -E '\\| pgpol +\\| (AP_SET|TMO_REQ)' run.md   # why a row got closed
```

## Stats (`.stats()`)

* `page_hit/miss/empty` — final counter values (the *_STATS CSR view)
* `hit_rate` — hits / (hits+miss+empty), the headline paging number
* `ap_set_per_bank` / `timeout_req_per_bank` — which banks the policy acts on
* `modes_seen` — every policy_mode value the run visited
"""

from __future__ import annotations

from collections import deque
from typing import Deque, Dict, Optional

from cocotb.triggers import RisingEdge, Timer

from ._base import TrackerEvent, is_high, safe_int, _sim_time_ns, auto_dump_register, tracker_clock


_NBA_SETTLE_PS = 1
_TRACKER_NAME  = "pgpol"

_MODE_NAMES = {
    0: "build_default", 1: "static_open", 2: "static_close", 3: "fixed_open",
    4: "adapt_time", 5: "adapt_access", 6: "rbl_static", 7: "rbl_dyn",
}


class PagePolicyTracker:
    """Background tracker for pumice_page_policy (+ rbl / row_pred children)."""
    SHORT_NAME = _TRACKER_NAME

    def __init__(self, dut, log=None,
                 output_dir: Optional[str] = None,
                 filename:   Optional[str] = None,
                 num_banks:  int = 8,
                 clk_signal: str = 'aclk'):
        self.dut = dut
        self._clk_h = tracker_clock(dut, log)
        self.log = log
        self.num_banks = num_banks
        self._clk = clk_signal
        self._cycle = 0
        self._last_mode    = None
        self._last_ap      = 0
        self._last_tmo_req = 0
        self._last_rbl     = 0
        self._last_acc     = 0
        self._last_hit     = 0
        self._last_miss    = 0
        self._last_empty   = 0
        self.events: Deque[TrackerEvent] = deque()
        self.output_path = auto_dump_register(
            self, _TRACKER_NAME, output_dir=output_dir, filename=filename,
        )

    # child-instance taps are optional; resolve once, tolerate absence
    def _child_vec(self, inst: str, sig: str) -> int:
        node = getattr(self.dut, inst, None)
        if node is None:
            return 0
        return safe_int(node, sig, 0)

    async def run(self) -> None:
        while True:
            await RisingEdge(self._clk_h)
            await Timer(_NBA_SETTLE_PS, units='ps')
            self._cycle += 1

            mode = safe_int(self.dut, 'policy_mode_i', 0)
            if mode != self._last_mode:
                self._push(f"MODE_{mode}",
                           data=f"name={_MODE_NAMES.get(mode, '?')} "
                                f"prev={self._last_mode}")
                self._last_mode = mode

            # per-bank auto-precharge mask edges
            ap = safe_int(self.dut, 'ap_close_o', 0) if is_high(self.dut, 'ap_mode_en_o') else 0
            if ap != self._last_ap:
                for b in range(self.num_banks):
                    now, was = (ap >> b) & 1, (self._last_ap >> b) & 1
                    if now and not was:
                        self._push("AP_SET", bank=b, data=f"mode={mode}")
                    elif was and not now:
                        self._push("AP_CLR", bank=b, data=f"mode={mode}")
                self._last_ap = ap

            # idle-timeout close request (fixed_open / adapt_time)
            tmo = 1 if is_high(self.dut, 'timeout_pre_req_o') else 0
            if tmo and not self._last_tmo_req:
                self._push("TMO_REQ",
                           bank=safe_int(self.dut, 'timeout_pre_bank_o', -1),
                           data=f"mode={mode}")
            self._last_tmo_req = tmo

            # page outcome counters (the *_STATS CSR view) -- emit on increment
            for sig, name, attr in (
                ('stat_page_hit_o',   'PAGE_HIT',   '_last_hit'),
                ('stat_page_miss_o',  'PAGE_MISS',  '_last_miss'),
                ('stat_page_empty_o', 'PAGE_EMPTY', '_last_empty'),
            ):
                cur = safe_int(self.dut, sig, 0)
                prev = getattr(self, attr)
                if cur != prev:
                    self._push(name, data=f"count={cur}")
                    setattr(self, attr, cur)

            # sub-predictor verdicts (optional children)
            rbl = self._child_vec('u_rbl', 'low_locality_o')
            if rbl != self._last_rbl:
                for b in range(self.num_banks):
                    now, was = (rbl >> b) & 1, (self._last_rbl >> b) & 1
                    if now and not was:
                        self._push("RBL_LOWLOC", bank=b, data="thrashing row")
                    elif was and not now:
                        self._push("RBL_CLR", bank=b)
                self._last_rbl = rbl

            acc = self._child_vec('u_row_pred', 'close_pred_o')
            if acc != self._last_acc:
                for b in range(self.num_banks):
                    now, was = (acc >> b) & 1, (self._last_acc >> b) & 1
                    if now and not was:
                        self._push("ACC_CLOSE", bank=b, data="predict single-access")
                    elif was and not now:
                        self._push("ACC_OPEN", bank=b, data="predict reuse")
                self._last_acc = acc

    def _push(self, event: str, **kw) -> None:
        ev = TrackerEvent(
            sim_time_ns=_sim_time_ns(), cycle=self._cycle,
            tracker=_TRACKER_NAME, event=event,
            rank=kw.get('rank', -1),
            bank=kw.get('bank', -1),
            slot=kw.get('slot', -1),
            data=kw.get('data', ""),
        )
        self.events.append(ev)
        if self.log:
            self.log.debug(ev.to_md_row())

    # ---------------- stats ----------------

    def _per_bank(self, event: str) -> Dict[int, int]:
        out: Dict[int, int] = {}
        for ev in self.events:
            if ev.event == event and ev.bank >= 0:
                out[ev.bank] = out.get(ev.bank, 0) + 1
        return out

    def stats(self) -> Dict[str, object]:
        hit   = safe_int(self.dut, 'stat_page_hit_o', 0)
        miss  = safe_int(self.dut, 'stat_page_miss_o', 0)
        empty = safe_int(self.dut, 'stat_page_empty_o', 0)
        total = hit + miss + empty
        return {
            'page_hit':             hit,
            'page_miss':            miss,
            'page_empty':           empty,
            'hit_rate':             (hit / total) if total else None,
            'act_count':            safe_int(self.dut, 'stat_act_o', 0),
            'pre_count':            safe_int(self.dut, 'stat_pre_o', 0),
            'ref_count':            safe_int(self.dut, 'stat_ref_o', 0),
            'ap_set_per_bank':      self._per_bank("AP_SET"),
            'timeout_req_per_bank': self._per_bank("TMO_REQ"),
            'rbl_lowloc_per_bank':  self._per_bank("RBL_LOWLOC"),
            'acc_close_per_bank':   self._per_bank("ACC_CLOSE"),
            'modes_seen':           sorted({int(ev.event[5:]) for ev in self.events
                                            if ev.event.startswith("MODE_")}),
            'cycles_observed':      self._cycle,
        }
