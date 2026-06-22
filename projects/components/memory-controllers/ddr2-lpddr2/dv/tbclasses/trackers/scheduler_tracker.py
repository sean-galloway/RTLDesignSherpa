# SPDX-License-Identifier: MIT
# SPDX-FileCopyrightText: 2024-2026 sean galloway
#
# Module: SchedulerTracker
# Purpose: Passive monitor for the scheduler FUB's external bus activity.

"""
Passive tracker for the `scheduler` FUB.

## Signals → events table

| Signal observed                  | Event emitted    | Notes                              |
|----------------------------------|------------------|------------------------------------|
| `cmd_valid_o` & `cmd_ready_i`    | `CMD_<op_name>`  | One per accepted command           |
| `evt_act_o` / `evt_rank/bank_o`  | `EVT_ACT`        | ACT issued to xbank_timers         |
| `evt_rd_o` / `evt_ap_o`          | `EVT_RD` / `RDA` | AP suffix when evt_ap_o high       |
| `evt_wr_o` / `evt_ap_o`          | `EVT_WR` / `WRA` | AP suffix when evt_ap_o high       |
| `evt_pre_o`                      | `EVT_PRE`        | PRE issued (open-page row-miss)    |
| `refresh_grant_o`                | `GRANT_REF`      | Scheduler granted refresh          |
| `pdn_grant_o`                    | `GRANT_PDN`      | Scheduler granted powerdown        |
| `mr_grant_o`                     | `GRANT_MR`       | Scheduler granted MR write         |
| `wr_issued_we_o`                 | `ISSUED_WR`      | mark-issued to wr CAM              |
| `rd_issued_we_o`                 | `ISSUED_RD`      | mark-issued to rd CAM              |

## Stats (`.stats()`)

* `total_cmds` — count of accepted commands
* `op_counts` — distribution by op mnemonic
* `bank_event_counts` — counts of act / rd / wr / pre events
* `grant_counts` — refresh / pdn / mr
* `per_bank_act_counts` — ACT activations per bank index
* `col_ops_with_ap` / `col_ops_open_page` — AP vs no-AP column ops
  (handy for confirming CLOSE vs OPEN policy in action)
"""

from __future__ import annotations

from collections import Counter, deque
from typing import Deque, Dict, Optional

import cocotb
from cocotb.triggers import RisingEdge, Timer

from ._base import TrackerEvent, is_high, safe_int, _sim_time_ns


_NBA_SETTLE_PS = 1
_TRACKER_NAME  = "sched"


# dram_op_e mnemonics (mirrors ddr2_lpddr2_pkg)
_OP_NAMES = {
    0x0: "NOP",  0x1: "ACT",  0x2: "RD",   0x3: "RDA",
    0x4: "WR",   0x5: "WRA",  0x6: "PRE",  0x7: "PREA",
    0x8: "REF",  0x9: "REFPB",0xA: "MRS",  0xB: "ZQCS", 0xC: "ZQCL",
}


class SchedulerTracker:
    """Background tracker for the scheduler."""

    def __init__(self, dut, log=None):
        self.dut = dut
        self.log = log
        self._cycle = 0
        # Unified event queue (the only one — all event types go here).
        self.events: Deque[TrackerEvent] = deque()

    async def run(self) -> None:
        while True:
            await RisingEdge(self.dut.mc_clk)
            await Timer(_NBA_SETTLE_PS, units='ps')
            self._cycle += 1
            self._sample_cmd()
            self._sample_bank_events()
            self._sample_grants()
            self._sample_issued()

    # ---------------- sub-samplers ----------------

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

    def _sample_cmd(self) -> None:
        if not is_high(self.dut, 'cmd_valid_o'): return
        if not is_high(self.dut, 'cmd_ready_i'): return
        op = safe_int(self.dut, 'cmd_op_o', 0)
        op_name = _OP_NAMES.get(op, f"OP_{op:#x}")
        rank = safe_int(self.dut, 'cmd_rank_o', 0)
        bank = safe_int(self.dut, 'cmd_bank_o', 0)
        row  = safe_int(self.dut, 'cmd_row_o',  0)
        col  = safe_int(self.dut, 'cmd_col_o',  0)
        ln   = safe_int(self.dut, 'cmd_len_o',  0)
        self._push(f"CMD_{op_name}", rank=rank, bank=bank,
                   data=f"row={row:#x} col={col:#x} len={ln}")

    def _sample_bank_events(self) -> None:
        rank = safe_int(self.dut, 'evt_rank_o', 0)
        bank = safe_int(self.dut, 'evt_bank_o', 0)
        ap   = is_high(self.dut, 'evt_ap_o')
        if is_high(self.dut, 'evt_act_o'):
            self._push("EVT_ACT", rank=rank, bank=bank, data="ap=0")
        if is_high(self.dut, 'evt_rd_o'):
            self._push("EVT_RDA" if ap else "EVT_RD", rank=rank, bank=bank,
                       data=f"ap={int(ap)}")
        if is_high(self.dut, 'evt_wr_o'):
            self._push("EVT_WRA" if ap else "EVT_WR", rank=rank, bank=bank,
                       data=f"ap={int(ap)}")
        if is_high(self.dut, 'evt_pre_o'):
            self._push("EVT_PRE", rank=rank, bank=bank)

    def _sample_grants(self) -> None:
        if is_high(self.dut, 'refresh_grant_o'):
            self._push("GRANT_REF")
        if is_high(self.dut, 'pdn_grant_o'):
            self._push("GRANT_PDN")
        if is_high(self.dut, 'mr_grant_o'):
            self._push("GRANT_MR")

    def _sample_issued(self) -> None:
        if is_high(self.dut, 'wr_issued_we_o'):
            self._push("ISSUED_WR", slot=safe_int(self.dut, 'wr_issued_slot_o', 0))
        if is_high(self.dut, 'rd_issued_we_o'):
            self._push("ISSUED_RD", slot=safe_int(self.dut, 'rd_issued_slot_o', 0))

    # ---------------- statistics ----------------

    def stats(self) -> Dict[str, object]:
        op_counts: Counter[str] = Counter()
        bank_event_counts: Counter[str] = Counter()
        grant_counts: Counter[str] = Counter()
        per_bank_acts: Counter[int] = Counter()
        ap_count = 0
        nonap_count = 0
        for ev in self.events:
            if ev.event.startswith("CMD_"):
                op_counts[ev.event[4:]] += 1
            elif ev.event.startswith("EVT_"):
                bank_event_counts[ev.event[4:]] += 1
                if ev.event == "EVT_ACT":
                    per_bank_acts[ev.bank] += 1
                if ev.event in ("EVT_RDA", "EVT_WRA"):
                    ap_count += 1
                elif ev.event in ("EVT_RD", "EVT_WR"):
                    nonap_count += 1
            elif ev.event.startswith("GRANT_"):
                grant_counts[ev.event[6:]] += 1
        total_cmds = sum(op_counts.values())
        return {
            'total_cmds':         total_cmds,
            'op_counts':          dict(op_counts),
            'bank_event_counts':  dict(bank_event_counts),
            'grant_counts':       dict(grant_counts),
            'per_bank_act_counts':dict(per_bank_acts),
            'col_ops_with_ap':    ap_count,
            'col_ops_open_page':  nonap_count,
            'cycles_observed':    self._cycle,
        }

    # ---------------- helpers ----------------

    def last_event(self, event_name: str) -> Optional[TrackerEvent]:
        for ev in reversed(self.events):
            if ev.event == event_name:
                return ev
        return None
