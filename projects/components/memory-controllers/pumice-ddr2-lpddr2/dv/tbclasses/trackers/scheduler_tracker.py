# SPDX-License-Identifier: MIT
# SPDX-FileCopyrightText: 2024-2026 sean galloway
#
# Module: SchedulerTracker
# Purpose: Passive monitor for the scheduler FUB's external bus activity.

"""
Passive tracker for the command arbiter (`pumice_cmd_arbiter`).

RETARGETED 2026-08-27: the pre-rearchitecture `scheduler` FUB is gone; the
pick core is now `pumice_cmd_arbiter` inside `pumice_mem_cmd_scheduler`
(scope `u_sched.u_arbiter`). The command/event/grant taps carried over
unchanged; the powerdown / MR / issued-strobe taps did not survive the
rearchitecture and were dropped. Added: the PUMICE-006 Axis-1 policy
state, so a pick can be explained and not just observed.

## Signals → events table

| Signal observed                  | Event emitted    | Notes                              |
|----------------------------------|------------------|------------------------------------|
| `cmd_valid_o` & `cmd_ready_i`    | `CMD_<op_name>`  | One per accepted command           |
| `evt_act_o` / `evt_rank/bank_o`  | `EVT_ACT`        | ACT issued to the bank timers          |
| `evt_rd_o` / `evt_ap_o`          | `EVT_RD` / `RDA` | AP suffix when evt_ap_o high       |
| `evt_wr_o` / `evt_ap_o`          | `EVT_WR` / `WRA` | AP suffix when evt_ap_o high       |
| `evt_pre_o`                      | `EVT_PRE`        | PRE issued (open-page row-miss)    |
| `refresh_grant_o`                | `GRANT_REF`      | Arbiter granted refresh            |
| `sched_order_mode_i` change      | `ORDER_<n>`      | 1 in_order, 3 age_threshold        |
| `sched_access_pref_i` change     | `PREF_<n>`       | 2 row_first, 3 precharge_first     |
| `sched_row_sel_i`/`col_sel` chg  | `ROWSEL_<n>` /   | 1 most_pending, 2 fewest_pending   |
|                                  | `COLSEL_<n>`     |                                    |
| `sched_prio_sub_i` change        | `PRIO_<n>`       | 1 none(fair), 3 age_boost          |
| `sched_qos_en_i` change          | `QOS_ON/OFF`     | AxQOS as the outer pick key        |
| `r_wr_drain` edge                | `WRDRAIN_ON/OFF` | SCHED_WR_WM write-batch window     |
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
from typing import Deque, Dict, Optional  # noqa: F401

import cocotb
from cocotb.triggers import RisingEdge, Timer

from ._base import TrackerEvent, is_high, safe_int, _sim_time_ns, auto_dump_register, tracker_clock


_NBA_SETTLE_PS = 1
_TRACKER_NAME  = "sched"


# dram_op_e mnemonics (mirrors pumice_pkg)
_OP_NAMES = {
    0x0: "NOP",  0x1: "ACT",  0x2: "RD",   0x3: "RDA",
    0x4: "WR",   0x5: "WRA",  0x6: "PRE",  0x7: "PREA",
    0x8: "REF",  0x9: "REFPB",0xA: "MRS",  0xB: "ZQCS", 0xC: "ZQCL",
}


class SchedulerTracker:
    """Background tracker for the scheduler."""
    SHORT_NAME = _TRACKER_NAME

    def __init__(self, dut, log=None,
                 output_dir: Optional[str] = None,
                 filename:   Optional[str] = None):
        self.dut = dut
        self._clk_h = tracker_clock(dut, log)
        self.log = log
        self._cycle = 0
        # Axis-1 policy snapshot (emit-on-change).
        self._last_policy: Dict[str, int] = {}
        # Unified event queue (the only one — all event types go here).
        self.events: Deque[TrackerEvent] = deque()
        # Register the end-of-sim atexit dump. Returns the resolved path.
        self.output_path = auto_dump_register(
            self, _TRACKER_NAME, output_dir=output_dir, filename=filename,
        )

    async def run(self) -> None:
        # The arbiter runs on aclk; the pre-rearchitecture scheduler used
        # mc_clk. Accept either so the tracker works at both scopes.
        while True:
            await RisingEdge(self._clk_h)
            await Timer(_NBA_SETTLE_PS, units='ps')
            self._cycle += 1
            self._sample_cmd()
            self._sample_bank_events()
            self._sample_grants()
            self._sample_issued()
            self._sample_policy()

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
        # The rearchitected arbiter grants ONLY refresh; powerdown and MR
        # are handled outside it (their old taps were removed with the
        # pre-rearchitecture scheduler).
        if is_high(self.dut, 'refresh_grant_o'):
            self._push("GRANT_REF")

    def _sample_issued(self) -> None:
        # Slot-level issue/commit moved to the CAMs -- see CamTracker
        # (camrd ISSUE / camwr COMMIT). Kept as a no-op hook so the run()
        # loop shape stays stable for anyone reading the old flow.
        return

    def _sample_policy(self) -> None:
        """PUMICE-006 Axis-1 policy state. Emitted on CHANGE only, so a
        run's policy timeline is a handful of rows you can grep beside
        the picks they explain."""
        for sig, tag, names in (
            ('sched_order_mode_i',  'ORDER',
             {0: 'fr_fcfs', 1: 'in_order', 2: 'fr_fcfs', 3: 'age_threshold'}),
            ('sched_access_pref_i', 'PREF',
             {0: 'column_first', 1: 'column_first', 2: 'row_first',
              3: 'precharge_first'}),
            ('sched_row_sel_i',     'ROWSEL',
             {0: 'oldest', 1: 'most_pending', 2: 'fewest_pending'}),
            ('sched_col_sel_i',     'COLSEL',
             {0: 'oldest', 1: 'most_pending', 2: 'fewest_pending'}),
            ('sched_prio_sub_i',    'PRIO',
             {0: 'load_over_store', 1: 'none', 2: 'load_over_store',
              3: 'age_boost'}),
        ):
            cur = safe_int(self.dut, sig, 0)
            if self._last_policy.get(sig) != cur:
                self._push(f"{tag}_{cur}", data=f"name={names.get(cur, '?')}")
                self._last_policy[sig] = cur

        qos = 1 if is_high(self.dut, 'sched_qos_en_i') else 0
        if self._last_policy.get('qos') != qos:
            self._push("QOS_ON" if qos else "QOS_OFF")
            self._last_policy['qos'] = qos

        # write-batching drain window (internal reg; absent when the
        # tracker is scoped somewhere without it)
        drain = 1 if is_high(self.dut, 'r_wr_drain') else 0
        if self._last_policy.get('drain') != drain:
            self._push("WRDRAIN_ON" if drain else "WRDRAIN_OFF",
                       data=f"high_wm={safe_int(self.dut, 'sched_wr_high_wm_i', 0)} "
                            f"low_wm={safe_int(self.dut, 'sched_wr_low_wm_i', 0)}")
            self._last_policy['drain'] = drain

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
