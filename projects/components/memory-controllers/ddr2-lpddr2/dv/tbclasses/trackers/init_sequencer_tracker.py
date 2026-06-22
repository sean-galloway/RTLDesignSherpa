# SPDX-License-Identifier: MIT
# SPDX-FileCopyrightText: 2024-2026 sean galloway

"""
Passive tracker for the `init_sequencer` FUB.

## Signals → events table

| Signal observed               | Event emitted    | Notes                                  |
|-------------------------------|------------------|----------------------------------------|
| `init_busy_o` 1→0             | `INIT_DONE`      | Cold-boot complete                     |
| `dfi_init_start_o` 0→1        | `DFI_INIT_START` | PHY init request asserted              |
| `mr_seq_we_o` pulse           | `MR_WRITE`       | data=`idx=N val=0xN` — MR-write strobe |
| `zqcl_req_o` pulse            | `ZQCL_REQ`       | ZQ calibration request                 |

## Stats (`.stats()`)

* `init_duration_cycles` — from reset deassert to INIT_DONE
* `mr_write_log` — list of (MR index, value) in order
"""

from __future__ import annotations

from collections import deque
from typing import Deque, Dict, List, Tuple

import cocotb
from cocotb.triggers import RisingEdge, Timer

from ._base import TrackerEvent, is_high, safe_int, _sim_time_ns


_NBA_SETTLE_PS = 1
_TRACKER_NAME  = "init"


class InitSequencerTracker:
    """Background tracker for init_sequencer."""

    def __init__(self, dut, log=None):
        self.dut = dut
        self.log = log
        self._cycle = 0
        self.events: Deque[TrackerEvent] = deque()
        self._last_init_busy   = -1
        self._last_init_start  = -1
        self._init_done_cycle  = None
        self._init_start_cycle = 0

    async def run(self) -> None:
        while True:
            await RisingEdge(self.dut.mc_clk)
            await Timer(_NBA_SETTLE_PS, units='ps')
            self._cycle += 1
            self._sample()

    def _sample(self) -> None:
        # init_busy_o: 1→0 = init done
        ib = safe_int(self.dut, 'init_busy_o', 1) & 0x1
        if self._last_init_busy == -1:
            self._last_init_busy = ib
            self._init_start_cycle = self._cycle
        elif ib == 0 and self._last_init_busy == 1:
            self._push("INIT_DONE",
                       data=f"duration={self._cycle - self._init_start_cycle}cyc")
            self._init_done_cycle = self._cycle
        self._last_init_busy = ib

        # dfi_init_start_o: 0→1 edge
        s = safe_int(self.dut, 'dfi_init_start_o', 0) & 0x1
        if s and not self._last_init_start:
            self._push("DFI_INIT_START")
        self._last_init_start = s

        # mr_seq_we_o pulse
        if is_high(self.dut, 'mr_seq_we_o'):
            idx = safe_int(self.dut, 'mr_seq_index_o', 0)
            val = safe_int(self.dut, 'mr_seq_data_o',  0)
            self._push("MR_WRITE", data=f"idx={idx} val={val:#x}")

        # ZQCL request
        if is_high(self.dut, 'zqcl_req_o'):
            self._push("ZQCL_REQ")

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

    def mr_write_log(self) -> List[Tuple[int,int]]:
        log: List[Tuple[int,int]] = []
        for ev in self.events:
            if ev.event == "MR_WRITE":
                # parse "idx=N val=0xN"
                try:
                    parts = dict(p.split('=') for p in ev.data.split())
                    log.append((int(parts['idx']), int(parts['val'], 0)))
                except Exception:
                    pass
        return log

    def stats(self) -> Dict[str, object]:
        return {
            'init_done_cycle':       self._init_done_cycle,
            'init_duration_cycles':  (self._init_done_cycle - self._init_start_cycle)
                                      if self._init_done_cycle is not None else None,
            'mr_write_count':        sum(1 for ev in self.events
                                         if ev.event == "MR_WRITE"),
            'mr_write_log':          self.mr_write_log(),
            'cycles_observed':       self._cycle,
        }
