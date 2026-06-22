# SPDX-License-Identifier: MIT
# SPDX-FileCopyrightText: 2024-2026 sean galloway

"""
Passive tracker for the `powerdown_ctrl` FUB.

v1 powerdown_ctrl is minimal (CKE per rank + active/APD state). This
tracker becomes much more useful when category E (power management)
lands and adds SR/DPD states.

## Signals → events table

| Signal observed               | Event emitted | Notes                                  |
|-------------------------------|---------------|----------------------------------------|
| `pdn_req_o` change            | `PDN_REQ_<n>` | 1 → powerdown requested; 0 → release   |
| `dfi_cke_o[r]` 1→0            | `CKE_DROP`    | Per-rank powerdown entry               |
| `dfi_cke_o[r]` 0→1            | `CKE_RISE`    | Per-rank powerdown exit                |

## Stats (`.stats()`)

* `cke_residency` — cycles each rank's CKE was low (powerdown time)
* `pdn_req_count` — number of pdn requests issued
"""

from __future__ import annotations

from collections import deque
from typing import Deque, Dict

import cocotb
from cocotb.triggers import RisingEdge, Timer

from ._base import TrackerEvent, is_high, safe_int, _sim_time_ns


_NBA_SETTLE_PS = 1
_TRACKER_NAME  = "pdn"


class PowerdownTracker:
    """Background tracker for powerdown_ctrl."""

    def __init__(self, dut, log=None, num_ranks: int = 1):
        self.dut = dut
        self.log = log
        self.NR = num_ranks
        self._cycle = 0
        self.events: Deque[TrackerEvent] = deque()
        self._last_pdn_req = 0
        self._last_cke: int = -1
        self._cke_low_cycles = [0] * num_ranks

    async def run(self) -> None:
        while True:
            await RisingEdge(self.dut.mc_clk)
            await Timer(_NBA_SETTLE_PS, units='ps')
            self._cycle += 1
            self._sample()

    def _sample(self) -> None:
        pdn_req = safe_int(self.dut, 'pdn_req_o', 0) & 0x1
        if pdn_req != self._last_pdn_req:
            self._push(f"PDN_REQ_{pdn_req}", data=f"prev={self._last_pdn_req}")
            self._last_pdn_req = pdn_req

        cke = safe_int(self.dut, 'dfi_cke_o', (1 << self.NR) - 1)
        if self._last_cke == -1:
            self._last_cke = cke
            return
        # Per-rank edge detect.
        for r in range(self.NR):
            cur_bit  = (cke >> r) & 0x1
            prev_bit = (self._last_cke >> r) & 0x1
            if cur_bit == 0 and prev_bit == 1:
                self._push("CKE_DROP", rank=r)
            elif cur_bit == 1 and prev_bit == 0:
                self._push("CKE_RISE", rank=r)
            if cur_bit == 0:
                self._cke_low_cycles[r] += 1
        self._last_cke = cke

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

    def stats(self) -> Dict[str, object]:
        req_count = sum(1 for ev in self.events
                        if ev.event.startswith("PDN_REQ_1"))
        return {
            'pdn_req_count':   req_count,
            'cke_residency':   {f"r{r}": n for r, n in enumerate(self._cke_low_cycles)},
            'cycles_observed': self._cycle,
        }
