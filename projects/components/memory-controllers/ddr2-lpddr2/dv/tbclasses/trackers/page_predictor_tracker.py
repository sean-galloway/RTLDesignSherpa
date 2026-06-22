# SPDX-License-Identifier: MIT
# SPDX-FileCopyrightText: 2024-2026 sean galloway

"""
Passive tracker for the `page_predictor` FUB.

## Signals → events table

| Signal observed                  | Event emitted   | Notes                              |
|----------------------------------|-----------------|------------------------------------|
| `evt_act_i` pulse                | `ACT_SEEN`      | Input ACT event (with row info)    |
| `predict_open_o[r][b]` 0→1       | `PREDICT_OPEN`  | Counter MSB went high (hit-likely) |
| `predict_open_o[r][b]` 1→0       | `PREDICT_CLOSE` | Counter MSB went low (miss-likely) |

## Stats (`.stats()`)

* `act_count_per_bank` — total ACTs seen per (rank, bank)
* `predict_transitions` — number of OPEN↔CLOSE flips per (rank, bank)
* `time_in_predict_open` — cycles spent predicting open per (rank, bank)
"""

from __future__ import annotations

from collections import Counter, deque
from typing import Deque, Dict, List

import cocotb
from cocotb.triggers import RisingEdge, Timer

from ._base import TrackerEvent, is_high, safe_int, _sim_time_ns


_NBA_SETTLE_PS = 1
_TRACKER_NAME  = "pgpred"


class PagePredictorTracker:
    """Background tracker for page_predictor."""

    def __init__(self, dut, log=None,
                 num_ranks: int = 1, num_banks: int = 8):
        self.dut = dut
        self.log = log
        self.NR = num_ranks
        self.NB = num_banks
        self._cycle = 0
        self.events: Deque[TrackerEvent] = deque()
        self._last_predict: List[List[int]] = [[0]*num_banks for _ in range(num_ranks)]
        self._open_cycles : Dict[tuple, int] = {}

    async def run(self) -> None:
        while True:
            await RisingEdge(self.dut.mc_clk)
            await Timer(_NBA_SETTLE_PS, units='ps')
            self._cycle += 1
            self._sample()

    def _sample(self) -> None:
        # ACT input event
        if is_high(self.dut, 'evt_act_i'):
            rank = safe_int(self.dut, 'evt_rank_i', 0)
            bank = safe_int(self.dut, 'evt_bank_i', 0)
            row  = safe_int(self.dut, 'evt_row_i',  0)
            self._push("ACT_SEEN", rank=rank, bank=bank, data=f"row={row:#x}")

        # predict_open transitions
        sig = getattr(self.dut, 'predict_open_o', None)
        if sig is None:
            return
        for r in range(self.NR):
            for b in range(self.NB):
                cur = _read_2d_bit(sig, r, b, self.NB)
                if cur != self._last_predict[r][b]:
                    if cur:
                        self._push("PREDICT_OPEN",  rank=r, bank=b)
                    else:
                        self._push("PREDICT_CLOSE", rank=r, bank=b)
                    self._last_predict[r][b] = cur
                if cur:
                    self._open_cycles[(r, b)] = self._open_cycles.get((r, b), 0) + 1

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
        act_count: Counter[str] = Counter()
        flips:     Counter[str] = Counter()
        for ev in self.events:
            if ev.event == "ACT_SEEN":
                act_count[f"r{ev.rank}b{ev.bank}"] += 1
            elif ev.event in ("PREDICT_OPEN", "PREDICT_CLOSE"):
                flips[f"r{ev.rank}b{ev.bank}"] += 1
        return {
            'act_count_per_bank':      dict(act_count),
            'predict_transitions':     dict(flips),
            'time_in_predict_open':    {f"r{r}b{b}": n
                                        for (r, b), n in self._open_cycles.items()},
            'cycles_observed':         self._cycle,
        }


def _read_2d_bit(sig, r: int, b: int, num_banks: int) -> int:
    try:
        v = sig[r][b]
        return int(v.value if hasattr(v, 'value') else v) & 0x1
    except Exception:
        try:
            return (int(sig.value) >> (r * num_banks + b)) & 0x1
        except Exception:
            return 0
