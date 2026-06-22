# SPDX-License-Identifier: MIT
# SPDX-FileCopyrightText: 2024-2026 sean galloway

"""
Passive tracker for the `rd_cl_aligner` FUB.

Tracks per-op lifecycle through the v2 three-pipeline (EN / CAPTURE /
EMIT) multi-outstanding design.

## Signals → events table

| Signal observed                  | Event emitted | Notes                              |
|----------------------------------|---------------|------------------------------------|
| `op_valid_i` & `op_ready_o`      | `OP_ACCEPT`   | data=`slot=N id=N len=N`           |
| `dfi_rddata_en_o` pulse          | `EN_CYC`      | One per cycle EN is driven         |
| `dfi_rddata_valid_i` pulse       | `CAPTURE_CYC` | One per DFI cycle captured         |
| `rd_inject_valid_o` & `ready_i`  | `EMIT_BEAT`   | One per consumed rd_inject beat    |
| `rd_inject_last_o` & handshake   | `EMIT_LAST`   | Final beat of a burst              |
| `rd_beat_we_o` pulse             | `BEAT_WE`     | Per-beat strobe to rd CAM          |

## Stats (`.stats()`)

* `ops_accepted` / `bursts_completed`
* `en_cycles_driven` / `dfi_cycles_captured` / `beats_emitted`
* `capture_emit_overlap_ratio` — overlap (proves multi-outstanding)
* `en_capture_overlap_ratio` — EN+CAPTURE simultaneity
"""

from __future__ import annotations

from collections import deque
from typing import Deque, Dict

import cocotb
from cocotb.triggers import RisingEdge, Timer

from ._base import TrackerEvent, is_high, safe_int, _sim_time_ns


_NBA_SETTLE_PS = 1
_TRACKER_NAME  = "rdalign"


class RdClAlignerTracker:
    """Background tracker for rd_cl_aligner."""

    def __init__(self, dut, log=None):
        self.dut = dut
        self.log = log
        self._cycle = 0
        self.events: Deque[TrackerEvent] = deque()
        self._en_cycles = 0
        self._capture_cycles = 0
        self._emit_cycles = 0
        self._en_cap_overlap = 0
        self._cap_emit_overlap = 0
        self._bursts_completed = 0

    async def run(self) -> None:
        while True:
            await RisingEdge(self.dut.mc_clk)
            await Timer(_NBA_SETTLE_PS, units='ps')
            self._cycle += 1
            self._sample()

    def _sample(self) -> None:
        # OP acceptance
        if is_high(self.dut, 'op_valid_i') and is_high(self.dut, 'op_ready_o'):
            slot = safe_int(self.dut, 'op_slot_i', 0)
            ax_id = safe_int(self.dut, 'op_id_i',  0)
            ln    = safe_int(self.dut, 'op_len_i', 0)
            self._push("OP_ACCEPT", slot=slot, data=f"id={ax_id} len={ln}")

        en_high  = is_high(self.dut, 'dfi_rddata_en_o')
        cap_high = is_high(self.dut, 'dfi_rddata_valid_i')
        emit_hs  = is_high(self.dut, 'rd_inject_valid_o') and \
                   is_high(self.dut, 'rd_inject_ready_i')

        if en_high:
            self._push("EN_CYC")
            self._en_cycles += 1
        if cap_high:
            self._push("CAPTURE_CYC")
            self._capture_cycles += 1
        if emit_hs:
            self._push("EMIT_BEAT")
            self._emit_cycles += 1
            if is_high(self.dut, 'rd_inject_last_o'):
                self._push("EMIT_LAST")
                self._bursts_completed += 1

        # rd_beat_we_o pulse to rd CAM
        if is_high(self.dut, 'rd_beat_we_o'):
            slot = safe_int(self.dut, 'rd_beat_slot_o', 0)
            self._push("BEAT_WE", slot=slot)

        # Overlap metrics
        if en_high and cap_high:
            self._en_cap_overlap += 1
        if cap_high and emit_hs:
            self._cap_emit_overlap += 1

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
        ops_accepted = sum(1 for ev in self.events if ev.event == "OP_ACCEPT")
        return {
            'ops_accepted':              ops_accepted,
            'bursts_completed':          self._bursts_completed,
            'en_cycles_driven':          self._en_cycles,
            'dfi_cycles_captured':       self._capture_cycles,
            'beats_emitted':             self._emit_cycles,
            'en_capture_overlap':        self._en_cap_overlap,
            'capture_emit_overlap':      self._cap_emit_overlap,
            'en_capture_overlap_ratio':  (self._en_cap_overlap /
                                          max(1, self._en_cycles + self._capture_cycles)),
            'capture_emit_overlap_ratio':(self._cap_emit_overlap /
                                          max(1, self._capture_cycles + self._emit_cycles)),
            'cycles_observed':           self._cycle,
        }
