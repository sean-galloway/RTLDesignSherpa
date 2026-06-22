# SPDX-License-Identifier: MIT
# SPDX-FileCopyrightText: 2024-2026 sean galloway

"""
Passive tracker for the `wr_beat_sequencer` FUB.

Tracks per-op lifecycle through the v2 multi-outstanding pipeline so
you can verify that PULL really overlaps DRIVE and measure latency
end-to-end per burst.

## Signals → events table

| Signal observed                  | Event emitted | Notes                              |
|----------------------------------|---------------|------------------------------------|
| `op_valid_i` & `op_ready_o`      | `OP_ACCEPT`   | data=`slot=N len=N`                |
| `beat_pull_strb_o` pulse         | `PULL_BEAT`   | data=`slot=N`                      |
| `dfi_wrdata_en_o` pulse          | `DRIVE_CYC`   | One per DFI cycle of drive         |
| `b_complete_strb_o` pulse        | `B_COMPLETE`  | Slot retired                       |

## Stats (`.stats()`)

* `ops_accepted` — total OP_ACCEPT events
* `beats_pulled` — total PULL_BEAT events
* `dfi_cycles_driven` — total DRIVE_CYC events
* `bursts_completed` — total B_COMPLETE events
* `pull_drive_overlap_ratio` — cycles where both PULL and DRIVE were
  active simultaneously (proves the v2 multi-outstanding pipelining)
"""

from __future__ import annotations

from collections import deque
from typing import Deque, Dict, Optional

import cocotb
from cocotb.triggers import RisingEdge, Timer

from ._base import TrackerEvent, is_high, safe_int, _sim_time_ns, auto_dump_register


_NBA_SETTLE_PS = 1
_TRACKER_NAME  = "wrbeat"


class WrBeatSequencerTracker:
    """Background tracker for wr_beat_sequencer."""
    SHORT_NAME = _TRACKER_NAME

    def __init__(self, dut, log=None,
                 output_dir: "Optional[str]" = None,
                 filename:   "Optional[str]" = None):
        self.dut = dut
        self.log = log
        self._cycle = 0
        self.events: Deque[TrackerEvent] = deque()
        self._pull_active_cycles = 0
        self._drive_active_cycles = 0
        self._overlap_cycles = 0
        self.output_path = auto_dump_register(
            self, _TRACKER_NAME, output_dir=output_dir, filename=filename,
        )

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
            ln   = safe_int(self.dut, 'op_len_i',  0)
            self._push("OP_ACCEPT", slot=slot, data=f"len={ln}")

        # Pull beat
        pull = is_high(self.dut, 'beat_pull_strb_o')
        if pull:
            slot = safe_int(self.dut, 'beat_pull_slot_o', 0)
            self._push("PULL_BEAT", slot=slot)
            self._pull_active_cycles += 1

        # Drive cycle
        drive = is_high(self.dut, 'dfi_wrdata_en_o')
        if drive:
            self._push("DRIVE_CYC")
            self._drive_active_cycles += 1

        # Overlap metric (the v2 win — only happens with multi-outstanding)
        if pull and drive:
            self._overlap_cycles += 1

        # b_complete
        if is_high(self.dut, 'b_complete_strb_o'):
            slot = safe_int(self.dut, 'b_complete_slot_o', 0)
            self._push("B_COMPLETE", slot=slot)

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
        ops_accepted     = sum(1 for ev in self.events if ev.event == "OP_ACCEPT")
        bursts_completed = sum(1 for ev in self.events if ev.event == "B_COMPLETE")
        return {
            'ops_accepted':            ops_accepted,
            'beats_pulled':            self._pull_active_cycles,
            'dfi_cycles_driven':       self._drive_active_cycles,
            'bursts_completed':        bursts_completed,
            'overlap_cycles':          self._overlap_cycles,
            'pull_drive_overlap_ratio': (self._overlap_cycles /
                                         max(1, self._pull_active_cycles
                                              + self._drive_active_cycles)),
            'cycles_observed':         self._cycle,
        }
