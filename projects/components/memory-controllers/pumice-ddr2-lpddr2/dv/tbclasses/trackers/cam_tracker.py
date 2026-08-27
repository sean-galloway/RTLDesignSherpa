# SPDX-License-Identifier: MIT
# SPDX-FileCopyrightText: 2026 sean galloway
#
# Module: CamTracker
# Purpose: Passive monitor for the AXI4-interface CAMs (pumice_rd_cmd_cam /
#          pumice_wr_data_cam) -- entry lifecycle + occupancy, so a
#          transaction can be followed from insert to retire.

"""
Passive tracker for the pumice CAMs.

ONE class serves both CAMs; pick the flavour at construction:

    CamTracker(dut.u_ifc.u_rd_cam, kind='rd')   # short name "camrd"
    CamTracker(dut.u_ifc.u_wr_cam, kind='wr')   # short name "camwr"

The CAMs are where an AXI transaction lives between its address handshake
and its retirement, so their lifecycle is the spine a paging / scheduling
investigation hangs off: an entry's INSERT gives it a slot, the scheduler
ISSUEs (rd) or COMMITs (wr) that slot, and the drain retires it.

## Signals → events table

| Signal observed                       | Event emitted | Notes                              |
|---------------------------------------|---------------|------------------------------------|
| `ins_valid_i` & `ins_ready_o`         | `INSERT`      | data=`bank/row/col/id` of the entry |
| `ins_valid_i` & !`ins_ready_o`        | `INS_STALL`   | CAM full -- upstream backpressured  |
| rd: `issue_valid_i` & `issue_ready_o` | `ISSUE`       | scheduler issued this slot to DRAM  |
| rd: `drain_valid_o` & `drain_ready_i` | `DRAIN`       | beat released to rd_intake (AR order) |
| rd: … & `drain_last_o`                | `DRAIN_LAST`  | entry retires                       |
| wr: `commit_valid_i` & `commit_ready_o` | `COMMIT`    | drain-to-DFI started for this slot  |
| wr: `commit_done_valid_o`             | `DONE`        | entry evicted, B response released  |
| `sch_valid_o` popcount change         | `OCC_<n>`     | schedulable occupancy snapshot      |

`OCC_<n>` is the signal to watch against the write-batching watermarks
(`SCHED_WR_WM`) and the QoS/most-pending selects, which all key off this
same schedulable population.

## Grep examples

```
grep '| camrd   |' run.md                  # read CAM lifecycle only
grep '| camwr   | OCC_' run.md             # write occupancy vs the watermarks
grep -E '\\| cam(rd|wr) +\\| INS_STALL' run.md   # CAM-full backpressure
grep '| camrd   | .* | s3 ' run.md         # everything slot 3 did
```

## Stats (`.stats()`)

* `inserts` / `issues` / `retires` — lifecycle totals (conservation check)
* `insert_stall_cycles` — cycles the CAM held off its intake
* `max_occupancy` / `avg_occupancy` — how full it actually ran
* `slot_residency` — cycles between a slot's INSERT and its retire event
"""

from __future__ import annotations

from collections import deque
from typing import Deque, Dict, List, Optional

from cocotb.triggers import RisingEdge, Timer

from ._base import TrackerEvent, is_high, safe_int, _sim_time_ns, auto_dump_register, tracker_clock


_NBA_SETTLE_PS = 1


class CamTracker:
    """Background tracker for a pumice CAM (read or write flavour)."""

    def __init__(self, dut, kind: str = 'rd', log=None,
                 output_dir: Optional[str] = None,
                 filename:   Optional[str] = None,
                 clk_signal: str = 'aclk'):
        assert kind in ('rd', 'wr'), "kind must be 'rd' or 'wr'"
        self.dut  = dut
        self._clk_h = tracker_clock(dut, log)
        self.kind = kind
        self.log  = log
        self._clk = clk_signal
        self._name = f"cam{kind}"
        self.SHORT_NAME = self._name
        self._cycle = 0
        self._last_occ = 0
        self._ins_cycle: Dict[int, int] = {}   # slot -> insert cycle
        self._residency: List[int] = []
        self._stall_cycles = 0
        self.events: Deque[TrackerEvent] = deque()
        self.output_path = auto_dump_register(
            self, self._name, output_dir=output_dir, filename=filename,
        )

    @staticmethod
    def _popcount(v: int) -> int:
        return bin(v).count('1')

    async def run(self) -> None:
        while True:
            await RisingEdge(self._clk_h)
            await Timer(_NBA_SETTLE_PS, units='ps')
            self._cycle += 1

            ins_v = is_high(self.dut, 'ins_valid_i')
            ins_r = is_high(self.dut, 'ins_ready_o')
            if ins_v and ins_r:
                self._push("INSERT",
                           bank=safe_int(self.dut, 'ins_bank_i', -1),
                           data=(f"row=0x{safe_int(self.dut, 'ins_row_i', 0):x} "
                                 f"col=0x{safe_int(self.dut, 'ins_col_i', 0):x} "
                                 f"id={safe_int(self.dut, 'ins_id_i', 0)} "
                                 f"qos={safe_int(self.dut, 'ins_qos_i', 0)}"))
            elif ins_v and not ins_r:
                self._stall_cycles += 1
                self._push("INS_STALL", data="CAM full")

            if self.kind == 'rd':
                if is_high(self.dut, 'issue_valid_i') and is_high(self.dut, 'issue_ready_o'):
                    slot = safe_int(self.dut, 'issue_slot_i', -1)
                    self._ins_cycle.setdefault(slot, self._cycle)
                    self._push("ISSUE", slot=slot)
                if is_high(self.dut, 'drain_valid_o') and is_high(self.dut, 'drain_ready_i'):
                    last = is_high(self.dut, 'drain_last_o')
                    self._push("DRAIN_LAST" if last else "DRAIN",
                               data=f"id={safe_int(self.dut, 'drain_id_o', 0)}")
            else:
                if is_high(self.dut, 'commit_valid_i') and is_high(self.dut, 'commit_ready_o'):
                    slot = safe_int(self.dut, 'commit_slot_i', -1)
                    self._ins_cycle.setdefault(slot, self._cycle)
                    self._push("COMMIT", slot=slot)
                if is_high(self.dut, 'commit_done_valid_o'):
                    self._push("DONE",
                               data=f"id={safe_int(self.dut, 'commit_done_id_o', 0)}")

            occ = self._popcount(safe_int(self.dut, 'sch_valid_o', 0))
            if occ != self._last_occ:
                self._push(f"OCC_{occ}", data=f"prev={self._last_occ}")
                self._last_occ = occ

    def _push(self, event: str, **kw) -> None:
        ev = TrackerEvent(
            sim_time_ns=_sim_time_ns(), cycle=self._cycle,
            tracker=self._name, event=event,
            rank=kw.get('rank', -1),
            bank=kw.get('bank', -1),
            slot=kw.get('slot', -1),
            data=kw.get('data', ""),
        )
        self.events.append(ev)
        if self.log:
            self.log.debug(ev.to_md_row())

    # ---------------- stats ----------------

    def _count(self, *events: str) -> int:
        return sum(1 for ev in self.events if ev.event in events)

    def occupancy_series(self) -> List[int]:
        return [int(ev.event[4:]) for ev in self.events
                if ev.event.startswith("OCC_")]

    def stats(self) -> Dict[str, object]:
        occ = self.occupancy_series()
        retire_ev = "DRAIN_LAST" if self.kind == 'rd' else "DONE"
        issue_ev  = "ISSUE" if self.kind == 'rd' else "COMMIT"
        return {
            'kind':                self.kind,
            'inserts':             self._count("INSERT"),
            'issues':              self._count(issue_ev),
            'retires':             self._count(retire_ev),
            'insert_stall_cycles': self._stall_cycles,
            'max_occupancy':       max(occ) if occ else 0,
            'avg_occupancy':       (sum(occ) / len(occ)) if occ else None,
            'cycles_observed':     self._cycle,
        }
