# SPDX-License-Identifier: MIT
# SPDX-FileCopyrightText: 2026 sean galloway
#
# Verification layer + shared data types for the monbus_<p1>_<p2>_group
# family. cocotb-free: operates purely on already-parsed MonitorPacket
# objects so it is usable from the cocotb-aware MonbusGroupHarness AND
# from plain post-processing scripts.

from dataclasses import dataclass, field
from enum import Enum
from typing import Any, Dict, List, Optional


class BeatOrder(Enum):
    """Order of the three 64-bit beats that make up one 24-byte record.

    LO_HI_TS  -- beat0 = packet[63:0],  beat1 = packet[127:64], beat2 = ts
                 (the err-FIFO slice-counter pop order seen on the drain
                 read port).
    TS_HI_LO  -- beat0 = ts,            beat1 = packet[127:64], beat2 = packet[63:0]
                 (the canonical parse_stream bulk-trace layout written on
                 the master-write port).
    """
    LO_HI_TS = "lo_hi_ts"
    TS_HI_LO = "ts_hi_lo"


@dataclass(frozen=True)
class BeatLayout:
    """How a 3x64-bit record is laid out on one side of the group."""
    beats_per_record: int = 3            # 24-byte stride
    order: BeatOrder = BeatOrder.TS_HI_LO
    ts_mode: int = 1                     # forwarded to parse_stream (trace side)

    @property
    def stride_bytes(self) -> int:
        return self.beats_per_record * 8


@dataclass
class MonbusGroupStats:
    """Running counters maintained by MonbusGroupHarness."""
    drain_reads: int = 0
    drain_beats: int = 0
    trace_beats: int = 0
    trace_aw: int = 0
    records_parsed: int = 0
    skipped_zero_records: int = 0
    irq_first_cycle: Optional[int] = None
    irq_rising_edges: int = 0
    max_err_fifo_count: int = 0
    max_write_fifo_count: int = 0
    err_fifo_full_seen: bool = False
    write_fifo_full_seen: bool = False
    trace_backpressure_cycles: int = 0
    block_ready_gated: bool = False


class MonbusGroupScoreboard:
    """Lightweight expectation checker over a harness's received packets.

    Register expectations with expect(**criteria) (same criteria semantics
    as MonitorPacket.matches / MonbusSlave.find_packets), then call
    check(harness) -- every registered expectation must match at least one
    received packet.
    """

    def __init__(self, log=None) -> None:
        self.log = log
        self._expectations: List[Dict[str, Any]] = []
        self._errors: List[str] = []

    def expect(self, **criteria) -> None:
        """Register a criteria set that must match >=1 received packet."""
        self._expectations.append(dict(criteria))

    def check(self, harness) -> bool:
        """Assert each expectation matched. Returns True iff all matched."""
        self._errors = []
        packets = harness.received_packets
        for crit in self._expectations:
            n = sum(1 for p in packets if p.matches(**crit))
            if n == 0:
                self._errors.append(f"no packet matched {crit}")
        ok = not self._errors
        if self.log:
            if ok:
                self.log.info(
                    f"MonbusGroupScoreboard: all {len(self._expectations)} "
                    f"expectations matched across {len(packets)} packets")
            else:
                for e in self._errors:
                    self.log.error(f"MonbusGroupScoreboard: {e}")
        return ok

    @property
    def errors(self) -> List[str]:
        return list(self._errors)

    def report(self) -> Dict[str, Any]:
        return {
            "expectations": len(self._expectations),
            "errors": list(self._errors),
            "passed": not self._errors,
        }
