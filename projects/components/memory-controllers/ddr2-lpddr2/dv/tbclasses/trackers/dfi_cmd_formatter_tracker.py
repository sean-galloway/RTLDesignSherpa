# SPDX-License-Identifier: MIT
# SPDX-FileCopyrightText: 2024-2026 sean galloway

"""
Passive tracker for the `dfi_cmd_formatter` FUB.

Decodes (cs_n, ras_n, cas_n, we_n) into the JEDEC DRAM command per
JESD79-2F Table 49 (DDR2) and emits one event per non-NOP command.
Useful for verifying scheduler-issued ops translated to the wire-level
encoding the PHY expects.

## Signals → events table

| Signal observed                       | Event emitted | Notes                              |
|---------------------------------------|---------------|------------------------------------|
| `dfi_cs_n_o` + ras/cas/we_n decode    | `WIRE_<op>`   | ACT / RD / WR / PRE / REF / MRS    |
| `dfi_cke_o` change                    | `CKE_<val>`   | Per-rank CKE (bit vector)          |
| `dfi_odt_o` change                    | `ODT_<val>`   | Per-rank ODT enable                |

## Compliance (`.compliance_issues()`)

* Returns list of decoded commands whose (ras_n, cas_n, we_n) combo
  doesn't match any JEDEC truth-table entry. Should always be empty.
"""

from __future__ import annotations

from collections import Counter, deque
from typing import Deque, Dict, List

import cocotb
from cocotb.triggers import RisingEdge, Timer

from ._base import TrackerEvent, is_high, safe_int, _sim_time_ns


_NBA_SETTLE_PS = 1
_TRACKER_NAME  = "dficmd"


# (ras_n, cas_n, we_n) → DRAM command (per JESD79-2F Table 49 for DDR2)
_JEDEC_DDR2 = {
    (0, 1, 1): "ACT",
    (1, 0, 1): "RD",       # CS=0, A10 selects RD vs RDA
    (1, 0, 0): "WR",       # CS=0, A10 selects WR vs WRA
    (0, 1, 0): "PRE",      # A10 selects PRE-one vs PRE-all
    (0, 0, 1): "REF",
    (0, 0, 0): "MRS",
    (1, 1, 1): "NOP",
}


class DfiCmdFormatterTracker:
    """Background tracker for dfi_cmd_formatter."""

    def __init__(self, dut, log=None):
        self.dut = dut
        self.log = log
        self._cycle = 0
        self.events: Deque[TrackerEvent] = deque()
        self._last_cke = -1
        self._last_odt = -1
        self._unknown_encodings: List[tuple] = []

    async def run(self) -> None:
        while True:
            await RisingEdge(self.dut.mc_clk)
            await Timer(_NBA_SETTLE_PS, units='ps')
            self._cycle += 1
            self._sample()

    def _sample(self) -> None:
        cs_n  = safe_int(self.dut, 'dfi_cs_n_o',  1)
        # Only sample when at least one rank is selected.
        if cs_n == ((1 << _bit_width(self.dut, 'dfi_cs_n_o', 1)) - 1):
            pass   # all 1s = no chip selected → likely NOP

        ras_n = safe_int(self.dut, 'dfi_ras_n_o', 1) & 0x1
        cas_n = safe_int(self.dut, 'dfi_cas_n_o', 1) & 0x1
        we_n  = safe_int(self.dut, 'dfi_we_n_o',  1) & 0x1
        addr  = safe_int(self.dut, 'dfi_address_o', 0)
        bank  = safe_int(self.dut, 'dfi_bank_o',    0)

        # Decode JEDEC; treat NOP as silent.
        cmd = _JEDEC_DDR2.get((ras_n, cas_n, we_n))
        if cmd is None:
            self._unknown_encodings.append((ras_n, cas_n, we_n))
            cmd = f"UNKNOWN_{ras_n}{cas_n}{we_n}"
        if cmd != "NOP" and cs_n == 0:
            # Distinguish A10 auto-precharge variants for RD/WR/PRE.
            a10 = (addr >> 10) & 0x1
            if cmd == "RD"  and a10: cmd = "RDA"
            if cmd == "WR"  and a10: cmd = "WRA"
            if cmd == "PRE" and a10: cmd = "PREA"
            self._push(f"WIRE_{cmd}",
                       data=f"bank={bank} addr={addr:#x} cs_n={cs_n}")

        # CKE/ODT changes
        cke = safe_int(self.dut, 'dfi_cke_o', 0)
        if cke != self._last_cke and self._last_cke != -1:
            self._push(f"CKE_{cke:#x}", data=f"prev={self._last_cke:#x}")
        self._last_cke = cke

        odt = safe_int(self.dut, 'dfi_odt_o', 0)
        if odt != self._last_odt and self._last_odt != -1:
            self._push(f"ODT_{odt:#x}", data=f"prev={self._last_odt:#x}")
        self._last_odt = odt

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

    def compliance_issues(self) -> List[tuple]:
        return list(self._unknown_encodings)

    def stats(self) -> Dict[str, object]:
        wire_counts: Counter[str] = Counter()
        for ev in self.events:
            if ev.event.startswith("WIRE_"):
                wire_counts[ev.event[5:]] += 1
        return {
            'wire_cmd_counts':      dict(wire_counts),
            'unknown_encodings':    len(self._unknown_encodings),
            'cycles_observed':      self._cycle,
        }


def _bit_width(dut, name: str, default: int) -> int:
    sig = getattr(dut, name, None)
    if sig is None:
        return default
    try:
        return len(sig)
    except Exception:
        return default
