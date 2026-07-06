# SPDX-License-Identifier: MIT
# SPDX-FileCopyrightText: 2024-2026 sean galloway

"""
Passive tracker for the `xbank_timers` FUB.

## Signals → events table

| Signal observed                  | Event emitted              | Notes                              |
|----------------------------------|----------------------------|------------------------------------|
| `bank_state_o[r][b]` change      | `STATE_<NEW>`              | IDLE / ACTIVATING / ACTIVE / RD_BUSY / WR_BUSY / PRECHARGING |
| `bank_open_row_o[r][b]` change   | `ROW_OPEN`                 | data=`row=0xN` — recorded per (rank,bank) |
| `bank_row_active_o[r][b]` 0→1    | `ROW_ACTIVE_SET`           | Bank entered ACTIVE/RD/WR state    |
| `bank_row_active_o[r][b]` 1→0    | `ROW_ACTIVE_CLR`           | Bank returned to IDLE (after PRE)  |

## Stats (`.stats()`)

* `per_bank_state_counts` — how many cycles each bank spent in each state
* `row_changes` — count of ROW_OPEN events per (rank, bank)
* `auto_pre_inferred` — banks that went RD/WR_BUSY → PRECHARGING directly
"""

from __future__ import annotations

from collections import Counter, deque
from typing import Deque, Dict, List, Optional, Tuple

import cocotb
from cocotb.triggers import RisingEdge, Timer

from ._base import TrackerEvent, is_high, safe_int, _sim_time_ns, auto_dump_register


_NBA_SETTLE_PS = 1
_TRACKER_NAME  = "xbank"

_STATE_NAMES = {
    0: "IDLE", 1: "ACTIVATING", 2: "ACTIVE",
    3: "RD_BUSY", 4: "WR_BUSY", 5: "PRECHARGING", 6: "REFRESHING",
}


class XBankTimersTracker:
    """Background tracker for xbank_timers per-(rank, bank) state."""
    SHORT_NAME = _TRACKER_NAME

    def __init__(self, dut, log=None,
                 output_dir: "Optional[str]" = None,
                 filename:   "Optional[str]" = None,
                 num_ranks: int = 1, num_banks: int = 8):
        self.dut = dut
        self.log = log
        self.NR = num_ranks
        self.NB = num_banks
        self._cycle = 0
        self.events: Deque[TrackerEvent] = deque()
        self.output_path = auto_dump_register(
            self, _TRACKER_NAME, output_dir=output_dir, filename=filename,
        )

        self._last_state    : List[List[int]] = [[0]*num_banks for _ in range(num_ranks)]
        self._last_open_row : List[List[int]] = [[0]*num_banks for _ in range(num_ranks)]
        self._last_active   : List[List[int]] = [[0]*num_banks for _ in range(num_ranks)]
        self._state_cycle_counts: Dict[Tuple[int,int,str], int] = {}

    async def run(self) -> None:
        while True:
            await RisingEdge(self.dut.mc_clk)
            await Timer(_NBA_SETTLE_PS, units='ps')
            self._cycle += 1
            self._sample()

    def _sample(self) -> None:
        # bank_state_o is a packed 2D vector; index by [rank][bank] is
        # accessible in cocotb via getitem on the signal. If indexing
        # fails, fall back to interpreting the raw value.
        st_sig    = getattr(self.dut, 'bank_state_o',      None)
        row_sig   = getattr(self.dut, 'bank_open_row_o',   None)
        active_sig= getattr(self.dut, 'bank_row_active_o', None)

        for r in range(self.NR):
            for b in range(self.NB):
                st  = _read_2d(st_sig,    r, b, self.NB) if st_sig    is not None else 0
                row = _read_2d(row_sig,   r, b, self.NB) if row_sig   is not None else 0
                act = _read_2d(active_sig,r, b, self.NB) if active_sig is not None else 0

                # State transition
                if st != self._last_state[r][b]:
                    name = _STATE_NAMES.get(st & 0x7, f"S{st:x}")
                    self._push(f"STATE_{name}", rank=r, bank=b,
                               data=f"prev={_STATE_NAMES.get(self._last_state[r][b] & 0x7, '?')}")
                    self._last_state[r][b] = st

                # Per-state cycle counter
                cur_state_name = _STATE_NAMES.get(st & 0x7, f"S{st:x}")
                key = (r, b, cur_state_name)
                self._state_cycle_counts[key] = self._state_cycle_counts.get(key, 0) + 1

                # Row open change
                if row != self._last_open_row[r][b]:
                    self._push("ROW_OPEN", rank=r, bank=b,
                               data=f"row={row:#x}")
                    self._last_open_row[r][b] = row

                # row_active edges
                if act and not self._last_active[r][b]:
                    self._push("ROW_ACTIVE_SET", rank=r, bank=b)
                elif (not act) and self._last_active[r][b]:
                    self._push("ROW_ACTIVE_CLR", rank=r, bank=b)
                self._last_active[r][b] = act

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
        per_bank_state_counts: Dict[str, int] = {}
        for (r, b, name), n in self._state_cycle_counts.items():
            per_bank_state_counts[f"r{r}b{b}.{name}"] = n
        row_changes_per_bank: Counter[str] = Counter()
        for ev in self.events:
            if ev.event == "ROW_OPEN":
                row_changes_per_bank[f"r{ev.rank}b{ev.bank}"] += 1
        # Auto-pre is when a bank goes RD/WR_BUSY → PRECHARGING directly
        # (with PAGE_POLICY=CLOSE, every column op auto-precharges).
        auto_pre_count = 0
        prev_for: Dict[Tuple[int,int], str] = {}
        for ev in self.events:
            if not ev.event.startswith("STATE_"):
                continue
            name = ev.event[6:]
            key = (ev.rank, ev.bank)
            if name == "PRECHARGING" and prev_for.get(key) in ("RD_BUSY", "WR_BUSY"):
                auto_pre_count += 1
            prev_for[key] = name
        return {
            'per_bank_state_cycle_counts': per_bank_state_counts,
            'row_changes_per_bank':        dict(row_changes_per_bank),
            'auto_pre_inferred':           auto_pre_count,
            'cycles_observed':             self._cycle,
        }


def _read_2d(sig, r: int, b: int, num_banks: int) -> int:
    """Read sig[r][b] from a 2D packed array.  In cocotb the [r][b]
    indexing usually works if the SV declaration is logic [NR-1:0][NB-1:0]
    or `unpacked` arrays. Fall back to flat bit-slice for packed vectors."""
    try:
        v = sig[r][b]
        return int(v.value if hasattr(v, 'value') else v)
    except Exception:
        pass
    try:
        flat = int(sig.value)
        # Assume 1-bit per (rank, bank) for state-like signals — caller
        # should pass the right signal. For multi-bit per cell this will
        # be wrong; the proper [r][b] indexing branch above should fire.
        return (flat >> (r * num_banks + b)) & 0x1
    except Exception:
        return 0
