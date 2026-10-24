# SPDX-License-Identifier: MIT
# SPDX-FileCopyrightText: 2026 sean galloway
"""Grant-order measurement at a bridge slave port (bridge TASK-015).

The fabric ID at a slave port is {master index, local id} (bridge TASK-005),
so the top BRIDGE_ID_WIDTH bits of AWID at an AW handshake name the master the
arbiter just granted. Logging those handshakes gives the arbiter's grant
sequence exactly, with no model of what was pending.

Fairness is judged inside the contended window -- from the last master's
first grant to the first master's last grant -- where every master still has
bursts to issue, so every grant was a contended one:

  share       each master's fraction of the grants in the window;
  worst wait  for each master, the most grants to OTHER masters between two
              of its own. A matrix arbiter (least recently served) and a
              round-robin both bound it at n - 1 with n persistent
              requesters; a priority arbiter does not bound it at all.
"""
from collections import defaultdict

import cocotb
from cocotb.triggers import RisingEdge

from bridge_perf_probe import hi


class GrantLog:
    """Samples `<prefix>_awvalid && <prefix>_awready` at a slave port every
    fabric edge and records (cycle, master index) from AWID's top bits."""

    def __init__(self, tb, prefix, id_width, bridge_id_width):
        d = tb.dut
        self.tb = tb
        self.v = getattr(d, f"{prefix}_awvalid")
        self.r = getattr(d, f"{prefix}_awready")
        self.id = getattr(d, f"{prefix}_awid")
        self.shift = id_width - bridge_id_width
        self.mask = (1 << bridge_id_width) - 1
        self.grants = []            # (cycle, master)
        self.cycle = 0

    def start(self):
        cocotb.start_soon(self._run())
        return self

    async def _run(self):
        while True:
            await RisingEdge(self.tb.clock)
            self.cycle += 1
            if hi(self.v) and hi(self.r):
                try:
                    m = (int(self.id.value) >> self.shift) & self.mask
                except ValueError:
                    continue
                self.grants.append((self.cycle, m))

    def analyze(self, masters):
        """Over the contended window: {master: share}, {master: worst wait in
        foreign grants}, the window's grant count, its span in cycles and the
        longest run of cycles with no grant at all (the slot sat idle)."""
        first = {m: None for m in masters}
        last = {m: None for m in masters}
        for c, m in self.grants:
            if m in first:
                if first[m] is None:
                    first[m] = c
                last[m] = c
        missing = [m for m in masters if first[m] is None]
        if missing:
            raise AssertionError(f"masters {missing} never got a grant at this port")
        lo = max(first.values())
        hi_ = min(last.values())
        win = [(c, m) for c, m in self.grants if lo <= c <= hi_ and m in first]
        count = defaultdict(int)
        worst = defaultdict(int)
        since = {m: None for m in masters}       # foreign grants since m's last grant
        for _, m in win:
            count[m] += 1
            for k in masters:
                if k == m:
                    if since[k] is not None:
                        worst[k] = max(worst[k], since[k])
                    since[k] = 0
                elif since[k] is not None:
                    since[k] += 1
        total = len(win)
        share = {m: (count[m] / total if total else 0.0) for m in masters}
        gaps = [b - a for (a, _), (b, _) in zip(win, win[1:])]
        return share, dict(worst), total, (hi_ - lo + 1), (max(gaps) if gaps else 0)
