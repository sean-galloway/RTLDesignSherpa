# SPDX-License-Identifier: MIT
# SPDX-FileCopyrightText: 2026 sean galloway
"""Light Ocelus checks ON SILICON (granite TASK-008).

Needs a bitstream built with GRANITE_HAS_MON=1. The board harness answers the
plane's AXI-Lite packet writer with a write-ack sink and keeps no packet
memory, so these checks read the MON_* status CSRs. The programming follows
the sim's McOcelusTB.program_monitors: every source on except the core's
DROPPED event (below), and Error / Timeout / Debug routed to the error window.

One write-then-read pass of `txn` bursts, then:

  MON_RD_STATS.COMPLETIONS == txn, MON_WR_STATS.COMPLETIONS == txn
  MON_RD_STATS.ERRORS == 0, MON_WR_STATS.ERRORS == 0, MON_CORE_STATS.ERRORS == 0
  MON_ERR_STATUS.REC_COUNT > 0     (mc_monlite debug records reached the writer)
  the write/read pass itself has mismatched == 0

MON_ERR_STATUS.DROPPED (events lost at the sources) is reported and not checked.
A repeat of a pending debug event is dropped by design, and under traffic the
debug events (direction flips, page-timeout precharges) repeat faster than the
plane drains them: a 64-burst pass loses a few hundred. The core's DROPPED
event is therefore left OFF. It is an Error-class packet, so with it on
MON_CORE_STATS.ERRORS counts drop reports (about 20 a pass on the board,
2026-11-02), and each report clears the count MON_ERR_STATUS.DROPPED reads.
Off, ERRORS counts only real error events and DROPPED accumulates.

The counters clear while their source is disabled, and they are 16 bits wide,
so every check is on a window. The checks run in that window, after the plane
is enabled.

    make run SEQUENCES="init ocelus" RUN_ARGS="--controller granite"
    make run SEQUENCES="init ocelus" RUN_ARGS="--controller granite --txn 200"
"""

from __future__ import annotations

import time

import pumice_env  # noqa: F401  (import side effect: sys.path setup)

from sequence import Sequence

# Packet types (rtl/amba/ocelus monitor_packet_t): Error 0, Timeout 3, Debug 0xF.
_ERR_SELECT = (1 << 0) | (1 << 3) | (1 << 15)
# Every core event except DROPPED (mc_event_e 0x06; see the module docstring).
_CORE_EV_EN = 0xFFFF & ~(1 << 0x06)
# The sink ignores addresses; these only have to form valid windows.
_TRACE_BASE, _TRACE_LIMIT = 0x0010_0000, 0x0010_FFFF
_ERR_BASE, _ERR_LIMIT = 0x0011_0000, 0x0011_0FFF


def program_monitors(dev) -> None:
    """Every source on (core DROPPED excepted), Error / Timeout / Debug to the error window."""
    dev.write("MON_BASE_ADDR", VAL=_TRACE_BASE)
    dev.write("MON_LIMIT_ADDR", VAL=_TRACE_LIMIT)
    dev.write("MON_ERR_BASE_ADDR", VAL=_ERR_BASE)
    dev.write("MON_ERR_LIMIT_ADDR", VAL=_ERR_LIMIT)
    dev.write("MON_ROUTE", PKT_MASK=0, ERR_SELECT=_ERR_SELECT)
    dev.write("MON_CORE_EV", EV_EN=_CORE_EV_EN)
    dev.write("MON_CTRL", RD_EN=1, WR_EN=1, CORE_EN=1, ERROR_EN=1,
              COMPL_EN=1, TIMEOUT_EN=1)


def read_stats(dev) -> dict:
    f = dev.field
    rd, wr = dev.read("MON_RD_STATS"), dev.read("MON_WR_STATS")
    es = dev.read("MON_ERR_STATUS")
    return {
        "rd_compl": f("MON_RD_STATS", "COMPLETIONS", rd),
        "rd_err":   f("MON_RD_STATS", "ERRORS", rd),
        "wr_compl": f("MON_WR_STATS", "COMPLETIONS", wr),
        "wr_err":   f("MON_WR_STATS", "ERRORS", wr),
        "core_err": f("MON_CORE_STATS", "ERRORS"),
        "rec":      f("MON_ERR_STATUS", "REC_COUNT", es),
        "dropped":  f("MON_ERR_STATUS", "DROPPED", es),
    }


def window(before: dict, after: dict) -> dict:
    d = {k: (after[k] - before[k]) & 0xFFFF for k in after}
    # saturating sum, not a wrapping counter: a delta unless it pinned
    d["dropped"] = (after["dropped"] - before["dropped"]
                    if after["dropped"] >= before["dropped"] else after["dropped"])
    return d


def problems(d: dict, rd_bursts: int, wr_bursts: int) -> list:
    """Every check that failed on window `d`; empty = pass."""
    bad = []
    if d["rd_compl"] == 0 and d["wr_compl"] == 0:
        return ["no completions counted: is this a GRANITE_HAS_MON=1 bitstream?"]
    if d["rd_compl"] != rd_bursts:
        bad.append(f"read completions {d['rd_compl']} != {rd_bursts} bursts")
    if d["wr_compl"] != wr_bursts:
        bad.append(f"write completions {d['wr_compl']} != {wr_bursts} bursts")
    for k in ("rd_err", "wr_err", "core_err"):
        if d[k]:
            bad.append(f"{k} = {d[k]}")
    if d["rec"] == 0:
        bad.append("no error-window records: mc_monlite debug events did not reach the writer")
    return bad


class Ocelus(Sequence):
    name = "ocelus"
    description = "Ocelus plane on the board: completions, errors and records via MON_* CSRs"
    requires = ("init",)

    def run(self, ctx):
        dev = ctx.bus.pumice.regs
        test = ctx.result("init")["test"]
        blen = ctx.param("burst_len", 8)
        txn = ctx.param("txn_count", 64)
        if not 0 < txn < 0x10000:
            raise ValueError(f"txn_count {txn} must fit the 16-bit MON counters")

        program_monitors(dev)
        before = read_stats(dev)
        ctx.say(f"[ocelus] enabled; bl{blen} x {txn} txn @ 0x{test.base:08X}")
        res = test.run(burst_len=blen, txn_count=txn)
        time.sleep(0.05)   # the trace writer's flush timeout is 1024 cycles
        d = window(before, read_stats(dev))
        ctx.say(f"[ocelus] window: rd_compl={d['rd_compl']} wr_compl={d['wr_compl']} "
                f"rd_err={d['rd_err']} wr_err={d['wr_err']} core_err={d['core_err']} "
                f"records={d['rec']} dropped={d['dropped']} mismatched={res.mismatched}")

        bad = problems(d, txn, txn)
        if not res.ok:
            bad.insert(0, f"write/read pass failed (mismatched={res.mismatched})")
        if bad:
            raise RuntimeError("ocelus: " + "; ".join(bad))
        return {"ok": True, **d, "burst_len": blen, "txn_count": txn}
