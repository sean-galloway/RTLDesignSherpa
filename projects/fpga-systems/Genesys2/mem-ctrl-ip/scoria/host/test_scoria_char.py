#!/usr/bin/env python3
"""Board-less tests for scoria_char geometry and the access-pattern families.

The families are named for what they do to the DRAM -- "page miss every burst",
"activates pipeline across banks" -- and those are claims about address
arithmetic, so they are checkable without hardware. This decodes addresses back
into (bank, row, col) and asserts each family does what its name says.

Worth having because the failure mode is silent: a stride that is wrong by a
factor of the bank count still produces a clean bandwidth number, just for a
different access pattern than the label on the table.

    ./test_scoria_char.py        # exit 1 on any failure
"""
from __future__ import annotations
import os, sys

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import scoria_char as sc
from scoria_char import Geometry, Scenario, strides_for


def decode(addr: int, g: Geometry):
    """AXI byte address -> (bank, row, col) for the live bank_lsb arrangement.

    Mirrors scoria_addr_mapper: column is the low field, the bank field starts
    at bank_lsb (in bus-word units), row sits above it.
    """
    word = addr >> g.byte_offset                 # bus-word index
    col = word & ((1 << g.col_width) - 1)
    bank = (word >> g.bank_lsb) & ((1 << g.bank_width) - 1)
    row = word >> (g.bank_lsb + g.bank_width)
    return bank, row, col


def _fail(msg): print(f"  FAIL {msg}"); return 1


def main() -> int:
    g = sc.DEFAULT_GEOM
    bad = 0

    # ---- geometry against the board's own report -------------------------
    if g.device_bytes != 1 << 30:
        bad += _fail(f"device_bytes {g.device_bytes} != 1 GiB (board reported 1.0 GiB)")
    if g.page_bytes != 4096:
        bad += _fail(f"page_bytes {g.page_bytes} != 4096")
    if g.burst_len_multiple != 4:
        bad += _fail(f"burst_len_multiple {g.burst_len_multiple} != 4")
    if sc.peak_mb_s(g) != 3200:
        bad += _fail(f"peak {sc.peak_mb_s(g)} != 3200 MB/s")

    # ---- row_major: every burst stays inside ONE page --------------------
    s = Scenario("rm", sc.FAM_ROW_MAJOR, burst_len=8)
    stride, wrap = strides_for(s, g)
    seen = set()
    for i in range(64):
        a = (i * stride) & wrap
        seen.add(decode(a, g)[:2])               # (bank, row)
    if len(seen) != 1:
        bad += _fail(f"row_major touched {len(seen)} (bank,row) pairs, expected 1: {sorted(seen)[:4]}")

    # ---- col_major: EVERY step changes the row, bank stays put -----------
    s = Scenario("cm", sc.FAM_COL_MAJOR, burst_len=8)
    stride, wrap = strides_for(s, g)
    banks, rows = set(), set()
    for i in range(32):
        b, r, _ = decode((i * stride) & wrap, g)
        banks.add(b); rows.add(r)
    if len(banks) != 1:
        bad += _fail(f"col_major spanned {len(banks)} banks, expected 1 (a page miss "
                     f"needs the SAME bank): {sorted(banks)}")
    if len(rows) != 32:
        bad += _fail(f"col_major hit {len(rows)} distinct rows in 32 steps, expected 32 "
                     f"-- it is not missing the page every burst")

    # ---- col_major_interleaved: EVERY step changes the bank --------------
    s = Scenario("ci", sc.FAM_COL_INTERLEAVE, burst_len=8)
    stride, wrap = strides_for(s, g)
    seq = [decode((i * stride) & wrap, g)[0] for i in range(8)]
    if sorted(seq) != list(range(8)):
        bad += _fail(f"col_major_interleaved visited banks {seq}, expected each of 0..7 "
                     f"once -- activates cannot pipeline otherwise")

    # ---- incremental: contiguous, unwrapped ------------------------------
    s = Scenario("inc", sc.FAM_INCREMENTAL, burst_len=8)
    stride, wrap = strides_for(s, g)
    if wrap != 0:
        bad += _fail(f"incremental wrap {wrap} != 0 (it must march the whole space)")
    if stride != s.burst_bytes(g):
        bad += _fail(f"incremental stride {stride} != burst_bytes {s.burst_bytes(g)}")

    # ---- bank_lsb actually MOVES the bank field --------------------------
    # The whole reason bank_stride is derived rather than equated to page_bytes.
    g2 = Geometry(bank_lsb=13)
    if g2.bank_stride == g.bank_stride:
        bad += _fail("bank_stride did not change with bank_lsb -- it is hardcoded")
    s = Scenario("ci", sc.FAM_COL_INTERLEAVE, burst_len=8)
    stride, wrap = strides_for(s, g2)
    seq = [decode((i * stride) & wrap, g2)[0] for i in range(8)]
    if sorted(seq) != list(range(8)):
        bad += _fail(f"at bank_lsb=13 interleave visited {seq}, expected 0..7 -- the "
                     f"family does not follow the live address map")

    # ---- stall attribution has EIGHT buckets, including zq ---------------
    if len(sc.StallStats._F) != 8:
        bad += _fail(f"StallStats has {len(sc.StallStats._F)} buckets, expected 8")
    if "zq" not in sc.StallStats._F:
        bad += _fail("StallStats has no zq bucket -- ZQ waits would be charged to banktimer")
    z = sc.StallStats(bp=1, refresh=2, turnaround=3, tccd=4, actlimit=5,
                      banktimer=6, noreq=7, zq=90)
    if z.total != 118:
        bad += _fail(f"StallStats.total {z.total} != 118 (the sum cross-check is broken)")
    if z.limiter() != "zq":
        bad += _fail(f"limiter() said {z.limiter()!r}, expected 'zq'")

    # ---- derived ratios --------------------------------------------------
    r = sc.derived_ratios({sc.FAM_INCREMENTAL: 2000.0, sc.FAM_COL_MAJOR: 500.0,
                           sc.FAM_COL_INTERLEAVE: 1500.0})
    if abs(r["page_penalty"] - 4.0) > 1e-9:
        bad += _fail(f"page_penalty {r['page_penalty']} != 4.0")
    if abs(r["bank_parallel"] - 3.0) > 1e-9:
        bad += _fail(f"bank_parallel {r['bank_parallel']} != 3.0")
    if sc.derived_ratios({sc.FAM_COL_MAJOR: 0.0})["page_penalty"] is not None:
        bad += _fail("derived_ratios divided by zero instead of returning None")

    print(f"  {'FAILED' if bad else 'all checks pass'}"
          f"{f' -- {bad} failure(s)' if bad else ''}")
    return 1 if bad else 0


if __name__ == "__main__":
    raise SystemExit(main())
