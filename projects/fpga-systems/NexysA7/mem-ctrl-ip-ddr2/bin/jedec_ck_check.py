#!/usr/bin/env python3
# SPDX-License-Identifier: MIT
# SPDX-FileCopyrightText: 2026 sean galloway
"""JEDEC DDR2 check at CK resolution over a granite perf-proxy DRAM trace.

The trace is `PERF_DRAM_TRACE=<path>` from test_granite_char_perf.py: every command the DRAM model
accepted as [cycle, kind, bank, dfi_phase] (kind ACT / RD / WR / PRE / PREA / AP); CK = 2 * cycle +
phase for the DFI 1:2 build. The controller's own timers are MC-cycle counters and the DRAM model's
checker compares against CK counts at the wrong clock, so neither says whether a command stream is
legal to the CK -- this does, for the MT47H64M16 DDR2-400 minima at CL 3 / BL4 / AL 0. An
auto-precharge is checked as a PRE at the DRAM's internal close time, max(RD + BL/2 + tRTP - 2,
WR + WL + BL/2 + tWR, ACT + tRAS). Method and the measurement it was written for:
vault/handbook/dv/dram-cycle-model.md (memory-controllers MC-020, 2026-11-21).

    jedec_ck_check.py <trace.json> [...]      -> commands checked and the violation counts per rule
"""
import json, sys
T = dict(tRCD=3, tRP=3, tRAS=9, tRC=12, tRRD=2, tFAW=9, tRFC=26, tWR=3, tRTP=2, tWTR=2, tCCD=2)
WL, HALF_BL = 2, 2
def check(path):
    ev = json.load(open(path))
    viol = {}
    def v(k): viol[k] = viol.get(k, 0) + 1
    last_act = {}; last_rd = {}; last_wr = {}; last_pre = {}; open_row = {}; acts = []; last_ref = -10**9; last_wr_any = -10**9
    for e in ev:
        cyc, kind, bank = e[0], e[1], e[2]
        ph = e[3] if len(e) > 3 else 0
        t = 2 * cyc + ph
        if kind == "ACT":
            if bank in last_pre and t - last_pre[bank] < T["tRP"]: v("tRP")
            if bank in last_act and t - last_act[bank] < T["tRC"]: v("tRC")
            if acts and t - acts[-1] < T["tRRD"]: v("tRRD")
            if len(acts) >= 4 and t - acts[-4] < T["tFAW"]: v("tFAW")
            if t - last_ref < T["tRFC"]: v("tRFC")
            last_act[bank] = t; acts.append(t); acts = acts[-4:]
        elif kind in ("RD", "WR"):
            if bank not in last_act or t - last_act[bank] < T["tRCD"]: v("tRCD")
            if kind == "RD" and t - last_wr_any < WL + HALF_BL + T["tWTR"]: v("tWTR")
            if kind == "RD": last_rd[bank] = t
            else: last_wr[bank] = t; last_wr_any = t
        elif kind in ("PRE", "AP"):
            # AP: the DRAM closes internally at max(RD + rd_to_pre, WR + WL + BL/2 + tWR, ACT + tRAS); the next ACT must
            # follow that by tRP -- model it as a PRE at that time
            if kind == "AP":
                cands = [last_act.get(bank, -10**9) + T["tRAS"]]
                if bank in last_rd and last_rd[bank] >= last_act.get(bank, -10**9): cands.append(last_rd[bank] + HALF_BL + T["tRTP"] - 2)
                if bank in last_wr and last_wr[bank] >= last_act.get(bank, -10**9): cands.append(last_wr[bank] + WL + HALF_BL + T["tWR"])
                t = max(cands)
            else:
                if bank in last_act and t - last_act[bank] < T["tRAS"]: v("tRAS")
                if bank in last_rd and last_rd[bank] > last_act.get(bank, -10**9) and t - last_rd[bank] < HALF_BL + T["tRTP"] - 2: v("tRTP")
                if bank in last_wr and last_wr[bank] > last_act.get(bank, -10**9) and t - last_wr[bank] < WL + HALF_BL + T["tWR"]: v("tWR")
            last_pre[bank] = t
        elif kind == "PREA":
            for b in list(last_act): last_pre[b] = max(last_pre.get(b, -10**9), t)
        elif kind in ("REF", "REFA"):
            last_ref = t
    return len(ev), viol
if __name__ == "__main__":
    for p in sys.argv[1:]:
        n, viol = check(p)
        print(p.split("/")[-1], "commands", n, "violations", viol or "none")
