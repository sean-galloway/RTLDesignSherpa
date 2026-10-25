#!/usr/bin/env python3
# SPDX-License-Identifier: MIT
# SPDX-FileCopyrightText: 2026 sean galloway
#
# sched_trace_timeline.py -- per-descriptor timeline of channel 0 from a CHAR_TRACE_OUT
# trace (stream TASK-021). Produce the trace with the sim profile runner:
#   CHAR_POINTS=chain_ch1_b32_d16 CHAR_CSV_OVERRIDE=csv/task021_probe.csv \
#   CHAR_TRACE_OUT=/tmp/t.jsonl pytest dv/tests/test_stream_g_profiles.py -k gscale1-g-2of2
# then: bin/sched_trace_timeline.py /tmp/t.jsonl
"""Per-descriptor timeline of channel 0 from a CHAR_TRACE_OUT trace (TASK-021).
Reconstructs the sampled state per cycle from the change records and prints, per
descriptor start (take or in-place advance): the start kind, cycles since the
previous start, head-valid -> STAGE latency, STAGE -> start latency, the state
walk between starts, and the gap between the previous descriptor's last read
request and this start."""
import json, sys
ST = {1:'IDLE',2:'FETCH',4:'XFER',8:'COMPLETE',16:'NEXT',32:'ERROR'}
ev = [json.loads(l) for l in open(sys.argv[1])]
state = {}; rows = []
head_up = stage_at = None; last_rd = None; walk = []; prev_start = None; kicks = 0
prev = {}
for e in ev:
    cyc = e['cyc']; state.update({k: v for k, v in e.items() if k != 'cyc'})
    s = state
    # descriptor fetch AR handshake (shared engine; all channels, one channel active here)
    if s.get('desc_ar') == 1 and s.get('desc_arready') == 1 and (prev.get('desc_ar'), prev.get('desc_arready')) != (1, 1):
        fetch_at = cyc
    if 'head' in e and e['head'] == 1: head_up = cyc
    if s.get('wr_en') == 1 and s.get('wr_addr') == 0 and ('wr_en' in e or 'wr_data' in e or 'wr_addr' in e):
        d = s.get('wr_data', 0)
        if d & ((1 << 10) | (1 << 15)): stage_at = cyc
        cmdst = d & 0x7f
        if cmdst: walk.append(f"cmd:{ST.get(cmdst, cmdst)}")
    if 'state' in e: walk.append(ST.get(e['state'], str(e['state'])))
    if s.get('rd_req') == 1: last_rd = cyc
    start = None
    if e.get('take') == 1: start = 'take'
    if e.get('advance') == 1: start = 'advance'
    if start:
        rows.append(dict(cyc=cyc, kind=start, since_prev=(cyc - prev_start) if prev_start else None,
                         head_to_stage=(stage_at - head_up) if (stage_at and head_up and stage_at >= head_up) else None,
                         stage_to_start=(cyc - stage_at) if stage_at else None,
                         gap_after_last_rd=(cyc - last_rd) if (last_rd and prev_start) else None,
                         walk=' '.join(walk[-6:])))
        prev_start = cyc; walk = []; head_up = None; stage_at = None
    prev = dict(s)
print(f"{'cyc':>7s} {'start':8s} {'dT':>5s} {'head>STG':>8s} {'STG>start':>9s} {'lastRD>start':>12s}  state walk since previous start")
for r in rows:
    f = lambda v: '' if v is None else str(v)
    print(f"{r['cyc']:7d} {r['kind']:8s} {f(r['since_prev']):>5s} {f(r['head_to_stage']):>8s} {f(r['stage_to_start']):>9s} {f(r['gap_after_last_rd']):>12s}  {r['walk']}")
print(f"\n{len(rows)} descriptor starts; advances: {sum(1 for r in rows if r['kind']=='advance')}, takes: {sum(1 for r in rows if r['kind']=='take')}")
