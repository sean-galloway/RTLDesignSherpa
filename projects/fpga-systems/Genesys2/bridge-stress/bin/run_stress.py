#!/usr/bin/env python3
# SPDX-License-Identifier: MIT
# SPDX-FileCopyrightText: 2026 sean galloway
"""Bridge stress model: the board program.

Runs bin/bstress.py profiles on the Genesys 2 over its UART -- the same
library, verdict and window plan the simulation runs (dv/tests/
test_bs_harness.py). The bitstream is checked against the build's TOML
before anything is programmed.

    python3 bin/run_stress.py                          # every profile, 3 seeds
    python3 bin/run_stress.py --profiles chaos --seeds 20 --txns 20000
    python3 bin/run_stress.py --soak 600               # chaos, new seed per run, 10 min
    python3 bin/run_stress.py --profiles bursts        # every path carries FIXED/WRAP/narrow

Output: reports/board/<build>_<YYYYMMDD_HHMMSS>.csv and .json (one row per
run). Exit code 1 if any run fails.
"""
from __future__ import annotations

import argparse
import csv
import json
import sys
import time
from dataclasses import replace
from datetime import datetime
from pathlib import Path

import bstress

AREA = bstress.AREA
BUILDS = {'axi4': 'bridge_bs_axi4', 'axi3': 'bridge_bs_axi3', 'axi5': 'bridge_bs_axi5',
          'xil': 'bridge_bs_xil', 'xmix': 'bridge_bs_xmix', 'mixb': 'bridge_bs_mixed_b'}
ACLK_HZ = 100e6


def _probe(link) -> bool:
    from uart_link import open_bridge
    v = open_bridge(channel=link).read(bstress.CTL_BASE)
    return v is not None and (v >> 16) == 0x4253


def _port_perf(build, res: dict) -> list[dict]:
    """Per stress-master direction: bursts, beats, MB/s, latency (cycles), peak
    outstanding -- the figures StressHarness.summary prints, kept per run."""
    t = res['ctl']['TIMER'] or 1
    out = []
    for m in build.stress_masters:
        for dr in ('rd', 'wr'):
            r = res[f'{m.name}.{dr}']
            if not r['issued']:
                continue
            out.append(dict(port=m.name, dir=dr, dw=m.dw, bursts=r['completed'], beats=r['beats'],
                            mbps=round(r['beats'] * (m.dw // 8) / (t / ACLK_HZ) / 1e6, 1),
                            lat_mean=round(r['lat_sum'] / max(1, r['completed']), 1),
                            lat_max=r['lat_max'], out_max=r['out_max']))
    return out


def main() -> int:
    ap = argparse.ArgumentParser(description=__doc__.split('\n')[0])
    ap.add_argument('--build', default='axi4', choices=sorted(BUILDS))
    ap.add_argument('--port', default='auto')
    ap.add_argument('--baud', type=int, default=115200)
    ap.add_argument('--profiles', nargs='+', default=list(bstress.PROFILES))
    ap.add_argument('--seeds', type=int, default=3, help='seeds per profile (1..n)')
    ap.add_argument('--seed0', type=int, default=1)
    ap.add_argument('--txns', type=int, default=4000, help='bursts per master direction')
    ap.add_argument('--soak', type=float, default=0.0,
                    help='seconds: repeat chaos with a fresh seed until the time is up')
    ap.add_argument('--full-axi', action='store_true',
                    help='no-op since bridge BUG-018/019: every path already carries full AXI4')
    ap.add_argument('--timeout', type=float, default=120.0, help='seconds per run')
    ap.add_argument('--exclude', nargs='+', default=[],
                    help='slaves to leave out of the plan (e.g. mig): no window targets them')
    args = ap.parse_args()

    toml = AREA / 'rtl/bridges/configs' / f'{BUILDS[args.build]}.toml'
    build = bstress.load_build(toml)
    unknown = set(args.exclude) - {s.name for s in build.slaves}
    if unknown:
        sys.exit(f'--exclude: no such slave {sorted(unknown)}')
    for p in args.profiles:
        if p not in bstress.PROFILES:
            sys.exit(f'unknown profile {p!r}; have {sorted(bstress.PROFILES)}')

    from uart_link import find_port, open_bridge
    port = find_port(_probe, want=args.port, baudrate=args.baud, label='bridge stress harness')
    bus = open_bridge(port=port, baudrate=args.baud)
    h = bstress.StressHarness(bus, build)
    h.identify()
    if args.exclude:
        # after identify (it counts the bitstream's ports) and after the hole
        # is chosen (it must stay clear of the excluded slave's range too)
        h.build = build = replace(build, slaves=tuple(s for s in build.slaves
                                                     if s.name not in args.exclude))
        print(f'[bstress] excluded from the plan: {args.exclude}')
    print(f'[bstress] {build.name}: {len(build.masters)} masters, {len(build.slaves)} slaves '
          f'on {port}')
    if any(m.vendor for m in build.masters):
        import bstress_xil
        h.vendor = bstress_xil.XilVendors(h)
    if build.memories:
        # build-xil: EXT_STS0 [0] DDR3 init_done, [10] init_error (bs_genesys2_xil_top)
        t0 = time.monotonic()
        while not h.ctl.read('EXT_STS0') & 1:
            if h.ctl.read('EXT_STS0') >> 10 & 1:
                sys.exit(f"[bstress] DDR3 calibration failed (EXT_STS0 {h.ctl.read('EXT_STS0'):#010x})")
            if time.monotonic() - t0 > 10:
                sys.exit(f"[bstress] DDR3 never calibrated (EXT_STS0 {h.ctl.read('EXT_STS0'):#010x})")
            time.sleep(0.1)
        print(f"[bstress] DDR3 calibrated; EXT_STS0 {h.ctl.read('EXT_STS0'):#010x}")

    plan = []
    if args.soak:
        plan = None
    else:
        for p in args.profiles:
            for s in range(args.seed0, args.seed0 + args.seeds):
                plan.append((p, s))

    out_dir = AREA / 'reports' / 'board'
    out_dir.mkdir(parents=True, exist_ok=True)
    stamp = datetime.now().strftime('%Y%m%d_%H%M%S')
    rows, perf, failed = [], [], 0
    t_end = time.monotonic() + args.soak
    seed = args.seed0
    while True:
        if plan is None:
            if time.monotonic() > t_end:
                break
            name, s = 'chaos', seed
            seed += 1
        else:
            if not plan:
                break
            name, s = plan.pop(0)
        prof = bstress.PROFILES[name]
        if args.full_axi:
            prof = replace(prof, full_axi=True)
        res = h.run(prof, s, args.txns, timeout_s=args.timeout)
        ok, why = h.verdict(res)
        print(h.summary(res, ACLK_HZ))
        print(f"  -> {'PASS' if ok else 'FAIL'}" + ('' if ok else ': ' + '; '.join(why)))
        failed += not ok
        rows.append(dict(build=build.name, profile=name, seed=s, txns=args.txns,
                         full_axi=prof.full_axi, ok=ok, cycles=res['ctl']['TIMER'],
                         reasons=' | '.join(why)))
        perf.append(dict(rows[-1], ports=_port_perf(h.build, res)))
        if not res['meta']['finished']:
            print('[bstress] run did not finish; the harness may need a reset (reprogram) '
                  'before another GO is accepted')
            break

    csv_path = out_dir / f'{build.name}_{stamp}.csv'
    with csv_path.open('w', newline='') as f:
        w = csv.DictWriter(f, fieldnames=list(rows[0]) if rows else ['build'])
        w.writeheader()
        w.writerows(rows)
    # the JSON also carries each run's per-port figures (what h.summary prints)
    csv_path.with_suffix('.json').write_text(json.dumps(perf, indent=1))
    print(f'[bstress] {len(rows) - failed}/{len(rows)} passed -> {csv_path}')
    return 1 if failed else 0


if __name__ == '__main__':
    sys.exit(main())
