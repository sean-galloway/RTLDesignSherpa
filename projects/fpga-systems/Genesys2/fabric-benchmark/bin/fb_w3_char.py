#!/usr/bin/env python3
# SPDX-License-Identifier: MIT
# SPDX-FileCopyrightText: 2026 sean galloway
"""Fabric benchmark board program: W3, the contention pair (bin/fb_w3.py).

STREAM and the injector share S0. Each point is (flavor, gap, outstanding) at
one STREAM configuration; the injector's gap sets the mix.

    python3 bin/fb_w3_char.py --leg a --calibrate          # idle 0..1920, mirror, out 4
    python3 bin/fb_w3_char.py --leg a --idle 0 480         # the sweep at two gaps
    python3 bin/fb_w3_char.py --leg a --dry-run

The gap is given as idle cycles between injector bursts (gap << gap_shift,
0..1920). --calibrate walks a ladder of gaps once per flavor (outstanding 4) to
find the gaps that give each mix; the sweep then runs both flavors x --idle x
--outstanding.

Output: reports/board/w3_<leg>_<stamp>.csv (+ JSON). Exit 1 if any point
fails its data check.
"""
from __future__ import annotations

import argparse
import csv
import json
import sys
from datetime import datetime
from pathlib import Path

import fb_map
import fb_w3

AREA = Path(__file__).resolve().parent.parent
FIELDS = ('leg', 'flavor', 'idle_cycles', 'gap', 'gap_shift', 'outstanding', 'channels', 'descriptors', 'bytes_per_desc',
          'pass', 'inj_share', 'stream_beats', 'inj_beats', 'window_cycles',
          'stream_mibs', 'inj_mibs', 'inj_bp', 'inj_starv', 'error')


def row(leg, cfg, r) -> dict:
    inj = r['inj']
    rnd = lambda v, n: None if v is None else round(v, n)
    return {'leg': leg, 'flavor': r['flavor'], 'idle_cycles': inj.idle_cycles, 'gap': inj.gap,
            'gap_shift': inj.gap_shift, 'outstanding': inj.outstanding,
            'channels': cfg.num_channels, 'descriptors': cfg.descriptors_per_channel,
            'bytes_per_desc': cfg.transfer_bytes, 'pass': r['verdict'],
            'inj_share': rnd(r.get('inj_share'), 4), 'stream_beats': r.get('stream_beats'),
            'inj_beats': r.get('inj_beats'), 'window_cycles': r.get('window_cycles'),
            'stream_mibs': rnd(r.get('stream_mibs'), 1), 'inj_mibs': rnd(r.get('inj_mibs'), 1),
            'inj_bp': (r.get('inj_meter') or {}).get('bp'),
            'inj_starv': (r.get('inj_meter') or {}).get('starv'),
            'error': '; '.join(r['why'])}


def main() -> int:
    ap = argparse.ArgumentParser(description=__doc__.splitlines()[0])
    ap.add_argument('--leg', required=True)
    ap.add_argument('--port', default='auto')
    ap.add_argument('--baud', type=int, default=115200)
    ap.add_argument('--channels', type=int, default=8)
    ap.add_argument('--size', default='128K', help="bytes per descriptor (K/M suffix); 4 MB total by default, well inside the injector's 16 MB")
    ap.add_argument('--desc', type=int, default=4)
    ap.add_argument('--flavors', nargs='+', default=['f3', 'mirror'])
    ap.add_argument('--idle', type=int, nargs='+', default=[0],
                    help="injector idle cycles between bursts (0..1920)")
    ap.add_argument('--outstanding', type=int, nargs='+', default=[2, 4])
    ap.add_argument('--calibrate', action='store_true',
                    help="a ladder of gaps once per flavor, outstanding 4")
    ap.add_argument('--dry-run', action='store_true')
    args = ap.parse_args()

    from fb_char import parse_size
    fb_map.stream_host_path()
    from descriptor_builder import CharConfig
    nbytes = parse_size(args.size)
    cfg = CharConfig(name=f"w3_{args.channels}ch_{args.desc}desc_{args.size}",
                     num_channels=args.channels, descriptors_per_channel=args.desc,
                     transfer_bytes=nbytes)
    if args.calibrate:
        ladder = (0, 15, 30, 60, 120, 240, 480, 960, 1920)
        points = [(f, fb_w3.Inj.for_idle(i, outstanding=4)) for f in args.flavors for i in ladder]
    else:
        points = [(f, fb_w3.Inj.for_idle(i, outstanding=o))
                  for f in args.flavors for i in args.idle for o in args.outstanding]
    print(f"fb_w3_char: leg {args.leg}, {cfg.name}, {len(points)} point(s)")
    for f, inj in points:
        print(f"  {f} idle {inj.idle_cycles} (gap {inj.gap} << {inj.gap_shift}) "
              f"outstanding {inj.outstanding}")
    if args.dry_run:
        return 0

    from uart_axi_bridge import UARTAxiBridge
    from harness_addrs import autodetect_port
    from characterization import CharacterizationRunner

    out_dir = AREA / 'reports' / 'board'
    out_dir.mkdir(parents=True, exist_ok=True)
    stamp = datetime.now().strftime('%Y%m%d_%H%M%S')
    tag = 'w3cal' if args.calibrate else 'w3'
    csv_path = out_dir / f"{tag}_{args.leg}_{stamp}.csv"
    rows = []
    port = autodetect_port(args.baud, want=args.port)
    with UARTAxiBridge(port, args.baud) as bridge:
        runner = CharacterizationRunner(bridge, data_width=fb_map.DATA_WIDTH,
                                        builder=fb_map.make_builder())
        runner.log = lambda m: None
        if not runner.ping():
            print("fb_w3_char: ping failed")
            return 1
        for i, (flavor, inj) in enumerate(points, 1):
            print(f"[{i}/{len(points)}]", end='', flush=True)
            r = fb_w3.run_point(runner, bridge, cfg, flavor, inj,
                                log=lambda m: print(m, flush=True))
            rows.append(row(args.leg, cfg, r))
    with open(csv_path, 'w', newline='') as fh:
        w = csv.DictWriter(fh, fieldnames=FIELDS)
        w.writeheader()
        w.writerows(rows)
    csv_path.with_suffix('.json').write_text(json.dumps(rows, indent=2))
    bad = sum(not r['pass'] for r in rows)
    print(f"fb_w3_char: {len(rows) - bad}/{len(rows)} pass -> {csv_path}")
    return 1 if bad else 0


if __name__ == '__main__':
    sys.exit(main())
