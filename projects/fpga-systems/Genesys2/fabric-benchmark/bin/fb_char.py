#!/usr/bin/env python3
# SPDX-License-Identifier: MIT
# SPDX-FileCopyrightText: 2026 sean galloway
"""Fabric benchmark board program: the W2 sweep, and the DDR3 workload chain.

The same Genesys 2 STREAM characterization runner the K0 sim drives
(dv/tbclasses/fb_harness_tb.py), over the board's UART instead of the sim
channel, with the same DescriptorBuilder (bin/fb_map.py). Nothing in here knows
which leg is loaded -- the leg is the bitstream -- so the one program runs every
leg and the label only names the output file.

Per run the runner reports its verdict, the on-chip run timer, the CRC valid
and match masks of every active channel, and the bus meters, and this program
adds STREAM's latency histograms over the same window (bin/fb_latency.py: log2
bins, so p50/p90/p99 are bin lower edges in cycles); a run passes only
when the verdict is PASS and every active channel's CRC is valid and matches.

    python3 bin/fb_char.py --leg a                       # default sweep
    python3 bin/fb_char.py --leg b1 --channels 1 8 --sizes 64K 1M --desc 4
    python3 bin/fb_char.py --leg a --dry-run             # list the runs only
    python3 bin/fb_char.py --leg a --chain               # W1-F2, W1-F1, W4, drain

--chain runs bin/fb_workloads.CHAIN on every sweep point instead of W2: each
step reads or writes DDR3 at S0, and both drains end in a per-channel CRC check
against the fill's LFSR CRCs (fb_workloads has the verdict rules). It is an
integrity check: its rows carry the verdict and S0 counts, no bandwidth.

Output: reports/board/w2_<leg>_<YYYYMMDD_HHMMSS>.csv (one row per run; k3_ for
--chain, one row per step) and the same rows as JSON beside it. The exit code is
1 if any run fails.
"""
from __future__ import annotations

import argparse
import csv
import json
import sys
from datetime import datetime
from pathlib import Path

import fb_latency
import fb_map
import fb_workloads

AREA = Path(__file__).resolve().parent.parent
SIZE_UNITS = {'K': 1024, 'M': 1024 * 1024}
# Headline sweep: channel counts x bytes per descriptor, 4 descriptors each.
# The largest run is 8 ch x 4 x 1 MB = 32 MB moved, well inside each
# channel's 32 MB window (fb_map.CH_ADDR_LSB).
DEFAULT_CHANNELS = (1, 2, 4, 8)
DEFAULT_SIZES = ('4K', '64K', '1M')
DEFAULT_DESC = 4
FIELDS = ('leg', 'name', 'step', 'channels', 'descriptors', 'bytes_per_desc', 'pass',
          'crc_valid', 'crc_match', 'cycles_total', 'bus_throughput_mbps',
          'peak_mbps', 'pct_of_peak', 'm_rd_util', 'm_wr_util', 's_rd_util', 's_wr_util',
          's0_rd_beats', 's0_wr_beats', 'error') + fb_latency.COLUMNS


def parse_size(text: str) -> int:
    t = text.strip().upper()
    mult = SIZE_UNITS.get(t[-1], 1)
    return int(t[:-1] if t[-1] in SIZE_UNITS else t) * mult


def plan(channels, sizes, desc, prefix='w2'):
    fb_map.stream_host_path()
    from descriptor_builder import CharConfig
    runs = []
    for size in sizes:
        nbytes = parse_size(size)
        if desc * nbytes > 1 << fb_map.CH_ADDR_LSB:
            sys.exit(f"fb_char: {desc} x {size} exceeds a channel's "
                     f"{(1 << fb_map.CH_ADDR_LSB) >> 20} MB window")
        for ch in channels:
            runs.append(CharConfig(name=f"{prefix}_{ch}ch_{desc}desc_{size}", num_channels=ch,
                                   descriptors_per_channel=desc, transfer_bytes=nbytes))
    return runs


def row(leg, cfg, res, slv, lat=None) -> dict:
    """m_*_util: STREAM's own port (master-side observer, the runner's
    metrics); s_*_util: the fabric's output to the endpoints (slave-side
    observer, same window).

    peak_mbps is one direction of the 128-bit bus at the board's clock
    (the runner's bus_max_one_dir_mbps, MiB/s like every figure here). The
    runner's own "net-moved" ceiling halves it because on STREAM's board
    reads and writes share one DDR; in W2 they go to separate endpoints, so
    a run moves its bytes at up to the full one-direction rate."""
    peak = res.get('bus_max_one_dir_mbps')
    mbps = res.get('bus_throughput_mbps')
    crc = res.get('crc') or {}
    met = res.get('metrics') or {}
    # STREAM's perf window measures data movement only: it opens at the kick
    # and closes after 16 quiet cycles. A descriptor fetch slower than that
    # (B2, 1 channel) closes it before the first data beat, so the buckets
    # hold none of the run's data. Report no utilization rather than a wrong one.
    short = [s for s in ('r', 'w')
             if (met.get(f'{s}_window_cycles') or 0) < (met.get(f'{s}_firstlast_cycles') or 0) // 2]
    util = (lambda v: None) if short else (lambda v: v)
    active = (1 << cfg.num_channels) - 1
    ok = bool(res.get('pass')) and crc.get('valid_mask') == active and crc.get('match_mask') == active
    return {'leg': leg, 'name': cfg.name, 'step': 'w2', 'channels': cfg.num_channels,
            'descriptors': cfg.descriptors_per_channel, 'bytes_per_desc': cfg.transfer_bytes,
            'pass': ok, 'crc_valid': f"0x{crc.get('valid_mask', 0):X}",
            'crc_match': f"0x{crc.get('match_mask', 0):X}",
            'cycles_total': res.get('bus_cycles_total'),
            'bus_throughput_mbps': round(mbps, 1) if mbps else mbps,
            'peak_mbps': round(peak, 1) if peak else peak,
            'pct_of_peak': round(100 * mbps / peak, 1) if mbps and peak else None,
            'm_rd_util': util(met.get('datapath_utilization_r')),
            'm_wr_util': util(met.get('datapath_utilization_w')),
            's_rd_util': util(round(slv['r_util'], 4)), 's_wr_util': util(round(slv['w_util'], 4)),
            'error': res.get('error') or ('' if ok else 'crc mask short of every active channel')
                     or (f"perf window closed early ({'/'.join(short)}); no utilization" if short else ''),
            **(fb_latency.columns(lat) if lat else {})}


def chain_row(leg, cfg, res) -> dict:
    """One chain step: an integrity verdict, not a bandwidth figure. W1/W4
    rates are set by S0's controller, not the fabric (PRD §6, K3), so the
    throughput and utilization columns are left empty on purpose."""
    crc = res.get('crc') or {}
    return {'leg': leg, 'name': cfg.name, 'step': res['step'], 'channels': cfg.num_channels,
            'descriptors': cfg.descriptors_per_channel, 'bytes_per_desc': cfg.transfer_bytes,
            'pass': res['verdict'], 'crc_valid': f"0x{crc.get('valid_mask', 0):X}",
            'crc_match': f"0x{crc.get('match_mask', 0):X}",
            's0_rd_beats': res.get('s0_rd_beats'), 's0_wr_beats': res.get('s0_wr_beats'),
            'error': '; '.join(res['why'])}


def main() -> int:
    ap = argparse.ArgumentParser(description=__doc__.splitlines()[0])
    ap.add_argument('--leg', required=True, help="label for the loaded bitstream (a, b1, b2)")
    ap.add_argument('--port', default='auto')
    ap.add_argument('--baud', type=int, default=115200)
    ap.add_argument('--channels', type=int, nargs='+', default=list(DEFAULT_CHANNELS))
    ap.add_argument('--sizes', nargs='+', default=list(DEFAULT_SIZES))
    ap.add_argument('--desc', type=int, default=DEFAULT_DESC)
    ap.add_argument('--chain', action='store_true', help="the DDR3 workload chain, not W2")
    ap.add_argument('--dry-run', action='store_true')
    ap.add_argument('--verbose', '-v', action='store_true')
    args = ap.parse_args()

    kind = 'k3' if args.chain else 'w2'
    runs = plan(args.channels, args.sizes, args.desc, prefix=kind)
    print(f"fb_char: leg {args.leg}, {len(runs)} {'chain' if args.chain else 'run'}(s)")
    for cfg in runs:
        print(f"  {cfg.name}")
    if args.dry_run:
        return 0

    fb_map.stream_host_path()
    from uart_axi_bridge import UARTAxiBridge
    from harness_addrs import autodetect_port
    from characterization import CharacterizationRunner
    from fb_slave_meters import read_slave_side

    out_dir = AREA / 'reports' / 'board'
    out_dir.mkdir(parents=True, exist_ok=True)
    stamp = datetime.now().strftime('%Y%m%d_%H%M%S')
    csv_path = out_dir / f"{kind}_{args.leg}_{stamp}.csv"

    rows = []
    port = autodetect_port(args.baud, want=args.port)
    with UARTAxiBridge(port, args.baud) as bridge:
        runner = CharacterizationRunner(bridge, data_width=fb_map.DATA_WIDTH,
                                        builder=fb_map.make_builder(), verbose=args.verbose)
        if not runner.ping():
            print("fb_char: ping failed (UART link, harness_csr SCRATCH or BUILD_ID)")
            return 1
        for i, cfg in enumerate(runs, 1):
            print(f"[{i}/{len(runs)}] {cfg.name} ...", flush=True)
            if args.chain:
                for res in fb_workloads.run_chain(runner, bridge, cfg,
                                                  log=lambda m: print(m, flush=True)):
                    rows.append(chain_row(args.leg, cfg, res))
                continue
            res = runner.run_config(cfg)
            r = row(args.leg, cfg, res, read_slave_side(bridge), fb_latency.read_latency(bridge))
            rows.append(r)
            print(f"    {'PASS' if r['pass'] else 'FAIL'}  {r['bus_throughput_mbps']} MB/s "
                  f"({r['pct_of_peak']}% of {r['peak_mbps']})  "
                  f"cycles {r['cycles_total']}  crc {r['crc_valid']}/{r['crc_match']}  "
                  f"util rd {r['m_rd_util']}/{r['s_rd_util']} wr {r['m_wr_util']}/{r['s_wr_util']}  "
                  f"lat p50 rd {r['rd_first_p50']}/{r['rd_last_p50']} wr {r['wr_b_p50']}"
                  + (f"  ({r['error']})" if r['error'] else ''), flush=True)

    with open(csv_path, 'w', newline='') as fh:
        w = csv.DictWriter(fh, fieldnames=FIELDS)
        w.writeheader()
        w.writerows(rows)
    csv_path.with_suffix('.json').write_text(json.dumps(rows, indent=2))
    bad = sum(not r['pass'] for r in rows)
    print(f"fb_char: {len(rows) - bad}/{len(rows)} pass -> {csv_path}")
    return 1 if bad else 0


if __name__ == '__main__':
    sys.exit(main())
