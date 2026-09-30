#!/usr/bin/env python3
# SPDX-License-Identifier: MIT
# SPDX-FileCopyrightText: 2026 sean galloway
"""Parse the Vivado post-route reports of one RAPIDS build into a small JSON that
make_byte_perf_report.py reads for its build-and-resources section.

  extract_build_metrics.py --reports-dir <dir> --bitstream <bit> --tag <name>
        --config "BYTE_CRC=1 USE_OBSERVERS=1 ..." [--commit <sha>] --out <json>

<dir> holds utilization_impl.txt and timing_summary.txt as written by the
flow. Every number is parsed from those files; none is typed in.
"""
import argparse
import hashlib
import json
import os
import re
import sys


def _cell(text, name):
    m = re.search(r'^\|\s*' + re.escape(name) + r'\s*\|\s*(\d+)\s*\|', text, re.M)
    return int(m.group(1)) if m else None


def parse_util(path):
    t = open(path).read()
    return {'slice_luts': _cell(t, 'Slice LUTs'), 'lut_logic': _cell(t, 'LUT as Logic'),
            'lut_dist_ram': _cell(t, 'LUT as Distributed RAM'),
            'slice_regs': _cell(t, 'Slice Registers'), 'bram_tiles': _cell(t, 'Block RAM Tile'),
            'dsp': _cell(t, 'DSPs')}


def parse_timing(path):
    lines = open(path).read().splitlines()
    for i, ln in enumerate(lines):
        if ln.strip().startswith('WNS(ns)'):
            v = lines[i + 2].split()
            return {'wns_ns': float(v[0]), 'tns_ns': float(v[1]), 'tns_failing': int(v[2]),
                    'endpoints': int(v[3]), 'whs_ns': float(v[4]), 'ths_failing': int(v[6])}
    raise SystemExit(f"no Design Timing Summary row in {path}")


def main():
    ap = argparse.ArgumentParser(description=__doc__.splitlines()[0])
    ap.add_argument('--reports-dir', required=True)
    ap.add_argument('--bitstream', required=True)
    ap.add_argument('--tag', required=True)
    ap.add_argument('--config', required=True)
    ap.add_argument('--commit', default=None)
    ap.add_argument('--out', required=True)
    a = ap.parse_args()
    sha = hashlib.sha256(open(a.bitstream, 'rb').read()).hexdigest()
    doc = {'tag': a.tag, 'config': a.config, 'commit': a.commit,
           'bitstream': os.path.basename(a.bitstream), 'bitstream_sha256': sha,
           'util': parse_util(os.path.join(a.reports_dir, 'utilization_impl.txt')),
           'timing': parse_timing(os.path.join(a.reports_dir, 'timing_summary.txt'))}
    with open(a.out, 'w') as fh:
        json.dump(doc, fh, indent=2)
        fh.write('\n')
    print(f"wrote {a.out}: LUT {doc['util']['slice_luts']} BRAM {doc['util']['bram_tiles']} "
          f"WNS {doc['timing']['wns_ns']:+.3f} sha {sha[:16]}")


if __name__ == '__main__':
    sys.exit(main())
