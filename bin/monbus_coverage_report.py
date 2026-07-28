#!/usr/bin/env python3
# SPDX-License-Identifier: MIT
# SPDX-FileCopyrightText: 2024-2026 sean galloway
#
# RTL Design Sherpa - Industry-Standard RTL Design and Verification
# https://github.com/sean-galloway/RTLDesignSherpa
#
# Module: monbus_coverage_report
# Purpose: Aggregate monbus packet-type coverage and diff against the enum space
# Subsystem: tooling
"""Packet-type coverage matrix: which (protocol, pkt_type, event_code) tuples
have actually been OBSERVED being emitted in pre-si, vs everything defined.

This is the sign-off artifact for the board-validation gate ("test all the
different types and make sure they happen" -- see
vault/handbook/fpga/monitor-board-coverage.md).
The NONE rows are the work list: each either gets a provoking test or a
documented unreachable/reserved rationale.

Collection:
    MONBUS_COVERAGE=1 pytest val/amba/ ...        # hook in MonbusSlave records
    # tuples land in /tmp/monbus_coverage/coverage.jsonl (MONBUS_COVERAGE_FILE
    # overrides). Delete the file first for a clean collection run.

Report:
    python3 bin/monbus_coverage_report.py [coverage.jsonl ...]
    python3 bin/monbus_coverage_report.py --markdown coverage_matrix.md

Ground truth is imported from TBClasses.monbus.monbus_types (the Python mirror
of the SV monitor packages) -- no SystemVerilog parsing. The per-protocol
packet-type -> enum-class mapping below is the same one monbus_validators uses.
"""

import argparse
import json
import os
import sys
from collections import defaultdict

sys.path.insert(0, os.path.join(os.path.dirname(os.path.dirname(
    os.path.abspath(__file__))), 'bin'))

from TBClasses.monbus.monbus_types import (          # noqa: E402
    ProtocolType, PktType,
    AXIErrorCode, AXITimeoutCode, AXICompletionCode, AXIThresholdCode,
    AXIPerformanceCode, AXIAddrMatchCode, AXIDebugCode,
    APBErrorCode, APBTimeoutCode, APBCompletionCode, APBThresholdCode,
    APBPerformanceCode,
    ARBErrorCode, ARBTimeoutCode, ARBCompletionCode, ARBThresholdCode,
    ARBPerformanceCode, ARBDebugCode,
)

# (protocol, pkt_type) -> event-code enum class. Tuples not listed here have
# no defined event-code space (reserved packet types) and are reported only
# if OBSERVED (which would itself be a finding).
ENUM_MAP = {
    (ProtocolType.PROTOCOL_AXI, PktType.PktTypeError):       AXIErrorCode,
    (ProtocolType.PROTOCOL_AXI, PktType.PktTypeTimeout):     AXITimeoutCode,
    (ProtocolType.PROTOCOL_AXI, PktType.PktTypeCompletion):  AXICompletionCode,
    (ProtocolType.PROTOCOL_AXI, PktType.PktTypeThreshold):   AXIThresholdCode,
    (ProtocolType.PROTOCOL_AXI, PktType.PktTypePerf):        AXIPerformanceCode,
    (ProtocolType.PROTOCOL_AXI, PktType.PktTypeAddrMatch):  AXIAddrMatchCode,
    (ProtocolType.PROTOCOL_AXI, PktType.PktTypeDebug):       AXIDebugCode,
    (ProtocolType.PROTOCOL_APB, PktType.PktTypeError):       APBErrorCode,
    (ProtocolType.PROTOCOL_APB, PktType.PktTypeTimeout):     APBTimeoutCode,
    (ProtocolType.PROTOCOL_APB, PktType.PktTypeCompletion):  APBCompletionCode,
    (ProtocolType.PROTOCOL_APB, PktType.PktTypeThreshold):   APBThresholdCode,
    (ProtocolType.PROTOCOL_APB, PktType.PktTypePerf):        APBPerformanceCode,
    (ProtocolType.PROTOCOL_ARB, PktType.PktTypeError):       ARBErrorCode,
    (ProtocolType.PROTOCOL_ARB, PktType.PktTypeTimeout):     ARBTimeoutCode,
    (ProtocolType.PROTOCOL_ARB, PktType.PktTypeCompletion):  ARBCompletionCode,
    (ProtocolType.PROTOCOL_ARB, PktType.PktTypeThreshold):   ARBThresholdCode,
    (ProtocolType.PROTOCOL_ARB, PktType.PktTypePerf):        ARBPerformanceCode,
    (ProtocolType.PROTOCOL_ARB, PktType.PktTypeDebug):       ARBDebugCode,
}


def load_observations(paths):
    """observed[(proto, ptype, code)] -> set of test names"""
    observed = defaultdict(set)
    for path in paths:
        if not os.path.exists(path):
            print(f"WARNING: no such file: {path}", file=sys.stderr)
            continue
        with open(path) as f:
            for line in f:
                line = line.strip()
                if not line:
                    continue
                try:
                    rec = json.loads(line)
                except json.JSONDecodeError:
                    print(f"WARNING: bad JSONL line skipped in {path}",
                          file=sys.stderr)
                    continue
                test = rec.get('test', 'unknown').split(' ')[0]
                for proto, ptype, code in rec.get('tuples', []):
                    observed[(proto, ptype, code)].add(test)
    return observed


def build_matrix(observed):
    rows = []          # (proto_name, ptype_name, code_name, code, tests)
    covered = missing = reserved = 0
    for (proto, ptype), enum_cls in sorted(ENUM_MAP.items()):
        for member in enum_cls:
            # Enum classes pad to 16 entries with RESERVED-named members;
            # those are not real event codes and belong in a separate bucket
            # (an OBSERVED reserved code is a finding, an unobserved one is
            # not a coverage gap). 117 of 288 members are padding.
            is_reserved = 'RESERVED' in member.name or 'RSVD' in member.name
            tests = observed.get((int(proto), int(ptype), int(member)), set())
            if is_reserved and not tests:
                reserved += 1
                continue
            rows.append((proto.name.replace('PROTOCOL_',''),
                         ptype.name.replace('PktType',''), member.name,
                         int(member), sorted(tests)))
            if tests:
                covered += 1
            else:
                missing += 1
    # observations outside the defined space are findings in themselves
    defined = {(int(p), int(t), int(m))
               for (p, t), cls in ENUM_MAP.items() for m in cls}
    stray = {k: v for k, v in observed.items() if k not in defined}
    return rows, covered, missing, stray, reserved


def main():
    ap = argparse.ArgumentParser(description=__doc__)
    ap.add_argument('jsonl', nargs='*',
                    default=['/tmp/monbus_coverage/coverage.jsonl'])
    ap.add_argument('--markdown', metavar='FILE',
                    help='also write the matrix as a markdown table')
    ap.add_argument('--none-only', action='store_true',
                    help='print only the uncovered rows (the work list)')
    args = ap.parse_args()

    observed = load_observations(args.jsonl)
    rows, covered, missing, stray, reserved = build_matrix(observed)

    total = covered + missing
    print(f"packet-type coverage: {covered}/{total} REAL tuples observed "
          f"({missing} NONE; {reserved} reserved-named members excluded)")
    print()
    width = max(len(r[2]) for r in rows) + 2
    for proto, ptype, code_name, code, tests in rows:
        if args.none_only and tests:
            continue
        status = ','.join(tests[:2]) + ('...' if len(tests) > 2 else '') \
            if tests else 'NONE'
        print(f"  {proto:<4} {ptype:<11} {code_name:<{width}} "
              f"0x{code:02X}  {status}")

    if stray:
        print(f"\nSTRAY observations outside the defined enum space "
              f"({len(stray)}) -- these are findings:")
        for (p, t, c), tests in sorted(stray.items()):
            print(f"  proto={p} type={t} code=0x{c:02X}  "
                  f"{','.join(sorted(tests)[:3])}")

    if args.markdown:
        with open(args.markdown, 'w') as f:
            f.write("# Monbus packet-type coverage matrix\n\n")
            f.write(f"Observed {covered}/{total} defined tuples "
                    f"({missing} NONE).\n\n")
            f.write("| Protocol | Packet type | Event code | Value | "
                    "Emitting test(s) |\n|---|---|---|---|---|\n")
            for proto, ptype, code_name, code, tests in rows:
                cell = '<br>'.join(tests[:4]) if tests else '**NONE**'
                f.write(f"| {proto} | {ptype} | {code_name} | 0x{code:02X} "
                        f"| {cell} |\n")
        print(f"\nmarkdown matrix written: {args.markdown}")

    return 1 if missing else 0


if __name__ == '__main__':
    sys.exit(main())
