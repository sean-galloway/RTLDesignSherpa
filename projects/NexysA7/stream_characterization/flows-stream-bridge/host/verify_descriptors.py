#!/usr/bin/env python3
# SPDX-License-Identifier: MIT
# SPDX-FileCopyrightText: 2024-2026 sean galloway
#
# Module: verify_descriptors
# Purpose: Write a config's descriptor chain into desc_ram, then read every
#          word back over AXIL and compare against what we wrote. Rules out
#          desc_ram storage / write-path / read-path bit-rot as a cause of
#          STK:desc_err on the heavy multi-channel + long-chain configs.
#
# Requires: desc_ram.sv AXIL read side returning real data (not DECERR).
#           Bitstreams before this RTL change will all read 0xDEADDEAD with
#           DECERR — this script will report 100% mismatch in that case,
#           which IS the test for whether the AXIL read engine landed.
#
# Usage:
#   source env_python
#   python3 host/verify_descriptors.py --port /dev/ttyUSB2 --configs 16desc_7ch_1MB
#   python3 host/verify_descriptors.py --port /dev/ttyUSB2 --all   # full matrix
#
# Output: one line per failing word. Per-config summary line at the end with
#         total writes, total mismatches, and the first few diffs.

import argparse
import os
import sys
from pathlib import Path
from typing import Iterable, List, Tuple

# Match the existing host scripts' REPO_ROOT discovery.
_here = Path(__file__).resolve().parent
_repo_root = os.environ.get("REPO_ROOT")
if not _repo_root:
    cand = _here
    while cand != Path("/") and not (cand / ".git").is_dir():
        cand = cand.parent
    if (cand / ".git").is_dir():
        _repo_root = str(cand)
if not _repo_root:
    raise RuntimeError(
        "REPO_ROOT not set and not auto-discoverable. Source env_python first."
    )

sys.path.insert(0, str(_here))
sys.path.insert(0, os.path.join(_repo_root, "projects/components/converters/bin"))

from descriptor_builder import (                              # noqa: E402
    DescriptorBuilder,
    CharConfig,
    build_char_matrix,
    CTRL_VALID,
    _W_CONTROL,
)
from uart_axi_bridge import UARTAxiBridge                     # noqa: E402


# -----------------------------------------------------------------
# Core verifier
# -----------------------------------------------------------------

def _writes_to_desc_groups(
    writes: List[Tuple[int, int]],
) -> dict:
    """Group writes by 32-byte descriptor index. Returns
       {desc_idx: {word_idx (0..7): expected_data}}."""
    groups: dict = {}
    for addr, data in writes:
        idx = addr >> 5
        wi = (addr & 0x1F) >> 2
        groups.setdefault(idx, {})[wi] = data
    return groups


def verify_one_config(
    bridge: UARTAxiBridge,
    builder: DescriptorBuilder,
    cfg: CharConfig,
    verbose: bool = False,
    max_diffs_to_print: int = 16,
) -> Tuple[int, int, List[Tuple[int, int, int]]]:
    """Build cfg's descriptor chain, write it, read every word back, and
       diff. Returns (total_words, mismatches, [(addr, exp, got), ...])."""

    test = builder.build_test(cfg)
    writes = test["descriptor_writes"]

    # --- write phase ---
    for addr, data in writes:
        ok = bridge.write(addr, data)
        if not ok:
            print(f"[{cfg.name}] WRITE FAIL at 0x{addr:08X}")
            return (len(writes), len(writes), [])

    # --- read phase ---
    diffs: List[Tuple[int, int, int]] = []
    printed = 0
    for addr, expected in writes:
        got = bridge.read(addr)
        if got is None:
            diffs.append((addr, expected, -1))
            if printed < max_diffs_to_print:
                print(f"[{cfg.name}] READ FAIL at 0x{addr:08X}")
                printed += 1
            continue
        if got != expected:
            diffs.append((addr, expected, got))
            if printed < max_diffs_to_print:
                print(
                    f"[{cfg.name}] DIFF 0x{addr:08X}: "
                    f"exp=0x{expected:08X}  got=0x{got:08X}  "
                    f"xor=0x{expected ^ got:08X}"
                )
                printed += 1

    return (len(writes), len(diffs), diffs)


def _decode_descriptor_words(words: dict, fmt_indent: str = "    ") -> str:
    """Render a per-descriptor view of 8 words for log output."""
    lines = []
    src = words.get(0, 0) | (words.get(1, 0) << 32)
    dst = words.get(2, 0) | (words.get(3, 0) << 32)
    beats = words.get(4, 0)
    nxt   = words.get(5, 0)
    ctrl  = words.get(6, 0)
    rsv   = words.get(7, 0)
    valid = bool(ctrl & CTRL_VALID)
    lines.append(
        f"{fmt_indent}src=0x{src:016X} dst=0x{dst:016X} beats={beats} "
        f"next=0x{nxt:08X} ctrl=0x{ctrl:08X} (VALID={int(valid)}) rsv=0x{rsv:08X}"
    )
    return "\n".join(lines)


# -----------------------------------------------------------------
# Main
# -----------------------------------------------------------------

def main() -> int:
    ap = argparse.ArgumentParser(description=__doc__)
    ap.add_argument("--port", default="/dev/ttyUSB2")
    ap.add_argument("--baud", type=int, default=115200)
    ap.add_argument(
        "--configs",
        nargs="+",
        default=["16desc_7ch_1MB"],
        help="Config names to verify (default: 16desc_7ch_1MB). Use --all to "
             "sweep the full 40-config matrix.",
    )
    ap.add_argument("--all", action="store_true",
                    help="Sweep every config in build_char_matrix().")
    ap.add_argument("--transfer-bytes", type=int, default=1024 * 1024)
    ap.add_argument("--verbose", "-v", action="store_true")
    args = ap.parse_args()

    matrix = build_char_matrix(transfer_bytes=args.transfer_bytes)
    by_name = {c.name: c for c in matrix}

    if args.all:
        cfgs: Iterable[CharConfig] = matrix
    else:
        cfgs = []
        for name in args.configs:
            if name not in by_name:
                print(f"Unknown config: {name}")
                print(f"Available: {', '.join(sorted(by_name))[:80]}...")
                return 2
            cfgs.append(by_name[name])

    builder = DescriptorBuilder()

    total_pass = 0
    total_fail = 0
    with UARTAxiBridge(args.port, args.baud) as bridge:
        for cfg in cfgs:
            print(f"\n=== {cfg.name} "
                  f"({cfg.num_channels}ch x {cfg.descriptors_per_channel}desc) ===")
            n_words, n_diff, diffs = verify_one_config(
                bridge, builder, cfg, verbose=args.verbose,
            )
            verdict = "PASS" if n_diff == 0 else "FAIL"
            print(f"{verdict}  {cfg.name}: {n_diff}/{n_words} mismatches")
            if n_diff:
                # Show which descriptors look corrupted (first few)
                bad_desc_idx = sorted(
                    {(a >> 5) for (a, _, _) in diffs}
                )[:8]
                print(f"  affected desc indices: {bad_desc_idx}")
                total_fail += 1
            else:
                total_pass += 1

    print(f"\nSummary: {total_pass} pass, {total_fail} fail of "
          f"{total_pass + total_fail} configs")
    return 0 if total_fail == 0 else 1


if __name__ == "__main__":
    sys.exit(main())
