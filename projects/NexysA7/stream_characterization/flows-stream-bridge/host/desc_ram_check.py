#!/usr/bin/env python3
# SPDX-License-Identifier: MIT
# SPDX-FileCopyrightText: 2026 sean galloway
#
# desc_ram_check.py — unified descriptor-RAM readback / compare tool.
#
# Always: rebuild the expected (golden) descriptor chain from the CLI
# config, read every word back from desc_ram via UART, and diff. Use
# one of the following modes to control what happens before the read:
#
#   1. Read-only (default).
#        python3 desc_ram_check.py
#      Use after some other run has loaded desc_ram (e.g. a manual
#      run_characterization or a previous --kick session that hung).
#      No FPGA reprogram, no writes. Just reads current SRAM contents
#      and compares against the golden chain for the given config.
#
#   2. Preload only.
#        python3 desc_ram_check.py --write
#      (Re)programs the FPGA (unless --no-program), soft-resets the
#      unit, writes the chain, then reads back and diffs. Equivalent to
#      a write/read round-trip sanity check.
#
#   3. Preload + kick + wait + read.
#        python3 desc_ram_check.py --write --kick
#      Reprograms, writes the chain, configures STREAM, fires the kick
#      burst, waits up to --timeout seconds for TIMER_STATUS.done or
#      CSR_STATUS.any_error, then reads back and diffs. Used to
#      detect whether STREAM or another master writes into desc_ram
#      during the run.
#
# Other useful flags:
#   --no-program     skip make program (e.g. board already in a clean state)
#   --golden-only    print the golden chain, don't touch the FPGA
#   --json OUT.json  save golden + readback to JSON for offline review

import argparse
import json
import os
import subprocess
import sys
import time

sys.path.insert(0, os.path.dirname(__file__))
sys.path.insert(0,
    '/mnt/data/github/RTLDesignSherpa/projects/components/converters/bin')

from descriptor_builder import DescriptorBuilder, CharConfig
from uart_axi_bridge import UARTAxiBridge

# ---------------------------------------------------------------------------
# Address constants (mirror host/run_characterization.py)
# ---------------------------------------------------------------------------
HARNESS_CSR_BASE    = 0x0001_0000
STREAM_APB_BASE     = 0x0000_0000

CSR_CTRL            = HARNESS_CSR_BASE + 0x00
CSR_STATUS          = HARNESS_CSR_BASE + 0x04
CSR_BUILD_ID        = HARNESS_CSR_BASE + 0x24
CSR_TIMER_CTRL      = HARNESS_CSR_BASE + 0x28
CSR_TIMER_STATUS    = HARNESS_CSR_BASE + 0x2C
CSR_TIMER_EXPECTED  = HARNESS_CSR_BASE + 0x38
CSR_KICK_GO         = HARNESS_CSR_BASE + 0xC0

EXPECTED_BUILD_ID   = 0x5354_5243   # "STRC"

# Desc_ram observation counters (offsets within harness_csr).
# Free-running, only cleared by CSR_CTRL[1] clear_stats pulse — they
# survive soft reset, so they give a snapshot of the wedge at the
# moment STREAM stopped issuing.
OBS_REGS = [
    ('DESC_SRAM_AR_HS',  0xD4),  # AXIL AR handshakes at SRAM port
    ('DESC_SRAM_R_HS',   0xD8),  # AXIL R handshakes at SRAM port
    ('DESC_AR_HS',       0xE0),  # 256b AR at STREAM m_axi_desc
    ('DESC_AR_STALL',    0xE4),
    ('DESC_R_HS',        0xE8),  # 256b R at STREAM m_axi_desc
    ('DESC_R_STALL',     0xEC),
    ('DESC_AW_HS',       0xF0),  # host AXIL AW at SRAM port
    ('DESC_W_HS',        0xF4),
    ('DESC_B_HS',        0xF8),
    ('DESC_VR_LIVE',     0xFC),  # live 16b snapshot (see harness.sv comment)
]

# DESC_VR_LIVE bit layout (matches harness_csr / stream_char_harness).
DESC_VR_BITS = [
    's2_awvalid',  's2_awready',
    's2_wvalid',   's2_wready',
    's2_bvalid',   's2_bready',
    's2_arvalid',  's2_arready',
    's2_rvalid',   's2_rready',
    'desc_arvalid','desc_arready',
    'desc_rvalid', 'desc_rready',
]


def kick_addr_csr(ch: int) -> int:
    if ch < 4:
        return HARNESS_CSR_BASE + 0xB0 + 4 * ch
    return HARNESS_CSR_BASE + 0xC4 + 4 * (ch - 4)


APB_GLOBAL_CTRL     = STREAM_APB_BASE + 0x100
APB_CHANNEL_ENABLE  = STREAM_APB_BASE + 0x120
APB_SCHED_TIMEOUT   = STREAM_APB_BASE + 0x200
APB_SCHED_CONFIG    = STREAM_APB_BASE + 0x204
APB_DESCENG_CONFIG  = STREAM_APB_BASE + 0x220
APB_DESCENG_AD0_B   = STREAM_APB_BASE + 0x224
APB_DESCENG_AD0_L   = STREAM_APB_BASE + 0x228
APB_AXI_XFER_CONFIG = STREAM_APB_BASE + 0x2A0


# ---------------------------------------------------------------------------
# Helpers
# ---------------------------------------------------------------------------
def reprogram_fpga():
    flow_root = os.path.abspath(os.path.join(os.path.dirname(__file__), '..'))
    print(f"[reset] Reprogramming FPGA via Vivado batch (~30s)...")
    r = subprocess.run(['make', 'program'], cwd=flow_root, capture_output=True)
    if r.returncode != 0:
        print(r.stdout.decode()[-1200:])
        print(r.stderr.decode()[-1200:])
        raise SystemExit("make program failed")
    print("[reset] Reprogram done.")


def build_golden(args):
    """Return (writes, kicks, label)."""
    builder = DescriptorBuilder(data_width=args.data_width)
    cfg = CharConfig(
        name=f"{args.descriptors}desc_{args.channels}ch_{args.transfer_bytes // 1024}KB",
        num_channels=args.channels,
        descriptors_per_channel=args.descriptors,
        transfer_bytes=args.transfer_bytes,
    )
    td = builder.build_test(cfg)
    return td['descriptor_writes'], td['kick_addresses'], cfg.name


def write_chain(bridge, writes, label='preload'):
    print(f"[{label}] writing {len(writes)} descriptor words ...")
    for i, (addr, data) in enumerate(writes):
        if not bridge.write(addr, data):
            print(f"  WR FAIL @ idx={i} addr=0x{addr:08X} data=0x{data:08X}")
            raise SystemExit(2)
        if i and (i % 256 == 0):
            print(f"    {i}/{len(writes)}")
    print(f"[{label}] done.")


def configure_and_kick(bridge, args, kicks):
    print("[config] STREAM ...")
    bridge.write(APB_SCHED_CONFIG,     0x0F)
    bridge.write(APB_SCHED_TIMEOUT,    0xFFFFFFFF)
    bridge.write(APB_DESCENG_CONFIG,   0x01)
    bridge.write(APB_DESCENG_AD0_B,    0x00000000)
    bridge.write(APB_DESCENG_AD0_L,    0xFFFFFFFF)
    bridge.write(APB_AXI_XFER_CONFIG,
                 (15 & 0xFF) | ((15 & 0xFF) << 8))
    ch_mask = (1 << args.channels) - 1
    bridge.write(APB_GLOBAL_CTRL,      0x01)
    bridge.write(APB_CHANNEL_ENABLE,   ch_mask)

    bytes_per_beat = args.data_width // 8
    expected_beats = (args.transfer_bytes * args.channels *
                      args.descriptors) // bytes_per_beat
    bridge.write(CSR_TIMER_CTRL,       0x1)
    bridge.write(CSR_TIMER_EXPECTED,   expected_beats)
    print(f"[config] timer expected_beats={expected_beats}")

    print("[kick] burst ...")
    mask = 0
    for ch, addr in sorted(kicks.items()):
        bridge.write(kick_addr_csr(ch), addr & 0xFFFFFFFF)
        mask |= (1 << ch)
    bridge.write(CSR_KICK_GO, mask)
    print(f"[kick] mask=0x{mask:02X}")


def wait_for_done(bridge, deadline_s):
    deadline = time.time() + deadline_s
    result = 'timeout'
    while time.time() < deadline:
        ts = bridge.read(CSR_TIMER_STATUS) or 0
        st = bridge.read(CSR_STATUS) or 0
        if ts & 0x01:
            result = 'done'
            break
        if st & 0x02:
            result = 'any_error'
            break
        time.sleep(0.5)
    ts = bridge.read(CSR_TIMER_STATUS) or 0
    st = bridge.read(CSR_STATUS) or 0
    print(f"[wait] result={result}  timer_status=0x{ts:08X}  status=0x{st:08X}")
    return result, ts, st


def soft_reset_and_probe(bridge, attempts=3, ping_settle_s=0.1):
    """Pulse CSR_CTRL[3] (soft_reset_pulse) to release the harness-level
    aresetn, then probe CSR_BUILD_ID to confirm the bus is alive again.

    Returns True if a BUILD_ID read of EXPECTED_BUILD_ID came back at
    least once. SRAM contents (BRAM) survive aresetn, so this recovers
    the bus without wiping the descriptors we want to inspect."""
    for i in range(attempts):
        print(f"[recover] CSR_CTRL[3] soft-reset pulse "
              f"(attempt {i+1}/{attempts}) ...")
        bridge.write(CSR_CTRL, 0x08)
        time.sleep(ping_settle_s)
        # Drain any stale serial chatter before probing.
        try:
            bridge.ser.reset_input_buffer()
        except AttributeError:
            pass
        bid = bridge.read(CSR_BUILD_ID)
        if bid == EXPECTED_BUILD_ID:
            print(f"[recover] bus alive (BUILD_ID=0x{bid:08X}).")
            return True
        print(f"[recover] BUILD_ID read returned {bid!r} (want "
              f"0x{EXPECTED_BUILD_ID:08X}).")
        time.sleep(0.2)
    return False


def dump_obs(bridge):
    """Read the desc_ram observation counters + live snapshot. The
    counters are free-running and survive a soft reset, so they hold
    the wedge-time state of all valid/ready pairs across the descriptor
    path: bridge port (s2_*), STREAM m_axi_desc, host writes."""
    print("[obs] desc_ram observation counters:")
    snap = None
    for name, off in OBS_REGS:
        val = bridge.read(HARNESS_CSR_BASE + off)
        if val is None:
            print(f"    {name:<16} = READ_FAIL")
            continue
        print(f"    {name:<16} = 0x{val:08X}  ({val})")
        if name == 'DESC_VR_LIVE':
            snap = val
    if snap is not None:
        print("[obs] DESC_VR_LIVE decoded:")
        for i, bit_name in enumerate(DESC_VR_BITS):
            print(f"    [{i:>2}] {bit_name:<14} = {(snap >> i) & 1}")


def read_chain(bridge, addrs, label='readback'):
    print(f"[{label}] {len(addrs)} words ...")
    out = {}
    for i, addr in enumerate(addrs):
        out[addr] = bridge.read(addr)
        if i and (i % 256 == 0):
            print(f"    {i}/{len(addrs)}")
    print(f"[{label}] done.")
    return out


def diff_report(writes, readbacks):
    mismatches = []
    for addr, expected in writes:
        got = readbacks.get(addr)
        if got != expected:
            mismatches.append((addr, expected, got))
    return mismatches


def print_diff(golden_writes, mismatches):
    if not mismatches:
        print("\n" + "=" * 72)
        print(f"CLEAN: all {len(golden_writes)} descriptor words match.")
        print("       desc_ram contents == golden chain.")
        return 0

    golden_map = dict(golden_writes)
    print("\n" + "=" * 72)
    print(f"DIRTY: {len(mismatches)} / {len(golden_writes)} mismatched words.")
    print("=" * 72)

    by_desc = {}
    for addr, exp, got in mismatches:
        base = addr & ~0x1F
        by_desc.setdefault(base, []).append((addr, exp, got))

    for base in sorted(by_desc.keys()):
        rows = by_desc[base]
        ctrl_addr = base + 0x18
        ctrl = golden_map.get(ctrl_addr)
        ch   = (ctrl >> 4) & 0xF if ctrl is not None else '?'
        print(f"\n--- desc @ 0x{base:08X} (channel {ch}) — "
              f"{len(rows)} word(s) modified ---")
        for addr, exp, got in rows:
            word_idx = (addr & 0x1F) >> 2
            got_str = f"0x{got:08X}" if got is not None else "READ_FAIL"
            xor_str = (f"0x{exp ^ got:08X}"
                       if got is not None else "n/a")
            print(f"    word[{word_idx}] @ 0x{addr:08X}  "
                  f"expected 0x{exp:08X}  got {got_str}  xor {xor_str}")
    return 1


# ---------------------------------------------------------------------------
# Main
# ---------------------------------------------------------------------------
def main():
    p = argparse.ArgumentParser(formatter_class=argparse.RawDescriptionHelpFormatter,
                                 description=__doc__)
    p.add_argument('--port',           default='/dev/ttyUSB2')
    p.add_argument('--baud',           type=int, default=115200)
    p.add_argument('--channels',       type=int, default=7)
    p.add_argument('--descriptors',    type=int, default=16)
    p.add_argument('--transfer-bytes', type=int, default=1024 * 1024)
    p.add_argument('--data-width',     type=int, default=128)

    p.add_argument('--write',  action='store_true',
                   help='preload desc_ram with the golden chain before reading back')
    p.add_argument('--kick',   action='store_true',
                   help='after --write, configure STREAM and fire the kick; '
                        'implies --write')
    p.add_argument('--no-program', action='store_true',
                   help='skip "make program" (default is to reprogram '
                        'before --write)')
    p.add_argument('--timeout',     type=float, default=120.0,
                   help='seconds to wait for timer.done when --kick is set')
    p.add_argument('--recover',    action='store_true',
                   help='after --kick, pulse CSR_CTRL[3] soft_reset (and '
                        'probe BUILD_ID) before the readback. Bridge/'
                        'STREAM logic resets, SRAM contents (BRAMs) '
                        'survive — lets the readback succeed after a '
                        'STREAM wedge.')
    p.add_argument('--no-readback', action='store_true',
                   help='skip the per-word desc_ram readback. Useful '
                        'after a wedge where reads of the SRAM time out '
                        'but the obs counters in harness_csr are still '
                        'reachable.')

    p.add_argument('--golden-only', action='store_true',
                   help='just print the golden chain summary and exit')
    p.add_argument('--json',
                   help='save golden + readback to JSON for offline review')

    args = p.parse_args()
    if args.kick:
        args.write = True   # kick needs a preload

    writes, kicks, label = build_golden(args)

    print(f"Config: {label}")
    print(f"  channels       = {args.channels}")
    print(f"  desc/channel   = {args.descriptors}")
    print(f"  bytes/desc     = {args.transfer_bytes} "
          f"({args.transfer_bytes // 1024} KB)")
    print(f"  data_width     = {args.data_width} bits")
    print(f"  total writes   = {len(writes)} 32-bit words")
    print(f"  total descs    = {args.channels * args.descriptors}")

    if args.golden_only:
        return 0

    if args.write and not args.no_program:
        reprogram_fpga()

    readbacks = {}
    with UARTAxiBridge(args.port, args.baud) as bridge:
        if args.write:
            # Soft reset + clear stats before preload.
            bridge.write(CSR_CTRL, 0x08)
            time.sleep(0.01)
            bridge.write(CSR_CTRL, 0x02)
            time.sleep(0.01)
            write_chain(bridge, writes)

        if args.kick:
            configure_and_kick(bridge, args, kicks)
            wait_for_done(bridge, args.timeout)
            if args.recover:
                if not soft_reset_and_probe(bridge):
                    print("[recover] Soft reset did NOT bring the bus back.")
                    print("[recover] Cannot read desc_ram without a hard")
                    print("[recover] reprogram, which would wipe the BRAM.")
                    print("[recover] Aborting before readback.")
                    sys.exit(3)
                # Counters survive soft reset (gated on aresetn, not on
                # clear_stats unless CTRL[1] is pulsed) — they're a free
                # snapshot of what STREAM and the bridge actually did
                # before the wedge, even when the desc_ram path itself
                # is dead.
                dump_obs(bridge)

        if args.no_readback:
            print("[readback] skipped (--no-readback).")
            sys.exit(0)

        readbacks = read_chain(bridge, [a for a, _ in writes])

    mismatches = diff_report(writes, readbacks)

    if args.json:
        with open(args.json, 'w') as fh:
            json.dump({
                'config': label,
                'channels': args.channels,
                'descriptors': args.descriptors,
                'transfer_bytes': args.transfer_bytes,
                'data_width': args.data_width,
                'mode': {
                    'wrote': args.write,
                    'kicked': args.kick,
                    'programmed': args.write and not args.no_program,
                },
                'golden':    [(a, w) for a, w in writes],
                'readbacks': [(a, readbacks.get(a)) for a, _ in writes],
                'mismatches': mismatches,
            }, fh, indent=2)
        print(f"[json] {args.json}")

    rc = print_diff(writes, mismatches)
    sys.exit(rc)


if __name__ == '__main__':
    main()
