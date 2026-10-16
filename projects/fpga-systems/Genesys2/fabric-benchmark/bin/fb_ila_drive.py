#!/usr/bin/env python3
# SPDX-License-Identifier: MIT
# SPDX-FileCopyrightText: 2026 sean galloway
"""Host half of fpga/tcl/capture_ila.tcl: one DDR3 fill then one drain.

Runs the first two steps of fb_workloads.CHAIN (W1-F2, W1-F1) at 1 channel
(default 2 descriptors x 64 KB, which stalls reliably) with a short timeout, and prints fb_ctl's S0
counters and live handshake bits after each. The ILA is already armed on the
drain's first S0 read; this program only has to make that read happen.
Not run on its own -- capture_ila.tcl holds the board lock and starts it.
"""
import argparse
import os
import sys

os.environ.setdefault('CHAR_POLL_TIMEOUT_S', '5')
import fb_map  # noqa: E402
import fb_workloads  # noqa: E402

LIVE = ('ARVALID', 'ARREADY', 'RVALID', 'RREADY', 'AWVALID', 'AWREADY',
        'WVALID', 'WREADY', 'BVALID', 'BREADY')
COUNTS = ('S0_AW_COUNT', 'S0_B_COUNT', 'S0_AR_COUNT', 'S0_RD_BEATS', 'S0_WR_BEATS',
          'S0_RVALID_CYCLES')


def snapshot(bridge) -> str:
    regs = fb_workloads._regs()['STATUS']
    st = bridge.read(fb_workloads.C('STATUS'))
    live = ' '.join(f"{n}={(st >> int(regs['S0_' + n]['offset'])) & 1}" for n in LIVE)
    cnt = ' '.join(f"{k}={bridge.read(fb_workloads.C(k))}" for k in COUNTS)
    return f"status=0x{st:X} {live} | {cnt}"


def main() -> int:
    ap = argparse.ArgumentParser(description=__doc__.splitlines()[0])
    ap.add_argument('--port', default='/dev/ttyUSB1')
    ap.add_argument('--baud', type=int, default=115200)
    ap.add_argument('--desc', type=int, default=2)
    ap.add_argument('--bytes', type=int, default=65536)
    args = ap.parse_args()
    fb_map.stream_host_path()
    from uart_axi_bridge import UARTAxiBridge
    from characterization import CharacterizationRunner
    from descriptor_builder import CharConfig
    cfg = CharConfig(name='ila', num_channels=1, descriptors_per_channel=args.desc,
                     transfer_bytes=args.bytes)
    with UARTAxiBridge(args.port, args.baud) as bridge:
        runner = CharacterizationRunner(bridge, data_width=fb_map.DATA_WIDTH,
                                        builder=fb_map.make_builder())
        runner.log = lambda m: None
        if not runner.ping():
            print("fb_ila_drive: ping failed")
            return 1
        for step, src, dst in fb_workloads.CHAIN[:2]:
            res = fb_workloads.run_step(runner, bridge, cfg, src, dst)
            print(f"{step}: error={res.get('error')} {snapshot(bridge)}", flush=True)
        fb_workloads.set_workload(bridge, False, False)
    return 0


if __name__ == '__main__':
    sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
    sys.exit(main())
