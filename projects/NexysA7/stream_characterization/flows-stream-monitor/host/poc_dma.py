#!/usr/bin/env python3
"""R5 -- on-silicon DMA -> monbus -> tally sweep, the end-to-end coverage routine.

Reuses the proven flows-stream-bridge/host primitives (build_stream_bus for the
DMA, mon_configs for the monitor cones) and adds the monitor-flow's dense-bin
sweep. This is the routine the 34-min monitors-on cosim was too slow to finish;
on real-time UART it runs in seconds.

Flow: enable monitor cones -> run a small DMA on ch0 -> wait idle -> sweep the
stream tally's dense bins + UNEXPECTED. A non-zero total proves the
monbus -> tally path is live on silicon (which tuples land where is then refined
by loading a matching profile legal set -- the testplan sequence work).

Usage:  source env_python && python3 poc_dma.py [--port /dev/ttyUSB2] [--config debug-compl]
"""
import os
import sys
import time
import argparse

_REPO = os.environ.get("REPO_ROOT") or os.path.abspath(
    os.path.join(os.path.dirname(__file__), *[".."] * 5))
_BRIDGE_HOST = os.path.join(
    _REPO, "projects/NexysA7/stream_characterization/flows-stream-bridge/host")
sys.path.insert(0, os.path.join(_REPO, "projects/components/converters/bin"))
sys.path.insert(0, _BRIDGE_HOST)
from uart_axi_bridge import UARTAxiBridge          # noqa: E402
from stream_device import build_stream_bus, STREAM_APB_BASE  # noqa: E402
import mon_configs                                 # noqa: E402

STREAM_TALLY_CFG = 0x0010_0000
N_PROFILE        = 64                    # dense bins 0..63 + UNEXPECTED at 64


def main(argv=None):
    ap = argparse.ArgumentParser()
    ap.add_argument("--port", default=os.environ.get("MON_UART", "/dev/ttyUSB2"))
    ap.add_argument("--config", default="debug-compl",
                    help="mon_configs preset (perf-mon/debug-basic/debug-compl/debug-all/debug-core)")
    ap.add_argument("--channel", type=int, default=0)
    ap.add_argument("--bytes", type=int, default=4096)
    a = ap.parse_args(argv)
    print(f"[poc_dma] UART {a.port} @ 115200, mon='{a.config}', "
          f"ch{a.channel}, {a.bytes} B")

    bridge = UARTAxiBridge(port=a.port)
    bus = build_stream_bus(bridge)
    stream = bus["stream"]

    # 1) enable the monitor cones (mon_configs addresses are STREAM-APB-relative)
    cfg = mon_configs.get(a.config)
    cfg.apply(lambda addr, val: bridge.write(STREAM_APB_BASE + addr, val))
    print(f"  monitors: applied '{cfg.name}' ({', '.join(cfg.cones)})")

    # 2) program + kick a small legacy DMA
    kick_addr = stream.load_chain(a.channel, num_descriptors=1, transfer_bytes=a.bytes)
    stream.run(a.channel, kick_addr)
    print(f"  DMA kicked (kick_addr=0x{kick_addr:08X}); waiting for idle...")

    # 3) poll completion
    t0 = time.time()
    done = False
    while time.time() - t0 < 10.0:
        if stream.channel_idle(a.channel):
            done = True
            break
        time.sleep(0.05)
    print(f"  channel {'IDLE (done)' if done else 'STILL BUSY (timeout)'} "
          f"after {time.time()-t0:.2f}s")

    # 4) sweep the dense bins + UNEXPECTED
    total = 0
    nonzero = []
    for bn in range(N_PROFILE + 1):
        v = bridge.read(STREAM_TALLY_CFG + bn * 4) or 0
        total += v
        if v:
            nonzero.append((bn, v))
    print(f"  tally sweep: total={total} packets across {len(nonzero)} bin(s)")
    for bn, v in nonzero:
        tag = " (UNEXPECTED)" if bn == N_PROFILE else ""
        print(f"    bin[{bn}]{tag} = {v}")

    ok = total > 0
    print(f"\n=== R5 {'PASS' if ok else 'FAIL'}: "
          f"{'monbus->tally path live on silicon' if ok else 'no packets counted'} ===")
    try:
        bridge.ser.close()
    except Exception:
        pass
    return 0 if ok else 1


if __name__ == "__main__":
    sys.exit(main())
