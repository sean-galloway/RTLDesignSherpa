# SPDX-License-Identifier: MIT
# SPDX-FileCopyrightText: 2026 sean galloway
"""Measure MonBus bulk-trace compression -- ONE program, cosim and board.

Route the in-core monbus group at the comp_sram capture memory, run a
monitors-on DMA through the board's own program (CharacterizationRunner
.run_config) with COMPRESS_EN set, read the ring back and decode it with the
reference model (TBClasses.monbus.monbus_compressor.Decoder, a bit-exact mirror
of the RTL encoder that evolves the same CAM state).

Reports slots-per-packet and the saving against the raw 3-beat encoding
({tag,timestamp}, packet[127:64], packet[63:0]). A capture that measures
exactly 3.00 slots/packet is UNCOMPRESSED whatever the enable bits say -- that
is how a hardcoded USE_MON_COMPRESSION(0) went unnoticed while this class of
test kept passing. Reference: 1.12 slots/packet (62.5%) in cosim, 1.01 (66.4%)
on the Genesys 2 mon bitstream.

Library + launcher (see the stream host-objects note): `test_stream_mon_compress`
imports `measure_compression` and drives it over the cosim bridge under
cocotb.external; build-mon/host/host_mon_compress.py is the CLI over pyserial.
"""
from __future__ import annotations

import argparse
import os
import sys
from typing import Callable, List

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import stream_env  # noqa: F401,E402  (path setup)
from characterization import CharacterizationRunner, CharConfig  # noqa: E402
from stream_monitors import BASIC_CLASSES, MonitorProgram, route_monbus  # noqa: E402
from TBClasses.monbus.monbus_compressor import Decoder  # noqa: E402

RAW_SLOTS_PER_PACKET = 3.0
CAPTURE_WINDOW = "comp_sram"


def read_capture(bridge, cap_base: int, max_slots: int) -> List[int]:
    """The head of the capture ring as 64-bit slots, stopping at the first
    empty slot. There is no group write-pointer register, and decoding
    trailing zeros would manufacture packets that were never emitted."""
    populated: List[int] = []
    for i in range(max_slots):
        lo = bridge.read(cap_base + 8 * i)
        hi = bridge.read(cap_base + 8 * i + 4)
        slot = ((0 if hi is None else hi) << 32) | (0 if lo is None else lo)
        if slot == 0:
            break
        populated.append(slot)
    return populated


def measure_compression(bridge, *, channel: int = 0, descriptors: int = 4,
                        xfer_bytes: int = 16384, max_slots: int = 4096,
                        log: Callable[[str], object] = print,
                        runner: CharacterizationRunner | None = None) -> dict:
    """Run the workload and decode the capture. Returns a dict with `ok`, and
    the figures (`populated`, `decoded`, `slots_per_pkt`, `saving_pct`) plus
    `reason` when not ok. Never raises on a hardware result -- the caller
    (CLI or cosim assertion) decides how loud to be."""
    runner = runner or CharacterizationRunner(bridge)
    runner.log = log
    # The cosim's constants: types 0-3 through the mask, compression ON. The
    # runner applies the program inside configure_stream (after its reset) and
    # sets WRMON_ENABLE.COMPRESS_EN last from its `compression` flag.
    runner.mon_config = MonitorProgram(BASIC_CLASSES, name="compress-basic", compress=True)
    runner.compression = True
    window = {}

    def pre_kick(br):
        window["base"], window["limit"] = route_monbus(br, CAPTURE_WINDOW)
        log(f"  capture window {CAPTURE_WINDOW} 0x{window['base']:06X}.."
            f"0x{window['limit']:06X}; COMPRESS_EN=1 on WRMON")

    cfg = CharConfig(name=f"mon_compress_{descriptors}x{xfer_bytes}",
                     num_channels=1, descriptors_per_channel=descriptors,
                     transfer_bytes=xfer_bytes, channels=[channel])
    res = runner.run_config(cfg, pre_kick=pre_kick)
    out = {"ok": False, "dma_pass": bool(res.get("pass")), "dma": res,
           "populated": 0, "decoded": 0, "slots_per_pkt": None, "saving_pct": None}
    if not out["dma_pass"]:
        out["reason"] = f"DMA did not pass ({res.get('error')}); capture is not meaningful"
        return out

    populated = read_capture(bridge, window["base"], max_slots)
    decoded = list(Decoder().decode(populated))
    out["populated"], out["decoded"] = len(populated), len(decoded)
    if not populated:
        out["reason"] = (f"capture is EMPTY at 0x{window['base']:06X}: nothing reached "
                         f"{CAPTURE_WINDOW} (routing lost, or nothing emitted)")
        return out
    if not decoded:
        out["reason"] = (f"{len(populated)} slots captured but NOTHING decoded: the "
                         f"stream does not match the reference decoder's CAM evolution")
        return out
    bad = [p for p, _ts in decoded if ((p >> 124) & 0xF) > 0xF]
    if bad:
        out["reason"] = f"{len(bad)} decoded packets carry an impossible packet_type"
        return out

    ratio = len(populated) / len(decoded)
    out["slots_per_pkt"] = ratio
    out["saving_pct"] = 100.0 * (1.0 - ratio / RAW_SLOTS_PER_PACKET)
    log(f"  {len(populated)} populated slots -> {len(decoded)} decoded packets")
    log(f"  {ratio:.2f} slots per packet -> {out['saving_pct']:.1f}% smaller than raw 3-beat")
    if ratio >= RAW_SLOTS_PER_PACKET:
        out["reason"] = ("3.00 slots/packet is the RAW ratio: this capture is UNCOMPRESSED. "
                         "The bitstream must carry USE_MON_COMPRESSION=1 (gated on "
                         "USE_AXI_MONITORS) and the harness must pass it to u_stream.")
        return out
    out["ok"] = True
    return out


def main(argv=None) -> int:
    p = argparse.ArgumentParser(description=(__doc__ or "").split("\n")[0])
    p.add_argument("--port", default="auto")
    p.add_argument("--baud", type=int, default=115200)
    p.add_argument("--channel", type=int, default=0)
    p.add_argument("--descriptors", type=int, default=4)
    p.add_argument("--bytes", type=int, default=16384, dest="xfer_bytes")
    p.add_argument("--slots", type=int, default=4096,
                   help="how many 64-bit capture slots to read back at most")
    args = p.parse_args(argv)

    from harness_addrs import autodetect_port, describe_build
    from uart_axi_bridge import UARTAxiBridge
    port = autodetect_port(args.baud, want=args.port)
    with UARTAxiBridge(port, args.baud) as br:
        print(f"mon_compress: port={port}  {describe_build(br)}")
        res = measure_compression(br, channel=args.channel, descriptors=args.descriptors,
                                  xfer_bytes=args.xfer_bytes, max_slots=args.slots)
    if res["ok"]:
        print("  PASS: capture is compressed and decodes cleanly")
        return 0
    print(f"  FAIL: {res['reason']}")
    return 1


if __name__ == "__main__":
    raise SystemExit(main())
