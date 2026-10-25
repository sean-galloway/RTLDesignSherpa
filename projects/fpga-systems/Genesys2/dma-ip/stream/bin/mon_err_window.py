# SPDX-License-Identifier: MIT
# SPDX-FileCopyrightText: 2026 sean galloway
"""Prove the monbus ERROR WINDOW end to end -- ONE program, cosim and board.

STREAM's monitor egress is monbus_axil4_group_1wr (stream TASK-019): packets
whose type is selected by <MON>_ERR_CFG.ERR_SELECT are written as raw 24-byte
records into the error window (MON_GROUP_ERR_BASE/LIMIT_ADDR: the top 4 KB of
comp_sram on this bridge), one stream_irq pulse and one MON_ERR_REC_COUNT step
per record landed. Nothing drains a FIFO any more; the host reads memory.

This routes COMPLETION packets (type 1) from the datapath monitors to the error
window, runs a monitors-on DMA through the board's own program
(CharacterizationRunner.run_config), and then checks what the hardware says
against what is in memory:

  * MON_ERR_REC_COUNT advanced (records landed), by no more than the window holds
  * every slot the count claims parses as a non-zero record
  * every record is a Completion from an AXI monitor (nothing else was selected)
  * no Completion is in the trace window (the two routes are exclusive)

A count that advances with zero slots behind it, or a record of another type,
is a routing or addressing bug, not noise.

Library + launcher (see the stream host-objects note): `test_stream_mon_err_window`
imports `probe_err_window` and drives it over the cosim bridge under `bridge`;
build-mon/host/host_mon_err_window.py is the CLI over pyserial.
"""
from __future__ import annotations

import argparse
import os
import sys
from typing import Callable, List, Tuple

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import stream_env  # noqa: F401,E402  (path setup)
from characterization import CharacterizationRunner, CharConfig  # noqa: E402
from stream_monitors import (BASIC_CLASSES, DATAPATH_MONITORS, PKT_COMPL,  # noqa: E402
                             MonitorProgram, route_monbus)
from stream_addrs import A  # noqa: E402  (by name, never offsets)
from bridge_windows import monbus_err_window, monbus_capture_window  # noqa: E402
from dump_monbus import RECORD_BYTES, read_one_record, format_record  # noqa: E402
from TBClasses.monbus import MonitorPacket  # noqa: E402

TRACE_WINDOW = "comp_sram"     # the trace goes to comp_sram (minus the error window)
PROTOCOL_AXI = 0


def read_count(bridge) -> int:
    v = bridge.read(A("MON_ERR_REC_COUNT"))
    return (0 if v is None else v) & 0xFFFF


def read_records(bridge, first: int, n: int) -> List[Tuple[MonitorPacket, int]]:
    """Records `first` .. `first + n - 1` out of the error window ring."""
    base, limit = monbus_err_window()
    capacity = (limit + 1 - base) // RECORD_BYTES
    out = []
    for k in range(n):
        slot = base + ((first + k) % capacity) * RECORD_BYTES
        out.append(read_one_record(bridge.read, slot))
    return out


def trace_has_completion(bridge, max_records: int = 512) -> bool:
    """Scan the head of the trace window for an AXI Completion record."""
    base, _limit = monbus_capture_window()
    for k in range(max_records):
        pkt, ts = read_one_record(bridge.read, base + k * RECORD_BYTES)
        if pkt.raw_packet == 0 and ts == 0:
            return False
        if int(pkt.packet_type) == PKT_COMPL and int(pkt.protocol) == PROTOCOL_AXI:
            return True
    return False


def probe_err_window(bridge, *, channel: int = 0, descriptors: int = 4,
                     xfer_bytes: int = 16384,
                     log: Callable[[str], object] = print,
                     runner: CharacterizationRunner | None = None) -> dict:
    """Run the workload and audit the error window. Returns a dict with `ok`,
    the figures (`before`, `after`, `landed`, `capacity`, `records`) and
    `reason` when not ok. Never raises on a hardware result."""
    runner = runner or CharacterizationRunner(bridge)
    runner.log = log
    runner.mon_config = MonitorProgram(BASIC_CLASSES, monitors=DATAPATH_MONITORS,
                                       name="err-window-compl", err_select=1 << PKT_COMPL)
    runner.compression = False
    seen = {}

    def pre_kick(br):
        tb, tl = route_monbus(br, TRACE_WINDOW)
        eb, el = monbus_err_window()
        seen["before"] = read_count(br)
        log(f"  trace window 0x{tb:06X}..0x{tl:06X}; error window 0x{eb:06X}..0x{el:06X}; "
            f"ERR_SELECT=compl on RDMON/WRMON; MON_ERR_REC_COUNT before = {seen['before']}")

    cfg = CharConfig(name=f"mon_err_window_{descriptors}x{xfer_bytes}",
                     num_channels=1, descriptors_per_channel=descriptors,
                     transfer_bytes=xfer_bytes, channels=[channel])
    res = runner.run_config(cfg, pre_kick=pre_kick)
    base, limit = monbus_err_window()
    capacity = (limit + 1 - base) // RECORD_BYTES
    out = {"ok": False, "dma_pass": bool(res.get("pass")), "dma": res,
           "before": seen.get("before"), "after": None, "landed": 0,
           "capacity": capacity, "records": []}
    if not out["dma_pass"]:
        out["reason"] = f"DMA did not pass ({res.get('error')}); the error window is not meaningful"
        return out

    after = read_count(bridge)
    landed = (after - out["before"]) & 0xFFFF
    out["after"], out["landed"] = after, landed
    log(f"  MON_ERR_REC_COUNT after = {after}: {landed} record(s) landed (window holds {capacity})")
    if landed == 0:
        out["reason"] = ("MON_ERR_REC_COUNT did not advance: no Completion reached the error "
                         "window (ERR_SELECT routing lost, COMPL_EN off, or PKT_MASK dropping type 1)")
        return out
    if landed > capacity:
        out["reason"] = (f"{landed} records landed but the window holds {capacity}: the ring "
                         "wrapped inside one run, so the oldest records are gone")
        return out

    records = read_records(bridge, out["before"], landed)
    out["records"] = records
    empty = [k for k, (p, ts) in enumerate(records) if p.raw_packet == 0 and ts == 0]
    if empty:
        out["reason"] = (f"count says {landed} records but slot(s) {empty} read as zero: "
                         "the count and the window disagree (window address wrong?)")
        return out
    wrong = [(k, int(p.packet_type), int(p.protocol)) for k, (p, _ts) in enumerate(records)
             if int(p.packet_type) != PKT_COMPL or int(p.protocol) != PROTOCOL_AXI]
    if wrong:
        out["reason"] = (f"{len(wrong)} record(s) are not AXI Completions (slot, type, protocol): "
                         f"{wrong[:4]} -- only type 1 was selected for the error window")
        return out
    for p, ts in records[:4]:
        log("  " + format_record(p, ts))
    if landed > 4:
        log(f"  ... {landed - 4} more")
    if trace_has_completion(bridge):
        out["reason"] = "an AXI Completion is ALSO in the trace window: the two routes must be exclusive"
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
    args = p.parse_args(argv)

    from harness_addrs import autodetect_port, describe_build
    from uart_axi_bridge import UARTAxiBridge
    port = autodetect_port(args.baud, want=args.port)
    with UARTAxiBridge(port, args.baud) as br:
        print(f"mon_err_window: port={port}  {describe_build(br)}")
        res = probe_err_window(br, channel=args.channel, descriptors=args.descriptors,
                               xfer_bytes=args.xfer_bytes)
    if res["ok"]:
        print(f"  PASS: {res['landed']} Completion record(s) landed in the error window and read back")
        return 0
    print(f"  FAIL: {res['reason']}")
    return 1


if __name__ == "__main__":
    raise SystemExit(main())
