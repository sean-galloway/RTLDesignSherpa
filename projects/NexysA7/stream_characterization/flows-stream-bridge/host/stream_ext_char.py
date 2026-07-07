# SPDX-License-Identifier: MIT
# SPDX-FileCopyrightText: 2026 sean galloway
"""Extended-addressing characterization for STREAM (row/col x row/col).

Sweeps the four traversal modes (row/row, row/col, col/row, col/col) over a set
of WxH tiles and measures RD/WR datapath throughput + bus utilization via the
NAMED RDMON_PERF / WRMON_PERF windows (stream_regmap). One program, board + sim.

Emits one record per (mode, size) with the raw perf buckets and derived metrics,
so the report generator produces the same tables/curves from sim or board data.

Requires the DUT built with USE_ROW_COL_MAJOR_ADDRESSING=1. STREAM must already
be configured (GLOBAL_EN + scheduler + descriptor engine + AXI); the caller does
that once (the board main() below, or the sim TB) before run_sweep().
"""

from __future__ import annotations

import json
from typing import List, Tuple

from stream_ext_suite import CASES, program_case, wait_done

# Default sweep: throughput-vs-size per mode. row modes burst; col modes are
# single-beat, so col/col at the large sizes dominates board runtime.
DEFAULT_SIZES: List[Tuple[int, int]] = [(64, 64), (256, 256), (1024, 1024), (2048, 2048)]

# Char-harness datapath monitor + perf-window offsets (relative to the STREAM
# APB base). These are the addresses the char harness's AXIL xbar actually
# decodes (the monitor block predates the stream_regmap 0x1000 relocation, which
# the char build does NOT expose). Enable sequence + perf layout match the proven
# rw_perf path in stream_char_tb.py.
_RDMON = dict(ENABLE=0x260, PKT_MASK=0x26C, ERR_CFG=0x270, PERF=0x300)
_WRMON = dict(ENABLE=0x280, PKT_MASK=0x28C, ERR_CFG=0x290, PERF=0x330)
_PERF_OFF = dict(CTRL=0x00, STATUS=0x04, WINDOW=0x08, PROD=0x0C, BP=0x10,
                 STARV=0x14, IDLE=0x18, BEATS=0x1C, BYTE_LO=0x20, BYTE_HI=0x24,
                 BURST=0x28)
_MON_ENABLE = 0x0F            # COMPL/TIMEOUT/ERR/... enable
_MON_PKT_MASK_ALLOW = 0xFFF0  # clear the RDL drop-all default


def enable_monitors(stream) -> None:
    """Enable the RD/WR datapath monitors (PKT_MASK + ENABLE + ERR_CFG) so their
    perf windows observe the bus. Full sequence matching rw_perf."""
    a = stream.regs.start_address
    for mon in (_RDMON, _WRMON):
        stream.bridge.write(a + mon["PKT_MASK"], _MON_PKT_MASK_ALLOW)
        stream.bridge.write(a + mon["ENABLE"], _MON_ENABLE)
        stream.bridge.write(a + mon["ERR_CFG"], 0x0)


def _read_perf(stream, mon: dict) -> dict:
    """Read one datapath perf window. bucket_total = PROD+BP+STARV+IDLE is the
    closed-window length (WINDOW_CYCLES is live/zeroed on close; buckets hold)."""
    a = stream.regs.start_address + mon["PERF"]

    def r(off: int) -> int:
        return stream.bridge.read(a + off) or 0

    prod, bp = r(_PERF_OFF["PROD"]), r(_PERF_OFF["BP"])
    starv, idle = r(_PERF_OFF["STARV"]), r(_PERF_OFF["IDLE"])
    return {
        "prod": prod, "bp": bp, "starv": starv, "idle": idle,
        "total": prod + bp + starv + idle,
        "beats": r(_PERF_OFF["BEATS"]), "bursts": r(_PERF_OFF["BURST"]),
        "bytes": (r(_PERF_OFF["BYTE_HI"]) << 32) | r(_PERF_OFF["BYTE_LO"]),
    }


def _perf_run(stream, on: bool) -> None:
    """Drive the RD/WR perf-window RUN bit. Rising edge clears + opens the
    window; falling edge closes (buckets hold)."""
    v = 1 if on else 0
    a = stream.regs.start_address
    stream.bridge.write(a + _RDMON["PERF"] + _PERF_OFF["CTRL"], v)
    stream.bridge.write(a + _WRMON["PERF"] + _PERF_OFF["CTRL"], v)


def measure_mode(stream, channel: int, case: str, W: int, H: int,
                 *, poll_max: int = 20000) -> dict:
    """Run one (mode, size) with the perf windows open; return a record."""
    _perf_run(stream, False)          # ensure low (clean rising edge next)
    _perf_run(stream, True)           # open + clear
    kick = program_case(stream, channel, case, W, H)
    stream.run(channel, kick)
    res = wait_done(stream, channel, poll_max=poll_max)
    _perf_run(stream, False)          # close

    rd, wr = _read_perf(stream, _RDMON), _read_perf(stream, _WRMON)
    return _derive({
        "case": case, "W": W, "H": H, "beats": W * H,
        "ok": res["ok"], "reason": res["reason"], "rd": rd, "wr": wr,
    })


def _derive(rec: dict) -> dict:
    """Add per-direction bytes/cycle throughput + utilization (buckets are the
    closed-window length; throughput is dimensionless bytes/cycle here — the
    report multiplies by the clock to get GB/s)."""
    for d in ("rd", "wr"):
        p = rec[d]
        tot = p["total"] or 1
        p["bytes_per_cycle"] = p["bytes"] / tot
        p["util"] = p["prod"] / tot          # productive fraction
        p["avg_burst_beats"] = (p["beats"] / p["bursts"]) if p["bursts"] else 0.0
    return rec


def run_sweep(stream, *, channel: int = 0, sizes=DEFAULT_SIZES, cases=CASES,
              poll_max: int = 20000, progress=None) -> List[dict]:
    """Sweep cases x sizes; return one record per (mode, size)."""
    enable_monitors(stream)          # by name; perf windows need the monitors on
    records = []
    for (W, H) in sizes:
        for case in cases:
            if progress:
                progress(f"{case} {W}x{H}")
            records.append(measure_mode(stream, channel, case, W, H, poll_max=poll_max))
    return records


# ---------------------------------------------------------------------------
# FPGA entry point
# ---------------------------------------------------------------------------
def _configure(stream, harness_csr_base: int) -> None:
    """One-time STREAM config by name (+ harness soft-reset). Mirrors the sim
    TB's _configure_stream_for_ext, board-side."""
    stream.bridge.write(harness_csr_base + 0x00, 0x08)   # CSR_CTRL soft_reset pulse
    stream.write_word("GLOBAL_CTRL", 0x01)               # GLOBAL_EN
    stream.write_word("SCHED_CONFIG", 0x0F)              # en+timeout+err+compl
    stream.write_word("SCHED_TIMEOUT_CYCLES", 0xFFFFFFFF)
    stream.write_word("DESCENG_CONFIG", 0x01)
    stream.write_word("DESCENG_ADDR0_BASE", 0x0000_0000)
    stream.write_word("DESCENG_ADDR0_LIMIT", 0xFFFF_FFFF)
    stream.write_word("DESCENG_ADDR1_BASE", 0x0000_0000)
    stream.write_word("DESCENG_ADDR1_LIMIT", 0xFFFF_FFFF)
    stream.write_word("AXI_XFER_CONFIG", (15 & 0xFF) | ((15 & 0xFF) << 8))


def main(argv=None) -> int:
    import argparse
    import os
    import sys

    _here = os.path.dirname(os.path.abspath(__file__))
    sys.path.insert(0, _here)
    for up in range(3, 8):
        cand = os.path.join(_here, *([".."] * up), "projects/components/converters/bin")
        if os.path.isdir(cand):
            sys.path.insert(0, cand)
            break
    from uart_axi_bridge import UARTAxiBridge
    from stream_device import Stream
    from descriptor_builder import STREAM_APB_BASE, DESC_RAM_BASE, HARNESS_CSR_BASE

    ap = argparse.ArgumentParser(description="STREAM extended-addressing characterization")
    ap.add_argument("--port", default="/dev/ttyUSB1")
    ap.add_argument("--baud", type=int, default=115200)
    ap.add_argument("--channel", type=int, default=0)
    ap.add_argument("--out", default="ext_char.json")
    ap.add_argument("--sizes", default="64x64,256x256,1024x1024,2048x2048")
    args = ap.parse_args(argv)

    sizes = [tuple(int(x) for x in s.split("x")) for s in args.sizes.split(",")]

    with UARTAxiBridge(args.port, args.baud) as bridge:
        stream = Stream(bridge, "stream0",
                        regs_base=STREAM_APB_BASE, desc_ram_base=DESC_RAM_BASE)
        _configure(stream, HARNESS_CSR_BASE)
        records = run_sweep(stream, channel=args.channel, sizes=sizes,
                            progress=lambda s: print(f"  {s}"))

    with open(args.out, "w") as f:
        json.dump({"records": records, "sizes": [list(s) for s in sizes]}, f, indent=2)
    print(f"wrote {len(records)} records -> {args.out}")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
