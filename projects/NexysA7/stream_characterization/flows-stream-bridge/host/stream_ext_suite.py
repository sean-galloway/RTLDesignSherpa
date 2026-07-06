# SPDX-License-Identifier: MIT
# SPDX-FileCopyrightText: 2026 sean galloway
"""FPGA test suite for STREAM extended (dma_address_gen) addressing.

SEPARATE from the existing characterization tests. Exercises the four read/write
traversal combinations over a WxH tile, driven entirely through the named
`Stream` API so the SAME program runs on the NexysA7 (pyserial `UARTAxiBridge`)
and in cocotb sim (injected channel). Requires the DUT built with
USE_ROW_COL_MAJOR_ADDRESSING=1.

Traversal <-> addressing mode (per direction, keyed off stride_0 vs beat_size):
  row = row-major     = contiguous inner (stride_0 = beat_size)  -> burst
  col = column-major  = strided   inner (stride_0 = row_pitch)   -> per-beat (arlen=0)

  case      read      write     what it is
  --------  --------  --------  ---------------------------------------------
  row/row   burst     burst     2D-tiled contiguous copy
  row/col   burst     per-beat  transpose (read rows, write columns)
  col/row   per-beat  burst     transpose mirror (read columns, write rows)
  col/col   per-beat  per-beat  column-major copy (both single-beat)

For a WxH tile the read/write DATA stream (and its order) is identical across all
four cases — only the addresses differ — so a data-integrity peer (the char
harness crc_check) yields the SAME result for every case; the cases differ in the
address pattern and the throughput (per-beat modes are single-beat on that side).
"""

from __future__ import annotations

# STREAM one-hot channel_state_t (stream_pkg.sv)
CH_IDLE  = 0x01
CH_ERROR = 0x20

CASES = ("row/row", "row/col", "col/row", "col/col")


def _layout(mode: str, W: int, H: int, bs: int) -> dict:
    """addr-gen cfg for one direction. row = contiguous rows (burst); col =
    strided columns (per-beat). row_pitch = W beats."""
    row_pitch = W * bs
    if mode == "row":
        return dict(s0=bs, s1=row_pitch, inner=W)       # burst W-beat rows
    if mode == "col":
        return dict(s0=row_pitch, s1=bs, inner=H)       # single-beat, walk columns
    raise ValueError(f"mode must be 'row' or 'col', got {mode!r}")


def build_case(case: str, W: int, H: int, bs: int):
    """Return (rd_cfg, wr_cfg) dicts for a 'rd/wr' case."""
    rd_mode, wr_mode = case.split("/")
    return _layout(rd_mode, W, H, bs), _layout(wr_mode, W, H, bs)


def program_case(stream, channel: int, case: str, W: int, H: int) -> int:
    """Program one case's extended descriptor into the channel; return kick addr."""
    bs = stream.desc.bytes_per_beat
    rd, wr = build_case(case, W, H, bs)
    return stream.load_ext(channel, W * H * bs, rd=rd, wr=wr)


def wait_done(stream, channel: int, *, start_poll: int = 64,
              poll_max: int = 100_000) -> dict:
    """Poll channel state to completion. Returns {ok, reason}.

    `start_poll` bounds the wait-to-leave-IDLE phase (a short transfer may finish
    before it is observed; over a slow transport each poll is a real bus read, so
    this must not spin). Then poll to return to IDLE, failing on CH_ERROR.
    """
    for _ in range(start_poll):
        if stream.channel_state(channel) != CH_IDLE:
            break
    for _ in range(poll_max):
        st = stream.channel_state(channel)
        if st == CH_ERROR:
            return dict(ok=False, reason="CH_ERROR")
        if st == CH_IDLE:
            return dict(ok=True, reason="idle")
    return dict(ok=False, reason="timeout")


def run_case(stream, channel: int, case: str, W: int, H: int,
             *, poll_max: int = 500_000) -> dict:
    """Program + kick + wait for one case. Returns a result dict."""
    kick = program_case(stream, channel, case, W, H)
    stream.run(channel, kick)
    res = wait_done(stream, channel, poll_max=poll_max)
    res.update(case=case, beats=W * H, kick=kick)
    return res


def run_suite(stream, *, channel: int = 0, W: int = 4, H: int = 4,
              cases=CASES, poll_max: int = 500_000) -> dict:
    """Run all four cases on one channel; return {case: result}."""
    return {case: run_case(stream, channel, case, W, H, poll_max=poll_max)
            for case in cases}


# ---------------------------------------------------------------------------
# FPGA entry point: same program the sim runs, over a real UART.
# ---------------------------------------------------------------------------
def main(argv=None) -> int:
    import argparse
    import os
    import sys

    # converters/bin holds UARTAxiBridge; host/ holds Stream.
    _here = os.path.dirname(os.path.abspath(__file__))
    sys.path.insert(0, _here)
    for up in range(3, 8):
        cand = os.path.join(_here, *([".."] * up), "projects/components/converters/bin")
        if os.path.isdir(cand):
            sys.path.insert(0, cand)
            break
    from uart_axi_bridge import UARTAxiBridge
    from stream_device import Stream
    from descriptor_builder import STREAM_APB_BASE, DESC_RAM_BASE

    ap = argparse.ArgumentParser(description="STREAM extended-addressing FPGA suite")
    ap.add_argument("--port", default="/dev/ttyUSB1")
    ap.add_argument("--baud", type=int, default=115200)
    ap.add_argument("--channel", type=int, default=0)
    ap.add_argument("--width", type=int, default=4, help="tile width (beats/row)")
    ap.add_argument("--height", type=int, default=4, help="tile height (rows)")
    args = ap.parse_args(argv)

    with UARTAxiBridge(args.port, args.baud) as bridge:
        stream = Stream(bridge, "stream0",
                        regs_base=STREAM_APB_BASE, desc_ram_base=DESC_RAM_BASE)
        results = run_suite(stream, channel=args.channel,
                            W=args.width, H=args.height)

    all_ok = True
    for case in CASES:
        r = results[case]
        all_ok &= r["ok"]
        print(f"  {case:8s}  {'PASS' if r['ok'] else 'FAIL':4s}  "
              f"{r['beats']} beats  ({r['reason']})")
    print(f"stream_ext_suite: {'PASS' if all_ok else 'FAIL'}")
    return 0 if all_ok else 1


if __name__ == "__main__":
    raise SystemExit(main())
