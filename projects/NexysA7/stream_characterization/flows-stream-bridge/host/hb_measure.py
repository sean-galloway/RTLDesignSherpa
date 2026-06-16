#!/usr/bin/env python3
"""hb_measure.py — clean on-board half-beat measurement.

Runs the compressed (half-beat) workload, reads the bulk-trace SRAM, decodes
the 64-bit slots with the golden Decoder (round-trip sanity), and reports the
reduction vs the raw-equivalent (records * 3 beats). Self-contained: the raw
baseline is analytic (raw = 3 beats/record) so no separate off-run is needed,
and the decode confirms every slot is well-formed.

    source env_python
    python3 host/hb_measure.py --port /dev/ttyUSB2 --channels 1 --config 4desc_1ch_1MB --size 1MB
"""
import argparse, io, contextlib, subprocess, sys
from pathlib import Path

REPO = "/mnt/data/github/RTLDesignSherpa"
sys.path.insert(0, f"{REPO}/projects/components/converters/bin")
sys.path.insert(0, str(Path(__file__).resolve().parent))

from dump_monbus_sram import read_sram_region, words32_to_words64
from TBClasses.monbus.monbus_compressor import Decoder

H = 0x10000
CSR_DBG_WR_PTR   = H + 0x08
CSR_DBG_OVERFLOW = H + 0x0C
DEBUG_SRAM_BASE  = 0x40000
STREAM_APB_BASE  = 0x20000
APB_CHANNEL_RESET = STREAM_APB_BASE + 0x124


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--port", default="/dev/ttyUSB2")
    ap.add_argument("--channels", required=True)
    ap.add_argument("--config", required=True)
    ap.add_argument("--size", default="1MB")
    ap.add_argument("--mon-config", default="debug-all")
    args = ap.parse_args()

    # Full cluster reset BEFORE the run. The soft-reset pulse alone (CTRL
    # bit 3) is NOT enough between back-to-back invocations: per-channel
    # STREAM state and the stat accumulators survive it, and that stale
    # state perturbs the captured event stream (and thus the compressed
    # beat count) run-to-run. Localization proved this: with soft-reset
    # only, repeated 8desc_8ch runs gave 261 vs 405 beats; with the full
    # reset below they are bit-identical (212 rec / 405 beats every run,
    # CRC ok). The compressor itself is bit-exact to the golden model in
    # cosim on the exact stream (val/amba/test_monbus_halfbeat.py), so the
    # variation was reset, not the codec. Sequence: soft-reset pulse ->
    # settle -> per-channel reset pulse -> clear_stats -> settle.
    import time
    from uart_axi_bridge import UARTAxiBridge
    with contextlib.redirect_stdout(io.StringIO()):
        with UARTAxiBridge(port=args.port, baudrate=115200) as b:
            b.write(H + 0x00, 0x08)             # soft_reset pulse
            time.sleep(0.15)
            b.write(APB_CHANNEL_RESET, 0xFF)    # per-channel reset (all 8)
            time.sleep(0.05)
            b.write(APB_CHANNEL_RESET, 0x00)
            b.write(H + 0x00, 0x02)             # clear_stats / trace ptr
            time.sleep(0.15)

    # Run the compressed workload (run_characterization clears the trace ptr at
    # start and sets WRMON.COMPRESS_EN for --compression on).
    cmd = [sys.executable, "host/run_characterization.py", "--port", args.port,
           "--compression", "on", "--mon-config", args.mon_config,
           "--size", args.size, "--channels", str(args.channels),
           "--configs", args.config]
    r = subprocess.run(cmd, cwd=f"{REPO}/projects/NexysA7/stream_characterization/flows-stream-bridge",
                       capture_output=True, text=True)
    crc_ok = "CRC MATCH" in r.stdout

    from uart_axi_bridge import UARTAxiBridge
    buf = io.StringIO()
    with contextlib.redirect_stdout(buf):
        with UARTAxiBridge(port=args.port, baudrate=115200) as b:
            wr = b.read(CSR_DBG_WR_PTR) & 0xFFFFFFFF
            ov = b.read(CSR_DBG_OVERFLOW) & 1
            words = read_sram_region(b.read, DEBUG_SRAM_BASE, wr * 4) if not ov else None

    if ov:
        print(f"{args.config}: TRACE OVERFLOWED (wr_ptr={wr}) — use a smaller "
              f"workload for a clean count.")
        return
    slots = words32_to_words64(words)
    # Decode with the golden (handles RAW / A / B / C / HALF_PAIR).
    try:
        records = list(Decoder().decode(slots))
        rt = "OK"
    except Exception as e:
        records, rt = [], f"DECODE-FAIL: {e}"

    beats = len(slots)
    nrec = len(records)
    raw_beats = nrec * 3
    red = (1 - beats / raw_beats) * 100 if raw_beats else 0.0
    print(f"{args.config}: CRC={'ok' if crc_ok else 'MISMATCH'}  decode={rt}  "
          f"records={nrec}  half-beat beats={beats}  raw-equiv={raw_beats}  "
          f"reduction={red:.1f}%")


if __name__ == "__main__":
    main()
