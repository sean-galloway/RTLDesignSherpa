# Troubleshooting

## Current state

The primary `stream-bridge` flow is working: cocotb gate + full FPGA sweeps are
collected, with data in the perf (v1.4) and compression (v1.3) writeups
(`flows-stream-bridge/progress/STATUS = 90-DONE`). `flows-vivado-mcdma` is a
skeleton (blinks an LED, drives no transfers); `flows-idma-bridge` is area +
cosim only.

## Known issues

| Symptom | Cause / workaround |
|---------|--------------------|
| Configs hang after a long mixed session | State-accumulation wedge (4–7 active channels under `debug-compl`): `AXI_RD/WR_COMPLETE = 0`, and a per-run soft/cluster reset does **not** clear it — only `make program` (full reprogram) does. Reset-completeness gap, not data corruption. Tracked in `rtl/amba/KNOWN_ISSUES/axi_monitor_blockready_hang_partial_channels.md`. |
| A later no-delay run silently under-performs | Sticky `RESP_DELAY`: a `--resp-delays` sweep leaves the CSR set. **Re-program before a matrix/size sweep.** |
| `16desc_*` configs trip `trace.overflow` | Benign — bounds the 2048-beat debug trace, not the bus-meter counters. |
| `run_characterization.py -o` crashes on save | `-o` paths are relative to `host/`; use an absolute path or `../../reports/perf`. |

: Known issues and workarounds

## Cannot find the board

The USB-UART re-enumerates on replug. Use `--port auto` (SCRATCH magic
`0xC0FFEE5A`) or a stable `/dev/serial/by-id/...` path — never a hardcoded
`/dev/ttyUSB*`. Confirm alive with `dump_status.py` → `BUILD_ID = 0x5354_5243`.

## Not simulatable

The Vivado MCDMA IP is VHDL — Verilator cannot simulate it, so MCDMA validation
is FPGA-only. The full iDMA end-to-end (desc64 + backend) is not built (width
mismatch); its two halves are characterized separately for the area comparison.

## Board fit vs sim geometry

`NUM_CHANNELS` is reduced 8 → 4 for sim (Artix BRAM); the as-built
characterization bitstream is 8-channel with monitors on (the perf build). Timing
closes at +0.031 ns WNS after trimming monitors to perf-only.

## Which README to trust

The dated `flows-stream-bridge/README.md` ("Phase 1", 2026-04) describes an
earlier 5-slave `axil_decode_5s` / `axil2apb` decoder. The **current** design uses
the generated `bridge_stream_char_axil`; trust `PORT_MAP.md` and
`flows-stream-bridge/host/ADDRESS_MAP.md` (July 2026), and the regmap generator, over that README.
