# rapids

On-chip characterization of the byte-granular RAPIDS DMA (`rapids_top`,
rapids TASK-019) on the Digilent Genesys 2. This area is the byte-granular
sibling of [rapids_beats](../rapids_beats/): the same bench, harness shape,
UART host flow and golden-CRC methodology, built around the product RTL in
`projects/components/dma-ip/rapids/rtl/{fub,macro,top}` instead of the beats
stepping stone. The beats area is kept as is; nothing here changes it.

What is different from rapids_beats:

- the DUT is `rapids_top`: descriptor lengths in BYTES, byte-granular
  addresses, WSTRB and TSTRB carry partial beats, one AXIS packet per
  descriptor;
- the AXIS generator can end every packet on a partial beat (`GEN_LASTB`),
  and both data checkers CRC the strobed bytes in address order (`BYTE_CRC`)
  instead of one 32-bit slice per beat, so a one-byte transfer is checked as
  one byte;
- the host has a byte campaign (`--byte-smoke`, `--bytes N --offset K`) with
  byte-wise goldens, and the beat campaigns still run (the host scales beats
  to bytes when `BUILD.BYTE_DUT` reads 1);
- the harness ID is `RAPB` (0x5241_5042), so a host never mistakes one
  bitstream for the other.

## Layout

```
rapids/
├── README.md
├── docs/            (book and reports to come)
├── reports/         make_byte_perf_report.py, generate_reports_pdf.sh, perf/ (byte characterization report)
└── flows-rapids/    the build + host flow (mirror of flows-rapids-beats)
    ├── rtl/         rapids_byte_harness.sv, rapids_byte_top.sv, rapids_byte_genesys2_top.sv
    ├── filelists/   constraints/  tcl/  bin/
    ├── host/        run_characterization.py, byte_perf.py, rapids_byte_io.py, rapids_byte_golden.py, ...
    ├── byte_perf.sh the one-command characterization: preflight, run, regenerate the report
    ├── dv/          cocotb harness self-check (sink, source, byte cases)
    └── Makefile     sim / synth / bitstream / program / smoke / suite
```

## Status

Characterized on silicon 2026-09-30. Report v0.2 (`reports/perf/`, final):

- Standard bitstream (`BYTE_CRC=1`, sha256 `cfad34c3...`): 117/117 byte-wise
  points pass, plus 4/4 directed sequences. Build: WNS +0.301 ns at 100 MHz,
  92,874 LUTs, 68 BRAM tiles. The byte-wise CRC checkers take 9 cycles per
  32-byte beat, so large-transfer rates sit at the harness ceiling of
  3200 / 9 = 355.6 MB/s (11.1 % of the 3200 MB/s peak, 100 MHz x 32 B).
- Measurement bitstream (`BYTE_CRC=0`, word-wide checkers, sha256
  `48e1282c...`): 28/28 beat-aligned points pass and reach 3182 MB/s sink and
  3199 MB/s source at 8 channels, 4096 beats (99.4 % and 100.0 % of peak).
  Build: WNS +0.077 ns, 86,065 LUTs, 52 BRAM tiles. The word-wide checker
  CRCs slice 0 of each beat only, so it is compared with the beats golden.
- The beat-aligned utilization is NOT unchanged versus RAPIDS Beats: 73 of
  112 cells differ by more than 0.5 pp. The deltas are fixed start-up cycle
  terms (the sink waits for the channel's packet record; the rest is not yet
  isolated), and the 4096-beat rows agree within 1.13 pp. Isolated in sim
  and accepted as by design (nothing can happen before the descriptor is
  loaded; rapids TASK-021, closed).
- AXI RRESP/BRESP error injection is not exercised on silicon (the harness
  memory always answers OKAY): rapids TASK-020.

The board keeps the standard byte-CRC bitstream (`754c3c2d...`, restored and
re-verified 2026-10-01 after the variant sweep); `flows-rapids/bitstream/` is
a gitignored build area and may hold either build.

## Quick start

```bash
source env_python
cd projects/fpga-systems/Genesys2/rapids/flows-rapids
make sim                      # harness self-check: beat campaigns + byte cases
make bitstream                # Genesys 2, 8 channels, 256-bit, 4 KB per channel
make program
python3 host/run_characterization.py --channels 8 --byte-smoke

# one command: writes the results JSON and regenerates the report.
# Checks for other users of the board/UART, and records CSR_ID/BUILD/sentinel at
# the start and end of each run (a mid-run reprogram aborts instead of recording).
./byte_perf.sh --profile standard           # PRELIMINARY (*_prelim_*.json)
./byte_perf.sh --profile full --final       # final numbers
```
