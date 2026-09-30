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

Characterized on silicon 2026-09-30 (`reports/board/`): beat smoke PASS on
both halves; byte campaign 7/7 PASS (1 B at offset 1, 2 B at 31, 32, 37,
100 at 7, 96 at 17, 203 B across a 4 KB boundary), sink write-CRC and source
egress-CRC each equal to the byte-wise golden. Build (`reports/build/`):
WNS +0.258 ns at 100 MHz with observers, 89,746 LUTs, 68 BRAM tiles.

Byte characterization report v0.1 (`reports/perf/`, PRELIMINARY, standard
profile, 105 points): 103 pass; sink 203 B at offset 1 fails the golden on
both points it was run (sim repro pending). Large-transfer rates sit at the
harness checker ceiling of 3200 / 9 = 355.6 MB/s (the byte-wise CRC checkers
take 9 cycles per 32-byte beat), so the "beat-aligned utilization unchanged"
check against RAPIDS Beats is not yet settled; it needs a build with the
word-wide checkers. Final numbers are rerun after the channel-reset fix.

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
