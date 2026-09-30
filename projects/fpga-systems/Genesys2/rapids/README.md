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
├── reports/
└── flows-rapids/    the build + host flow (mirror of flows-rapids-beats)
    ├── rtl/         rapids_byte_harness.sv, rapids_byte_top.sv, rapids_byte_genesys2_top.sv
    ├── filelists/   constraints/  tcl/  bin/
    ├── host/        run_characterization.py, rapids_byte_io.py, rapids_byte_golden.py, ...
    ├── dv/          cocotb harness self-check (sink, source, byte cases)
    └── Makefile     sim / synth / bitstream / program / smoke / suite
```

## Quick start

```bash
source env_python
cd projects/fpga-systems/Genesys2/rapids/flows-rapids
make sim                      # harness self-check: beat campaigns + byte cases
make bitstream                # Genesys 2, 8 channels, 256-bit, 4 KB per channel
make program
python3 host/run_characterization.py --channels 8 --byte-smoke
```
