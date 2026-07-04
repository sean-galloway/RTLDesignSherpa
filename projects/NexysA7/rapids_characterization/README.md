# rapids_characterization

On-chip characterization of the split RAPIDS **beats** DMA on the Digilent
Nexys A7-100T. The RAPIDS core is split into two wholly-separate engines —
`rapids_src_beats` (memory → AXIS, read-only) and `rapids_snk_beats`
(AXIS → memory, write-only) — behind one shared APB (`SRC @ 0x0000` /
`SNK @ 0x1000`) with a merged MonBus egress. This harness drives both data
paths on real hardware over UART and validates every beat against a
deterministic golden CRC.

## Layout

```
rapids_characterization/                    ← this directory (umbrella)
├── README.md                               this file
├── docs/                                    house-style findings report
│   ├── rapids_characterization_findings.md  the report (source)
│   ├── characterization_styles.yaml         corporate style
│   ├── title.md  generate_pdf.sh            PDF pipeline (md_to_docx --style)
│   └── assets/{mmd,png}/                     mermaid + matplotlib figures
└── flows-rapids-beats/                      the build + host flow
    ├── rtl/       rapids_char_harness.sv, rapids_char_top.sv (pin top)
    ├── flists/    filelists      constraints/  NexysA7 XDC
    ├── tcl/       Vivado create_project / build_all / program
    ├── host/      rapids_char_io.py, descriptor_builder.py,
    │              rapids_char_golden.py, run_characterization.py, dump_status.py
    ├── dv/        cocotb harness self-check TB
    └── Makefile   sim / synth / bitstream / program / smoke / suite / flow
```

## Findings report

- [rapids_characterization_findings.md](docs/rapids_characterization_findings.md)
  — architecture, timing closure @ 100 MHz, utilization, the golden-CRC
  methodology, and the on-silicon results. Regenerate the styled DOCX/PDF with:
  ```bash
  cd docs && ./generate_pdf.sh --rev 1.0
  ```

## Quick start

```bash
source env_python                 # sets REPO_ROOT / SIM=verilator
cd projects/NexysA7/rapids_characterization/flows-rapids-beats

make sim          # cocotb harness self-check (sink + source, golden CRC)
make bitstream    # synth + impl + bitstream (NexysA7, timing-closed @ 100 MHz)
make program      # flash the board (JTAG)
make smoke        # fast golden-validated confidence check over UART
make suite        # full sweep: channels × beats × backpressure × seed (JSON report)
```

`CHANNELS` is kept in lockstep between the bitstream build generic and the host
(`make suite CHANNELS=4`). The on-chip data comes from reusable AXIS/AXI4
pattern generators + CRC checkers; both paths are validated against
`host/rapids_char_golden.py` (independent golden model).

## Status

Characterized on silicon: `make smoke` PASS (both paths), `make suite` 48/48 PASS
(channels {1,2,4} × beats {1,4,8,16} × backpressure {off,on} × seed {2}), both
data paths CRC-verified against the golden. Timing closed at 100 MHz
(WNS +0.007 ns, 0 failing endpoints; `NUM_CHANNELS=4`, `SRAM_DEPTH=256` board-fit).

## Related

- Component: [rapids](../../components/rapids/) — [PRD](../../components/rapids/PRD.md) · [spec](../../components/rapids/docs/)
- Sibling flow (template): [stream_characterization](../stream_characterization/)
