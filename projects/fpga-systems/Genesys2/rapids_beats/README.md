# rapids_beats

On-chip characterization of the split RAPIDS **beats** DMA on the Digilent
Nexys A7-100T. The RAPIDS core is split into two wholly-separate engines —
`rapids_src_beats` (memory → AXIS, read-only) and `rapids_snk_beats`
(AXIS → memory, write-only) — behind one shared APB (`SRC @ 0x0000` /
`SNK @ 0x1000`) with a merged MonBus egress. This harness drives both data
paths on real hardware over UART and validates every beat against a
deterministic golden CRC.

## Layout

```
rapids_beats/                    ← this directory (umbrella)
├── README.md                               this file
├── docs/                                    house-style findings report
│   ├── rapids_beats_findings.md  the report (source)
│   ├── characterization_styles.yaml         corporate style
│   ├── title.md  generate_pdf.sh            PDF pipeline (md_to_docx --style)
│   └── assets/{mmd,png}/                     mermaid + matplotlib figures
└── flows-rapids-beats/                      the build + host flow
    ├── rtl/       rapids_char_harness.sv, rapids_char_top.sv (pin top)
    ├── filelists/ filelists      constraints/  NexysA7 XDC
    ├── tcl/       Vivado create_project / build_all / program
    ├── host/      rapids_char_io.py, descriptor_builder.py,
    │              rapids_char_golden.py, run_characterization.py, dump_status.py
    ├── dv/        cocotb harness self-check TB
    └── Makefile   sim / synth / bitstream / program / smoke / suite / flow
```

## The FPGA system book

- [docs/rapids_fpga_system/rapids_fpga_system_index.md](docs/rapids_fpga_system/rapids_fpga_system_index.md)
  — the bench, the harness block by block, the build variants and why each
  exists (one RTL, several bitstreams), and the host flow; Graphviz diagrams
  under `docs/rapids_fpga_system/assets/graphviz/`. Built as
  `docs/RAPIDS_FPGA_System_v1.0.pdf` by `docs/generate_fpga_system_pdf.sh`.
- [docs/rapids_axis_system/rapids_axis_system_index.md](docs/rapids_axis_system/rapids_axis_system_index.md)
  — the AXIS4 side, which is what makes this build different from STREAM's:
  the two stream ports, the generator and checker, the ingress window, the
  AXIS meters and the AXIS observer. Built as `docs/RAPIDS_AXIS_System_v1.0.pdf`
  by `docs/generate_axis_system_pdf.sh`.

## Findings report

- [rapids_beats_findings.md](docs/rapids_beats_findings.md)
  — architecture, timing closure @ 100 MHz, utilization, the golden-CRC
  methodology, and the on-silicon results. Regenerate the styled DOCX/PDF with:
  ```bash
  cd docs && ./generate_pdf.sh --rev 1.0
  ```

## Quick start

```bash
source env_python                 # sets REPO_ROOT / SIM=verilator
cd projects/fpga-systems/Genesys2/rapids_beats/flows-rapids-beats

make sim                   # cocotb harness self-check (sink + source, golden CRC)
make bitstream BOARD=genesys2  # synth + impl + bitstream (Genesys 2, timing-closed @ 100 MHz)
make program BOARD=genesys2    # flash the board (JTAG)
make smoke                 # fast golden-validated confidence check over UART
make suite BOARD=genesys2      # full sweep: channels × beats × backpressure × seed (JSON report)
```

`CHANNELS` is kept in lockstep between the bitstream build generic and the host
(`make suite CHANNELS=4`). The on-chip data comes from reusable AXIS/AXI4
pattern generators + CRC checkers; both paths are validated against
`flows-rapids-beats/host/rapids_char_golden.py` (independent golden model).

## Status

Characterized on silicon 2026-10-03 post-fix (commit 71d48b6f7):

- `make smoke` PASS (both paths).
- Default suite re-run 2026-10-03 post-fix: 48/48 PASS
  (`reports/rapids_char_suite_2026-10-03.json`), channels {1,2,4} × beats
  {1,4,8,16} × backpressure {off,on} × seed {2}, both data paths CRC-verified
  against the golden.
- Bare k325t image: sha256 `168acd76ee2fd61305a2c426f2b504f30243af0619bc9cd13b1ab107f8b23d10`,
  WNS +0.343 ns, 62,109 LUTs.
- Observers image: sha256 `d22db961...`, WNS +0.471 ns, preserved as
  `flows-rapids-beats/bitstream/rapids_char_obs_20261003.bit` (the tree's
  `rapids_char.bit` is the bare image). Observer campaigns:
  139 configs across 7 runs, all PASS (see `reports/perf/README.md` for the
  2026-10-03 JSONs).
- 3.2 GB/s peak (32 B × 100 MHz) is unchanged at the saturated points on the
  2026-10-03 re-measurement.

## Related

- Component: [rapids](../../../components/dma-ip/rapids/) — [PRD](../../../components/dma-ip/rapids/PRD.md) · [spec](../../../components/dma-ip/rapids/docs/)
- Sibling flow (template): [stream](../stream/)
