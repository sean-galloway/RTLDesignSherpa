# stream_characterization

On-chip DMA characterization on the Digilent Nexys A7-100T board. Drives
a 2 × 2 comparison matrix — `{STREAM in-house, Vivado MCDMA}` ×
`{in-house bridge, Vivado bridge}` — through a shared instrumentation
harness so each cell of the matrix is measured against the same
benchmarks under the same memory model.

## Layout

```
stream_characterization/                       ← this directory (umbrella)
│
├── README.md                                  this file
├── Makefile                                   orchestrates all flows
│
├── docs/                                      shared comparison writeup
│   ├── characterization_v1_findings.md
│   ├── STREAM_CharacterizationReport_v0.90.{docx,pdf}
│   ├── characterization_styles.yaml
│   ├── title.md
│   ├── generate_pdf.sh
│   └── assets/                                graphviz + plot PNGs
│
├── stream_char_framework/                     shared instrumentation
│   ├── rtl/                                   axi_response_delay,
│   │                                          axil_decode_5s, axil2apb,
│   │                                          harness_csr, desc_ram,
│   │                                          debug_sram, leds, 7-seg
│   └── host/                                  plot_results.py (DUT-agnostic)
│
├── rtl-vivado/                                vendor IP archives
│   └── axi_mcdma_0/                           xci, xdc, hdl, synth
│
├── flows-stream-bridge/                       cell (1,1): in-house DMA + in-house bridge
│   ├── rtl/, tcl/, constraints/, dv/, host/
│   ├── csv/, plots/, reports/, bitstream/     committed outputs
│   ├── build/                                 .gitignored Vivado work
│   ├── Makefile
│   └── README.md
│
├── flows-vivado-mcdma/                        cell (1,2): Vivado MCDMA + in-house bridge   (SKELETON)
│   └── (same structure)
│
├── flows-stream-vivado-bridge/                cell (2,1): in-house DMA + Vivado bridge     (FUTURE)
│
└── flows-vivado-mcdma-vivado-bridge/          cell (2,2): Vivado × Vivado                 (FUTURE)
```

## How to use it

Everything is driven from this directory's `Makefile`, which delegates
to each flow's own Makefile. Per-flow short names: `stream-bridge`,
`vivado-mcdma`, `stream-vivado-bridge`, `vivado-mcdma-vivado-bridge`.

```bash
# build / program / sim ONE flow
make bitstream-stream-bridge
make program-vivado-mcdma
make sim-stream-bridge

# build EVERY flow's bitstream in sequence (10–30 min × N)
make all-bitstreams

# regenerate the comparison report
make docs

# show the full target catalogue
make help
```

Each flow's working directory keeps its own `bitstream/`, `csv/`,
`plots/`, `reports/`, and gitignored `build/` — so RTL bring-up and
data gathering for one flow can never accidentally contaminate another.
The umbrella `docs/` pulls plots from every flow at doc-build time, so
the writeup stays a self-contained bundle.

## Why the matrix

Comparing in-house IP against vendor IP one-component-at-a-time
isolates where the cost (or the benefit) actually comes from. Cells are
ordered so each row swaps the DMA and each column swaps the bridge;
deltas across a row attribute to the DMA change, deltas across a
column attribute to the bridge change.

| | in-house bridge | Vivado bridge |
|---|---|---|
| **STREAM (in-house)** | `flows-stream-bridge` | `flows-stream-vivado-bridge` |
| **MCDMA (Vivado)**    | `flows-vivado-mcdma`  | `flows-vivado-mcdma-vivado-bridge` |

## Status

| Cell | Build | Validation strategy | Sweeps | Doc data |
|---|---|---|---|---|
| stream-bridge | working | cocotb gate + FPGA sweeps | collected (delay 0–512, ch×delay 1–4×0–512, etc.) | in writeup |
| vivado-mcdma | skeleton elaborates; harness not yet wired through MCDMA | **FPGA-only** (Vivado IP is VHDL → Verilator can't simulate; see flow's `dv/README.md`) | — | — |
| stream-vivado-bridge | not yet built | cocotb gate + FPGA sweeps | — | — |
| vivado-mcdma-vivado-bridge | not yet built | FPGA-only (same VHDL constraint as MCDMA) | — | — |

See each flow's own `README.md` for the per-flow detail.
