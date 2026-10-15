<!-- RTL Design Sherpa Documentation Header -->
<table>
<tr>
<td width="80">
  <a href="https://github.com/sean-galloway/RTLDesignSherpa">
    <img src="https://raw.githubusercontent.com/sean-galloway/RTLDesignSherpa/main/docs/logos/Logo_200px.png" alt="RTL Design Sherpa" width="70">
  </a>
</td>
<td>
  <strong>RTL Design Sherpa</strong> · <em>Learning Hardware Design Through Practice</em><br>
  <sub>
    <a href="https://github.com/sean-galloway/RTLDesignSherpa">GitHub</a> ·
    <a href="https://github.com/sean-galloway/RTLDesignSherpa/blob/main/docs/DOCUMENTATION_INDEX.md">Documentation Index</a> ·
    <a href="https://github.com/sean-galloway/RTLDesignSherpa/blob/main/LICENSE">MIT License</a>
  </sub>
</td>
</tr>
</table>

---

# Binary BCH FPGA Loop — Genesys 2

**Board-validated BCH(4224,4120) t=8 codec wrapped in a UART-controlled loop.**

This build area demonstrates the landed BCH component on real silicon: a
pattern generator feeds a BCH encoder, a bit-granular error injector corrupts
the codeword, a riBM decoder recovers it, and an independent checker verifies
the result. The same host programs run in cocotb simulation and on the board
because the harness boundary is the ASCII UART wire.

| | |
|---|---|
| **Primary board** | Digilent Genesys 2 (Kintex-7 XC7K325T-2, serial `200300B818A0`) |
| **Secondary board** | Digilent Nexys A7-100T (Artix-7 XC7A100T-1) — full profile or `BCH_PROFILE=small` |
| **Toolchain** | Vivado 2025.1 |
| **Harness clock** | 100 MHz on Genesys 2; 100 MHz full profile / 50 MHz small profile on Nexys A7 |
| **Host link** | UART 115200-8N1 |
| **Codec** | BCH(4224,4120) t=8 over GF(2^13), shortened from n=8191 (board profile) |
| **Small profile** | BCH(248,224) t=3 over GF(2^8), shortened from n=255 |

---

## What this build demonstrates

- **End-to-end BCH validation on FPGA.** The codec chain runs at 100 MHz on the
  Genesys 2 with both AXI-Stream and AXI4 integration styles.
- **Deterministic, reproducible campaigns.** Every board run uses fixed seeds by
  default and replays bit-exactly in cocotb.
- **Post-encoder error injection.** Errors are injected after the encoder so the
  parity bits are exposed to corruption, matching real storage/channel behavior.
- **Independent on-chip oracle.** The decoder reports ok/corrected/
  uncorrectable/frame, while a separate regenerated-LFSR checker reports
  `data_err` and CRC, so the verdict does not rely on the block under test.
- **UART-equivalence simulation.** The real `uart_axil_bridge` RTL and the host
  Python programs drive the same cocotb testbench that runs on the board.

---

## Build pieces

### RTL tops

| Module | File | Role |
|---|---|---|
| `bch_loop_genesys2_top` | `build-loop/rtl/bch_loop_genesys2_top.sv` | Genesys 2 board top: 200 MHz LVDS → MMCM → 100 MHz, UART, LEDs. |
| `bch_loop_top` | `build-loop/rtl/bch_loop_top.sv` | Nexys A7-100T board top; full profile at 100 MHz, small profile divides to 50 MHz. |
| `bch_loop_harness` | `build-loop/rtl/bch_loop_harness.sv` | Board-agnostic datapath, CSR wiring, observer mux, status aggregation. |
| `bch_axi4_pipeline` | `build-loop/rtl/bch_axi4_pipeline.sv` | AXI4 flavour: memory-to-memory codec chain over three job memories. |
| `bch_loop_cfg_pkg` | `build-loop/rtl/bch_loop_cfg_pkg.sv` | One source of geometry, UART baud, build IDs (`BCHP`, `BCHS`). |
| `bch_loop_regs` | `build-loop/rtl/generated/bch_loop_regs/rtl/bch_loop_regs.sv` | PeakRDL-generated CSR block from `build-loop/rtl/bch_loop_regs.rdl`. |
| `bridge_bch_loop_axil` | `rtl/bridges/generated/bridge_bch_loop_axil/bridge_bch_loop_axil.sv` | Generated 1-master × 3-slave AXI4-Lite-to-APB fabric. |

### Harness / FPGA flow

| File | Role |
|---|---|
| `build-loop/Makefile` | Build variables; includes global `make/fpga_flow.mk`. |
| `build-loop/fpga/tcl/create_project.tcl` | Vivado project creation. |
| `build-loop/fpga/tcl/build_all.tcl` | Synthesis + implementation + bitstream. |
| `build-loop/fpga/constraints/bch_loop_genesys2.xdc` | Genesys 2 pin/timing constraints. |
| `build-loop/fpga/constraints/bch_loop.xdc` | Nexys A7 constraints. |
| `bin/regen_bridges.sh` | Regenerates the 1×3 fabric from `rtl/bridges/configs/bridge_bch_loop_axil.toml`. |
| `bin/build_image_matrix.sh` | Serial build of both Genesys 2 images. |

### Host scripts

| File | Role |
|---|---|
| `build-loop/host/bch_loop.py` | `BchLoopDriver`: by-name CSR access, status collection, observer readers. |
| `build-loop/host/bch_loop_programs.py` | Authored-once programs: `smoke`, `bypass`, `run`, `sweep`, `verdict`. |
| `build-loop/host/host_bch_loop.py` | CLI front-end over the programs. |
| `bin/run_smoke.py` | Campaign runner that opens the driver and prints reports. |
| `bin/seq_*.py` | Deterministic campaign sequences: `init`, `smoke`, `sweep`, `random`, `soak`. |

---

## How to build and run

All commands are relative to `projects/fpga-systems/Genesys2/ecc-ip/bch/`.

### Build one image

```bash
# Genesys 2, AXI-Stream flavour (the board-validated default)
make -C build-loop bitstream BCH_TARGET=genesys2 BCH_IFACE=AXIS

# Genesys 2, AXI4 flavour
make -C build-loop bitstream BCH_TARGET=genesys2 BCH_IFACE=AXI4

# Nexys A7 small profile
make -C build-loop bitstream BCH_TARGET=nexys_a7_100t BCH_PROFILE=small
```

### Build the image matrix

```bash
./bin/build_image_matrix.sh
```

This produces `build-loop/fpga/bitstream/bch_loop_genesys2_axis.bit` and
`bch_loop_genesys2_axi4.bit`.

### Program the board

```bash
make -C build-loop program BCH_TARGET=genesys2
```

The shared board layer verifies the JTAG serial before programming.

### Run a campaign

```bash
# init + smoke + sweep over the UART
bin/run_smoke.py --board genesys2 --port /dev/ttyUSB0 --sequences init smoke sweep
```

The host reads `BUILD_ID` and `TOPOLOGY` to confirm the bitstream and detect
AXIS vs AXI4 automatically.

### Regenerate collateral

```bash
make regmap            # CSR RTL + dv/tbclasses/bch_loop_regs_regmap.py from RDL
bin/regen_bridges.sh   # 1x3 AXIL/APB fabric from TOML
```

### Run UART-equivalence simulation

```bash
make -C build-loop sim
```

This runs the unmodified host programs against the real `uart_axil_bridge` and
`bch_loop_harness` in cocotb.

---

## Documentation

| Document | Path | What it covers |
|---|---|---|
| **Harness architecture (living copy)** | `docs/UART_HARNESS.md` | Datapath, CSR wiring, testing choices, operating procedure. |
| **Harness book / PDF** | `docs/bch_uart_harness/` + `Binary_BCH_UART_Harness_v0.1.pdf` | Publication-ready harness guide with block diagrams. |
| **Board validation report / PDF** | `docs/bch_board_validation/` + `Binary_BCH_Board_Validation_v0.1.pdf` | Campaign methodology and the 2026-10-05 million-block soak. |
| **Address map** | `docs/bch_uart_harness/ch02_the_harness/03_address_map.md` | UART harness CSR/memory address space, dot + rendered PNG. |
| **Build record** | `stable/MANIFEST.md` | Last kept build reports, WNS, LUT counts, validation summary. |
| **Run artifacts** | `stable/results/` | Published campaign JSON, figures, and `FINDINGS.md`. |

### Block diagrams

- AXIS datapath and register path: `docs/bch_uart_harness/assets/graphviz/01_bch_axis_loop.dot`
- AXI4 memory-to-memory datapath: `docs/bch_uart_harness/assets/graphviz/02_bch_axi4_loop.dot`
- UART harness control path: `docs/bch_uart_harness/assets/graphviz/03_uart_harness_control.dot`
- Address map: `docs/bch_uart_harness/assets/graphviz/04_address_map.dot`

Render all diagrams with the directory's `regenerate_all_graphviz.sh` script.

---

## Project layout

```
projects/fpga-systems/Genesys2/ecc-ip/bch/
├── README.md                          # This file
├── Makefile                           # Area dispatcher (delegates to build-loop/)
├── bin/                               # Campaign runners and helper scripts
├── build-loop/                        # Single build directory
│   ├── rtl/                           # Tops, harness, datapath, config package, RDL
│   ├── dv/                            # cocotb UART-equivalence testbench
│   ├── host/                          # Python driver and programs
│   └── fpga/                          # Tcl, constraints, bitstreams, reports
├── docs/
│   ├── UART_HARNESS.md                # Living architecture copy
│   ├── bch_uart_harness/              # Harness book source + assets
│   └── bch_board_validation/          # Board validation book source + assets
└── stable/                            # Last kept build reports and results
```

---

## License

Part of the RTL Design Sherpa project. See the repository root `LICENSE` file.
