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

<!-- End Header -->

**[← Back to Genesys2](../README.md)** | **[← FPGA Systems Index](../../index.md)**

# scoria DDR3 on the Genesys 2

A/B characterization of the **scoria DDR3/LPDDR3 controller** against **LiteDRAM**
on the same board, same DRAM, same harness instruments. Two bitstreams:
`build-scoria` (the subject) and `build-litedram` (the yardstick). Both use the
same UART-based characterization harness so a bandwidth or latency number from
one is directly comparable with the other.

- **Address map:** [docs/ADDRESS_MAP.md](docs/ADDRESS_MAP.md)
- **Controller docs:** `projects/components/mem-ctrl-ip/research-ip/scoria-ddr3-lpddr3/docs/`
- **Status:** `build-litedram` built and booted (BIOS memtest pass);
  `build-scoria` RTL complete, no silicon run yet.

## What the two builds demonstrate

| | `build-scoria` | `build-litedram` |
|---|---|---|
| **Top** | `scoria_char_top` | `litedram_ddr3_board_top` |
| **Controller** | scoria DDR3/LPDDR3 | LiteDRAM generated core |
| **PHY** | LiteDRAM `k7ddrphy` | LiteDRAM `k7ddrphy` (same PHY) |
| **Host path** | UART → `uart_axil_bridge` → `bridge_scoria_char_axil` | LiteDRAM BIOS console over UART |
| **Stimulus** | 4 write + 4 read AXI pattern generators | VexRiscv BIOS memtest (self-contained) |
| **Purpose** | Measure scoria bandwidth/latency on real DDR3 | Prove the board, pins, PHY and DRAM are sound |

The LiteDRAM build is the denominator. Running it first answers "is the hardware
OK?" before any scoria result is interpreted.

## Board

- **FPGA:** Digilent Genesys 2, Kintex-7 XC7K325T-2FFG900C
- **DRAM:** 2 × Micron MT41J256M16 (4 Gb ×16), 32-bit data bus, 1 GiB total
- **Input clock:** 200 MHz LVDS differential pair (`clk200_p`/`clk200_n`)
- **Host link:** USB-UART (FT232R), 115200-8N1
- **Reset:** `cpu_reset_n` (active-low pushbutton)
- **LEDs:** 8, mapped per build

## Clocks (scoria build)

The scoria build runs the controller at **80 MHz**, not 100 MHz:

| Clock | Source | Frequency | Purpose |
|---|---|---|---|
| `sys` | MMCM CLKOUT1 / 10 | 80 MHz | Controller, harness, UART bridge |
| `sys4x` | MMCM CLKOUT0 / 2.5 | 320 MHz | DDR3 CK (4 phases × 80 MHz) |
| `idelay_ref` | MMCM CLKOUT2 / 4 | 200 MHz | `IDELAYCTRL` reference |

80 MHz keeps DDR3 within spec (tCK 3.125 ns < 3.3 ns max) and closes timing on
`scoria_top` where 100 MHz misses by 1.26 ns (`scoria BUG-003`). The LiteDRAM
build uses the generated core's own PLL and runs at its chosen rate.

## Layout

| Path | Holds |
|---|---|
| `build-scoria/` | scoria board top + harness + PHY build |
| `build-litedram/` | LiteDRAM board-proof build |
| `rtl/` | Shared harness (`scoria_char_harness.sv`), macro (`scoria_char_macro.sv`), DFI adapter (`dfi_flat_to_k7ddrphy.sv`), bridge config |
| `host/` | Python driver stack: `scoria_device.py`, `ddr3_char.py`, `scoria_char.py` |
| `bin/` | PHY generator (`gen_k7ddrphy.py`), blackbox generator, bridge helper |
| `dv/` | Shared block sim tests (pytest) |
| `docs/` | Address map, diagrams |

## RTL tops and harness pieces

### `scoria_char_top` (build-scoria)

- Clocking and reset (`IBUFDS`, `MMCME2_BASE`, `BUFG`, `IDELAYCTRL`, sync chain)
- `scoria_char_harness` — UART bridge, CSRs, DFI delay lines, LED driver
- `dfi_flat_to_k7ddrphy` — flat phase-packed DFI → per-phase DFI for K7DDRPHY
- `k7ddrphy` — generated LiteDRAM PHY

### `scoria_char_harness`

- `uart_axil_bridge` — host UART → 32-bit AXI4-Lite
- `bridge_scoria_char_axil` — 1×3 address decode to controller APB, harness CSR,
  chargen APB
- `harness_csr` — build ID, control/status, timer, DFI tuning, PHY CSR
  indirection, perf observability
- `scoria_char_macro` — AXI traffic generators + scoria controller
- `dfi_cmd_delay` / `dfi_rddata_delay` — tunable alignment delays
- `led_status_driver` — 8 LED status

### `scoria_char_macro`

- `char_engine_block` — 4 write + 4 read AXI4 pattern generators
- `apb4_to_peakrdl` — APB shim to scoria's PeakRDL cpuif
- `scoria_top_geared` — AXI width gearing + `scoria_top` core

### `litedram_ddr3_board_top` (build-litedram)

Thin wrapper around the generated `litedram_genesys2_ddr3` core. The AXI user
port is tied idle; the BIOS memtest runs through the VexRiscv's own port.

## How to build and run

Prerequisites: Xilinx Vivado, the repo Python env (`source env_python` from
`$REPO_ROOT`), and for `build-scoria` a LiteX venv (default
`/tmp/claude-1000/litex-venv`, override with `LITEX_VENV=`).

```bash
cd projects/fpga-systems/Genesys2/mem-ctrl-ip/scoria

# --- build-litedram: the board proof ---
make bitstream BUILD=litedram
make program BUILD=litedram
# Watch the BIOS memtest over UART; expect init_done=1, init_error=0.

# --- build-scoria: the subject ---
make bitstream BUILD=scoria      # first run also generates the PHY (~3 min)
make program BUILD=scoria
make run BUILD=scoria            # runs host/ddr3_char.py sequence

# --- A/B back-to-back on one board ---
make ab

# --- lint / sim / reports ---
make lint BUILD=scoria
make sim BUILD=scoria            # shared dv/tests over the harness blocks
make utilization BUILD=scoria
make timing BUILD=scoria
```

Per-build help: `make -C build-scoria help` or `make -C build-litedram help`.

## Address map

The harness exposes three 4 KB windows over the UART bridge:

| Base | Size | Slave | What's behind it |
|---|---:|---|---|
| `0x0000_0000` | 4 KB | `scoria_apb` | scoria controller CSR (PeakRDL) |
| `0x0001_0000` | 4 KB | `harness_csr` | harness control/status/observability |
| `0x000A_0000` | 4 KB | `chargen_apb` | 4 write + 4 read pattern generators |

See [docs/ADDRESS_MAP.md](docs/ADDRESS_MAP.md) for the full register layout,
PHY calibration CSR indirection, and planned vs as-built notes.

## Diagrams

All diagrams are Graphviz `.dot` sources in `docs/assets/graphviz/`, rendered to
`.png` by `docs/assets/graphviz/regenerate_all_graphviz.sh`.

| Figure | Source | Subject |
|---|---|---|
| 1.1 | `scoria_uart_harness.dot` | host → UART → bridge → CSR decode → DUT |
| 2.1 | `scoria_litedram_stack.dot` | LiteDRAM board-proof stack (build-litedram) |
| 3.1 | `scoria_controller.dot` | scoria controller + AXI gearing + CSR (build-scoria) |
| A.1 | `scoria_address_map.dot` | UART-harness CSR/memory address map |

## Planned vs as-built

- **As-built:** `build-litedram` bitstream, BIOS memtest pass, timing reports.
- **As-built:** `build-scoria` RTL, harness, host scripts, generated bridge and
  PHY blackbox.
- **PLANNED:** first `build-scoria` silicon run and characterization matrix.
  The host scripts have been verified against the regmaps and a mock bridge but
  have not yet driven hardware.
- **PLANNED:** DFI monitor / trace-SRAM / observer expansion windows (the
  bridge's `.toml` deliberately leaves the 0x40000/0x80000/0x90000 holes empty).

## File structure

```
projects/fpga-systems/Genesys2/mem-ctrl-ip/scoria/
├── README.md
├── Makefile                        # area dispatcher (BUILD=scoria|litedram)
├── build-scoria/                   # scoria board build
│   ├── Makefile
│   ├── rtl/scoria_char_top.sv
│   ├── rtl/filelists/scoria_char_board.f
│   ├── rtl/generated/k7ddrphy.v    # generated PHY
│   ├── fpga/tcl/build_all.tcl
│   ├── fpga/constraints/*.xdc
│   └── host/                       # symlink to ../host
├── build-litedram/                 # LiteDRAM board-proof build
│   ├── Makefile
│   ├── rtl/litedram_ddr3_board_top.sv
│   ├── gen/gateware/litedram_genesys2_ddr3.v
│   └── results/bios_boot_memtest.log
├── rtl/                            # shared harness RTL
│   ├── scoria_char_harness.sv
│   ├── scoria_char_macro.sv
│   ├── dfi_flat_to_k7ddrphy.sv
│   └── bridges/
├── host/                           # Python driver stack
│   ├── scoria_device.py
│   ├── ddr3_char.py
│   └── scoria_char.py
├── bin/                            # generators and helpers
│   ├── gen_k7ddrphy.py
│   ├── gen_core_blackbox.py
│   └── regen_bridges.sh
├── dv/                             # shared sim tests
└── docs/
    ├── ADDRESS_MAP.md
    └── assets/graphviz/
```

## License

Part of the RTL Design Sherpa project. See the root repository `LICENSE` file.
