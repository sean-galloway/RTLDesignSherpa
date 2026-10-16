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

# Amber MESI L1 Pair-Rig on Genesys 2

A board bring-up for the **amber MESI L1 cache** on the Digilent Genesys 2
(Kintex-7 XC7K325T-2). Two independent cache instances share a coherent
memory image through a snooping pair fabric, driven by deterministic
CPU-request injectors and observed through a MonBus tally path. The host
talks to the design over UART through a generated AXI4-Lite bridge.

- **Docs:** [amber_fpga_system_index.md](docs/amber_fpga_system_index.md) — diagrams, address map, and build details.
- **Status:** As-built and bitstream-generated (`build-bringup/fpga/bitstream/amber_bringup.bit`).

## What the build demonstrates

1. **Two-core coherent cache pair** — two `amber_top` MESI L1 caches
   (`s128w4l64b64`: 128 sets, 4 ways, 64-byte line, 64-bit AXI bus) share a
   512 KB on-chip BRAM via `amber_pair_fabric`.
2. **Deterministic stress stimulus** — two `amber_cycle_injector` blocks
   issue pseudo-random read/write CPU requests from programmed seeds, with
   per-injector CRC-32 accumulation of issued write data and returned read
   data.
3. **Host control over UART** — a `uart_axil_bridge` translates ASCII write/read
   commands into AXI4-Lite transactions that program injectors, poll status,
   and read back MonBus tallies.
4. **Observation** — cache MonBus streams merge through `monbus_arbiter`, are
   ingested by `monbus_axil4_axil4_group`, and counted by
   `monbus_tally_axil`; the host reads the resulting bin counts.

## Board and clock

- **Board:** Digilent Genesys 2 (Kintex-7 `xc7k325tffg900-2`).
- **Clock:** 200 MHz LVDS oscillator → `IBUFDS` → `MMCME2_BASE`
  (`VCO=1350 MHz`, `CLKOUT0_DIVIDE=15`) → 90 MHz system clock.
- **UART:** 115200 8N1 on the FT232R USB-UART (`uart_tx_in` / `uart_rx_out`).
- **LEDs:** `LD7=busy`, `LD6=done`, `LD5=error`, `LD0=heartbeat`.

## Pieces in the build

| Path | What it holds |
| --- | --- |
| `rtl/amber_pair_genesys2_top.sv` | Board top: clocking, reset sync, LED heartbeat, harness instance. |
| `rtl/amber_pair_harness.sv` | Integration harness: UART bridge, generated AXIL decoder, CSR, injectors, caches, fabric, memory, MonBus tally path. |
| `rtl/amber_cycle_injector.sv` | Per-core stimulus engine: AXIL CSR slave, LFSR address/data generation, CRC-32 accumulators. |
| `rtl/bridges/configs/bridge_amber_axil.toml` | 1-master × 6-slave AXIL bridge definition. |
| `rtl/filelists/amber_pair_genesys2_top.f` | Top-level filelist closure. |
| `host/amber_board.py` | Named-register host driver and smoke campaign. |
| `host/amber_*_regmap.py` | Hand-authored register maps for `harness_csr`, `cycle_injector`, and `tally_cnt`. |
| `bin/run_smoke.py`, `bin/seq_*.py` | Board-level smoke sequences. |
| `bin/regen_bridges.sh` | Regenerates `bridge_amber_axil` from the TOML/CSV. |
| `fpga/tcl/` | Vivado project creation, synthesis/implementation, and ILA capture scripts. |
| `fpga/constraints/amber_pair_genesys2_top.xdc` | Pin and timing constraints. |
| `dv/` | SystemVerilog harness testbenches and cocotb tests. |
| `build-bringup/` | Vivado build directory, reports, and bitstreams. |

## How to build

From this directory:

```bash
# Regenerate the bridge (run whenever the .toml or .csv changes)
bash bin/regen_bridges.sh bridge_amber_axil

# Full synthesis + implementation + bitstream
make bitstream

# Or step-by-step from build-bringup/
make -C build-bringup project
make -C build-bringup synth
make -C build-bringup impl
make -C build-bringup bitstream
```

The default build produces `build-bringup/fpga/bitstream/amber_bringup.bit`.
An ILA debug variant is built with `make -C build-bringup ila`.

## How to run on the board

```bash
# Auto-detect the Genesys 2 UART port and run the coherence smoke test
python3 host/amber_board.py --smoke

# Force a specific port and transaction count
python3 host/amber_board.py --smoke --port /dev/ttyUSB0 --count 50000

# Write-only blind run (use when the read path is still being debugged)
python3 host/amber_board.py --smoke --blind
```

The smoke test:
1. Loads a legal-set profile into the MonBus tally CAM.
2. Configures both cycle injectors to hammer the same 4 KB region.
3. Starts both injectors.
4. Polls `STATUS` until both report `done`.
5. Dumps injector status, read/write CRCs, and tally bins.

## Performance sweep (board analysis)

```bash
# Run the 11-config matrix (region size x write mix x sharing) and save JSON
python3 host/amber_perf_sweep.py
```

The sweep is the stream-perf-analog for amber: it walks the working set
from 64 B (one line, maximal coherence ping-pong) through 128 KB (4x
capacity, thrash) at several write mixes, taking MonBus tally bins as
per-run differentials (tally_clear is tied off in the harness, so counts
accumulate run over run). From the bins it derives hit rate, snoop rate,
evictions, fills, drains, and AXI transaction counts per configuration.
The tally legal-set profile is keyed from wire truth — see
`build_default_profile()` in `host/amber_board.py`.

## Simulation

```bash
# From dv/tests/
make -C dv/tests test_amber_pair_harness_axil
make -C dv/tests test_amber_pair_harness_uart
```

## Address map and register details

See [docs/address_map.md](docs/address_map.md) for the host-visible address
space and per-aperture register maps.

## Diagrams

All diagrams are Graphviz `.dot` files in `docs/assets/graphviz/`, rendered to
`.png` by `docs/assets/graphviz/regenerate_all_graphviz.sh`.

| Figure | Subject |
| --- | --- |
| [amber_pair_genesys2_harness](docs/assets/graphviz/amber_pair_genesys2_harness.dot) | Whole-unit harness: host → UART → bridge → caches → fabric → memory |
| [amber_address_map](docs/assets/graphviz/amber_address_map.dot) | Host-visible AXIL address space |
| [amber_uart_harness](docs/assets/graphviz/amber_uart_harness.dot) | Host → UART → AXIL → CSR decode → DUT data path |
| [amber_cycle_injector](docs/assets/graphviz/amber_cycle_injector.dot) | Per-core stimulus engine internals |
| [amber_cache_top](docs/assets/graphviz/amber_cache_top.dot) | `amber_top` internals: L1 core, AXI masters, monitor |
| [amber_pair_fabric](docs/assets/graphviz/amber_pair_fabric.dot) | Snooping grant-pick fabric between the two caches and memory |
| [amber_tally_path](docs/assets/graphviz/amber_tally_path.dot) | Cache MonBus streams → merge → ingest → tally |

---

**Last Updated:** 2026-10-14
**Maintained By:** RTL Design Sherpa Project
