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

**[← Back to Genesys2](../../)** | **[← FPGA Systems Index](../../../index.md)**

# Jet MESI L1 Pair-Rig on Genesys 2

A board bring-up for the **jet MESI L1 cache** on the Digilent Genesys 2
(Kintex-7 XC7K325T-2). Two independent cache instances share a coherent
memory image through a snooping pair fabric, driven by deterministic
CPU-request injectors and observed through a MonBus tally path. The host
talks to the design over UART through a generated AXI4-Lite bridge.

- **Docs:** [jet_fpga_system_index.md](docs/jet_fpga_system_index.md) — diagrams, address map, and build details.
- **Status:** As-built and bitstream-generated (`build-bringup/fpga/bitstream/jet_bringup.bit`).

## What the build demonstrates

1. **Two-core coherent cache pair** — two `jet_top` MESI L1 caches
   (`s128w4l64b64`: 128 sets, 4 ways, 64-byte line, 64-bit AXI bus) share a
   512 KB on-chip BRAM via `jet_pair_fabric`.
2. **Deterministic stress stimulus** — two `amber_cycle_injector` blocks
   issue pseudo-random read/write CPU requests from programmed seeds, with
   per-injector CRC-32 accumulation of issued write data and returned read
   data, plus per-run latency instrumentation: min/max/sum, an 8-bucket
   log2 histogram, and a busy-cycle count.
3. **Host control over UART** — a `uart_axil_bridge` translates ASCII write/read
   commands into AXI4-Lite transactions that program injectors, poll status,
   and read back MonBus tallies.
4. **Observation** — cache MonBus streams merge through `monbus_arbiter`, are
   ingested by `monbus_axil4_group_1wr` (write-only: everything lands in the
   tally record window), and counted by
   `monbus_tally_axil`; the host reads the resulting bin counts. The tally's
   16-slot first-event latch bank captures raw packets under a watch mask and
   re-arms on every tally clear (harness CSR `CTRL[0]`/`CTRL[1]`).

## Board and clock

- **Board:** Digilent Genesys 2 (Kintex-7 `xc7k325tffg900-2`).
- **Clock:** 200 MHz LVDS oscillator → `IBUFDS` → `MMCME2_BASE`
  (`VCO=1350 MHz`, `CLKOUT0_DIVIDE=22.5`) → 60 MHz system clock.
  Reclocked from 90 MHz to 60 MHz because the jet v1 non-blocking pipeline
  does not close timing at 90 MHz (see `vault/tracking/projects/components/cache-ip/jet-mesi-l1/issue/open/ISSUE-001.md`).
- **UART:** 115200 8N1 on the FT232R USB-UART (`uart_tx_in` / `uart_rx_out`).
- **LEDs:** `LD7=busy`, `LD6=done`, `LD5=error`, `LD0=heartbeat`.

## Pieces in the build

| Path | What it holds |
| --- | --- |
| `rtl/jet_pair_genesys2_top.sv` | Board top: clocking, reset sync, LED heartbeat, harness instance. |
| `rtl/jet_pair_harness.sv` | Integration harness: UART bridge, generated AXIL decoder, CSR, injectors, caches, fabric, memory, MonBus tally path. |
| `rtl/amber_cycle_injector.sv` | Per-core stimulus engine: AXIL CSR slave, LFSR address/data generation, CRC-32 accumulators, per-run latency min/max/sum + log2 histogram + busy cycles. |
| `rtl/bridges/configs/bridge_jet_axil.toml` | 1-master × 6-slave AXIL bridge definition. |
| `rtl/filelists/jet_pair_genesys2_top.f` | Top-level filelist closure. |
| `host/jet_board.py` | Named-register host driver and smoke campaign. |
| `host/jet_*_regmap.py` | Hand-authored register maps for `harness_csr`, `cycle_injector`, and `tally_cnt`. |
| `bin/run_smoke.py`, `bin/seq_*.py` | Board-level smoke sequences. |
| `bin/regen_bridges.sh` | Regenerates `bridge_jet_axil` from the TOML/CSV. |
| `fpga/tcl/` | Vivado project creation, synthesis/implementation, and ILA capture scripts. |
| `fpga/constraints/jet_pair_genesys2_top.xdc` | Pin and timing constraints. |
| `dv/` | SystemVerilog harness testbenches and cocotb tests. |
| `build-bringup/` | Vivado build directory, reports, and bitstreams. |

## How to build

From this directory:

```bash
# Regenerate the bridge (run whenever the .toml or .csv changes)
bash bin/regen_bridges.sh bridge_jet_axil

# Full synthesis + implementation + bitstream
make bitstream

# Or step-by-step from build-bringup/
make -C build-bringup project
make -C build-bringup synth
make -C build-bringup impl
make -C build-bringup bitstream
```

The default build produces `build-bringup/fpga/bitstream/jet_bringup.bit`.
An ILA debug variant is built with `make -C build-bringup ila`.

## How to run on the board

```bash
# Auto-detect the Genesys 2 UART port and run the coherence smoke test
python3 host/jet_board.py --smoke

# Force a specific port and transaction count
python3 host/jet_board.py --smoke --port /dev/ttyUSB0 --count 50000

# Write-only blind run (use when the read path is still being debugged)
python3 host/jet_board.py --smoke --blind
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
python3 host/jet_perf_sweep.py
```

The sweep is the stream-perf-analog for jet: it walks the working set
from 64 B (one line, maximal coherence ping-pong) through 128 KB (4x
capacity, thrash) at several write mixes. Each run is a clean tally window:
harness CSR `CTRL[1]` (freeze) holds the bins for a coherent snapshot and
`CTRL[0]` (write-1-pulse clear) zeroes them for the next run — no
before/after subtraction. From the bins it derives hit rate, snoop rate,
evictions, fills, drains, and AXI transaction counts per configuration.
The tally legal-set profile is keyed from wire truth — see
`build_default_profile()` in `host/jet_board.py`.

## Simulation

```bash
# From dv/tests/
make -C dv/tests test_jet_pair_harness_axil
make -C dv/tests test_jet_pair_harness_uart
```

## Address map and register details

See [docs/address_map.md](docs/address_map.md) for the host-visible address
space and per-aperture register maps.

## Diagrams

All diagrams are Graphviz `.dot` files in `docs/assets/graphviz/`, rendered to
`.png` by `docs/assets/graphviz/regenerate_all_graphviz.sh`.

| Figure | Subject |
| --- | --- |
| [jet_pair_genesys2_harness](docs/assets/graphviz/jet_pair_genesys2_harness.dot) | Whole-unit harness: host → UART → bridge → caches → fabric → memory |
| [jet_address_map](docs/assets/graphviz/jet_address_map.dot) | Host-visible AXIL address space |
| [jet_uart_harness](docs/assets/graphviz/jet_uart_harness.dot) | Host → UART → AXIL → CSR decode → DUT data path |
| [jet_tally_path](docs/assets/graphviz/jet_tally_path.dot) | Cache MonBus streams → merge → ingest → tally |

---

**Last Updated:** 2026-11-01
**Maintained By:** RTL Design Sherpa Project
