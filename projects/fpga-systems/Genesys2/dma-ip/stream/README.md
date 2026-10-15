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

**[← Back to Genesys 2](../README.md)** | **[← FPGA Systems Index](../../index.md)**

# STREAM DMA on the Genesys 2

**Board:** Digilent Genesys 2 (Kintex-7 XC7K325T-2)  
**Purpose:** A characterization and monitor-validation harness for the STREAM
scatter-gather DMA IP. The same RTL source is built three ways -- `mon`,
`obs`, and `perf` -- so the DMA datapath, the in-core monitors, and the
interface observers are each measured against the same stimulus and memory
model.

- **System book:** [`docs/stream_fpga_system/`](docs/stream_fpga_system/stream_fpga_system_index.md) -- what is in the bitstream, the harness, the address map, the three builds, and the host flow.
- **Operator guide:** [`docs/stream_char_guide/`](docs/stream_char_guide/stream_char_guide_index.md) -- v0.90, predates the Genesys 2 port; the system book supersedes its system description.
- **Characterization findings:** [`docs/characterization_v1_findings.md`](docs/characterization_v1_findings.md)
- **Port map:** [`docs/PORT_MAP.md`](docs/PORT_MAP.md)

## What this build demonstrates

STREAM is a memory-to-memory scatter-gather DMA. This FPGA system wraps it
with:

- A UART host interface (`uart_axil_bridge`, 115200-8N1 ASCII `W`/`R`).
- A generated 1-to-N AXI4-Lite bridge that fans out to the DUT APB window,
  harness CSRs, descriptor RAM, monitor tallies, observer config, and capture
  SRAM.
- An LFSR read-source pattern generator and a write-sink CRC checker
  (`axi4_dma_slaves`), with programmable per-beat response delay
  (`axi_response_delay`) for latency-vs-bandwidth sweeps.
- Two interface observers (`axi4_intf_master_observer` on STREAM's own
  masters, `axi4_intf_slave_observer` on the DMA slaves) plus two
  `monbus_tally_axil` memories and a compressed-MonBus capture SRAM.
- One `stream_top_ch8` DUT, either 8 channels or 4 depending on the build.

The result is two measurement vehicles in one source tree:

| Build | `USE_AXI_MONITORS` | `OBS_ENABLE_MON_TAPS` | Channels | Measures |
|-------|:------------------:|:---------------------:|:--------:|----------|
| `mon` | 1 | 0 | 8 | in-core monitor coverage, compression, error/fault probes |
| `obs` | 0 | 1 | 4 | interface observers watching the DUT from outside |
| `perf`| 0 | 0 | 8 | the datapath itself, with no instrument in the way |

: Build overview

`mon` and `obs` are complementary, not redundant: they exercise the monitor
code from inside and outside the DUT. They cannot be built together -- the
combined LUT count exceeds the Kintex-7 device.

## The pieces

| Layer | Files | Role |
|-------|-------|------|
| Board top | `rtl/stream_genesys2_top.sv` | LVDS 200 MHz clock input, MMCM, reset sync, 8 user LEDs, pin constraints |
| Harness | `rtl/stream_harness.sv`, `rtl/harness_csr.sv`, `rtl/axi_response_delay.sv` | UART bridge, generated crossbar, control/status registers, descriptor RAM, tallies, capture SRAM, latency model, observers |
| DUT | `stream_top_ch8` (from `projects/components/dma-ip/stream/rtl/`) | STREAM DMA: APB config, descriptor engine, read/write engines, MonBus egress |
| Generated bridges | `rtl/bridges/generated/bridge_stream_mon_axil*` | 1-to-N crossbar from `rtl/bridges/configs/bridge_stream_mon_axil.toml` |
| FPGA flow | `fpga/tcl/`, `fpga/constraints/`, `make/fpga_flow.mk` | Vivado project, synthesis, implementation, bitstream, reports |
| Shared host libraries | `bin/` | UART link, register access by name, descriptor builder, characterization runners, plotting |
| Per-build host programs | `build-mon/host/`, `build-obs/host/`, `build-perf/host/` | Coverage, compression, observer campaign, bus-meter and perf sweeps |

: Pieces in the build

## How to build

The area Makefile is a dispatcher. Per-build Makefiles are variables only;
flow logic lives in `make/fpga_flow.mk`.

```bash
cd projects/fpga-systems/Genesys2/dma-ip/stream

# List targets
make help
make -C build-mon help

# Generate the bridge (PREBUILD), then synthesize / implement / bitstream
make bitstream                    # default BUILD=mon
make bitstream BUILD=obs
make bitstream BUILD=perf

# Other common targets
make lint BUILD=mon
make sim BUILD=mon
make program BUILD=mon
make utilization BUILD=mon
make timing BUILD=mon
```

The `mon` and `obs` instrumented builds run at 60 MHz on Genesys 2; `perf`
runs at 100 MHz. The bridge is regenerated before synthesis by
`bin/regen_bridges.sh` so the address map in hardware always matches its
`.toml` source.

## How to run on the board

1. Program the board:
   ```bash
   make program BUILD=mon
   ```
2. Find the UART port and run a per-build host program:
   ```bash
   cd build-mon
   ./host/host_mon_coverage.py --help
   ./host/host_mon_matrix.py
   ```
   ```bash
   cd build-obs
   ./host/host_obs_campaign.py --help
   ```
   ```bash
   cd build-perf
   ./host/host_characterize.py --help
   ./host/host_rw_perf.py
   ```

`stream_env` selects which `build-<x>/host/` layer is on the Python path; its
default is `mon`, and `build-perf` sets it explicitly to `perf` so a perf
program cannot accidentally import mon's copy of a sibling.

## Sign-off and reports

| Directory | Content |
|-----------|---------|
| `stable/` | Sign-off `mon` bitstream, reports, and `MANIFEST.md` |
| `stable-obs/` | Sign-off `obs` bitstream, reports, and `MANIFEST.md` |
| `reports/perf/` | Datapath utilization sweeps |
| `reports/compression/` | MonBus compression measurements |
| `reports/area/` | Area-vs-channel-count data |
| `reports/ext_addressing/` | Extended row/column addressing campaign |

: Reports and sign-off copies

## Address map

The host address map is drawn in
[`docs/stream_fpga_system/assets/graphviz/05_address_map.dot`](docs/stream_fpga_system/assets/graphviz/05_address_map.dot)
and explained in
[`docs/stream_fpga_system/ch02_harness/02_address_map.md`](docs/stream_fpga_system/ch02_harness/02_address_map.md).
Key bases:

| Base | Slave |
|------|-------|
| `0x0000_0000` | `stream_apb` -- STREAM DUT config |
| `0x0001_0000` | `harness_csr` -- control/status/timer/CRC/build identity |
| `0x0002_0000` | `desc_ram` -- descriptor preload |
| `0x0004_0000` | `stream_tally` -- in-core monitor tally |
| `0x000C_0000` | `slave_tally` -- observer tally |
| `0x0010_0000` | `stream_tally_cfg` -- tally CAM config |
| `0x0014_0000` | `slave_tally_cfg` -- tally CAM config |
| `0x0018_0000` | `slvmon_apb` -- slave observer config |
| `0x0019_0000` | `obs_apb` -- master observer config |
| `0x001A_0000` | `comp_sram` -- compressed MonBus capture memory |

: Key host address bases

Host tools resolve registers by name (`H("CTRL")`, `A("SCHED_CONFIG")`,
`O("MON_CTRL")`) against the generated regmaps; never hardcode offsets.
