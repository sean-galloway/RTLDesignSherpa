# AMBA Shared Infrastructure

The 21 modules in `rtl/amba/shared/` are the protocol-adjacent utility layer: bus characterization blocks, performance meters, boundary splitters, a BRAM-backed slave family, address generation, and clock gating. Every module has its own page in this directory — this file is the map, not a second copy of the module documentation. The per-module pages are the reference; when this table and a module page disagree, trust the page (and fix the table).

An earlier version of this README carried full parameter tables, port lists, and usage examples for a subset of the modules. Those copies rotted — a review round found a `monbus_arbiter` example that could not elaborate, invented clock-gate ports, pre-widening "64-bit packet" claims, and a complete section for a CDC module that had moved to `rtl/cdc/` — so the catalog now lives only in the pages that track their RTL. One copy of the truth. It's the only way this stays honest.

## Modules

| Module | What it is | Page |
|---|---|---|
| `axi4_master_wr_pattern_gen` | Write-side characterization master: LFSR/hash pattern generator with running CRC | [page](axi4_master_wr_pattern_gen.md) |
| `axi4_master_rd_crc_check` | Read-side characterization master: regenerates the pattern, per-beat compare + running CRC | [page](axi4_master_rd_crc_check.md) |
| `axi4_slave_rd_pattern_gen` | Slave-side read pattern generator (serves the expected stream) | [page](axi4_slave_rd_pattern_gen.md) |
| `axi4_slave_wr_crc_check` | Slave-side write CRC accumulator (no compare logic — integrity is an external CRC-vs-CRC check; 16-deep B FIFO) | [page](axi4_slave_wr_crc_check.md) |
| `axi4_dma_slaves` | Wrapper bundling the two slave-side blocks for DMA loopback | [page](axi4_dma_slaves.md) |
| `axis4_master_pattern_gen` | AXIS pattern source (same LFSR family) | [page](axis4_master_pattern_gen.md) |
| `axis4_slave_pattern_check` | AXIS pattern sink/checker | [page](axis4_slave_pattern_check.md) |
| `axi_bus_meter` | Always-on AXI bandwidth/beat/burst meter | [page](axi_bus_meter.md) |
| `axis_bus_meter` | AXIS variant of the bus meter | [page](axis_bus_meter.md) |
| `axi_perf_latency_hist` | Log2 latency histogram, one per metric (channels share it) | [page](axi_perf_latency_hist.md) |
| `axi_master_rd_splitter` | Boundary-crossing read splitter (RLAST consolidated to one per original burst) | [page](axi_master_rd_splitter.md) |
| `axi_master_wr_splitter` | Boundary-crossing write splitter with B consolidation | [page](axi_master_wr_splitter.md) |
| `axi_split_combi` | Pure combinational split decision used by both splitters | [page](axi_split_combi.md) |
| `sdpram_core` | BRAM glue + clear FSM backend of the slave family | [page](sdpram_core.md) |
| `sdpram_slave_axi4_axi4` / `_axi4_axil` / `_axil_axi4` / `_axil_axil` | Protocol-shaped wrappers over `sdpram_core` | [family page](sdpram_slave.md) |
| `axi_gen_addr` | AXI burst next-address generation (FIXED/INCR/WRAP) | [page](axi_gen_addr.md) |
| `amba_clock_gate_ctrl` | AMBA-side wrapper over `clock_gate_ctrl` (`clk_out`/`gating`/`idle` — no cycle counter) | [page](amba_clock_gate_ctrl.md) |

The `_cg` clock-gated wrapper pattern is described in
[clock_gated_variants.md](clock_gated_variants.md), and the per-module
inventory with RTL-extracted notes is
[DOCUMENTATION_STATUS.md](DOCUMENTATION_STATUS.md).

## What is NOT here

- **CDC.** `cdc_2_phase_handshake`, `cdc_4_phase_handshake`, `cdc_open_loop` and `cdc_synchronizer` live in `rtl/cdc/`, documented in the [rtl-cdc book](../../rtl-cdc/overview.md). Nothing in this directory documents them anymore.
- **Monitor internals.** `monbus_arbiter`, `monbus_group_core`, `monbus_compressor` and the monitor taps live in `rtl/amba/monitor/`, documented under [../monitor/](../monitor/monbus_group.md). One width fact worth pinning because the old copy here got it wrong twice: the monitor packet is **128 bits** with a **64-bit side-band timestamp** (192 bits per client through the arbiter skids).

## Known sharp edges

Recorded here because more than one page used to contradict them:

- The splitter defect cluster (intermediate RLASTs passing upstream, silent split-FIFO record drops, the write splitter's B consolidation missing the final split's error) is FIXED and closed in `vault/Tasks/amba`: RLAST is consolidated to one per original transaction, a full FIFO sets the sticky `o_split_fifo_overflow` output, and the final split's error folds into the consolidated BRESP. A generic AXI master can sit upstream of either splitter directly; both serialize acceptance (one outstanding transaction at a time) — the read side fences on its owed-beat RLAST counter, the write side on open response consolidation.
- The interface observer produces no monbus traffic at its documented parameter defaults — the `TAP_ENABLE_*` parameters gate the tap logic off and perf packets are disabled; override them to get the dump path. It now lives at `projects/components/misc/rtl/axi4_intf_master_observer.sv`; the `axi4_dma_observer` copy that used to sit here was retired 2026-08-14 (see below).
- `o_cfg_done_clear` on the sdpram family is a sticky level, not a pulse.

## Testing

Every module here is covered from `val/amba/` (the characterization masters carry an independent software CRC cross-check in their TBs). Run the area with `make -C val/amba clean-all && make -C val/amba run-all-func-parallel`.

## Navigation

[Back to rtl-amba index](../index.md) · [Monitor infrastructure](../monitor/monbus_group.md) · [rtl-cdc book](../../rtl-cdc/overview.md)
