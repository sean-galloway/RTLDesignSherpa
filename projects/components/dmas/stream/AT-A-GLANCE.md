# STREAM — at a glance

An 8-channel memory-to-memory DMA engine. One index page: every feature
area, 1-3 bullets each, so you can find the right file without reading the
tree.

Depth lives elsewhere and is linked per section — this page is a map, not a
second copy. Authority order: `/GLOBAL_REQUIREMENTS.md` > the handbook
(`vault/handbook/INDEX.md`) > `PRD.md` and the HAS/MAS specs > this page.

---

## The shape of it

`stream_top_ch8` -> `stream_core` -> per-channel scheduler groups + shared
data path:

    APB/CSR ──> stream_config_block ──┐
                                      v
    descriptors ──> scheduler_group_array (8x: scheduler + descriptor_engine)
                                      │
                        ┌─────────────┴─────────────┐
                        v                           v
                  axi_read_engine ──> sram_controller ──> axi_write_engine
                        │              (per-channel FIFOs)        │
                        └──────────> AXI4 master ports <──────────┘

* **8 channels, 512-bit data path, 64-bit addresses** (`NUM_CHANNELS=8`,
  `DATA_WIDTH=512`, `SRAM_DEPTH=4096` on `stream_top_ch8`).
* **No FSMs in the data path.** Streaming pipelines with valid/ready
  handshakes end to end; backpressure propagates rather than being managed.
* Read and write engines arbitrate across channels **space-aware** — a
  channel only competes when its SRAM side can actually take/supply data.

---

## Channel control (`rtl/macro/scheduler_group*.sv`)

* **`scheduler`** — the per-channel memory-to-memory DMA core: consumes a
  descriptor, walks the transfer, and drives the read/write engine requests.
* **`descriptor_engine`** — autonomous descriptor fetch with **chaining**, so
  a channel can run a linked list without host intervention. Prefetch and
  FIFO threshold are configurable.
* **`scheduler_group`** = scheduler + descriptor_engine + `monbus_arbiter`;
  **`scheduler_group_array`** instantiates 8 of them and shares the
  downstream resources.

## Data path (`rtl/fub/`)

* **`axi_read_engine` / `axi_write_engine`** — multi-channel AXI4 masters
  with space-aware arbitration. The write engine's SRAM drain is tied to the
  actual `m_axi_wvalid && m_axi_wready` handshake (decoupling it caused a
  lost-WLAST deadlock).
* **`sram_controller` + `sram_controller_unit`** — per-channel buffering
  built on the shared `gaxi_fifo_sync` primitive, with
  **`stream_latency_bridge`** (latency-1 skid) between stages.
* **`stream_alloc_ctrl` / `stream_drain_ctrl`** — virtual FIFOs that track
  space and occupancy WITHOUT carrying data, so the engines can arbitrate on
  credit rather than on the buffer itself.

## Addressing (`rtl/fub/stream_run_addr_gen.sv`)

* Wraps one `dma_address_gen` plus a base FIFO, producing the address
  sequence the scheduler consumes. Gated by
  `USE_ROW_COL_MAJOR_ADDRESSING`.
* **RUN-CONTIGUOUS** (`per_beat=0`, `stride_0 == beat_size`): transfers are
  runs of `inner_count` contiguous beats; the AXI engine bursts within a run.
  Covers linear, 2D-tiled contiguous, circular and reverse copies.
* **Per-beat / transpose** modes key off `stride_0`, for strided and
  row/column-major traversal.

## Top level (`rtl/top/`)

* **`stream_top_ch8`** — the deliverable: `stream_core` + `stream_regs`
  (PeakRDL) + `apb4_slave` (+ CDC) + `peakrdl_to_cmdrsp` + `cmdrsp_router`
  + `monbus_axil4_axil4_group`.
* **`stream_config_block`** — maps PeakRDL register outputs onto the core's
  configuration inputs, so the CSR layout and the core stay decoupled.
* **`cmdrsp_router`** — address-based routing of CMD/RSP transactions.

---

## Observability

* **Always-on cheap meters.** `axi_bus_meter` buckets every cycle
  (productive / backpressure / starvation / idle) and the beat/byte/burst
  counters run regardless of `USE_AXI_MONITORS` — the RTL says so at
  `stream_core.sv:1881` ("MUST survive USE_AXI_MONITORS=0"). Over-gating
  these was a real cause of zero perf readings.
* **Gated heavy monitors.** `axi4_master_rd_mon` / `axi4_master_wr_mon` and
  `axi_perf_latency_hist` sit behind `USE_AXI_MONITORS`; their packets are
  arbitrated onto the monitor bus by `monbus_arbiter`.
* **`perf_profiler`** per channel, and `monbus_axil4_axil4_group` at the top
  to drain monitor packets to SRAM / AXIL for the host.

## Verification (`dv/`)

Practice: `vault/handbook/dv/`.

* **Tiers** — `dv/tests/fub` (8 files), `dv/tests/macro` (6),
  `dv/tests/top` (7). 11 TB classes in `dv/tbclasses/`.
  (`dv/tests/performance_tests/` currently holds no tests.)
* **Pattern B throughout** (`projects/components/` rule): cocotb functions
  prefixed `cocotb_test_*` so pytest does not collect them, with thin pytest
  wrappers selecting one via `testcase=`.
* **`datapath_rd_test` / `datapath_wr_test`** — macro harnesses that stand up
  8 scheduler instances against one data-path direction, for isolating
  engine behaviour without the full top.

## Registers and docs

* **`regs/`** — PeakRDL-generated (`stream_regs`), with `stream_regs.vlt`
  waivers. Regenerate ONLY via `bin/peakrdl_generate.py`; DV accesses
  registers **by name** through the generated regmap, never by offset.
  Monitor registers live at 0x1000 in a separate `include`d regfile under
  one APB slave.
* **`docs/`** — HAS and MAS specs (latest v0.95 / v0.96, docx+pdf) built by
  `generate_has_pdf.sh` / `generate_mas_pdf.sh`, plus the mermaid->png
  diagram pipeline and the signal-contracts workbook generator.
* **`known_issues/`** — issue pages with `resolved/` kept for history.
  `TASKS.md` holds the local work list; cross-area work is in
  `vault/Tasks/`.

## Status

* Runs on the Genesys 2 (8 channels, ~99.8-100% utilization at 6.4 GB/s) and
  the Nexys A7 characterization flow.
* Known open behaviours are tracked in `known_issues/` and `TASKS.md` —
  including high-channel-count board timeouts that cosim does not reproduce.
