# STREAM DMA — Area Characterization

Resource (area) numbers for the STREAM scatter-gather DMA, for apples-to-apples
comparison against other SG-DMA cores (vendor / open-source).

- **Target:** Xilinx Artix-7 `xc7a100tcsg324-1` (Nexys A7-100T)
- **Tool:** Vivado 2025.1
- **Config:** 8 channels, 128-bit datapath, 32-bit address, `SRAM_DEPTH=256`,
  `AR/AW_MAX_OUTSTANDING=8`, CDC disabled (pclk = aclk). Matches the as-built
  characterization bitstream (`stream_char_top.sv`).
- **Monitors:** OFF. `stream_top_ch8` defaults to `USE_AXI_MONITORS=0`, so the
  descriptor AXI monitor and MonBus group are not instantiated. The monitors are
  an opt-in observability layer, not part of the datapath, so they are excluded
  from the comparison number.

## Methodology

The headline number is an **out-of-context (OOC) synthesis of `stream_top_ch8`
alone** — no characterization harness (UART bridge, CSR block, `axi4_dma_observer`,
response-delay model, trace SRAM). That scaffolding is measurement-only and is not
part of the DMA.

```bash
cd projects/NexysA7/stream_characterization/flows-stream-bridge
make area                       # -> reports/utilization_area_8ch_dw128_sd256.txt
# sweep a config (each writes its own report file, never clobbered):
AREA_NUM_CHANNELS=4 make area    # -> reports/utilization_area_4ch_dw128_sd256.txt
AREA_DATA_WIDTH=256 make area
AREA_SRAM_DEPTH=512 make area
```

Flow: `flows-stream-bridge/tcl/synth_area_dma.tcl` (OOC synth + flat and
hierarchical `report_utilization`). Raw reports live in
`flows-stream-bridge/reports/utilization_area_<tag>.txt`.

## Results

### Bare DMA, OOC (8ch / dw128 / sd256, monitors off) — 2026-06-24

| Resource             | Used   | Available | Util % |
|----------------------|-------:|----------:|-------:|
| Slice LUTs           | 15,667 |    63,400 | 24.7%  |
| — LUT as Logic       | 13,891 |    63,400 | 21.9%  |
| — LUT as Memory      |  1,776 |    19,000 |  9.3%  |
| Slice Registers (FF) | 10,603 |   126,800 |  8.4%  |
| F7 Muxes             |    312 |    31,700 |  1.0%  |
| F8 Muxes             |      4 |    15,850 |  0.0%  |
| Block RAM Tile       |   16.5 |       135 | 12.2%  |
| DSPs                 |      0 |       240 |  0.0%  |

BRAM detail: 16× RAMB36 + 1× RAMB18.

### Where the area goes (OOC hierarchy)

| Instance | Module | Total LUTs | FFs | BRAM |
|---|---|---:|---:|---:|
| `stream_top_ch8` | (top) | 15,667 | 10,603 | 16.5 |
| `u_stream_core` | stream_core | 13,553 | 9,217 | 16.5 |
| `u_scheduler_group_array` | scheduler_group_array (8× groups) | 8,712 | 5,825 | 0 |
| `u_axi_write_engine` | axi_write_engine | 846 | 632 | 0 |
| `u_rd_axi_skid` | axi4_master_rd (datapath AXI master) | 632 | 636 | 0 |
| `u_perf_profiler` | perf_profiler | 205 | 316 | 1× RAMB18 |
| `u_axi_read_engine` | axi_read_engine | 247 | 168 | 0 |
| `g_apb_passthrough.u_apb_slave` | apb_slave | 236 | 207 | 0 |

The scheduler/descriptor groups (one per channel) dominate at ~8.7k LUTs / 5.8k FF;
the bulk of the BRAM is the per-channel SRAM datapath inside `stream_core`.

### In-context cross-check (full bitstream, post-route) — 2026-06-24

From the as-built `stream_char_top` bitstream (`make bitstream`, timing met,
0 errors). Source: `reports/utilization_impl.txt` (flat, post-route physopt) and
`reports/utilization_hier_asbuilt.txt` (hierarchy off the routed checkpoint).

| Scope | Total LUTs | FFs | BRAM | Notes |
|---|---:|---:|---:|---|
| `stream_char_top` (whole platform) | 48,714 | 40,819 | 10.5 | 76.8% LUT util on the 100T |
| `u_harness` | 48,672 | 40,727 | 10.5 | DMA + observer + CSR + UART + trace + delay model |
| `u_stream` = `stream_top_ch8` | 21,527 | 20,855 | 8.5 | **monitors ON** here (`USE_AXI_MONITORS=1` for the perf measurement) |
| OOC bare DMA (above) | 15,667 | 10,603 | 16.5 | **monitors OFF**, post-synth |

**Read this carefully — the two `stream_top_ch8` numbers are not the same build:**

- The in-context `u_stream` (21.5k LUTs / 20.9k FF) is the **instrumented** DMA:
  the characterization bitstream turns the descriptor AXI monitor + MonBus group
  ON so it can measure the datapath. The ~5.9k-LUT / ~10.3k-FF gap over the OOC
  bare DMA is essentially the monitor/MonBus cost.
- The **OOC bare DMA (15,667 LUTs) is the apples-to-apples SG-DMA comparison
  number** — monitors compiled out.
- Methodology caveat: OOC is post-**synth**; the in-context figures are
  post-**route** (after `phys_opt`). The BRAM difference (16.5 OOC vs 8.5 impl)
  is a synth-estimate-vs-post-route-packing artifact, not a real datapath
  difference — both use `SRAM_DEPTH=256`. For a fully like-for-like number, run
  the OOC config through implementation as well; post-synth utilization is the
  standard area proxy and is sufficient for core-vs-core comparison.
