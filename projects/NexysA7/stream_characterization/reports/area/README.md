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

### Channel scaling (OOC, monitors off, dw128 / sd256) — 2026-06-24

Physical channel count swept via `AREA_NUM_CHANNELS` (datapath width and SRAM
depth held constant), so only the per-channel slices vary.

| Channels | Slice LUTs | — Logic | — Memory | Slice FFs | BRAM Tile |
|---------:|-----------:|--------:|---------:|----------:|----------:|
| 2        |      6,948 |   6,496 |      452 |     5,403 |       4.5 |
| 4        |     10,010 |   9,116 |      894 |     7,143 |       8.5 |
| 8        |     15,667 |  13,891 |    1,776 |    10,603 |      16.5 |

Scaling is close to linear: a fixed base (APB/CSR + shared control) of ~4.0k LUTs
plus **~1.45k LUTs, ~870 FFs, and ~2 BRAM tiles per channel** (the scheduler /
descriptor group + per-channel SRAM datapath). BRAM tracks the channel count
exactly — one 256-deep × 128-bit SRAM tile pair per channel.

`NUM_CHANNELS=1` now synthesizes **and passes functional verification**
(5,586 LUTs / 4,510 FF / 2.5 BRAM). Enabling it took two changes plus a latent
bug fix:

1. **Width guards.** `$clog2(1)=0` underflowed channel-ID part-selects to
   `[-1:0]`; guarded with `(NUM_CHANNELS > 1) ? $clog2(NUM_CHANNELS) : 1`.
2. **Single-client arbiter (`rtl/common/arbiter_single_client.sv`).** The
   descriptor-AR/read/write paths substitute a single-client grant when
   `NUM_CHANNELS==1` (the round-robin arbiter underflows at `CLIENTS==1`). The
   pre-existing substitute was a *combinational* passthrough (`grant=request`),
   which does **not** reproduce the arbiter's registered, ack-held grant timing
   — it injected a bubble beat at every write-burst boundary, corrupting any
   transfer longer than one burst. This was a latent 1-channel datapath bug,
   never caught because the top-level never built at 1 channel. The new module
   is the "req/grant + hold-for-ack" equivalent and reproduces the arbiter's
   `WAIT_GNT_ACK` lifecycle exactly. Caught by the `nc01` long tests in
   `test_stream_top.py` (multi-descriptor, multi-burst); verified fixed.

The change is a **verified no-op for `NUM_CHANNELS > 1`** — the 8-channel build
is byte-identical (15,667 / 10,603 / 16.5) before and after (the single-client
path isn't elaborated at N>1). A 1-channel STREAM is somewhat academic: the
production build is 8-channel and runs single-channel workloads by enabling one
channel at runtime via `cfg_channel_enable` (how the "1 channel" perf runs were
measured). The 1-channel *build* exists for the iDMA parity comparison.

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

---

## Open-source comparison: PULP iDMA — 2026-06-24

Best-in-class open-source SG-DMA (github.com/pulp-platform/iDMA, used in
Snitch/Occamy/Iguana silicon), OOC on the same `xc7a100t`, same datapath config
(128-bit data, 32-bit addr, 8 outstanding). Flow + reproduction:
`../flows-idma-bridge/` (`make setup && make area`). iDMA is single-channel per
engine, so we synthesize its pieces and compose them.

### iDMA component areas (OOC, dw128)

| Component | LUTs | FFs | BRAM | Role |
|---|---:|---:|---:|---|
| `idma_backend_synth_rw_axi` | 2,186 | 2,223 | 0 | mem-to-mem AXI datapath |
| `idma_desc64_synth` (+reg CSR) | 1,683 | 3,462 | 0 | descriptor-chain SG frontend |
| **one SG channel** (backend + desc64) | **3,869** | **5,685** | **0** | full single-channel SG DMA |
| `axi_mux_intf` 8→1 | 416 | 211 | 0 | shared-memory-port arbiter |

### STREAM vs iDMA at 1 channel (true parity)

The maximally apples-to-apples point: one channel, both complete single-channel
SG DMAs (descriptor fetch + read + write + config), same width/outstanding/part.
STREAM at `NUM_CHANNELS=1` is a real synthesis (see "1-channel build" note
below).

| Design (1 channel, dw128) | LUTs | FFs | BRAM |
|---|---:|---:|---:|
| **STREAM** (`stream_top_ch8`, monitors off) | 5,586 | 4,510 | 2.5 |
| iDMA (backend + desc64) | 3,869 | 5,685 | 0 |

**The architectures cross over.** At one channel iDMA is leaner in LUTs (3,869 vs
5,581): STREAM still pays for its multi-channel machinery (shared scheduler
infrastructure, APB CSR, an SRAM tile) that a single channel can't amortize.
STREAM is denser in FFs and spends 2.5 BRAM where iDMA spends none. But the
slopes invert with scale — see next.

### STREAM vs iDMA at 8 channels

STREAM shares its read/write engines across all 8 channels and buffers per
channel in BRAM. An 8-channel iDMA system is 8 independent engines plus a mux
to share the memory port:

| Design (8 channels, dw128) | LUTs | FFs | BRAM |
|---|---:|---:|---:|
| **STREAM** (`stream_top_ch8`, monitors off) | **15,667** | **10,603** | **16.5** |
| iDMA: 8×(backend+desc64) + 8→1 mux | 31,368 | 45,691 | 0 |
| ratio (iDMA / STREAM) | **2.0×** | **4.3×** | — |

**STREAM is ~2× denser in LUTs and ~4× in FFs at 8 channels**, trading ~16.5
BRAM tiles (its per-channel SRAM reorder buffers) for the savings. This is the
shared-engine + BRAM-buffered architecture paying off: iDMA replicates the full
read/write/legalize datapath per channel and uses no BRAM, so eight of them cost
far more logic.

### The crossover

| Channels | STREAM LUTs | iDMA LUTs (N×3,869 + mux) | winner |
|---------:|------------:|--------------------------:|:------|
| 1 | 5,586 | 3,869 | iDMA |
| 2 | 6,948 | ~7,940 | STREAM |
| 4 | 10,010 | ~15,700 | STREAM |
| 8 | 15,667 | 31,368 | STREAM |

STREAM scales as **~4.1k base + ~1.44k LUTs/channel**; iDMA scales as
**~3.87k LUTs/channel** (plus a small shared mux). The lines cross just above
**1 channel** (~N≈1.7): below it iDMA's lean single engine wins; at two channels
and up STREAM's shared engines + amortized base pull decisively ahead, and the
gap widens with channel count. STREAM is built for the multi-channel regime it
targets, and there it is the denser design by a wide margin.

### Methodology caveats (important — the comparison is not single-axis)

- **Not iso-throughput.** 8× iDMA = eight *independent, full-rate* engines (up to
  8× the aggregate memory bandwidth if the fabric allows). STREAM's 8 channels
  *share* one arbitrated datapath (one channel's bandwidth, time-sliced). If you
  only need one shared datapath behind 8 logical channels (STREAM's model), the
  fair iDMA build is **one** backend + a multi-channel frontend (iDMA `reg`/ND
  midend, not 8× desc64) — far smaller than 8 engines, and the closer
  architectural match. That config is not yet built here.
- **Component sum.** The 1-channel "3,869" sums two separately-synthesized
  wrappers; cross-boundary optimization between frontend and backend is not
  captured (minor).
- **iDMA 0 BRAM** is real: its backend is a register/LUT dataflow with shallow
  buffering. STREAM spends BRAM deliberately for bubble-free multi-channel
  switching (see the perf report's 100% datapath-utilization result).
- Both are post-synth OOC; same proxy, same part.

### Perf comparison (datapath) — see `../flows-idma-bridge/`

A cocotb cosim (`make perf` in flows-idma-bridge) drives the iDMA backend and
measures AXI bus utilization the same way STREAM's `axi4_dma_observer` does.
Config matched to STREAM's §5 (16-beat bursts, 8 outstanding → 128-beat
in-flight window). **On the datapath axis the two engines are equivalent:**

| memory latency (cyc) | iDMA backend | STREAM §5 (1ch) |
|---:|---:|---:|
| 0   | 100.0% | 100% |
| 128 | 88.6%  | 82%  |
| 256 | 47.7%  | 45%  |
| 512 | 24.8%  | 24%  |

Both track Little's Law `min(1, in-flight/L)`; the full burst×latency BDP surface
matches `min(1, 8·burst/L)` cell-for-cell. One-direction bus throughput at
saturation is 1600 MB/s (iDMA) vs STREAM's 1526 MB/s ceiling. So **STREAM does
not lag best-in-class open source on datapath efficiency — it matches it**, while
being ~2× denser at 8 channels (above). Open axes: desc64 frontend (end-to-end /
descriptor-fetch overhead), net mem-to-mem throughput (internal datapath
sharing), and bit-exact memory via STREAM's RTL slaves. Detail + caveats in
`../flows-idma-bridge/README.md`.
