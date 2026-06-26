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
- **Monitor CSRs:** read-as-zero. With monitors compiled out, their config/status
  registers are dead, but the PeakRDL block + cmd/rsp adapter still pay for their
  write storage, write-decode, and read-mux entries. The area flow regenerates a
  read-as-zero variant of `stream_regs` (`make regen-regs-nomon` → `sw=r`,
  address map byte-identical) and synthesizes against it, removing that dead CSR
  logic. Saves a **flat ~830–890 LUTs at every channel count** (the register
  block is channel-count independent). See `flows-stream-bridge/Makefile` and
  `projects/components/stream/bin/rdl_monitors_ro.py`.

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

### Bare DMA, OOC (8ch / dw128 / sd256, monitors off + RO CSRs) — 2026-06-26

Monitors fully off: `USE_AXI_MONITORS=0` (removes the data **and** descriptor AXI
monitors — base + transaction CAM + reporters) and `GEN_MON=0` (drops the
per-channel MonBus emitters), **plus the read-as-zero monitor CSRs** (see the
"Monitor CSRs" note above). Numbers below supersede the earlier monitors-off
figures that still carried the dead monitor register storage.

| Resource             | Used   | Available | Util % |
|----------------------|-------:|----------:|-------:|
| Slice LUTs           | 14,119 |    63,400 | 22.3%  |
| — LUT as Logic       | 12,343 |    63,400 | 19.5%  |
| — LUT as Memory      |  1,776 |    19,000 |  9.3%  |
| Slice Registers (FF) |  9,302 |   126,800 |  7.3%  |
| Block RAM Tile       |   16.5 |       135 | 12.2%  |
| DSPs                 |      0 |       240 |  0.0%  |

BRAM detail: 16× RAMB36 + 1× RAMB18.

### Where the area goes (OOC hierarchy, 8ch)

| Instance | Module | Total LUTs | FFs | BRAM |
|---|---|---:|---:|---:|
| `stream_top_ch8` | (top) | 14,119 | 9,302 | 16.5 |
| `u_stream_core` | stream_core | 12,805 | 8,367 | 16.5 |
| `u_scheduler_group_array` | scheduler_group_array (8× groups + shared desc fetch) | 8,127 | 5,280 | 0 |
| `u_axi_write_engine` | axi_write_engine | 846 | 632 | 0 |
| `u_rd_axi_skid` | axi4_master_rd (datapath AXI master) | 632 | 636 | 0 |
| `u_peakrdl_adapter` | peakrdl_to_cmdrsp (CSR read-mux + decode) | 558 | 81 | 0 |
| `u_axi_read_engine` | axi_read_engine | 247 | 168 | 0 |
| `g_apb_passthrough.u_apb_slave` | apb_slave | 236 | 207 | 0 |

The scheduler/descriptor groups (one per channel) dominate at ~8.1k LUTs / 5.3k FF;
the bulk of the BRAM is the per-channel SRAM datapath inside `stream_core`. The
read-as-zero CSRs land squarely in `u_peakrdl_adapter`: its read-mux over the now
constant-zero monitor readback entries collapses from **1,223 → 558 LUTs**, which
is most of the per-build saving; making `PERF_CONFIG` read-as-zero also prunes
the perf profiler down to a negligible stub.

### Channel scaling (OOC, monitors off + RO CSRs, dw128 / sd256) — 2026-06-26

Physical channel count swept via `AREA_NUM_CHANNELS` (datapath width and SRAM
depth held constant), so only the per-channel slices vary. All four rows use the
read-as-zero monitor CSRs (single methodology).

| Channels | Slice LUTs | — Logic | — Memory | Slice FFs | BRAM Tile |
|---------:|-----------:|--------:|---------:|----------:|----------:|
| 1        |      3,905 |   3,673 |      232 |     3,448 |       2.5 |
| 2        |      5,635 |   5,183 |      452 |     4,308 |       4.5 |
| 4        |      8,253 |   7,359 |      894 |     5,984 |       8.5 |
| 8        |     14,119 |  12,343 |    1,776 |     9,302 |      16.5 |

Scaling is close to linear: a fixed base (APB/CSR + shared control + shared desc
fetch) of **~2.45k LUTs** plus **~1.46k LUTs, ~840 FFs, and ~2 BRAM tiles per
channel** (the scheduler / descriptor group + per-channel SRAM datapath). BRAM
tracks the channel count exactly — one 256-deep × 128-bit SRAM tile pair per
channel. The read-as-zero CSRs cut a flat ~830–890 LUTs from every row versus the
earlier monitors-off figures (e.g. 8ch 14,965 → 14,119, 1ch 4,797 → 3,905), as
expected for a channel-count-independent register block.

`NUM_CHANNELS=1` synthesizes **and passes functional verification**
(3,905 LUTs / 3,448 FF / 2.5 BRAM). Enabling it took two changes plus a latent
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
is byte-identical before and after (the single-client path isn't elaborated at
N>1). A 1-channel STREAM is somewhat academic: the
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
| OOC bare DMA (above) | 14,119 | 9,302 | 16.5 | **monitors OFF + RO CSRs**, post-synth |

**Read this carefully — the two `stream_top_ch8` numbers are not the same build:**

- The in-context `u_stream` (21.5k LUTs / 20.9k FF) is the **instrumented** DMA:
  the characterization bitstream turns the descriptor AXI monitor + MonBus group
  ON so it can measure the datapath. The ~7.4k-LUT / ~11.6k-FF gap over the OOC
  bare DMA is the full observability cost — monitor/MonBus logic **plus** the
  monitor CSR storage/decode/read-mux (the latter is the read-as-zero saving).
- The **OOC bare DMA (14,119 LUTs) is the apples-to-apples SG-DMA comparison
  number** — monitors compiled out, monitor CSRs read-as-zero.
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
| **STREAM** (`stream_top_ch8`, monitors off + RO CSRs) | 3,905 | 3,448 | 2.5 |
| iDMA (backend + desc64) | 3,869 | 5,685 | 0 |

**At one channel the two are at parity.** STREAM is 3,905 LUTs vs iDMA's 3,869 —
a **+36 LUT (+0.9%) gap**, within synthesis noise. (Before the monitor CSRs were
made read-as-zero, STREAM 1ch was 4,797 LUTs / 24% larger; removing the dead
monitor register logic closed essentially all of that gap.) STREAM is also
**leaner in FFs** (3,448 vs 5,685 — desc64's prefetch FIFOs are FF-heavy), and
the LUT slopes tilt decisively toward STREAM with scale — see next.

### STREAM vs iDMA at 8 channels

STREAM shares its read/write engines across all 8 channels and buffers per
channel in BRAM. An 8-channel iDMA system is 8 independent engines plus a mux
to share the memory port:

| Design (8 channels, dw128) | LUTs | FFs | BRAM |
|---|---:|---:|---:|
| **STREAM** (`stream_top_ch8`, monitors off + RO CSRs) | **14,119** | **9,302** | **16.5** |
| iDMA: 8×(backend+desc64) + 8→1 mux | 31,368 | 45,691 | 0 |
| ratio (iDMA / STREAM) | **2.2×** | **4.9×** | — |

**STREAM is ~2.2× denser in LUTs and ~4.9× in FFs at 8 channels**, trading ~16.5
BRAM tiles (its per-channel SRAM reorder buffers) for the savings. This is the
shared-engine + BRAM-buffered architecture paying off: iDMA replicates the full
read/write/legalize datapath per channel and uses no BRAM, so eight of them cost
far more logic.

### The crossover

| Channels | STREAM LUTs | iDMA LUTs (N×3,869 + mux) | winner |
|---------:|------------:|--------------------------:|:------|
| 1 | 3,905 | 3,869 | tie (iDMA +36) |
| 2 | 5,635 | ~7,940 | STREAM |
| 4 | 8,253 | ~15,700 | STREAM |
| 8 | 14,119 | 31,368 | STREAM |

STREAM scales as **~2.45k base + ~1.46k LUTs/channel**; iDMA scales as
**~3.87k LUTs/channel** (plus a small shared mux). With the dead monitor CSRs
removed the lines now cross **right at 1 channel** (~N≈1.0): the single-channel
point is a dead heat, and at two channels and up STREAM's shared engines +
amortized base pull decisively ahead, the gap widening with channel count.
STREAM is built for the multi-channel regime it targets, and there it is the
denser design by a wide margin.

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
being ~2.2× denser at 8 channels and at LUT parity by one channel (above). Open axes: desc64 frontend (end-to-end /
descriptor-fetch overhead), net mem-to-mem throughput (internal datapath
sharing), and bit-exact memory via STREAM's RTL slaves. Detail + caveats in
`../flows-idma-bridge/README.md`.
