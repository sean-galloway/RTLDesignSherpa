# flows-idma-bridge

OOC **area** characterization flow for **PULP iDMA** (github.com/pulp-platform/iDMA,
Solderpad SHL-0.51), the best-in-class open-source scatter-gather DMA, for an
apples-to-apples comparison against STREAM. Parallel to `flows-stream-bridge`
(in-house) and `flows-vivado-mcdma` (AMD vendor IP). Results land in
`../reports/area/README.md`.

## Status: AREA-ONLY

This flow produces (a) out-of-context synthesis **area** (LUT/FF/BRAM) on the
`xc7a100tcsg324-1`, matching STREAM's `make area` methodology, and (b) a cocotb
**datapath-perf** cosim of the iDMA backend (`make perf`). FPGA bring-up (driving
iDMA on the board through the full characterization harness) is still future work.

## Toolchain (all gitignored, reproduced by `make setup`)

- **iDMA** pinned to `3c0cc3f`; dependencies resolved by **Bender** v0.32.0
  (`bender update` from the checked-in `Bender.lock`).
- iDMA RTL is **generated** (it ships templates, not flat RTL): the `mario`
  Python generator (mako/pyyaml/hjson) emits the `rw_axi` backend; the OpenTitan
  `regtool` (reggen: tabulate/mistletoe) emits the `desc64` register file. No
  morty needed.
- Python deps install into the repo venv.

## Usage

```bash
make setup    # clone iDMA + deps, fetch bender, install python deps (idempotent)
make area     # generate RTL + filelists, OOC-synth backend/desc64/mux, print summary
make perf     # cocotb cosim: iDMA backend datapath util vs memory-latency sweep
```

## Datapath perf cosim (`make perf`)

`dv/test_idma_backend_perf.py` drives the `idma_backend_synth_rw_axi` 1D request
interface directly (src, dst, length) and serves its AXI4 manager from a cocotb
memory model, measuring bus utilization the same way the STREAM `axi4_dma_observer`
does — `productive_beats / (last_beat_cycle - first_beat_cycle + 1)`. This
isolates the datapath (the headline util/throughput axis) without the desc64/reg
frontend. Knobs: `IDMA_XFER_BEATS`, `IDMA_RESP_DELAY` (memory latency),
`IDMA_MAX_LLEN` (AXI burst cap).

### Datapath util vs memory latency — matched to STREAM §5

Config matched to STREAM's §5 chan×delay (1 channel): **16-beat bursts**
(`max_llen=4`, `reduce_len=1`), **8 outstanding** → a **128-beat in-flight
window**, 4096-beat transfer. The cocotb memory imposes latency as an
overlapping per-response pipe (data ready at `arrival + L`), the same
Little's-Law model as STREAM's `axi_response_delay`.

| memory latency (cyc) | iDMA backend | STREAM §5 (1ch) | ideal `min(1,128/L)` |
|---:|---:|---:|---:|
| 0   | **100.0%** | 100% | 100% |
| 128 | 88.6%      | 82%  | 100% |
| 256 | 47.7%      | 45%  | 50%  |
| 512 | 24.8%      | 24%  | 25%  |

**The curves overlay.** Both track Little's Law with the same 128-beat window:
iDMA and STREAM are within a few points everywhere, and nearly identical at
256/512 cyc. The one visible gap is at 128 cyc (iDMA 88.6% vs STREAM 82%) — right
at the knee, where STREAM pays a bit more AR-issue overhead so its effective
in-flight is slightly below 128; the idealized cosim sits closer to the
theoretical knee. Net: **on the datapath axis the two engines are
equivalent** — both saturate the bus when latency is hidden and degrade per
Little's Law when it isn't.

**Throughput.** At full saturation each direction sustains **1600 MB/s**
(16 B/beat × 100 MHz) on the AXI manager — matching STREAM's 1526 MB/s
one-direction bus ceiling (STREAM's is a touch lower from AR-issue overhead).
The AR/R and AW/W channels are independent, so read and write each hit line
rate. *Net* mem-to-mem throughput additionally depends on each design's internal
read/write datapath sharing (STREAM's shared 128-bit SRAM path vs iDMA's
dataflow buffer) — a separate axis the cocotb memory here does not model (it
serves R and W independently), so only the one-direction bus rate is compared.

### BDP surface — util vs (burst size × memory latency)

Sweeping burst size (`max_llen`) and latency together maps the whole
bandwidth-delay-product surface. The in-flight window is `8 × burst` beats; util
tracks `min(1, in_flight / L)` across the board (2048-beat transfer):

| burst (in-flight) | L=0 | L=128 | L=256 | L=512 |
|---|---:|---:|---:|---:|
| 4 beats (32)  | 100% | 24.3% | 12.4% |  6.3% |
| 8 beats (64)  | 100% | 47.5% | 24.7% | 12.6% |
| 16 beats (128)| 100% | 88.9% | 48.5% | 25.4% |
| 32 beats (256)| 100% | 100%  | 89.9% | 50.3% |

Every cell matches `min(1, 8·burst / L)` within noise, and the knee marches right
as burst grows — doubling the burst doubles the latency the engine can hide. This
is exactly STREAM's §5 result: iDMA's datapath util is governed by
`in-flight = outstanding × burst` vs memory latency, the same Little's-Law
physics. (`make perf` runs the latency column at 16-beat bursts; sweep
`IDMA_MAX_LLEN`/`IDMA_RESP_DELAY` for the full surface.)

**Remaining caveats:**

- Backend only (no desc64 frontend), single channel — those are separate axes
  (descriptor-fetch startup overhead, multi-channel density).
- The memory is an idealized cocotb latency pipe, not STREAM's RTL
  `pattern_gen`/`crc_check` slaves, and data isn't CRC-checked here. For
  bit-exact memory + measurement parity (and data verification), wire iDMA's
  manager through STREAM's RTL slaves + the real `axi4_dma_observer` in a
  harness. The delay model and in-flight window are now matched, so the curve
  above is directly comparable.

Individual targets: `make gen`, `make area-backend`, `make area-desc64`,
`make area-mux`. Reports: `reports/idma_area_<tag>.txt`.

## What is synthesized

iDMA is single-channel per engine; STREAM is multi-channel. To compare we
synthesize the iDMA pieces separately and compose them:

| Top | Role | Comparable STREAM part |
|---|---|---|
| `idma_backend_synth_rw_axi` | mem-to-mem AXI datapath (legalizer + transport + read/write) | read/write engines + dataflow |
| `idma_desc64_synth` | descriptor-chain SG frontend + reg CSR | descriptor_engine + scheduler + APB |
| `axi_mux_intf` (8→1) | shared-memory-port arbiter for N engines | internal channel arbiter |

Config pinned to STREAM's FPGA datapath: `DataWidth=128`, `AddrWidth=32`,
`NumAxInFlight=8` (≈ `AR_MAX_OUTSTANDING`).

See `../reports/area/README.md` for the numbers, the composition into 1- and
8-channel systems, and the methodology caveats (8× independent engines vs
STREAM's shared, BRAM-buffered datapath).
