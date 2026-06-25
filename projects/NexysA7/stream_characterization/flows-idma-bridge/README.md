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

First result (512 beats, full burst, 8 outstanding):

| memory latency | R util | W util |
|---|---:|---:|
| 0 | **100.0%** | **100.0%** |
| 64 | 88.9% | 88.9% |
| 128 | 80.0% | 80.0% |

iDMA's datapath is **100% bubble-free at zero latency, like STREAM**, and falls
off in the BDP-limited regime as memory latency exceeds the in-flight window
(STREAM was 82% at delay 128; iDMA 80% here — same regime).

**Caveats (this is a first, approximate comparison):**

- The memory model imposes latency as an AR→first-R / W→B per-response delay
  (the BDP/Little's-Law latency knob). STREAM's RTL slave applies its
  `cfg_rd/wr_resp_delay` differently, and the burst/outstanding config here
  (`max_llen`, 8 in-flight) is not yet matched to STREAM's (`burst_len=16`,
  `AR_MAX_OUTSTANDING=8`), so the *delay-curve numbers* are not directly
  comparable — only the zero-latency headline and the qualitative falloff are.
  For exact parity, match the in-flight window or reuse STREAM's RTL pattern-gen
  / crc-check slaves + the real observer in the harness.
- Backend only (no desc64 frontend, single channel). Multi-channel and
  descriptor-fetch overhead are separate axes.

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
