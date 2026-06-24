# flows-idma-bridge

OOC **area** characterization flow for **PULP iDMA** (github.com/pulp-platform/iDMA,
Solderpad SHL-0.51), the best-in-class open-source scatter-gather DMA, for an
apples-to-apples comparison against STREAM. Parallel to `flows-stream-bridge`
(in-house) and `flows-vivado-mcdma` (AMD vendor IP). Results land in
`../reports/area/README.md`.

## Status: AREA-ONLY

This flow produces out-of-context synthesis area (LUT/FF/BRAM) on the
`xc7a100tcsg324-1`, matching STREAM's `make area` methodology. It does **not**
yet drive iDMA on the board — perf/throughput plumbing into the characterization
harness (observer + response-delay memory) is future work.

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
```

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
