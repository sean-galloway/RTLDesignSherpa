# Test Methodology

This chapter describes what is exercised on the FPGA block (Figure 2.1) and how
utilization, throughput, compression, and integrity are measured. The full
utilization definitions are in the project's
`DMA_UTILIZATION_MEASUREMENT.md`; this is the condensed operator view.

## What is under test

The STREAM scatter-gather DMA (`stream_top_ch8`), driven by descriptors and
measured on its 128-bit read/write payload buses. A programmable
`axi_response_delay` model sits in front of the pattern-gen/CRC-check slaves so
the DUT can be exercised against a range of emulated memory latencies.

## What is measured, and how

| Quantity | How it is obtained |
|----------|--------------------|
| Datapath utilization | `axi4_dma_observer` valid/ready buckets `OBS_{RD,WR}_{PROD,BP,STARV,IDLE}` over a timed window (see the four utilization definitions in `DMA_UTILIZATION_MEASUREMENT.md`) |
| Throughput | beats × bytes / window cycles, using `TIMER_CYCLES` and the first/last beat stamps (`TIMER_{R,W}_{FIRST,LAST}`) |
| Data integrity | per-channel `CRC_RD_PER_CH*` / `CRC_WR_PER_CH*` vs expected, with valid/match masks |
| MonBus compression | the compression observer counters (`COMP_TIER*`, overflow flags) — ratio of packed vs raw records |
| Area | out-of-context synthesis of the bare `stream_top_ch8` (`make area`) |
| Extended addressing | row/col-major throughput (requires `USE_ROW_COL_MAJOR_ADDRESSING`) |

: What is measured

**A measurement run:** program STREAM by name over APB, build and load
descriptors into `desc_ram`, set the memory-latency model (`RESP_DELAY`), kick via
`KICK_GO` (Waveform 5.1), let the timer window run, then read the meters, timer,
and CRCs. Monitor presets (`perf-mon`, `debug-compl`, …) select which MonBus cones
are active.

## Workloads

| Axis | Values |
|------|--------|
| Descriptors / channel | 1, 2, 4, 8, 16 |
| Channels | 1, 2, 4, 8 |
| Transfer size | 1 MB (per the 40-config matrix) |
| Response delay | 0, 128, … aclk cycles (memory-latency sweep) |

: Characterization workloads

## The oracle

Data integrity is judged by **per-channel golden CRC** on the write-sink checker
vs the read-source pattern generator. The same by-name config, descriptor bytes,
and CRC run in the UART-equivalence sim (Chapter 6).

## Measurement pitfalls

- **Sticky `RESP_DELAY`** — a delay sweep leaves the CSR set; re-program before a
  clean matrix/size sweep or a later no-delay run silently under-performs.
- After a long mixed session some configs wedge; only a full `make program`
  clears it (a reset-completeness gap, not codec/data corruption).
- `16desc_*` configs trip a benign `trace.overflow` — it bounds the debug trace,
  not the bus-meter counters.
