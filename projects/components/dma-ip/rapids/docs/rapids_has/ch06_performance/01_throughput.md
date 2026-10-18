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

# Throughput

RAPIDS moves bytes. The datapath moves beats. This chapter separates the two
figures because they differ for small and unaligned transfers, and it labels
every measured number with the build that produced it.

The sink path moves an AXI-Stream ingress stream into memory. The source path
reads memory and drives an AXI-Stream egress stream. The two paths are
independent engines with their own buffers, schedulers and AXI masters, so
their bandwidths add.

## Theoretical Maximum

A beat is `DATA_WIDTH / 8` bytes. The board build uses `DATA_WIDTH = 256`, so a
beat is 32 bytes. Per-direction bandwidth is the beat size times the clock.

| Item | Value |
|------|-------|
| Beat size | 32 bytes |
| Clock on the board | 100 MHz |
| Line rate per direction | 3.2 GB/s |
| Sink plus source together | 6.4 GB/s |

: Theoretical Maximum (256-bit Build)

The line rate scales linearly with the clock and with the data width. The
width does not change the per-beat behavior of the engines, so every
utilization figure below holds at any width and only the GB/s scale changes.

---

## Byte Efficiency

The byte-granular design accepts any start address and any length. The
memory side still moves whole beats. A transfer of `length` bytes that starts
at byte `offset` inside a beat occupies

    beats = (offset + length + BYTE_LANES - 1) >> OFF_W

beats on that side, with `BYTE_LANES = 32` and `OFF_W = 5` for 256 bits. The
useful fraction of those beats is

    efficiency = useful_bytes / (beats * BYTE_LANES)

Here `useful_bytes` is `length`. Efficiency is 1.0 only when both the start
and the end land on beat boundaries. The bus meters count a beat with
partial byte enables as a productive beat, so their utilization figures
measure the beat stream. The byte throughput is the beat throughput
multiplied by this efficiency.

| Length | Offset | Beats | Efficiency |
|--------|--------|-------|------------|
| 1 | 0 | 1 | 0.031 |
| 2 | 31 | 2 | 0.031 |
| 32 | 0 | 1 | 1.000 |
| 32 | 1 | 2 | 0.500 |
| 37 | 0 | 2 | 0.578 |
| 60 | 5 | 3 | 0.625 |
| 100 | 7 | 4 | 0.781 |
| 203 | 3 | 7 | 0.906 |

: Beats and Efficiency for Small and Unaligned Transfers

The loss is at most two partial beats per descriptor: one at the head and
one at the tail. It shrinks as the length grows. A 4 KB aligned transfer is
128 full beats and loses nothing. Software that needs the full line rate
should align buffers to the beat size and use lengths that are multiples of
it. Software that cannot align pays at most two beats per descriptor.

The offset applies to each half separately. The source half uses the
source address and the sink half uses the destination address. A copy whose
source and destination have different offsets can have a different beat count
on each half.

### 4 KB Boundaries

AXI bursts do not cross a 4 KB boundary, so a transfer is split at every
boundary it crosses. A page holds 128 beats at 32 bytes. The split adds
one burst per extra page, and each burst starts beat-aligned. It costs
burst-start overhead and no data. For large transfers the overhead
amortizes in the same way as any other burst boundary. The burst-length
sweep below gives the measured cost of short bursts.

### Head-of-Line Delay on the Sink Stream

The sink stream has one `s_axis_tready`. It is qualified by the `tid` of the
beat on the bus. A beat for a channel with no packet record yet stalls the
whole stream, including beats for other channels behind it. The queues
inside RAPIDS are per channel, so the cost is delay only. A sender that
posts each sink descriptor before its first beat never sees this stall. The
error chapter describes the rule.

---

## Measured Results

Three sets of results exist. They answer different questions and must not be
mixed.

| Set | Build | Question it answers |
|-----|-------|---------------------|
| Byte campaign | Byte-granular RAPIDS on the Genesys 2 | Are byte lengths and offsets correct on the board? |
| Beats performance report | RAPIDS Beats on the Genesys 2 | How fast does the beat datapath run? |
| Byte-build performance | None yet | How fast does the byte build run in beat mode? |

: Sources of Measured Figures

The byte checkers on the board build hold `ready` while they feed a
transfer. A performance row measured with them therefore does not show the
beat-mode backpressure behavior that the beats performance report was
designed to show. The beat-mode rows in the beats performance report come
from the beats build and are quoted as such below. A performance
characterization of the byte build needs a build whose checkers run in beat
mode, and that build does not exist yet.

### Byte Campaign (Correctness)

Source: `projects/fpga-systems/Genesys2/dma-ip/rapids/reports/board`, files
`rapids_byte_bytes_20260930_072516.json` and
`rapids_byte_smoke_20260930_072435.json`. Two channels were active, one
descriptor per channel.

| Packet bytes | Offset | Sink beats per channel | Result |
|--------------|--------|------------------------|--------|
| 1 | 1 | 1 | Pass |
| 2 | 31 | 2 | Pass |
| 32 | 0 | 1 | Pass |
| 37 | 0 | 2 | Pass |
| 100 | 7 | 4 | Pass |
| 96 | 17 | 4 | Pass |
| 203 | 3 (address 4035, crosses a 4 KB boundary) | 7 | Pass |

: Byte Campaign on the Board (7 of 7 Pass)

The smoke run, four beats on two channels, also passes. The beat count the
sink write master issued equals the formula in every row. Golden data
matched in every row on both halves. These rows prove correctness. They are
runs of one to seven beats, so their utilization figures are dominated by
launch and are not throughput.

### Shared Engines on the Board

Source: the two Genesys 2 bitstreams of the Resource Estimates chapter, `rapids_byte_pce.bit` (`SHARED_ENGINES = 0`) and `rapids_byte.bit` (`SHARED_ENGINES = 1`). Both were run back to back on 2026-10-17 on the same board, with the same host program. The records are `projects/fpga-systems/Genesys2/dma-ip/rapids/reports/perf/json/rapids_byte_perf_20261017_shared_engines0.json` and `..._shared_engines1.json`. Each run is the 117-point byte performance profile (`--byte-perf --profile standard`, 8 channels, byte-wise checkers) and then every directed sequence (`--byte-seq all`).

| Measure | Per-channel engines | Shared engines |
|---------|---------------------|----------------|
| Byte performance points passed | 117 of 117 | 117 of 117 |
| Directed sequences passed | 5 of 5 (378 checks) | 5 of 5 (378 checks) |
| Highest sink rate | 2560 MB/s | 2560 MB/s |
| Highest source rate | 356 MB/s | 356 MB/s |

: Board Results, SHARED_ENGINES 0 and 1

Every point is compared with itself across the two bitstreams:

| Half | Points compared | Geometric mean, shared / per-channel | Within 2 % | Shared slower by more than 2 % | Shared faster by more than 2 % |
|------|-----------------|---------------------------------------|------------|--------------------------------|--------------------------------|
| Sink | 109 | 1.000 | 99 | 6 (at most -2.4 %) | 4 (at most +5.8 %) |
| Source | 97 | 1.002 | 95 | 1 (-2.1 %) | 1 (+22.2 %) |

: Per-Point Comparison

The source rates are capped by the harness: the byte-wise checker takes 9 cycles per 32-byte beat, so 356 MB/s is 3200 / 9. The points that moved by more than 2 % are small transfers whose time is dominated by launch and descriptor fetch:

- The six slower sink points are all 8-channel, 33-byte, single-descriptor transfers (129.4 to 126.3 MB/s). All eight channels kick together, and the likely cause is that their first descriptor fetches now take turns at one AR issuer instead of eight. This has not been confirmed with a capture.
- The faster points are single-channel 203-byte sink transfers (up to +5.8 %) and a chain of 16 one-byte descriptors on 4 channels at the source (+22.2 %, 38.8 to 47.4 MB/s). These are consistent with the shared engine's R path, which writes each descriptor straight into its channel's FIFO, but the cause has not been isolated.

On sustained transfers the two builds measure the same. Sharing the engines costs no measurable throughput on this board.

### RAPIDS Beats Performance Report

Source: `projects/fpga-systems/Genesys2/dma-ip/rapids_beats/reports/perf/README.md`,
version 2.2. Build: RAPIDS Beats, 8 channels, 256 bits, 4 KB of buffer per
channel, 100 MHz. Every row is golden-CRC checked. Utilization is engaged
utilization: productive cycles over productive, backpressure and starvation
cycles.

| Path | Interface | Engaged utilization | Effective bandwidth |
|------|-----------|---------------------|---------------------|
| Sink | AXIS in | 99.7 % | 3.19 GB/s |
| Sink | AXI4 write | 100.0 % | 3.20 GB/s |
| Source | AXI4 read | 100.0 % | 3.20 GB/s |
| Source | AXIS out | 100.0 % | 3.20 GB/s |

: RAPIDS Beats Build, 8 Channels at 128 KB per Channel

The 0.3 point shortfall on the sink stream is a one-time 82-cycle fill
stall of the 4 KB per-channel buffer. It does not repeat inside a run.

| Beats per channel | AXIS in | AXI4 write | AXI4 read | AXIS out |
|-------------------|---------|------------|-----------|----------|
| 1 | 88.9 % | 38.1 % | 27.6 % | 27.6 % |
| 4 | 97.0 % | 84.2 % | 69.6 % | 69.6 % |
| 16 | 99.2 % | 95.5 % | 90.1 % | 90.1 % |
| 64 | 99.8 % | 98.5 % | 97.3 % | 97.3 % |
| 256 | 96.1 % | 99.7 % | 99.3 % | 99.3 % |
| 1024 | 99.0 % | 99.9 % | 99.8 % | 99.8 % |
| 4096 | 99.7 % | 100.0 % | 100.0 % | 100.0 % |

: RAPIDS Beats Build, Transfer Size Sweep at 8 Channels

| Active channels | AXIS in | AXI4 write | AXI4 read | AXIS out |
|-----------------|---------|------------|-----------|----------|
| 1 | 100.0 % | 99.9 % | 99.7 % | 99.7 % |
| 2 | 100.0 % | 99.9 % | 99.8 % | 99.8 % |
| 4 | 100.0 % | 100.0 % | 99.9 % | 99.9 % |
| 8 | 99.7 % | 100.0 % | 100.0 % | 100.0 % |

: RAPIDS Beats Build, Channel Scaling at 4096 Beats per Channel

| Beats per burst | AXIS in | AXI4 write | AXI4 read | AXIS out |
|-----------------|---------|------------|-----------|----------|
| 1 | 35.9 % | 35.6 % | 99.8 % | 99.8 % |
| 2 | 71.0 % | 71.0 % | 99.8 % | 99.8 % |
| 4 | 99.0 % | 99.9 % | 99.8 % | 99.8 % |
| 8 or more | 99.0 % | 99.9 % | 99.8 % | 99.8 % |

: RAPIDS Beats Build, Burst Length Sweep at 8 Channels and 1024 Beats

The beats report also holds the memory-latency sweeps and the buffer-depth
comparison. Those results belong to the beat datapath and are not repeated
here.

### Using the Beats Numbers

The byte build was not measured in beat mode, so the rows above are
reference points and not measurements of it. The memory-side figures count
beats. For a byte transfer, multiply the beat figure by the efficiency in the
byte efficiency table to estimate the byte rate. Treat the result as an
estimate until the byte build has its own performance run.

---

## Throughput Limiting Factors

| Factor | Effect | Mitigation |
|--------|--------|------------|
| Partial head and tail beats | At most two beats per descriptor carry fewer than 32 useful bytes | Align buffers to the beat size and use beat-multiple lengths |
| 4 KB boundaries | One extra burst per page crossed | Place large buffers on page boundaries |
| Short bursts | Below 4 beats the write side loses efficiency in the beats measurement | Keep the burst configuration at 4 beats or more |
| Buffer fill at run start | A one-time 82-cycle stall on the sink stream for the 4 KB build | A fixed cost per run, so its share shrinks as transfers grow |
| Head-of-line stall on the sink stream | Delay on all channels when one channel lacks a packet record | Post each sink descriptor before its first beat |
| Record queue full | The scheduler waits until a record is consumed; delay only | Chains longer than four descriptors run at the pace the data paths consume records |
| Memory latency | Reduces small-transfer efficiency | Use the beats report's latency sweeps to size outstanding depth |
| TYPE=EXT descriptors | Beat rows only, so no head or tail loss but no unaligned addressing | Keep EXT buffers aligned, which they must be anyway |

: Throughput Limiting Factors

Control descriptors move no payload. A control read gates on a memory
location and a control write issues a single write. Budget them as latency,
not bandwidth.

---

## Related Chapters

- [Latency Characteristics](../../rapids_beats_has/ch06_performance/02_latency.md):
  shared with RAPIDS Beats.
- [Descriptor Format](../ch05_programming/01_descriptor_format.md): the byte
  length, the offset and the beat-count formula.
- [Error Handling](../ch05_programming/04_error_handling.md): the length
  mismatch and the head-of-line rule.
