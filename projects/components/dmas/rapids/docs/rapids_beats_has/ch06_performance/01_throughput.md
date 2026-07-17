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

# Throughput Targets

RAPIDS Beats is a network-to-memory accelerator: the **sink** path moves an AXIS
ingress stream into system memory, and the **source** path reads system memory
and drives an AXIS egress stream. The two paths are **independent engines** (with
their own SRAM buffers, schedulers, and AXI masters), so a sink transfer and a
source transfer run concurrently and their bandwidths add.

## Theoretical Maximum

A beat is `DATA_WIDTH = 512` bits = 64 bytes. Per-direction bandwidth is
`DATA_WIDTH x f_aclk / 8`.

### Per-Interface Bandwidth

| Interface | Data Width | Frequency | Bandwidth |
|-----------|------------|-----------|-----------|
| Descriptor Fetch | 256 bits | 100 MHz | 3.2 GB/s |
| Sink AXI Write (to memory) | 512 bits | 100 MHz | 6.4 GB/s |
| Source AXI Read (from memory) | 512 bits | 100 MHz | 6.4 GB/s |
| AXIS ingress / egress (network) | 512 bits/beat | 100 MHz | 6.4 GB/s |

The table uses the Nexys A7 characterization clock (`CLK100MHZ`, 100 MHz). The
design targets 100-500 MHz; scale linearly (e.g. 12.8 GB/s per direction at
200 MHz, 32 GB/s at 500 MHz).

### Aggregate Bandwidth

- **Concurrent sink + source:** 12.8 GB/s at 100 MHz (6.4 sink + 6.4 source),
  since the two directions are separate engines against separate AXI masters.
- **Descriptor Overhead:** ~0.1% for large transfers; the descriptor engine
  prefetches (`DESCENG_CONFIG.PREFETCH_EN`) so chained fetches overlap the
  current transfer.

---

## Practical Throughput

A transfer is bounded by the slower of its two ends: a sink transfer by
`min(AXIS ingress, AXI write)`, a source transfer by `min(AXI read, AXIS
egress)`. The SRAM buffer decouples the two ends so a transient stall on one
side does not immediately stall the other.

### Single-Channel Performance

| Scenario | Expected Efficiency | Effective Bandwidth (100 MHz) |
|----------|---------------------|-------------------------------|
| Large sequential (>1MB) | >95% | >6.1 GB/s per direction |
| Medium sequential (64KB-1MB) | 85-95% | 5.4-6.1 GB/s |
| Small sequential (4KB-64KB) | 70-85% | 4.5-5.4 GB/s |
| Very small (<4KB) | 40-70% | 2.6-4.5 GB/s |

### Multi-Channel Performance

All channels of one direction share that direction's AXI master, so aggregate is
bounded by the shared master while per-channel throughput scales inversely with
active channel count.

| Active Channels (per direction) | Per-Channel BW | Aggregate BW (per direction) |
|---------------------------------|----------------|------------------------------|
| 1 | 6.4 GB/s | 6.4 GB/s |
| 2 | 3.2 GB/s | 6.4 GB/s |
| 4 | 1.6 GB/s | 6.4 GB/s |
| 8 | 0.8 GB/s | 6.4 GB/s |

**Note:** figures are at 100 MHz for a single direction. Sink and source run
concurrently, so full-duplex aggregate is twice the per-direction column.

---

## Throughput Limiting Factors

### Memory / Network System Factors

| Factor | Impact | Mitigation |
|--------|--------|------------|
| Memory latency | Reduces efficiency for small transfers | Deeper outstanding / larger SRAM |
| Memory or network bandwidth | Hard limit on the slower end | Match RAPIDS to the memory/network capability |
| AXIS backpressure | Stalls the network end (`s_axis_tready`/`m_axis_tready`) | SRAM buffering absorbs transient stalls |
| Interconnect contention | Variable impact | Priority / channel configuration |

### RAPIDS Internal Factors

| Factor | Impact | Mitigation |
|--------|--------|------------|
| Descriptor fetch overhead | Fixed per descriptor | Longer transfers; descriptor prefetch (`PREFETCH_EN`) |
| SRAM depth | Limits outstanding beats | Configure adequate `SRAM_DEPTH` |
| Arbitration overhead | Multi-channel penalty on the shared AXI master | Reduce active channels per direction |
| AXI transfer sizing | Small bursts lose efficiency | `AXI_XFER_CONFIG` RD/WR beats, ALLOC/DRAIN sizing |
| Control descriptors | `CTRL_READ`/`CTRL_WRITE` are synchronization, not payload | Use only for producer/consumer handshakes; see below |

**Control descriptors do not carry throughput.** A `CTRL_READ` (consumer gate)
polls a memory location until it matches; a `CTRL_WRITE` (producer doorbell)
issues one 32-bit write. They synchronize a channel with a producer/consumer and
occupy the channel while active, but move no payload -- budget them as latency,
not bandwidth (see Latency, Section 6.2).

---

## Performance Targets

### Design Targets

| Metric | Target | Condition |
|--------|--------|-----------|
| **Peak throughput (per direction)** | 6.4 GB/s | Single channel, 100 MHz, ideal |
| **Full-duplex aggregate** | 12.8 GB/s | Sink + source concurrent, 100 MHz |
| **Sustained throughput** | >6.1 GB/s | Large transfers, single channel |
| **Small transfer efficiency** | >50% | 4KB transfers |

### Verification Criteria

| Scenario | Pass Criteria |
|----------|---------------|
| Sink stream (large) | >95% of AXI write bandwidth |
| Source stream (large) | >95% of AXI read bandwidth |
| Multi-channel (per direction) | Aggregate within 5% of the shared master limit |
| Data integrity (all cases) | `wr_crc`/`rd_crc`/`chk_crc` == golden model |

---

## On-Silicon Validation

The characterization harness (`rapids_char_top` on the Nexys A7-100T, 100 MHz)
validates **data integrity** end to end via golden-CRC self-checks on both paths:
sink `wr_crc == golden`, source `rd_crc == chk_crc == golden`. The current
harness measures correctness and beat counts.

Per-direction bus utilization uses the same instrument the STREAM char does: the
shared, DMA-agnostic `axi4_dma_observer` (`rtl/amba/shared/`) dropped inline on
the harness AXI masters, auto-windowed in hardware, with aggregate PROD/BP/STARV/
IDLE buckets + beat/byte/burst counts surfaced at harness CSR `0x100-0x11C` and
read verbatim by `read_bus_meters.py`. RAPIDS maps to it cleanly -- a read tap on
the source master and a write tap on the sink master give a true per-direction
split (STREAM's shared master is aggregate-only). Wiring the observer into
`rapids_char_harness` is the remaining step to report measured GB/s here.

Latest on-silicon result (full characterization suite): **48 / 48 configurations
pass** across channels {1, 2, 4} x beats {1, 4, 8, 16} x backpressure {off, on} x
seeds {default, alternate}, sink and source, all golden-validated -- including
under injected AXIS backpressure.

---

**Last Updated:** 2026-07-13
