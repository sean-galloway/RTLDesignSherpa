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

# Architecture Overview

**Module:** `rapids_core.sv`
**Location:** `projects/components/dma-ip/rapids/rtl/macro/`
**Status:** Implemented
**Last Updated:** 2026-09-30

---

## Overview

RAPIDS moves data between AXI-Stream and system memory in units of bytes. A descriptor's length is a byte count in the existing 32-bit field, and its source and destination are byte addresses. A linear descriptor may start at any byte on either side. The design keeps the streaming, no-FSM data path of RAPIDS Beats and adds three things around it: byte-to-beat math in the scheduler, byte enables through the sink SRAM to the write master, and a shifter at each AXI-Stream edge that converts between packed stream beats and memory-aligned beats.

### Key Features

- **8 Independent Channels:** Each channel has its own descriptor chain and SRAM allocation.
- **Separate Data Paths:** Sink (network to memory) and source (memory to network).
- **Byte Granularity:** Length in bytes, byte addresses, any starting offset for linear descriptors.
- **Byte Enables:** The sink SRAM entry is `{strb, data}`; the write engine drives `WSTRB` from it.
- **Packet Records:** The scheduler issues one `{bytes, offset}` record per DATA descriptor to the AXIS shifter.
- **One AXIS Packet per Descriptor:** The source path emits exactly one packet, with `TLAST` on the final byte.
- **Safe Bursts:** AXI bursts never cross a 4 KB boundary; `AxADDR` is beat-aligned.
- **MonBus Integration:** Same monitor packets as RAPIDS Beats.

### What Is Shared with RAPIDS Beats

The descriptor engine, the control-read and control-write engines, the SRAM controllers, the register block and config block, and the MonBus specification are unchanged. Those chapters are linked from the RAPIDS Beats MAS.

---

## Block Diagram

### Figure 1.1.1: RAPIDS Architecture Block Diagram

```
                                   rapids_core
    +-------------------------------------------------------------------------+
    |                                                                         |
    |  +-------------------------------------------------------------------+  |
    |  |              scheduler_group_array (8 channels)                   |  |
    |  |  +----------------+  +----------------+       +----------------+  |  |
    |  |  | scheduler_grp  |  | scheduler_grp  |  ...  | scheduler_grp  |  |  |
    |  |  |  scheduler +   |  |                |       |                |  |  |
    |  |  |  desc engine   |  |                |       |                |  |  |
    |  |  +----------------+  +----------------+       +----------------+  |  |
    |  |     shared descriptor AXI master (round-robin)                    |  |
    |  +----------------------------+--------------------------------------+  |
    |     wr beats + wr_pkt records |          rd beats + rd_pkt records      |
    |         v                     |                       v                 |
    |  +--------------------+       |        +------------------------+       |
    |  |   rapids_snk       |                |   rapids_src           |       |
    |  |  snk_data_path_axis|                | src_data_path_axis     |       |
    |  |   ingress shifter  |                |   egress shifter       |       |
    |  |   + record queue   |                |   + record queue       |       |
    |  |        |           |                |        ^               |       |
    |  |  snk_data_path     |                | src_data_path          |       |
    |  |  {strb,data} SRAM  |                | data SRAM              |       |
    |  |        |           |                |        ^               |       |
    |  |  axi_write_engine  |                | axi_read_engine        |       |
    |  +--------|-----------+                +--------|---------------+       |
    +-----------|-------------------------------------|---------------------+
                v                                     ^
         AXI Write Master (WSTRB)              AXI Read Master
         (to system memory)                    (from system memory)
```

**Source:** `rapids_core.sv`, `rapids_snk.sv`, `rapids_src.sv`

: Table 1.1.1: Block Roles

| Block | Role |
|-------|------|
| scheduler | Loads a descriptor, computes beats from offset and length, issues the packet record, tracks completion |
| scheduler_group_array | Eight scheduler groups sharing one descriptor AXI master; per-channel packet-record ports |
| snk_data_path_axis | Converts packed AXIS beats into memory-aligned beats with byte enables; checks the packet length |
| snk_data_path | SRAM of `{strb, data}` entries plus the AXI write engine |
| src_data_path | SRAM of data entries plus the AXI read engine; unchanged from Beats |
| src_data_path_axis | Converts memory-aligned beats into packed stream beats with a partial last beat |

---

## Data Flow Overview

### Sink Path (Network to Memory)

### Figure 1.1.2: Sink Path Data Flow

```
1. Scheduler loads a descriptor, computes beats_total, pulses sched_wr_pkt_valid
        |   (record {bytes, offset} enters the per-channel record queue)
        v
2. s_axis packet arrives; tready is held low until the channel's record is known
        |
        v
3. Ingress shifter: stream beat << (offset*8), OR the spill of the previous beat
        |   low DATA_WIDTH bits = this memory beat, high bits become the new spill
        v
4. Fill logic writes {strb, data} into the sink SRAM (snk_sram_controller)
        |
        v
5. axi_write_engine: aligned AWADDR, capped burst, WSTRB from the SRAM entry
        |
        v
6. System memory; B response commits the beats and completes the descriptor
```

### Source Path (Memory to Network)

### Figure 1.1.3: Source Path Data Flow

```
1. Scheduler loads a descriptor, computes beats_total, pulses sched_rd_pkt_valid
        |
        v
2. axi_read_engine: aligned ARADDR, capped burst, beats into the source SRAM
        |
        v
3. src_data_path_axis reserves drain blocks (round-robin, cfg_drain_size beats)
        |
        v
4. Egress shifter: memory beat >> (offset*8), OR the next beat's low lanes
        |   the first pop only primes the hold; the last beat is partial
        v
5. m_axis: TDATA packed from lane 0, TSTRB contiguous, TLAST on the final byte
```

---

## Byte-Granular Design Points

: Table 1.1.2: Design Points

| Point | Rule |
|-------|------|
| Length unit | Bytes, in the existing 32-bit descriptor field |
| Beats moved | `(offset + length + BYTE_LANES - 1) >> OFF_W`, zero when length is zero |
| First burst | May begin mid-beat; the address it presents is beat-aligned and the offset is carried by the record |
| Later bursts | Beat-aligned |
| 4 KB rule | A burst is truncated at the next 4 KB boundary |
| Sink lanes not written | `WSTRB` bit is 0 |
| Source last beat | Partial; `TSTRB` marks the valid low lanes, `TLAST` set |
| TYPE=EXT | Beat-aligned by design (permanent): aligned addresses, beat-multiple lengths |

The 4 KB rule and the byte math are specified in [Scheduler](../ch02_fub_blocks/01_scheduler.md) and [AXI Read Engine](../ch02_fub_blocks/03_axi_read_engine.md).

---

## Chapter Map

| Topic | Chapter |
|-------|---------|
| Scheduler byte math and record issue | [Scheduler](../ch02_fub_blocks/01_scheduler.md) |
| Record queue interface | [Packet Record Interface](../ch04_interfaces/04_packet_record_interface_spec.md) |
| Ingress shifter | [Sink Data Path AXIS](../ch03_macro_blocks/04_snk_data_path_axis.md) |
| Egress shifter | [Source Data Path AXIS](../ch03_macro_blocks/07_src_data_path_axis.md) |
| Everything else | Linked from the RAPIDS Beats MAS via the index |
