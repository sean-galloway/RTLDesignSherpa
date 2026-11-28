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

# peregrine_icache

**Module:** `peregrine_icache.sv`

## Responsibility

peregrine's instruction cache (PRD P9): direct-mapped, read-only, blocking, one AXI4 read master, no dirty state, no coherence. It is the slot a cache-ip I\$ would replace. It meets the core's registered-read fetch contract.

## Parameters

<!-- GEN:params:peregrine_icache -->

| Parameter | Kind | Type | Default | Description |
|----------------|----------|------------|--------------|------------------------------|
| `SIZE_BYTES` | parameter | `int` | `4096` | Capacity, a power of two |
| `LINE_BYTES` | parameter | `int` | `64` | Line size, a power of two >= AXI_DW/8 |
| `AXI_DW` | parameter | `int` | `64` | Fabric data width, 32 or 64 |
| `AXI_IW` | parameter | `int` | `4` | AXI id width; the I\$ always uses id 0 |

: peregrine_icache parameters

<!-- /GEN -->

## Ports

<!-- GEN:ports:peregrine_icache -->

| Port | Dir | Width | Description |
|----------------------|----------|------------|----------------------------------|
| `clk` | input | `1` | Clock |
| `rst_n` | input | `1` | Reset (state and valid bits) |
| `fetch_addr` | input | `[31:0]` | the PC (registered in the core) |
| `fetch_addr_next_nw` | input | `[31:0]` | the next PC if not held |
| `hold` | input | `1` | the core holds (mem_wait) |
| `fetch_rdata` | output | `[31:0]` | Word at fetch_addr, the cycle after |
| `fetch_fault` | output | `1` | the fetch's refill failed (TASK-005) |
| `stall` | output | `1` | fetch_rdata is not the word at fetch_addr |
| `inv_req` | input | `1` | Invalidate request (level, fence.i) |
| `inv_ack` | output | `1` | Pulses on the cycle every valid bit clears |
| `m_axi_arid` | output | `[AXI_IW-1:0]` | Read address id |
| `m_axi_araddr` | output | `[31:0]` | Read address |
| `m_axi_arlen` | output | `[7:0]` | Burst length - 1 |
| `m_axi_arsize` | output | `[2:0]` | Beat size (log2 bytes) |
| `m_axi_arburst` | output | `[1:0]` | Burst type |
| `m_axi_arvalid` | output | `1` | Read address valid |
| `m_axi_arready` | input | `1` | Read address ready |
| `m_axi_rid` | input | `[AXI_IW-1:0]` | Read data id |
| `m_axi_rdata` | input | `[AXI_DW-1:0]` | Read data beat |
| `m_axi_rresp` | input | `[1:0]` | Read response |
| `m_axi_rlast` | input | `1` | Last read beat |
| `m_axi_rvalid` | input | `1` | Read data valid |
| `m_axi_rready` | output | `1` | Read data ready |

: peregrine_icache ports

<!-- /GEN -->

## Geometry at the Defaults

4096 B / 64 B lines = 64 sets; 8 beats per line at `AXI_DW = 64`; tag = PC[31:12], index = PC[11:6]; the data RAM holds one 64-bit beat per entry, addressed by `{index, beat}`.

| Storage | Implementation | Reset |
|---------|----------------|-------|
| Data | `r_data`, `ram_style = "block"`, one write port (refill), one synchronous read port (fetch) | None |
| Tags | `r_tag`, `ram_style = "distributed"`, one entry per set | None |
| Valid | `r_valid`, one flop per set | Cleared |

: peregrine_icache storage

## Hit Test

On the registered PC (`fetch_addr`): the set's valid bit (a flop) and a tag read one edge earlier, together with the data (`r_tag_q`). The hit is therefore a compare of two flops, and the tag RAM read is off the `stall -> mem_wait -> pipeline enable` path (TASK-001 stage 7).

`stall` is high whenever `fetch_rdata` is not the word at `fetch_addr`: a miss, the refill, the replay cycle, and an invalidate.

## Read Timing

The data, word-select and tag read registers read at `fetch_addr_next_nw` (the next PC as if the core were not held) with `~hold` as their enable. A held core keeps its PC, and the registers keep the PC's word. The one exception is the replay cycle after a refill, which reads at `fetch_addr` unconditionally, because the refill wrote the RAM under a held output. So `mem_wait` reaches the RAMs only as an enable, never through the address.

## Refill Sequencer

| State | Leaves when | Does |
|-------|-------------|------|
| `S_IDLE` | A miss (no invalidate pending) | Latch the PC's index and tag; beat counter to 0 |
| `S_AR` | `arready` | `arvalid` with the line address, `arlen = BEATS - 1`, INCR |
| `S_FILL` | The beat with `rlast` | `rready`; write each beat to `{index, beat}`; the last beat writes the tag and sets valid |
| `S_REPLAY` | Always, after one cycle | Re-read the PC's word; the next cycle's hit test passes |
| `S_FAULT` | An invalidate, or the PC outside the failed line | `fetch_fault` with `stall` low for every fetch from the failed line (TASK-005) |

: peregrine_icache refill states

The burst starts at the line's first beat (no critical word first).

**A failed refill** (TASK-005): `r_fill_err` collects `rresp[1]` over the burst. On the last beat a failed refill goes to `S_FAULT` instead of `S_REPLAY` and clears the set's valid bit instead of setting it (its beats have already overwritten the line the set held). In `S_FAULT`, `fetch_fault` and `~stall` hold for any fetch whose line is the failed one, so the core takes the faulted fetch whenever it is ready, held or not, and a sequential fetch behind it faults without another refill. The line compare is of two flops (the PC and the refill's line registers), like the hit's. The first fetch outside the line costs one stall cycle and returns to `S_IDLE`; a later fetch from the line refills it again. An invalidate is also taken in `S_FAULT` (a `fence.i` may follow a faulted fetch that is already in the pipeline).

## Invalidate

`inv_req` is a level, taken in `S_IDLE` or `S_FAULT` (never during a refill). That cycle clears every valid bit and pulses `inv_ack`, and it wins over a miss starting in the same cycle. `peregrine_top` raises it as the second step of `fence.i`.

---

**Last Updated:** 2026-11-27
