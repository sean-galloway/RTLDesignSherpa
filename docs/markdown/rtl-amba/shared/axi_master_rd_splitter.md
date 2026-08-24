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

# AXI Master Read Splitter

**Module:** `axi_master_rd_splitter.sv`
**Location:** `rtl/amba/shared/`
**Status:** Production Ready

---

## Overview

The AXI master read splitter takes a single upstream AXI read transaction and splits it into multiple downstream transactions when it crosses a boundary. That's what enables address range interleaving, memory-mapped I/O access, and heterogeneous memory system integration. The R-side return path consolidates RLAST to one pulse per original transaction, so a generic AXI4 master can sit upstream directly — see the consumer contract under R Channel Handling.

In modern SoC designs, memory systems are often partitioned across multiple address ranges, memory controllers, or protection domains. This module solves the fundamental problem of transactions that cross those architectural boundaries.

**The problem:**
- Upstream master issues single AXI read (ADDR=0x0FC0, LEN=7, 8 beats total, 64-byte beats)
- Transaction crosses 4KB boundary at 0x1000
- Downstream slaves require separate transactions per boundary region

**The solution:**
- The module detects the boundary crossing using combinational split logic
- Automatically generates N split transactions (where N >= 1)
- First split: ADDR=0x0FC0, LEN=0 (1 beat to boundary)
- Second split: ADDR=0x1000, LEN=6 (7 beats remaining)
- All response data aggregated transparently

**Key invariants:**
- Upstream sees exactly ONE transaction request/acceptance
- Downstream sees N split transactions (boundary-aligned)
- Total response beats equals the original transaction beat count
- All AXI signaling (ID, USER, PROT, QOS) preserved across splits

### Key Features

- Automatic boundary crossing detection and transaction splitting
- Configurable alignment boundary via the 12-bit `alignment_mask` port (4KB maximum — see Integration)
- AR channel forwarding with address/length calculation
- R channel pass-through with transparent ID handling
- Split transaction tracking via dedicated FIFO interface
- Zero added latency for non-split transactions
- Burst/ID/user fields carried through on the AR side; the R side CONSOLIDATES RLAST to one pulse per original transaction (owed-beat counter — see Consumer contract below), so a generic AXI4 master can sit upstream directly

---

## Parameters

| Parameter | Type | Default | Description |
|-----------|------|---------|-------------|
| AXI_ID_WIDTH | int | 8 | Width of AXI ID signals (ARID, RID) |
| AXI_ADDR_WIDTH | int | 32 | Width of AXI address bus (ARADDR) |
| AXI_DATA_WIDTH | int | 32 | Width of AXI data bus (RDATA), must be power of 2 (32-1024 bits) |
| AXI_USER_WIDTH | int | 1 | Width of AXI user extension fields (ARUSER, RUSER) |
| SPLIT_FIFO_DEPTH | int | 4 | Depth of split information tracking FIFO |
| IW | int | AXI_ID_WIDTH | Shorthand alias for ID width |
| AW | int | AXI_ADDR_WIDTH | Shorthand alias for address width |
| DW | int | AXI_DATA_WIDTH | Shorthand alias for data width |
| UW | int | AXI_USER_WIDTH | Shorthand alias for user width |

---

## Ports

### Clock and Reset

| Port | Direction | Width | Description |
|------|-----------|-------|-------------|
| aclk | input | 1 | Global clock for all AXI interfaces |
| aresetn | input | 1 | Active-low asynchronous reset |

### Configuration Interface

| Port | Direction | Width | Description |
|------|-----------|-------|-------------|
| alignment_mask | input | 12 | 12-bit boundary alignment mask (e.g., 0xFFF for 4KB boundaries) |
| block_ready | input | 1 | Backpressure from error monitor (suppresses fub_arready when asserted) |

### Master AXI Read Interface (Downstream)

**AR Channel (Address Read):**

| Port | Direction | Width | Description |
|------|-----------|-------|-------------|
| m_axi_arid | output | IW | Transaction ID for split read transactions |
| m_axi_araddr | output | AW | Calculated address for current split (aligned to boundaries) |
| m_axi_arlen | output | 8 | Calculated burst length for current split (AXI encoding: beats-1) |
| m_axi_arsize | output | 3 | Transfer size (preserved from original transaction) |
| m_axi_arburst | output | 2 | Burst type (preserved from original, typically INCR) |
| m_axi_arlock | output | 1 | Lock type (preserved from original) |
| m_axi_arcache | output | 4 | Cache attributes (preserved from original) |
| m_axi_arprot | output | 3 | Protection attributes (preserved from original) |
| m_axi_arqos | output | 4 | Quality of Service (preserved from original) |
| m_axi_arregion | output | 4 | Region identifier (preserved from original) |
| m_axi_aruser | output | UW | User-defined extension (preserved from original) |
| m_axi_arvalid | output | 1 | Valid signal for current split transaction |
| m_axi_arready | input | 1 | Ready signal from downstream slave |

**R Channel (Read Data):**

| Port | Direction | Width | Description |
|------|-----------|-------|-------------|
| m_axi_rid | input | IW | Response transaction ID (matches ARID) |
| m_axi_rdata | input | DW | Read data payload |
| m_axi_rresp | input | 2 | Response status (OKAY, EXOKAY, SLVERR, DECERR) |
| m_axi_rlast | input | 1 | Last beat indicator for current split |
| m_axi_ruser | input | UW | User-defined extension for response |
| m_axi_rvalid | input | 1 | Valid signal for response data |
| m_axi_rready | output | 1 | Ready signal to downstream slave (pass-through from fub) |

### Slave AXI Read Interface (Upstream / FUB)

**AR Channel (Address Read):**

| Port | Direction | Width | Description |
|------|-----------|-------|-------------|
| fub_arid | input | IW | Original transaction ID from upstream master |
| fub_araddr | input | AW | Original starting address (may cross boundaries) |
| fub_arlen | input | 8 | Original burst length (may span multiple boundaries) |
| fub_arsize | input | 3 | Transfer size per beat |
| fub_arburst | input | 2 | Burst type (FIXED, INCR, WRAP) |
| fub_arlock | input | 1 | Lock type for atomic operations |
| fub_arcache | input | 4 | Cache attributes |
| fub_arprot | input | 3 | Protection attributes |
| fub_arqos | input | 4 | Quality of Service priority |
| fub_arregion | input | 4 | Region identifier |
| fub_aruser | input | UW | User-defined extension |
| fub_arvalid | input | 1 | Valid signal for original transaction |
| fub_arready | output | 1 | Ready signal to upstream master (suppressed until all splits complete) |

**R Channel (Read Data):**

| Port | Direction | Width | Description |
|------|-----------|-------|-------------|
| fub_rid | output | IW | Response transaction ID (pass-through from m_axi) |
| fub_rdata | output | DW | Read data payload (pass-through from m_axi) |
| fub_rresp | output | 2 | Response status (pass-through from m_axi) |
| fub_rlast | output | 1 | Last beat indicator (consolidated: one per ORIGINAL transaction via the owed-beat counter) |
| fub_ruser | output | UW | User-defined extension (pass-through from m_axi) |
| fub_rvalid | output | 1 | Valid signal for response (pass-through from m_axi) |
| fub_rready | input | 1 | Ready signal from upstream master |

### Split Information Interface

| Port | Direction | Width | Description |
|------|-----------|-------|-------------|
| fub_split_addr | output | AW | Original transaction starting address |
| fub_split_id | output | IW | Original transaction ID |
| fub_split_cnt | output | 8 | Number of split transactions generated (2+ if split occurred) |
| fub_split_valid | output | 1 | Valid signal for split information |
| fub_split_ready | input | 1 | Ready signal from split information consumer |
| o_split_fifo_overflow | output | 1 | STICKY: a split-info record was dropped because the FIFO was full; stays high until reset |

---

## Functional Description

### Transaction Splitting Overview

The module operates as a transparent pass-through for non-split transactions and as an intelligent splitter for boundary-crossing ones.

**Non-split path (fast):**
- Transaction fully contained within a single boundary region
- AR signals pass directly from fub to m_axi
- fub_arready = m_axi_arready (immediate acceptance)
- R channel completely transparent
- Split count = 1

**Split path (multi-transaction):**
- Transaction crosses one or more boundary regions
- AR signals buffered and regenerated for each split
- fub_arready suppressed until the final split is accepted
- R channel remains transparent (ID-based aggregation)
- Split count = N (number of boundary crossings + 1)

### State Machine Architecture

The module implements a simple two-state FSM:

**IDLE state:**
- Awaits new transactions on the fub_ar interface
- Combinational split logic evaluates the boundary crossing
- If no split: immediate pass-through with fub_arready = m_axi_arready
- If split: buffer the transaction, transition to SPLITTING, suppress fub_arready

**SPLITTING state:**
- Issue the current split using the buffered address/length
- Update next_addr and remaining_len for the subsequent split
- If more splits needed: stay in SPLITTING, increment split_count
- If final split: assert fub_arready when accepted, return to IDLE

### Boundary Crossing Detection

A combinational logic module (axi_split_combi) provides the real-time splitting decisions:

**Inputs:**
- current_addr: transaction start address
- current_len: total beats remaining (AXI encoding)
- ax_size: bytes per beat
- alignment_mask: boundary size (e.g., 0xFFF for 4KB)

**Outputs:**
- split_required: transaction crosses a boundary
- split_len: beats to consume in the current split (AXI encoding)
- next_boundary_addr: address at next boundary alignment
- remaining_len_after_split: beats remaining after the current split

**Key calculation:**
```
next_boundary_addr = (current_addr | alignment_mask) + 1
bytes_to_boundary = next_boundary_addr - current_addr
beats_to_boundary = bytes_to_boundary >> ax_size
split_len = beats_to_boundary - 1  // AXI encoding
```

### AR Channel Forwarding Logic

**Address/length calculation:**
- IDLE state: use live fub_araddr and calculated split_len
- SPLITTING state: use buffered r_current_addr and split_len
- Always output the minimum of (split_len, current_len) for safety

**Control signals (ID, PROT, QOS, etc.):**
- IDLE state: pass through from the fub_ar* signals
- SPLITTING state: use the buffered r_orig_ar* signals (captured at acceptance)
- This keeps every split transaction carrying identical attributes

**Valid signal generation:**
- IDLE: m_axi_arvalid = fub_arvalid
- SPLITTING: m_axi_arvalid = 1 (always asserting the next split)

### Ready Signal Management

**The protocol constraint that drives everything here:**
- fub_arready must NOT assert until the entire original transaction is accepted
- The upstream master expects a single handshake for its request

**Ready logic:**
- IDLE + no split: fub_arready = m_axi_arready (immediate)
- IDLE + split needed: fub_arready = 0 (suppress until done)
- SPLITTING + intermediate: fub_arready = 0
- SPLITTING + final split: fub_arready = m_axi_arready (completes the handshake)

### R Channel Handling

The R channel is completely transparent:

**Pass-through signals:**
- fub_rid = m_axi_rid
- fub_rdata = m_axi_rdata
- fub_rresp = m_axi_rresp
- fub_rlast = owed-beat consolidation: `r_rbeats_active ? (r_rbeats_remaining == 1) : m_axi_rlast`
- fub_ruser = m_axi_ruser
- fub_rvalid = m_axi_rvalid
- m_axi_rready = fub_rready

**Consumer contract (read this before integrating):**
- Split transactions use the same ID as the original; downstream slaves respond with a matching ID and the upstream sees the concatenated beat stream
- `fub_rlast` is CONSOLIDATED to one pulse per ORIGINAL transaction: an owed-beat counter (`r_rbeats_remaining`, loaded with the original burst length at acceptance) retires one beat per upstream R handshake and asserts `fub_rlast` only on the final owed beat; intermediate splits' `m_axi_rlast` pulses are absorbed
- A standards-compliant generic AXI master can sit upstream directly — it sees exactly one RLAST per burst it issued — because acceptance is SERIALIZED: the owed-beat counter is single-transaction state, so `r_rbeats_active` fences admission (fub_arready, the FSM capture and m_axi_arvalid in IDLE all carry `!r_rbeats_active`) until the previous burst's final beat has returned. One outstanding upstream read at a time is the throughput cost of the consolidation; mutation-proven by the back-to-back scenario in the rd splitter TB. (The pre-fix behavior passed every intermediate RLAST through and required a beat-counting consumer; that defect was closed with the splitter cluster in vault/Tasks/amba)

### Split Information Tracking

A dedicated FIFO captures metadata for each completed transaction:

**FIFO write conditions:**
- Written when fub_arvalid && fub_arready (transaction accepted)
- Contains: {original_addr, transaction_id, split_count}

**Split count values:**
- No split: split_cnt = 1
- Split occurred: split_cnt = N (number of splits generated)

**Use cases:**
- Performance monitoring (detect excessive splitting)
- Error correlation (map responses to original requests)
- Debug visibility (trace transaction decomposition)

---

## Usage Example

### Basic Integration (4KB Boundary Alignment)

```systemverilog
axi_master_rd_splitter #(
    .AXI_ID_WIDTH       (8),
    .AXI_ADDR_WIDTH     (32),
    .AXI_DATA_WIDTH     (64),
    .AXI_USER_WIDTH     (1),
    .SPLIT_FIFO_DEPTH   (16)
) u_rd_splitter (
    .aclk               (axi_clk),
    .aresetn            (axi_rst_n),

    // 4KB boundary alignment
    .alignment_mask     (12'hFFF),

    // Error monitor backpressure
    .block_ready        (error_detected),

    // Upstream AXI read interface (from master)
    .fub_arid           (master_arid),
    .fub_araddr         (master_araddr),
    .fub_arlen          (master_arlen),
    .fub_arsize         (master_arsize),
    .fub_arburst        (master_arburst),
    .fub_arlock         (master_arlock),
    .fub_arcache        (master_arcache),
    .fub_arprot         (master_arprot),
    .fub_arqos          (master_arqos),
    .fub_arregion       (master_arregion),
    .fub_aruser         (master_aruser),
    .fub_arvalid        (master_arvalid),
    .fub_arready        (master_arready),

    .fub_rid            (master_rid),
    .fub_rdata          (master_rdata),
    .fub_rresp          (master_rresp),
    .fub_rlast          (master_rlast),
    .fub_ruser          (master_ruser),
    .fub_rvalid         (master_rvalid),
    .fub_rready         (master_rready),

    // Downstream AXI read interface (to memory system)
    .m_axi_arid         (mem_arid),
    .m_axi_araddr       (mem_araddr),
    .m_axi_arlen        (mem_arlen),
    .m_axi_arsize       (mem_arsize),
    .m_axi_arburst      (mem_arburst),
    .m_axi_arlock       (mem_arlock),
    .m_axi_arcache      (mem_arcache),
    .m_axi_arprot       (mem_arprot),
    .m_axi_arqos        (mem_arqos),
    .m_axi_arregion     (mem_arregion),
    .m_axi_aruser       (mem_aruser),
    .m_axi_arvalid      (mem_arvalid),
    .m_axi_arready      (mem_arready),

    .m_axi_rid          (mem_rid),
    .m_axi_rdata        (mem_rdata),
    .m_axi_rresp        (mem_rresp),
    .m_axi_rlast        (mem_rlast),
    .m_axi_ruser        (mem_ruser),
    .m_axi_rvalid       (mem_rvalid),
    .m_axi_rready       (mem_rready),

    // Split information for monitoring
    .fub_split_addr     (split_addr),
    .fub_split_id       (split_id),
    .fub_split_cnt      (split_count),
    .fub_split_valid    (split_valid),
    .fub_split_ready    (split_ready)
);

// Connect split information to monitoring infrastructure
gaxi_fifo_sync #(
    .DATA_WIDTH         (32 + 8 + 8),  // addr + id + count
    .DEPTH              (64)
) u_split_fifo (
    .axi_aclk           (axi_clk),
    .axi_aresetn        (axi_rst_n),
    .wr_valid           (split_valid),
    .wr_data            ({split_addr, split_id, split_count}),
    .wr_ready           (split_ready),
    .rd_valid           (monitor_split_valid),
    .rd_data            (monitor_split_data),
    .rd_ready           (monitor_split_ready),
    .count              (split_fifo_level)
);
```

### Transaction Splitting Example Scenario

**Original transaction:**
- Address: 0x0FC0 (4032 bytes into 4KB region)
- Length: 7 (8 beats total in AXI encoding)
- Size: 3'b011 (8 bytes per beat = 64 bits)
- Total bytes: 8 beats × 8 bytes = 64 bytes
- End address: 0x0FC0 + 64 - 1 = 0x0FFF

**Boundary analysis:**
- 4KB boundary at 0x1000
- Bytes to boundary: 0x1000 - 0x0FC0 = 64 bytes
- Beats to boundary: 64 / 8 = 8 beats
- Transaction crosses boundary: NO (ends exactly at boundary)
- Split required: NO

**Modified scenario (crosses boundary):**
- Address: 0x0FC0
- Length: 8 (9 beats)
- Total bytes: 9 × 8 = 72 bytes
- End address: 0x0FC0 + 72 - 1 = 0x1007

**Split sequence:**
1. First split: ADDR=0x0FC0, LEN=7 (8 beats to reach 0x1000)
2. Second split: ADDR=0x1000, LEN=0 (1 remaining beat)
3. Split count = 2

---

## Design Notes

### AXI Protocol Assumptions

The module enforces several assumptions you need to hold for correct operation:

**Assumption 1: Address alignment**
- All AXI addresses aligned to the data bus width
- If DATA_WIDTH = 512 bits, ARADDR is always 64-byte aligned
- Verified by assertions in axi_split_combi

**Assumption 2: Fixed transfer size**
- All transfers use the maximum size equal to the bus width
- ARSIZE always matches log2(DATA_WIDTH/8)
- Example: 64-bit bus → ARSIZE = 3'b011 (8 bytes)

**Assumption 3: Incrementing bursts only**
- Only INCR burst type supported (ARBURST = 2'b01)
- No FIXED or WRAP burst handling
- Simplifies the address calculation logic

**Assumption 4: No address wraparound**
- Transactions never wrap 0xFFFFFFFF → 0x00000000
- Guaranteed by system software / memory allocators
- Enables the simplified boundary crossing logic

### Performance Characteristics

**Latency:**
- No split: zero added cycles (combinational pass-through)
- Split required: 1 cycle per split transaction
- Example: 3-way split adds 2 cycles total latency

**Throughput:**
- Full AXI bandwidth for non-split traffic
- Sustained split traffic: limited by the split calculation (1 cycle/split)
- R channel: full bandwidth (pass-through)

**Area:**
- Minimal overhead: state machine + transaction buffer
- Major component: split information FIFO
- Configurable via the SPLIT_FIFO_DEPTH parameter

### Error Handling

**Split-FIFO overflow (observable, sticky):**
- The split-info FIFO's `wr_ready` is connected; a push attempted while the FIFO is full sets the STICKY output `o_split_fifo_overflow`, which stays high until reset — integration logic should treat it as a fatal configuration error (a split record was lost)
- Sizing the FIFO >= the true maximum outstanding split transactions is still a CORRECTNESS requirement; the sticky flag makes a violation observable rather than silent

**Protocol violations:**
- The module assumes well-formed AXI transactions
- Assertions validate the assumptions (address alignment, ax_size, no-WRAP — in `axi_split_combi`; burst TYPE itself is not asserted)
- Synthesis-time checks enforce parameter constraints

**Backpressure propagation:**
- `block_ready` gates the full acceptance path: `fub_arready`, the split-FSM capture, AND `m_axi_arvalid` in IDLE (`m_axi_arvalid = fub_arvalid && !block_ready`), so an AR presented while `block_ready=1` neither issues downstream nor is captured — blocking, not duplication (the TASK-061 duplication defect is fixed and mutation-proven)

### Integration Considerations

**Alignment mask configuration:**
- The mask port is 12 bits and zero-extended, so the largest expressible boundary is 0xFFF = 4KB; smaller powers of two (0x3F = 64B ... 0x7FF = 2KB) are the other legal values
- Driving a wider value (e.g. 0xFFFF hoping for 64KB) silently truncates to 0xFFF and splits at 4KB
- Must match downstream memory region alignment

**FIFO sizing:**
- SPLIT_FIFO_DEPTH should accommodate burst traffic
- Typical value: 16 entries for general-purpose use
- High-performance: 32-64 entries

**Clock domain constraints:**
- Single clock domain (aclk) for all interfaces
- No CDC required within the module
- Ensure timing closure on the split calculation path

---

## Related Modules

### Used By
- Memory controller wrappers requiring boundary-aligned transactions
- Multi-bank DRAM controllers with interleaving requirements
- Bridge modules interfacing heterogeneous memory regions
- DMA engines with address range constraints

### Uses
- **axi_split_combi.sv** — combinational splitting logic (boundary detection, length calculation)
- **gaxi_fifo_sync.sv** — split information tracking FIFO
- **reset_defs.svh** — standard reset macro definitions

### See Also
- **axi_master_wr_splitter.sv** — write channel splitting (AW + W channels)
- **axi_split_combi.sv** — combined read/write splitting wrapper

---

## Testing

- Tests: `val/amba/test_axi_master_rd_splitter.py`
- Testbench: `bin/TBClasses/amba/axi_master_rd_splitter_tb.py`

The back-to-back scenario in the testbench mutation-proves the RLAST consolidation, and the TASK-061 `block_ready` duplication fix is mutation-proven as well.

---

## References

### Source Code
- RTL: `rtl/amba/shared/axi_master_rd_splitter.sv`

### Documentation
- Architecture: `docs/markdown/rtl-amba/shared/README.md`
- AXI Specification: AMBA AXI4 Protocol Specification (ARM IHI 0022E)
- Design Guide: `docs/markdown/rtl-amba/index.md`

---

**Last Updated:** 2025-10-24

---

## Navigation

- [Back to Shared Infrastructure Index](README.md)
- [Back to rtl-amba Index](../index.md)
