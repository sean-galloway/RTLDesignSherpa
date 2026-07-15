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

# AXI4 Master Read CRC Checker

**Module:** `axi4_master_rd_crc_check.sv`
**Location:** `rtl/amba/shared/`
**Status:** Production Ready

---

## Overview

`axi4_master_rd_crc_check` is a CSR-programmed AXI4 read *master* and integrity checker for memory-controller characterization. It walks the *same* algorithmic address mix (via `dma_address_gen`) and the *same* LFSR / hash schedule as `axi4_master_wr_pattern_gen`, so each returned R beat can be compared bit-for-bit against a locally regenerated pattern. It also accumulates a CRC-32 over the regenerated stream, so the harness can compare `o_actual_crc` against the writer's `o_expected_crc`.

### Key Features

- CSR-programmed read workload with the *same descriptor shape* as the write pattern generator (one CSR word drives both)
- Fully decoupled AR and R paths — two independent `dma_address_gen` instances walk the same descriptor in parallel
- Two expected-data sources: 32-bit Fibonacci LFSR (phase counter) or address-derived Murmur3-fmix hash (out-of-order-safe)
- Pipelined compare (two isolated 32-bit multiplies) so the mode-1 hash closes 100 MHz; returned data rides the same stages to align the compare
- Three AR-ID generation modes: FIXED, COUNTER, LFSR
- Sticky `o_data_error` on any per-beat data mismatch, mismatch counter, and sticky `o_rresp_error` on non-OKAY R beats
- CRC-32 over the regenerated LFSR stream (`o_actual_crc`) comparable to the writer's expected CRC
- Optional debug FIFO capturing `(actual, expected, mismatch)` per R beat for ground-truth disagreement logging

---

## Module Purpose

The read half of a memory-controller integrity loop must know what it *should* receive. This block regenerates the writer's exact data locally — either from the same LFSR phase counter or from the same address hash — and compares every returned R beat against it, latching any mismatch. It also rolls the regenerated data into a CRC-32 that should equal the writer's expected CRC when the wire is clean. Together these give both a per-beat pinpoint (which beat disagreed) and a whole-run summary (CRC compare).

**Use Cases:**
- Reading back a DDR / memory controller and verifying the data written by `axi4_master_wr_pattern_gen`
- Address-pattern integrity sweeps sharing one descriptor with the write generator
- Multi-id / out-of-order read validation using hash (address-derived) expected data
- On-chip (FPGA) read checker in the DDR2 characterization harness

**Key Benefit:** End-to-end integrity in one block — per-beat compare localizes corruption while the CRC-32 gives a single comparable summary, both derived from exactly the writer's algorithm.

---

## Parameters

| Parameter | Type | Default | Description |
|-----------|------|---------|-------------|
| SKID_DEPTH_AR | int | 2 | AR skid depth |
| SKID_DEPTH_R | int | 4 | R skid depth |
| AXI_ID_WIDTH | int | 8 | AXI ID width |
| AXI_ADDR_WIDTH | int | 32 | AXI address width |
| AXI_DATA_WIDTH | int | 64 | AXI data width |
| AXI_USER_WIDTH | int | 1 | AXI user width |
| LFSR_WIDTH | int | 32 | LFSR width (must match writer) |
| LFSR_SEED | logic [31:0] | 32'hDEADBEEF | LFSR seed default (must match writer) |
| LFSR_TAPS | logic [47:0] | {12'd32, 12'd22, 12'd2, 12'd1} | Maximal-length Fibonacci taps |
| CRC_WIDTH | int | 32 | CRC width (must match writer) |
| CRC_DATA_WIDTH | int | 32 | Bits per CRC update |
| CRC_POLY | logic [CRC_WIDTH-1:0] | 32'h04C11DB7 | CRC polynomial |
| CRC_POLY_INIT | logic [CRC_WIDTH-1:0] | '1 | CRC initial value |
| CRC_XOROUT | logic [CRC_WIDTH-1:0] | '1 | CRC final XOR |
| TXN_COUNT_WIDTH | int | 16 | Width of `cfg_txn_count` |
| INDEX_WIDTH | int | 16 | `dma_address_gen` index width |
| STRIDE_WIDTH | int | 24 | `dma_address_gen` signed stride width |
| DBG_FIFO_DEPTH | int | 0 | >0 elaborates a debug FIFO capturing per-beat records; 0 ties `dbg_*` off |
| IW / AW / DW / UW | int | — | Aliases for id/addr/data/user widths |

**Note:** LFSR + CRC parameters must match `axi4_master_wr_pattern_gen` or the compare and CRC roll-up are meaningless. Internally `REPLICATION_FACTOR = (DW+31)/32` and `HSTAGES = 4` compare-pipeline stages.

---

## Port Groups

### Clock and Reset

| Port | Direction | Width | Description |
|------|-----------|-------|-------------|
| aclk | input | 1 | AXI clock |
| aresetn | input | 1 | Active-low asynchronous reset |

### Configuration (CSR) — same shape as the write generator

| Port | Direction | Width | Description |
|------|-----------|-------|-------------|
| cfg_start_addr | input | AW | Base address for `dma_address_gen` |
| cfg_addr_stride_0 | input | signed STRIDE_WIDTH | Address stride, dimension 0 |
| cfg_addr_stride_1 | input | signed STRIDE_WIDTH | Address stride, dimension 1 |
| cfg_addr_wrap_mask_0 | input | AW | Address wrap mask, dimension 0 |
| cfg_addr_wrap_mask_1 | input | AW | Address wrap mask, dimension 1 |
| cfg_burst_len | input | 8 | Beats per burst (1..256); `arlen = len − 1` |
| cfg_txn_count | input | TXN_COUNT_WIDTH | Total bursts to issue |
| cfg_axi_id | input | IW | FIXED-mode id / seed for COUNTER+LFSR modes |
| cfg_id_mode | input | 2 | AR-ID mode: 0=FIXED, 1=COUNTER, 2=LFSR |
| cfg_axi_size | input | 3 | `arsize` |
| cfg_axi_burst | input | 2 | `arburst` |
| cfg_lfsr_seed | input | LFSR_WIDTH | Seed override (0 → use param) |
| cfg_data_mode | input | 1 | 0 = phase-counter LFSR; 1 = address hash (OOO-safe) |
| cfg_hash_seed0/1/2 | input | 32 each | Murmur3-fmix mixer seeds |
| cfg_rd_gap | input | 4 | Inter-burst idle cycles (0..15), independent of the writer's gap |
| cfg_start | input | 1 | Pulse to begin the workload |
| cfg_done | output | 1 | High when all bursts complete and the compare pipeline drains |

### Telemetry

| Port | Direction | Width | Description |
|------|-----------|-------|-------------|
| o_actual_crc | output | CRC_WIDTH | Running CRC-32 over the regenerated LFSR stream |
| o_actual_crc_valid | output | 1 | High with `cfg_done` (LFSR mode) |
| o_data_error | output | 1 | Sticky on any per-beat data mismatch |
| o_rresp_error | output | 1 | Sticky on any non-OKAY R beat |
| o_beats_mismatched | output | TXN_COUNT_WIDTH | Count of mismatching R beats |

### M-Side AXI4 Read (out to fabric/controller)

| Port | Direction | Width | Description |
|------|-----------|-------|-------------|
| m_axi_arid … m_axi_arvalid | output | — | AR channel (id, addr, len, size, burst, lock, cache, prot, qos, region, user, valid) |
| m_axi_arready | input | 1 | AR ready |
| m_axi_rid, m_axi_rdata, m_axi_rresp, m_axi_rlast, m_axi_ruser, m_axi_rvalid | input | — | R channel |
| m_axi_rready | output | 1 | R ready |

### Debug Observability (active when DBG_FIFO_DEPTH > 0)

| Port | Direction | Width | Description |
|------|-----------|-------|-------------|
| dbg_valid | output | 1 | A captured record is available |
| dbg_ready | input | 1 | Bench pops a record |
| dbg_actual | output | DW | Returned data for this beat |
| dbg_expected | output | DW | Locally regenerated expected data |
| dbg_mismatch | output | 1 | This beat disagreed |

---

## Functional Description

### Workload FSM

A four-state FSM (`S_IDLE`, `S_RUN`, `S_GAP`, `S_DONE`) mirrors the write generator. `cfg_start` latches the CSR program and enters `S_RUN` (or `S_DONE` if `cfg_txn_count == 0`). `S_RUN` runs the AR and R paths concurrently; `S_GAP` inserts `cfg_rd_gap` idle cycles between bursts (pausing both AR and R together); `S_DONE` holds until re-armed. Because the config shape is identical to the writer, one harness CSR word drives both blocks.

### Decoupled AR and R Address Generation

Two independent `dma_address_gen` instances (`u_addr_gen_ar`, `u_addr_gen_r`) walk the same descriptor. The AR path issues one AR per index as fast as `arready` and the address pipeline allow; `arvalid` stays asserted from its first cycle to the last AR handshake at `cfg_rd_gap = 0`. The R path produces the current burst's base address (popped on `rlast`) so the hash-mode expected-data regen has the right anchor for the following beat. R beats are absorbed only after the AR for that burst is on the wire and the R address generator has produced the base.

### Expected Data: LFSR vs Address Hash

Muxed by `cfg_data_mode`:

- **Mode 0 (LFSR):** a 32-bit Fibonacci LFSR advances on every accepted R beat — the same logic as the writer, so with the same total beat count the two streams stay phase-aligned and match bit-for-bit. Replicated across the bus for the compare.
- **Mode 1 (address hash):** each 32-bit slice is a Murmur3-fmix function of the beat's byte address and the three hash seeds — a pure function of the address, so out-of-order returns still validate.

### Pipelined Compare

The mode-1 hash chains two 32-bit multiplies — the same ~25 ns / 4-DSP cone as the writer, too slow to feed the per-beat compare combinationally at 100 MHz. Each multiply is isolated in its own register stage (`HSTAGES = 4`); the returned `rdata` rides through the same stages so the compare happens at the pipeline output, aligned with the delayed expected value. Beat/burst accounting stays keyed on the R-beat handshake — only the data compare is delayed. A per-beat mismatch at the pipeline output sets `o_data_error` and increments `o_beats_mismatched`; `rresp` is checked immediately at the R beat (no hash dependency) into `o_rresp_error`. `cfg_done` waits for the compare pipeline to drain (`!(|r_cp_valid)`) so no trailing mismatch is missed.

### CRC Accumulation

A `dataint_crc` accumulates over the regenerated LFSR stream (not the returned `rdata`) — matching the writer's accounting so `o_actual_crc` equals the writer's `o_expected_crc` on a clean wire. `o_actual_crc_valid` sets with `cfg_done` in LFSR mode; hash mode relies on the per-beat compare (`o_data_error`).

### AR-ID Generation

`arid` is muxed by `cfg_id_mode` exactly like the writer's `awid`: FIXED, an 8-bit COUNTER, or an 8-bit Fibonacci LFSR (taps `{8,6,5,4}`, seeded `cfg_axi_id[7:0] | 1`).

### Out-of-Order Completion — Known Limitation

The v1 LFSR mirror advances on *arrival* index, so it is only correct with a single outstanding AR, or when all ARs share one ID (AXI4 mandates in-order R per id). With multiple outstanding ARs at distinct IDs the controller may return bursts interleaved / fully OOO, which reorders R beats versus the writer's W phase and breaks both the per-beat compare and the CRC roll-up. The header documents the v2 plan (per-address hash expected function + commutative CRC roll-up). Until then, the harness CSR must keep the read block single-outstanding (or all-same-id) when the controller has OOO enabled — or use hash data mode, which is inherently OOO-safe for the per-beat compare.

### Optional Debug FIFO

When `DBG_FIFO_DEPTH > 0` a `gaxi_fifo_sync` captures `(actual, expected, mismatch)` at each compare-pipeline output so the bench can walk the exact disagreements instead of inferring from `o_data_error`. When depth is 0 the generate `else` arm ties the `dbg_*` outputs off and the FIFO is not built.

### Standard Protocol Handler

AR/R skid buffering and AXI compliance are delegated to an `axi4_master_rd` instance; the FSM/LFSR/hash/compare logic drives its FUB side and the `m_axi_*` ports pass straight out to the fabric.

---

## Usage Example

```systemverilog
// Read checker paired with the write generator on a DDR2 sweep.
axi4_master_rd_crc_check #(
    .AXI_ID_WIDTH   (8),
    .AXI_ADDR_WIDTH (32),
    .AXI_DATA_WIDTH (64),
    .DBG_FIFO_DEPTH (0)
) u_rd_chk (
    .aclk    (aclk),
    .aresetn (aresetn),

    // SAME descriptor word as the write generator
    .cfg_start_addr       (csr_base_addr),
    .cfg_addr_stride_0    (csr_stride_0),
    .cfg_addr_stride_1    (24'sd0),
    .cfg_addr_wrap_mask_0 (csr_wrap_0),
    .cfg_addr_wrap_mask_1 ('0),
    .cfg_burst_len        (8'd16),
    .cfg_txn_count        (16'd1024),
    .cfg_axi_id           (8'd0),
    .cfg_id_mode          (2'd0),      // FIXED / single-outstanding-safe
    .cfg_axi_size         (3'd3),
    .cfg_axi_burst        (2'd1),
    .cfg_lfsr_seed        (32'd0),
    .cfg_data_mode        (1'b0),      // LFSR (CRC comparable to writer)
    .cfg_hash_seed0       (32'd0),
    .cfg_hash_seed1       (32'd0),
    .cfg_hash_seed2       (32'd0),
    .cfg_rd_gap           (4'd0),
    .cfg_start            (csr_start_pulse),
    .cfg_done             (rd_done),

    .o_actual_crc         (rd_actual_crc),
    .o_actual_crc_valid   (rd_actual_crc_valid),
    .o_data_error         (rd_data_error),
    .o_rresp_error        (rd_rresp_error),
    .o_beats_mismatched   (rd_beats_bad),

    // M-side AXI from the controller
    .m_axi_arid (arid), /* ... AR ... */ .m_axi_arready(arready),
    .m_axi_rid  (rid),  /* ... R  ... */ .m_axi_rready (rready),

    // Debug FIFO tied off (DBG_FIFO_DEPTH == 0)
    .dbg_valid (), .dbg_ready (1'b0),
    .dbg_actual(), .dbg_expected(), .dbg_mismatch()
);

// Clean-wire check: CRCs agree and no per-beat mismatch.
assign integrity_ok = (rd_actual_crc == wr_expected_crc) && !rd_data_error;
```

---

## Design Notes

- **Mirror the writer exactly:** LFSR seed schedule, CRC config, address descriptor, and ID modes are all mirror images of `axi4_master_wr_pattern_gen` — that symmetry is what makes the CRCs and per-beat expected values comparable.
- **Per-beat compare + CRC are complementary:** the compare localizes the failing beat; the CRC gives a single-register whole-run summary. Both are provided so a failure can be both detected and pinpointed.
- **Compare pipeline aligns delayed expected with delayed rdata:** the returned data is intentionally delayed the same `HSTAGES` as the hash so the compare is apples-to-apples, and `cfg_done` waits for the pipeline to drain.
- **OOO is a real v1 limitation:** with multi-id OOO completion, use hash data mode (`cfg_data_mode = 1`) or hold the read block single-outstanding — the header spells out the v2 per-address-hash fix.
- **Debug FIFO is opt-in:** `DBG_FIFO_DEPTH > 0` adds ground-truth per-beat capture at essentially no cost when disabled.

---

## Related Modules

### Used By
- `projects/NexysA7/ddr2-characterization/flows-ours-uart/rtl/ddr2_char_harness.sv` — on-chip read checker
- DDR2 characterization macro / harness CSR blocks under `projects/NexysA7/ddr2-characterization/`

### Uses
- **axi4_master_rd.sv** — standard AXI4 read master protocol handler (AR/R skid + compliance)
- **dma_address_gen.sv** — algorithmic address sequence generator (×2, decoupled AR/R)
- **shifter_lfsr_fibonacci.sv** — expected-data LFSR and 8-bit AR-ID LFSR
- **dataint_crc.sv** — CRC-32 accumulator
- **gaxi_fifo_sync.sv** — optional debug capture FIFO

### See Also
- **axi4_master_wr_pattern_gen.sv** — the matching write-side driver (same LFSR/CRC/hash/descriptor config)
- **axi4_slave_rd_pattern_gen.sv** — the slave-side read pattern source

---

## References

### Source Code
- RTL: `rtl/amba/shared/axi4_master_rd_crc_check.sv`
- Protocol Handler: `rtl/amba/axi4/axi4_master_rd.sv`

### Documentation
- Architecture: `docs/markdown/RTLAmba/shared/README.md`
- Index: `docs/markdown/RTLAmba/index.md`
- Harness: `projects/NexysA7/ddr2-characterization/README.md`

---

**Last Updated:** 2026-07-15

---

## Navigation

- [Back to Shared Infrastructure Index](README.md)
- [Back to RTLAmba Index](../index.md)
