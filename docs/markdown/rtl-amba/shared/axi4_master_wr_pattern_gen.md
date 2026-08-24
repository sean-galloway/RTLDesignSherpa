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

# AXI4 Master Write Pattern Generator

**Module:** `axi4_master_wr_pattern_gen.sv`
**Location:** `rtl/amba/shared/`
**Status:** Production Ready

---

## Overview

`axi4_master_wr_pattern_gen` is a CSR-programmed AXI4 write *master* for memory-controller characterization. On a start pulse it walks an algorithmic address mix (via `dma_address_gen`) and streams LFSR-pattern data through `axi4_master_wr`, accumulating a CRC-32 over the data it writes. It pairs with `axi4_master_rd_crc_check`, which regenerates the same pattern on the read side so the two CRCs (and per-beat compares) validate end-to-end data integrity through a real DRAM controller.

Bringing up a memory controller means driving it with realistic, deterministic write traffic and proving the data survives the round trip. This block drives the writes: it walks a programmable address pattern and emits reproducible data, folding that data into a CRC-32 that becomes the "expected" value for the read-side checker. The write data can be a simple LFSR phase counter (fast, but order-sensitive) or an address-derived hash (each beat's data is a pure function of its byte address, so multi-id / out-of-order completion still validates).

**Use cases:**
- Driving a DDR / memory-controller's AXI4 write port during characterization sweeps
- Generating the "golden" CRC / data that `axi4_master_rd_crc_check` compares against
- Address-pattern stress (incremental, row-major, column-major page attacks) via the `dma_address_gen` descriptor
- On-chip (FPGA) write stimulus in the DDR2 characterization harness

**Key benefit:** a CSR-driven, deterministic write generator whose data can be regenerated bit-for-bit anywhere — turning memory-controller bring-up into a single expected-vs-actual CRC comparison.

### Key Features

- CSR-programmed write workload: start address, address-generator strides/wrap masks, burst length, transaction count, AXI id/size/burst attributes
- Fully decoupled AW and W paths — two independent `dma_address_gen` instances walk the same descriptor in parallel
- Two data sources: a 32-bit Fibonacci LFSR (phase-counter) or an address-derived Murmur3-fmix hash (out-of-order-safe)
- Pipelined hash datapath (two isolated 32-bit multiplies) to close 100 MHz, decoupled from the AXI W handshake by a staging FIFO
- Three AW-ID generation modes: FIXED, COUNTER, LFSR
- CRC-32 accumulator over the written LFSR stream (`o_expected_crc`) for the read side to compare against
- Configurable inter-burst idle gap (`cfg_wr_gap`) for throughput-stress sweeps
- Sticky `o_bresp_error` on any non-OKAY write response; direct re-arm from the done state

---

## Parameters

| Parameter | Type | Default | Description |
|-----------|------|---------|-------------|
| SKID_DEPTH_AW | int | 2 | AW skid depth |
| SKID_DEPTH_W | int | 4 | W skid depth |
| SKID_DEPTH_B | int | 2 | B skid depth |
| AXI_ID_WIDTH | int | 8 | AXI ID width |
| AXI_ADDR_WIDTH | int | 32 | AXI address width |
| AXI_DATA_WIDTH | int | 64 | AXI data width |
| AXI_USER_WIDTH | int | 1 | AXI user width |
| AXI_WSTRB_WIDTH | int | AXI_DATA_WIDTH/8 | Write strobe width (derived) |
| LFSR_WIDTH | int | 32 | LFSR width; matches the slave side. CRC reflection is parameterized (CRC_REFIN/CRC_REFOUT, default 1) to the same standard CRC-32 convention as the slave blocks, so writer and slave CRCs interchange -- the old hardcoded REFIN/REFOUT=0 here broke that silently |
| LFSR_SEED | logic [31:0] | 32'hDEADBEEF | LFSR seed default |
| LFSR_TAPS | logic [47:0] | {12'd23, 12'd3, 12'd2, 12'd1} | Maximal-length Fibonacci taps (library-table primitive set) |
| BURST_LEN_MULTIPLE | int | 1 | Sim-only guard: cfg_start errors if `cfg_burst_len % BURST_LEN_MULTIPLE != 0` (set to the DRAM burst multiple) |
| CRC_REFIN | int | 1 | CRC input reflection -- MUST match the slave-side blocks |
| CRC_REFOUT | int | 1 | CRC output reflection (same constraint) |
| CRC_WIDTH | int | 32 | CRC width |
| CRC_DATA_WIDTH | int | 32 | Bits per CRC update (fixed 32 to match slave side) |
| CRC_POLY | logic [CRC_WIDTH-1:0] | 32'h04C11DB7 | CRC polynomial |
| CRC_POLY_INIT | logic [CRC_WIDTH-1:0] | '1 | CRC initial value |
| CRC_XOROUT | logic [CRC_WIDTH-1:0] | '1 | CRC final XOR |
| TXN_COUNT_WIDTH | int | 16 | Width of `cfg_txn_count` (up to 64K bursts) |
| INDEX_WIDTH | int | 16 | `dma_address_gen` index width |
| STRIDE_WIDTH | int | 24 | `dma_address_gen` signed stride width |
| IW / AW / DW / UW / SW | int | — | Aliases for id/addr/data/user/strobe widths |

**Note:** LFSR + CRC parameters mirror `axi4_master_rd_crc_check` exactly so the two blocks' CRC values are interchangeable. Internally `REP = (DW+31)/32` 32-bit slices per beat and `HSTAGES = 4` hash-pipeline stages.

---

## Ports

### Clock and Reset

| Port | Direction | Width | Description |
|------|-----------|-------|-------------|
| aclk | input | 1 | AXI clock |
| aresetn | input | 1 | Active-low asynchronous reset |

### Configuration (CSR)

| Port | Direction | Width | Description |
|------|-----------|-------|-------------|
| cfg_start_addr | input | AW | Base address handed to `dma_address_gen` |
| cfg_addr_stride_0 | input | signed STRIDE_WIDTH | Address stride, dimension 0 |
| cfg_addr_stride_1 | input | signed STRIDE_WIDTH | Address stride, dimension 1 (held at index 0 here) |
| cfg_addr_wrap_mask_0 | input | AW | Address wrap mask, dimension 0 |
| cfg_addr_wrap_mask_1 | input | AW | Address wrap mask, dimension 1 |
| cfg_burst_len | input | 8 | Beats per burst (1..255; the port is 8 bits, so 256 is not expressible -- it truncates to 0); `awlen = len − 1` |
| cfg_txn_count | input | TXN_COUNT_WIDTH | Total bursts to issue |
| cfg_axi_id | input | IW | FIXED-mode id / seed for COUNTER+LFSR modes |
| cfg_id_mode | input | 2 | AW-ID mode: 0=FIXED, 1=COUNTER, 2=LFSR |
| cfg_axi_size | input | 3 | `awsize` |
| cfg_axi_burst | input | 2 | `awburst` (INCR=1) |
| cfg_lfsr_seed | input | LFSR_WIDTH | Seed override (0 → use `LFSR_SEED` param) |
| cfg_data_mode | input | 1 | 0 = phase-counter LFSR; 1 = address-derived hash (OOO-safe) |
| cfg_hash_seed0/1/2 | input | 32 each | Murmur3-fmix mixer seeds (hash mode) |
| cfg_wr_gap | input | 4 | Inter-burst idle cycles (0..15) |
| cfg_start | input | 1 | Pulse to begin the workload |
| cfg_done | output | 1 | High once all B responses received |

### Telemetry

| Port | Direction | Width | Description |
|------|-----------|-------|-------------|
| o_expected_crc | output | CRC_WIDTH | End-of-run CRC-32 over the written LFSR stream, captured two cycles after the final W beat (holds the previous run's value, 0 after reset, until then); qualified by o_expected_crc_valid |
| o_expected_crc_valid | output | 1 | High with `cfg_done` (LFSR mode only) |
| o_bresp_error | output | 1 | Sticky on any non-OKAY BRESP |

### M-Side AXI4 Write (out to fabric/controller)

| Port | Direction | Width | Description |
|------|-----------|-------|-------------|
| m_axi_awid … m_axi_awvalid | output | — | AW channel (id, addr, len, size, burst, lock, cache, prot, qos, region, user, valid) |
| m_axi_awready | input | 1 | AW ready |
| m_axi_wdata, m_axi_wstrb, m_axi_wlast, m_axi_wuser, m_axi_wvalid | output | — | W channel (strobes tied full-beat) |
| m_axi_wready | input | 1 | W ready |
| m_axi_bid, m_axi_bresp, m_axi_buser, m_axi_bvalid | input | — | B channel |
| m_axi_bready | output | 1 | B ready |

---

## Functional Description

### Workload FSM

A four-state FSM (`S_IDLE`, `S_RUN`, `S_GAP`, `S_DONE`) sequences a run. On `cfg_start` the CSR program is latched (so software can change the `cfg_*` inputs on the next cycle without disturbing the run) and the block enters `S_RUN` (or `S_DONE` immediately if `cfg_txn_count == 0`). In `S_RUN` the AW and W paths run concurrently; `S_GAP` inserts `cfg_wr_gap` idle cycles between bursts; `S_DONE` awaits the final B responses. `S_DONE` also accepts a fresh `cfg_start` for a direct re-arm without passing back through `S_IDLE`.

### Decoupled AW and W Address Generation

Two independent `dma_address_gen` instances (`u_addr_gen_aw`, `u_addr_gen_w`) walk the *same* descriptor with the same indices, so both produce the identical address sequence. The AW path issues one AW per index at `awready` rate; the W path produces the current burst's base address for the hash datapath, popped on WLAST. `awvalid` stays continuously asserted from its first cycle to the last AW handshake when `cfg_wr_gap = 0` — the address generator produces one result per cycle once warmed. Outstanding depth is bounded by the slave's `awready` throttling, not by this block. Only `index_0` is walked (`index_1` held at 0); a second instance with a different `cfg_addr_stride_1` would exercise the 2D path.

### Data Path: LFSR vs Address Hash

Two data sources, muxed by `cfg_data_mode`:

- **Mode 0 (LFSR):** a 32-bit Fibonacci LFSR (`shifter_lfsr_fibonacci`, taps `{23,3,2,1}`) advances on every accepted W beat, replicated across the data bus (`REP` copies). The data stream is a deterministic function of `(seed, total_beats_so_far)`. This is order-sensitive and breaks under multi-id / out-of-order completion.
- **Mode 1 (address hash):** each 32-bit slice is a Murmur3-fmix-style function of its byte address and the three `cfg_hash_seed` values (xor-shift + odd multiplies). Because each beat's data depends only on its address, reorder does not perturb the per-beat compare on the read side.

The per-beat byte address is anchored on the W address-generator output and stepped by `2**awsize` bytes per beat. Full-beat writes only — `wstrb` is tied all-ones.

### Hash Pipeline and Staging FIFO

The mode-1 hash chains two 32-bit multiplies — combinationally a ~25 ns / 4-DSP cone that misses 100 MHz. Each multiply is isolated in its own register stage (`HSTAGES = 4`), with the WLAST/mode/LFSR-data riding alongside so the output stays beat-aligned. The pipeline is latency-insensitive: per-beat data values and order are unchanged, so the CRC / per-beat-compare contract still holds. A show-ahead staging FIFO (`gaxi_fifo_sync`, depth 16) between the pipeline output and the AXI W handshake lets W stream back-to-back independent of pipeline fill or master backpressure; a beat is admitted only when the generator has one and the FIFO has room for it plus the `HSTAGES` beats already in flight.

### AW-ID Generation

`awid` is muxed by `cfg_id_mode`: FIXED passes `cfg_axi_id` through; COUNTER is an 8-bit counter seeded at `cfg_axi_id[7:0]`, +1 per AW; LFSR is an 8-bit maximal-length Fibonacci LFSR (taps `{7,6,5,1}`) seeded with `cfg_axi_id[7:0] | 1` to avoid the all-zero seed. Internal counter/LFSR are 8-bit and zero-extended/truncated to `IW`.

### CRC Accumulation and Completion

A `dataint_crc` instance accumulates over the same LFSR stream sent on W (not over the hash), latched into `o_expected_crc` two cycles after the last W beat of the last burst (the CRC accumulator and its conditioned output register each lag one cycle) — meaningful only in LFSR mode, where `o_expected_crc_valid` sets. In hash mode the CRC is not load-bearing and validity is gated low; the harness uses the read side's per-beat compare instead. B responses are counted independently of FSM phase (except never accepted pre-start); `o_bresp_error` sticks on any non-OKAY BRESP. `cfg_done` asserts once in `S_DONE` with all `cfg_txn_count` B's received.

### Standard Protocol Handler

AW/W/B skid buffering and AXI compliance are delegated to an `axi4_master_wr` instance; the FSM/LFSR/hash logic drives its FUB side and the `m_axi_*` ports pass straight out to the fabric.

---

## Usage Example

```systemverilog
// Write driver for a DDR2 characterization sweep (LFSR data mode).
axi4_master_wr_pattern_gen #(
    .AXI_ID_WIDTH   (8),
    .AXI_ADDR_WIDTH (32),
    .AXI_DATA_WIDTH (64)
) u_wr_gen (
    .aclk    (aclk),
    .aresetn (aresetn),

    // CSR program (from the harness register block)
    .cfg_start_addr       (csr_base_addr),
    .cfg_addr_stride_0    (csr_stride_0),
    .cfg_addr_stride_1    (24'sd0),
    .cfg_addr_wrap_mask_0 (csr_wrap_0),
    .cfg_addr_wrap_mask_1 ('0),
    .cfg_burst_len        (8'd16),
    .cfg_txn_count        (16'd1024),
    .cfg_axi_id           (8'd0),
    .cfg_id_mode          (2'd0),      // FIXED
    .cfg_axi_size         (3'd3),      // 8 bytes/beat
    .cfg_axi_burst        (2'd1),      // INCR
    .cfg_lfsr_seed        (32'd0),     // use param default
    .cfg_data_mode        (1'b0),      // LFSR (golden CRC valid)
    .cfg_hash_seed0       (32'd0),
    .cfg_hash_seed1       (32'd0),
    .cfg_hash_seed2       (32'd0),
    .cfg_wr_gap           (4'd0),
    .cfg_start            (csr_start_pulse),
    .cfg_done             (wr_done),

    // Golden CRC for the read side to compare against
    .o_expected_crc       (wr_expected_crc),
    .o_expected_crc_valid (wr_expected_crc_valid),
    .o_bresp_error        (wr_bresp_error),

    // M-side AXI to the controller
    .m_axi_awid (awid), /* ... AW ... */ .m_axi_awready(awready),
    .m_axi_wdata(wdata),/* ... W  ... */ .m_axi_wready (wready),
    .m_axi_bid  (bid),  /* ... B  ... */ .m_axi_bready (bready)
);
```

---

## Design Notes

- **Two data modes for two threat models:** LFSR mode is the fast default with a single golden CRC; hash mode trades the CRC for OOO-safe per-beat verification when multi-id traffic reorders completions.
- **Hash pipelining was a timing fix:** the two-multiply Murmur cone was isolated into DSP-register stages specifically to close 100 MHz on FPGA; the staging FIFO then hides the added latency from the AXI handshake.
- **CRC follows the LFSR, not the wire:** the CRC absorbs the LFSR words (32-bit), keeping it interchangeable with the read checker and independent of bus width; it is only latched valid in LFSR mode.
- **Decoupled AW/W:** separate address generators mean AW can race ahead at `awready` rate while W streams at `wready` rate, exposing controller reorder/backpressure behavior a lock-stepped generator would mask.
- **Direct re-arm:** `S_DONE` re-latches on `cfg_start` so back-to-back sweeps don't require a return to idle.

---

## Related Modules

### Used By
- `projects/fpga-systems/NexysA7/pumice/build-perf/rtl/ddr2_char_harness.sv` — on-chip write driver
- DDR2 characterization macro / harness CSR blocks under `projects/NexysA7/ddr2-characterization/`

### Uses
- **axi4_master_wr.sv** — standard AXI4 write master protocol handler (AW/W/B skid + compliance)
- **dma_address_gen.sv** — algorithmic address sequence generator (×2, decoupled AW/W)
- **shifter_lfsr_fibonacci.sv** — LFSR data source and 8-bit AW-ID LFSR
- **dataint_crc.sv** — CRC-32 accumulator
- **gaxi_fifo_sync.sv** — show-ahead staging FIFO decoupling the hash pipeline from W

### See Also
- **axi4_master_rd_crc_check.sv** — the matching read-side driver + checker (same LFSR/CRC/hash config)
- **axi4_slave_wr_crc_check.sv** — the slave-side write CRC sink

---

## Testing

Covered from `val/amba/` with the rest of the shared area — run everything with `make -C val/amba clean-all && make -C val/amba run-all-func-parallel`. The characterization masters carry an independent software CRC cross-check in their TBs.

---

## References

### Source Code
- RTL: `rtl/amba/shared/axi4_master_wr_pattern_gen.sv`
- Protocol Handler: `rtl/amba/axi4/axi4_master_wr.sv`

### Documentation
- Architecture: `docs/markdown/rtl-amba/shared/README.md`
- Index: `docs/markdown/rtl-amba/index.md`
- Harness: `projects/NexysA7/ddr2-characterization/README.md`

---

**Last Updated:** 2026-07-15

---

## Navigation

- [Back to Shared Infrastructure Index](README.md)
- [Back to rtl-amba Index](../index.md)
