// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: 2024-2025 sean galloway
//
// RTL Design Sherpa - Industry-Standard RTL Design and Verification
// https://github.com/sean-galloway/RTLDesignSherpa
//
// Module: axi_master_rd_splitter
// Purpose: Axi Master Rd Splitter module
//
// Documentation: docs/markdown/rtl-amba/index.md
// Subsystem: amba
//
// Author: sean galloway
// Created: 2025-10-18

`timescale 1ns / 1ps
/*
### Assumption 1: Address is always aligned to the data bus width
**Assumption**: All AXI transactions are aligned to the data bus width.

- **Implication**: `AxADDRESS` is always set to match the data bus width
    - if DATA_WIDTH = 512bits, `AxADDRESS` is always 64-byte aligned

### Assumption 2: Fixed Transfer Size
**Assumption**: All AXI transfers use the maximum transfer size equal to the bus width.

- **Implication**: `AxSIZE` is always set to match the data bus width
- **Rationale**: Maximizes bus utilization and simplifies address alignment
- **Implementation**:
    - 32-bit bus → `AxSIZE = 3'b010` (4 bytes)
    - 64-bit bus → `AxSIZE = 3'b011` (8 bytes)
    - 128-bit bus → `AxSIZE = 3'b100` (16 bytes)

### Assumption 3: Incrementing Bursts Only
**Assumption**: All AXI bursts use incrementing address mode (`AxBURST = 2'b01`).

- **Implication**: No FIXED (`2'b00`) or WRAP (`2'b10`) bursts supported
- **Rationale**: Simplifies address generation logic and covers most use cases
- **Benefit**: Eliminates wrap boundary calculations and fixed address handling

### Assumption 4: No Address Wraparound
**Assumption**: Transactions never wrap around the top of address space (0xFFFFFFFF -> 0x00000000).

- **Implication**: No wraparound handling in boundary crossing logic
- **Rationale**: Real systems never allow this condition due to memory layout and software design
- **Benefit**: Dramatically simplified boundary crossing detection logic

### Transaction Splitting Flow Documentation

**Overview**: This module accepts AXI read transactions on the fub interface and splits them
across boundary crossings before forwarding to the master AXI interface.

**FUB_ARREADY Assertion Strategy**:
- **No Split Required**: `fub_arready` passes through `m_axi_arready` directly (immediate acceptance)
- **Split Required**: `fub_arready` ALSO asserts on the first split, i.e. at ADMISSION --
    the cycle the original is buffered and its owed-beat count loaded.

    It used to be suppressed until every split had been issued, which violated
    AXI A3.3.1: the R channel is a passthrough, so beats for the first split
    return as soon as that split is accepted downstream, and they reached the
    requester while the requester's own request was still unaccepted. Data
    must follow acceptance, so acceptance moved earlier (TASK-094).

    The next original is fenced off by `r_rbeats_active`, not by `fub_arready`:
    a second admission while beats are still owed would reload the single
    owed-beat counter mid-burst.

**Splitting Sequence for Boundary-Crossing Transactions**:

1. **Transaction Reception (IDLE State)**:
    - Original transaction arrives on fub_ar interface
    - Split combinational logic evaluates if boundary crossing occurs
    - If no split needed: immediate pass-through with `fub_arready = m_axi_arready`
    - If split needed: accept upstream too (data must follow acceptance), buffer the
        original, and transition to SPLITTING to issue the remaining splits

2. **First Split Generation (IDLE → SPLITTING)**:
    - Send first split using original address and calculated split_len
    - split_len represents beats that fit before the boundary
    - Transition to SPLITTING state, save next_addr and remaining_len

3. **Subsequent Splits (SPLITTING State)**:
    - Use saved next_addr and remaining_len for current transaction
    - Split logic recalculates if further splitting needed
    - If more splits required: send current split, update next_addr/remaining_len
    - If final split: send transaction and prepare for completion

4. **Transaction Completion**:
    - The upstream handshake already completed at admission; the FINAL split
        receiving `m_axi_arready = 1` returns the FSM to IDLE and reports the
        split record (with its true count) on the fub_split interface
    - The next original is admitted once all owed R beats have returned

**Key Properties**:
- FUB interface sees exactly one transaction (request → acceptance)
- Master AXI interface sees N split transactions (where N ≥ 1)
- All response data is passed through unchanged
- Total response beats equals original transaction beat count
- Split information is provided via fub_split interface for tracking

**Example Split Sequence** (4KB boundary, 64-byte beats):
```
Original: ADDR=0x0FC0, LEN=7 (8 beats, 512 bytes total)
→ Split 1: ADDR=0x0FC0, LEN=0 (1 beat, to boundary at 0x1000)
→ Split 2: ADDR=0x1000, LEN=6 (7 beats, remaining data)
```
*/

`include "reset_defs.svh"
module axi_master_rd_splitter
#(
    // AXI parameters
    parameter int AXI_ID_WIDTH      = 8,
    parameter int AXI_ADDR_WIDTH    = 32,
    parameter int AXI_DATA_WIDTH    = 32,
    parameter int AXI_USER_WIDTH    = 1,
    // FIFO depth
    parameter int SPLIT_FIFO_DEPTH  = 4,
    // short names
    parameter int IW = AXI_ID_WIDTH,
    parameter int AW = AXI_ADDR_WIDTH,
    parameter int DW = AXI_DATA_WIDTH,
    parameter int UW = AXI_USER_WIDTH
)
(
    // Global Clock and Reset
    input  logic aclk,
    input  logic aresetn,

    // Alignment mask signal (12-bit)
    input  logic [11:0] alignment_mask,

    // Master AXI Interface
    // Read address channel (AR)
    output logic [IW-1:0]              m_axi_arid,
    output logic [AW-1:0]              m_axi_araddr,
    output logic [7:0]                 m_axi_arlen,
    output logic [2:0]                 m_axi_arsize,
    output logic [1:0]                 m_axi_arburst,
    output logic                       m_axi_arlock,
    output logic [3:0]                 m_axi_arcache,
    output logic [2:0]                 m_axi_arprot,
    output logic [3:0]                 m_axi_arqos,
    output logic [3:0]                 m_axi_arregion,
    output logic [UW-1:0]              m_axi_aruser,
    output logic                       m_axi_arvalid,
    input  logic                       m_axi_arready,

    // Read data channel (R)
    input  logic [IW-1:0]              m_axi_rid,
    input  logic [DW-1:0]              m_axi_rdata,
    input  logic [1:0]                 m_axi_rresp,
    input  logic                       m_axi_rlast,
    input  logic [UW-1:0]              m_axi_ruser,
    input  logic                       m_axi_rvalid,
    output logic                       m_axi_rready,

    // Block ready from the errmon
    input  logic                       block_ready,

    // Slave AXI Interface
    // Read address channel (AR)
    input  logic [IW-1:0]              fub_arid,
    input  logic [AW-1:0]              fub_araddr,
    input  logic [7:0]                 fub_arlen,
    input  logic [2:0]                 fub_arsize,
    input  logic [1:0]                 fub_arburst,
    input  logic                       fub_arlock,
    input  logic [3:0]                 fub_arcache,
    input  logic [2:0]                 fub_arprot,
    input  logic [3:0]                 fub_arqos,
    input  logic [3:0]                 fub_arregion,
    input  logic [UW-1:0]              fub_aruser,
    input  logic                       fub_arvalid,
    output logic                       fub_arready,

    // Read data channel (R)
    output logic [IW-1:0]              fub_rid,
    output logic [DW-1:0]              fub_rdata,
    output logic [1:0]                 fub_rresp,
    output logic                       fub_rlast,
    output logic [UW-1:0]              fub_ruser,
    output logic                       fub_rvalid,
    input  logic                       fub_rready,

    // Output split information
    output logic [AW-1:0]              fub_split_addr,
    output logic [IW-1:0]              fub_split_id,
    output logic [7:0]                 fub_split_cnt,
    output logic                       fub_split_valid,
    // Sticky: a split-info record was dropped because the FIFO was
    // full. Sizing this FIFO is a correctness requirement, so the
    // violation has to be observable rather than silent.
    output logic                       o_split_fifo_overflow,
    input  logic                       fub_split_ready
);

    logic r_split_fifo_overflow;   // sticky: a split record was LOST
    assign o_split_fifo_overflow = r_split_fifo_overflow;


    //===========================================================================
    // Parameter Validation
    //===========================================================================
    initial begin
        assert (DW inside {32, 64, 128, 256, 512, 1024}) else
            $fatal(1, "AXI_DATA_WIDTH must be power of 2 between 32 and 1024 bits");
    end

    //===========================================================================
    // State definitions
    //===========================================================================
    typedef enum logic [1:0] {
        IDLE      = 2'b01,
        SPLITTING = 2'b10
    } split_state_t;

    split_state_t r_split_state;

    //===========================================================================
    // Transaction Storage - Buffer original transaction
    //===========================================================================

    // Buffered original transaction (captured when first accepted)
    logic [IW-1:0]  r_orig_arid;
    logic [AW-1:0]  r_orig_araddr;
    logic [7:0]     r_orig_arlen;
    logic [2:0]     r_orig_arsize;
    logic [1:0]     r_orig_arburst;
    logic           r_orig_arlock;
    logic [3:0]     r_orig_arcache;
    logic [2:0]     r_orig_arprot;
    logic [3:0]     r_orig_arqos;
    logic [3:0]     r_orig_arregion;
    logic [UW-1:0]  r_orig_aruser;

    // Current split transaction state
    logic [AW-1:0]  r_current_addr;
    logic [7:0]     r_current_len;
    logic [7:0]     r_split_count;

    //===========================================================================
    // Current Transaction Selection Logic
    //===========================================================================

    // Select current address and length based on splitting state
    logic [AW-1:0]  w_current_addr;
    logic [7:0]     w_current_len;
    logic [2:0]     w_current_size;

    always_comb begin
        if (r_split_state == IDLE) begin
            // IDLE: Use original transaction inputs
            w_current_addr = fub_araddr;
            w_current_len = fub_arlen;
            w_current_size = fub_arsize;
        end else begin
            // SPLITTING: Use buffered split state
            w_current_addr = r_current_addr;
            w_current_len = r_current_len;
            w_current_size = r_orig_arsize;
        end
    end

    //===========================================================================
    // Instantiate AXI Split Combinational Logic Module
    //===========================================================================

    // Signals from the split combinational logic
    logic           w_split_required;
    logic [7:0]     w_split_len;
    logic [AW-1:0]  w_next_boundary_addr;
    logic [7:0]     w_remaining_len_after_split;
    logic           w_new_split_needed;

    axi_split_combi #(
        .AW                        (AW),
        .DW                        (DW)
    ) inst_axi_split_combi (
        // Clock and reset for assertions
        .aclk                      (aclk),
        .aresetn                   (aresetn),

        // Inputs
        .current_addr              (w_current_addr),
        .current_len               (w_current_len),
        .ax_size                   (w_current_size),
        .alignment_mask            (alignment_mask),
        .is_idle_state             (r_split_state == IDLE),
        .transaction_valid         (fub_arvalid),

        // Essential outputs
        .split_required            (w_split_required),
        .split_len                 (w_split_len),
        .next_boundary_addr        (w_next_boundary_addr),
        .remaining_len_after_split (w_remaining_len_after_split),
        .new_split_needed          (w_new_split_needed)
    );

    //===========================================================================
    // State Management
    //===========================================================================

    // Determine if we're sending the final split transaction
    logic w_is_final_split;
    assign w_is_final_split = (r_split_state == SPLITTING) && !w_split_required;

    // ---- Upstream RLAST consolidation ------------------------------------
    // An N-way split produces N RLASTs downstream, and passing them all up
    // ends the burst N-1 times early for any generic AXI master (they
    // terminate on the first one). The upstream burst must see exactly ONE
    // RLAST, on the final beat of the ORIGINAL transaction -- the read-side
    // counterpart of the write side's WLAST regeneration.
    //
    // The count is captured when the original is ADMITTED (IDLE accept),
    // which since TASK-094 is also when fub_arready asserts -- the two were
    // deliberately made the same event, because R beats for split 1 start
    // flowing back as soon as split 1 is accepted downstream.
    logic [8:0] r_rbeats_remaining;
    logic       r_rbeats_active;

    // ADMISSION: the original is captured, its owed-beat count loaded, its
    // first (or only) split issued downstream, and -- since TASK-094 -- its
    // upstream AR handshake completed. One event, named once.
    logic w_admit;
    assign w_admit = (r_split_state == IDLE) && fub_arvalid && m_axi_arready
                     && !block_ready && !r_rbeats_active;

    // The last split of a multi-split original has been accepted downstream.
    logic w_final_accept;
    assign w_final_accept = w_is_final_split && m_axi_arready;

    `ALWAYS_FF_RST(aclk, aresetn,
        if (`RST_ASSERTED(aresetn)) begin
            r_rbeats_remaining <= 9'd0;
            r_rbeats_active <= 1'b0;
            r_split_state <= IDLE;
            r_current_addr <= '0;
            r_current_len <= '0;
            r_split_count <= 8'd0;

            // Reset buffered transaction
            r_orig_arid <= '0;
            r_orig_araddr <= '0;
            r_orig_arlen <= '0;
            r_orig_arsize <= '0;
            r_orig_arburst <= '0;
            r_orig_arlock <= '0;
            r_orig_arcache <= '0;
            r_orig_arprot <= '0;
            r_orig_arqos <= '0;
            r_orig_arregion <= '0;
            r_orig_aruser <= '0;
        end else begin

            // Retire one owed beat per upstream R handshake. Independent of
            // the split FSM: beats keep arriving while the FSM is still
            // issuing later splits.
            if (r_rbeats_active && fub_rvalid && fub_rready) begin
                r_rbeats_remaining <= r_rbeats_remaining - 9'd1;
                if (r_rbeats_remaining == 9'd1) r_rbeats_active <= 1'b0;
            end

            case (r_split_state)
                IDLE: begin
                    if (w_admit) begin
                        // Beats owed upstream for THIS original transaction.
                        r_rbeats_remaining <= 9'(fub_arlen) + 9'd1;
                        r_rbeats_active <= 1'b1;
                        // Buffer the original transaction
                        r_orig_arid <= fub_arid;
                        r_orig_araddr <= fub_araddr;
                        r_orig_arlen <= fub_arlen;
                        r_orig_arsize <= fub_arsize;
                        r_orig_arburst <= fub_arburst;
                        r_orig_arlock <= fub_arlock;
                        r_orig_arcache <= fub_arcache;
                        r_orig_arprot <= fub_arprot;
                        r_orig_arqos <= fub_arqos;
                        r_orig_arregion <= fub_arregion;
                        r_orig_aruser <= fub_aruser;

                        if (w_new_split_needed) begin
                            // Splitting required - transition to SPLITTING state
                            r_split_state <= SPLITTING;
                            r_current_addr <= w_next_boundary_addr;
                            r_current_len <= w_remaining_len_after_split;
                            r_split_count <= 8'd2; // First split sent, second split next
                        end
                        // If no split needed, stay in IDLE (pass-through transaction)
                    end
                end

                SPLITTING: begin
                    if (m_axi_arvalid && m_axi_arready) begin
                        if (w_split_required) begin
                            // More splits needed - continue splitting
                            r_current_addr <= w_next_boundary_addr;
                            r_current_len <= w_remaining_len_after_split;
                            r_split_count <= r_split_count + 8'd1;
                            // Stay in SPLITTING state
                        end else begin
                            // Final split transaction completed - return to IDLE
                            r_split_state <= IDLE;
                            r_split_count <= 8'd0;
                        end
                    end
                end

                // verilator coverage_off
                // DEFENSIVE: Illegal FSM state recovery
                default: r_split_state <= IDLE;
                // verilator coverage_on
            endcase
        end
    )


    //===========================================================================
    // AXI Signal Assignments
    //===========================================================================

    // AR Channel - Master side
    always_comb begin
        // Address and length based on split logic
        m_axi_araddr = w_current_addr;
        m_axi_arlen = w_split_required ? w_split_len : w_current_len;

        // Use buffered signals when in SPLITTING state, original signals when IDLE
        if (r_split_state == IDLE) begin
            m_axi_arid = fub_arid;
            m_axi_arsize = fub_arsize;
            m_axi_arburst = fub_arburst;
            m_axi_arlock = fub_arlock;
            m_axi_arcache = fub_arcache;
            m_axi_arprot = fub_arprot;
            m_axi_arqos = fub_arqos;
            m_axi_arregion = fub_arregion;
            m_axi_aruser = fub_aruser;
        end else begin
            m_axi_arid = r_orig_arid;
            m_axi_arsize = r_orig_arsize;
            m_axi_arburst = r_orig_arburst;
            m_axi_arlock = r_orig_arlock;
            m_axi_arcache = r_orig_arcache;
            m_axi_arprot = r_orig_arprot;
            m_axi_arqos = r_orig_arqos;
            m_axi_arregion = r_orig_arregion;
            m_axi_aruser = r_orig_aruser;
        end

        // Valid signal.
        //
        // BLOCK_READY MUST GATE THE DOWNSTREAM VALID, not only the upstream
        // ready and the FSM capture. With block_ready=1, fub_arvalid=1 and
        // m_axi_arready=1 the slave accepted the AR, the upstream handshake
        // never completed and the FSM never captured -- so the SAME AR was
        // re-presented and re-accepted every cycle. That is duplicated
        // downstream transactions, not blocked ones: the exact "gate one half
        // of the handshake" defect that turned monitor backpressure into
        // replay elsewhere in this repo.
        case (r_split_state)
            // r_rbeats_active is the ACCEPTANCE FENCE: the owed-beat RLAST
            // counter is single-transaction state, so a second admission while
            // beats are still returning would reload it mid-burst (early +
            // double RLAST upstream). Mirrors the write splitter's
            // r_waiting_for_responses fence.
            IDLE: m_axi_arvalid = fub_arvalid && !block_ready && !r_rbeats_active;
            SPLITTING: m_axi_arvalid = 1'b1;
            default: m_axi_arvalid = 1'b0;
        endcase
    end

    // AR Channel - Slave side ready logic
    //
    // AXI A3.3.1: a slave must not assert RVALID until the AR handshake it is
    // answering has COMPLETED. On the fub port this module IS that slave, and
    // its R channel is a straight passthrough -- so the upstream request must
    // be accepted no later than the cycle the FIRST split goes downstream,
    // because that split's read data can arrive immediately afterwards.
    //
    // This used to suppress fub_arready until the final split was accepted,
    // which for any split read put data upstream for a request the requester
    // had not yet seen accepted. Formal caught it with a legal downstream
    // slave (one that answers only what it accepted), so it could not be
    // blamed on a permissive environment. TASK-094.
    always_comb begin
        case (r_split_state)
            // Accept at ADMISSION, split or not. The gating terms are the same
            // ones that gate the downstream valid and the FSM capture, so the
            // upstream handshake and the first downstream split are the same
            // event and cannot come apart.
            IDLE:      fub_arready = m_axi_arready && !block_ready && !r_rbeats_active;
            // Already accepted. The remaining splits are issued from the
            // buffered copy and need nothing further from the requester; the
            // NEXT original waits on r_rbeats_active, not on this signal.
            SPLITTING: fub_arready = 1'b0;
            default:   fub_arready = 1'b0;
        endcase
    end

    // R Channel - Pass through all signals
    assign fub_rid = m_axi_rid;
    assign fub_rdata = m_axi_rdata;
    assign fub_rresp = m_axi_rresp;
    assign fub_ruser = m_axi_ruser;
    assign fub_rvalid = m_axi_rvalid;
    // One RLAST per ORIGINAL transaction. Falls back to the downstream
    // RLAST when no transaction is being tracked, so an unexpected beat is
    // still framed rather than swallowed.
    assign fub_rlast = r_rbeats_active ? (r_rbeats_remaining == 9'd1)
                                       : m_axi_rlast;
    assign m_axi_rready = fub_rready;

    //===========================================================================
    // Split information FIFO
    //===========================================================================

    // Pack the split info for the FIFO
    logic [AW+IW+8-1:0] split_fifo_din;
    logic w_split_fifo_valid;
    logic w_split_fifo_ready;

    // Sticky overflow, sole driving process for this register: a split
    // record arrived while the FIFO was full. The integration-validation
    // block at the end of the file only ASSERTS on the event.
    `ALWAYS_FF_RST(aclk, aresetn,
        if (`RST_ASSERTED(aresetn)) begin
            r_split_fifo_overflow <= 1'b0;
        end else if (w_split_fifo_valid && !w_split_fifo_ready) begin
            r_split_fifo_overflow <= 1'b1;
        end)

    // SIZING IS A CORRECTNESS REQUIREMENT HERE, SO SAY SO OUT LOUD.
    // wr_ready was unconnected and the push ungated, so once the FIFO
    // filled a split-info record was dropped silently -- the consumer
    // then reads someone else's record, or none, with nothing to
    // indicate it happened. A sticky flag cannot un-drop the record but
    // it turns a silent wrong answer into a visible one. Stalling the
    // command instead would be better still; that needs the accept path
    // to consult the FIFO, which is a larger change than this fix.

    // Reported ONCE per original, when its last split has been issued: at
    // admission for a pass-through, at the final split's acceptance otherwise.
    //
    // This was `fub_arvalid && fub_arready`, which landed on exactly those two
    // events ONLY because fub_arready was suppressed until the final split.
    // With acceptance moved to admission (TASK-094) the write has to name the
    // events directly -- otherwise every split read would report the
    // hardcoded estimate of 2 instead of its actual r_split_count.
    assign w_split_fifo_valid = (w_admit && !w_new_split_needed) || w_final_accept;

    // Always use the original transaction data at the time of acceptance
    always_comb begin
        if (r_split_state == IDLE) begin
            // IDLE writes only for a pass-through, which is exactly one
            // downstream transaction. (The old `w_new_split_needed ? 2 : 1`
            // estimate was unreachable: a split never wrote from IDLE.)
            split_fifo_din = {fub_araddr,
                                fub_arid,
                                8'd1};
        end else begin
            // SPLITTING state: use buffered original transaction data
            split_fifo_din = {r_orig_araddr,
                                r_orig_arid,
                                r_split_count};  // Actual split count
        end
    end

    // Instantiate the FIFO for split information
    gaxi_fifo_sync #(
        .REGISTERED        (0), // muxed output mode
        .DATA_WIDTH        (AW + IW + 8),
        .DEPTH             (SPLIT_FIFO_DEPTH)
    ) inst_split_info_fifo(
        .axi_aclk        (aclk),
        .axi_aresetn     (aresetn),
        .wr_valid        (w_split_fifo_valid),
        .wr_data         (split_fifo_din),
        .rd_ready        (fub_split_ready),
        .rd_valid        (fub_split_valid),
        .rd_data         ({fub_split_addr, fub_split_id, fub_split_cnt}),
        /* verilator lint_off PINCONNECTEMPTY */
        .wr_ready        (w_split_fifo_ready),
        .count          ()    // Not used
        /* verilator lint_on PINCONNECTEMPTY */
    );

    //===========================================================================
    // Additional Assertions for Integration Validation
    //===========================================================================

    // Ensure state machine consistency
    always_ff @(posedge aclk) begin
        /* verilator lint_off SYNCASYNCNET */
        if (aresetn) begin
            // Verify split count is reasonable
            /* verilator lint_off CMPCONST */
            /* verilator lint_off UNSIGNED */
            assert (r_split_count >= 0 && r_split_count <= 255) else
                $error("r_split_count (%0d) out of reasonable range", r_split_count);
            /* verilator lint_on CMPCONST */
            /* verilator lint_on UNSIGNED */

            // Verify ready logic correctness.
            //
            // The old "fub_arready must be 0 when a split is needed in IDLE"
            // check is GONE: it asserted the A3.3.1 violation itself. What
            // holds now is that the original is accepted exactly once -- at
            // admission -- and never again while its splits are being issued.
            if (r_split_state == SPLITTING) begin
                assert (fub_arready == 1'b0) else
                    $error("fub_arready must stay low once the original is admitted");
            end

            // Verify transaction buffering
            if (r_split_state == SPLITTING) begin
                assert (r_orig_arid != '0 || r_orig_araddr != '0) else
                    $error("Original transaction should be buffered in SPLITTING state");
            end

            // Verify split info FIFO write timing. Tied to the beat tracker
            // rather than to fub_arready, which no longer coincides with the
            // final split: a record is written either as the original is
            // admitted, or later while its beats are still owed.
            if (w_split_fifo_valid) begin
                assert (w_admit || r_rbeats_active) else
                    $error("Split info written outside an admitted transaction");
            end
        end
        /* verilator lint_on SYNCASYNCNET */
    end

endmodule : axi_master_rd_splitter
