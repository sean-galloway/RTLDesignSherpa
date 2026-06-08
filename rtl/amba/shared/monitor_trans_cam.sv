// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: 2024-2026 sean galloway
//
// RTL Design Sherpa - Industry-Standard RTL Design and Verification
// https://github.com/sean-galloway/RTLDesignSherpa
//
// Module: monitor_trans_cam
// Purpose: Multi-port ID CAM with payload storage for the AXI monitor
//          transaction manager family (axi_monitor_trans_mgr et al).
//
// Documentation: docs/markdown/RTLAmba/shared/monitor_trans_cam.md  (TBD)
// Subsystem: amba
//
// Author: sean galloway
// Created: 2026-06-08
//
// ============================================================================
// Storage model
// -------------
// DEPTH slots, each holds:
//   - valid bit
//   - ID  (ID_WIDTH bits, used as the CAM lookup key)
//   - payload (PAYLOAD_WIDTH bits, opaque to the CAM)
//
// Three independent combinational lookup ports return one-hot match
// vectors. Because AXI IDs are unique across outstanding transactions
// the match vectors are at most one-hot in normal use; an additional
// `data_match_first_oh` output gives the lowest-index match for AXI4
// writes (where the data channel has no WID and several entries can
// match the predicate the caller uses upstream).
//
// A built-in free-slot vector plus three priority-encoded "alloc"
// outputs let the caller atomically claim 0..3 free slots per cycle
// in the order (addr, data, resp), with mutex so a single free slot
// is never double-claimed. Allocation is request-driven: assert
// `addr_wants_alloc` / `data_wants_alloc` / `resp_wants_alloc` and the
// corresponding `*_alloc_oh` output identifies the slot to write.
//
// Per-slot writes use a one-hot enable + per-slot next-state inputs.
// Writing `entry_we[i]=1` with `entry_valid_next[i]=0` clears slot i.
// The caller is responsible for ensuring at most one logical update
// per slot per cycle (mutex between alloc and update phases). The
// payload semantics are entirely the caller's -- the CAM treats it
// as an opaque bag of bits.
//
// Synthesis notes
// ---------------
// The match vectors and free vector are marked (* keep = "true" *) so
// Vivado anchors them and does NOT fuse them into the downstream
// per-entry update cones. This preserves the trans_mgr 2026-04-23
// WNS-fix shape -- each match bit is 1 LUT, fully independent across
// entries. Per-slot storage lives in a `generate` loop of independent
// always_ff blocks, so each r_payload[i] update depends only on local
// one-hot bits and shared inputs.
//
// Testing
// -------
// Companion cocotb test: val/amba/test_monitor_trans_cam.py
// ============================================================================

`timescale 1ns / 1ps

`include "reset_defs.svh"

module monitor_trans_cam #(
    parameter int DEPTH         = 16,    // Number of CAM slots
    parameter int ID_WIDTH      = 8,     // Width of the CAM key (AXI ID)
    parameter int PAYLOAD_WIDTH = 128    // Per-slot payload, opaque to the CAM
) (
    input  logic                              clk,
    input  logic                              rst_n,

    // ---- Lookup ports (combinational) ----
    input  logic [ID_WIDTH-1:0]               lookup_addr_id,
    input  logic [ID_WIDTH-1:0]               lookup_data_id,
    input  logic [ID_WIDTH-1:0]               lookup_resp_id,

    output logic [DEPTH-1:0]                  addr_match_oh,
    output logic [DEPTH-1:0]                  data_match_oh,
    output logic [DEPTH-1:0]                  resp_match_oh,

    // Lowest-index version of data_match_oh, for callers (AXI4 writes)
    // that may see multiple matches and need a deterministic pick.
    output logic [DEPTH-1:0]                  data_match_first_oh,

    // ---- Free-slot vector + per-phase alloc picks ----
    output logic [DEPTH-1:0]                  free_oh,

    input  logic                              addr_wants_alloc,
    input  logic                              data_wants_alloc,
    input  logic                              resp_wants_alloc,
    output logic [DEPTH-1:0]                  addr_alloc_oh,
    output logic [DEPTH-1:0]                  data_alloc_oh,
    output logic [DEPTH-1:0]                  resp_alloc_oh,

    // ---- Per-slot write port ----
    // entry_we[i]=1 latches (entry_valid_next[i], entry_id_next[i],
    // entry_payload_next[i]) into slot i on the next rising edge.
    input  logic [DEPTH-1:0]                  entry_we,
    input  logic [DEPTH-1:0]                  entry_valid_next,
    input  logic [ID_WIDTH-1:0]               entry_id_next      [DEPTH],
    input  logic [PAYLOAD_WIDTH-1:0]          entry_payload_next [DEPTH],

    // ---- Per-slot read port (registered) ----
    output logic [DEPTH-1:0]                  entry_valid,
    output logic [ID_WIDTH-1:0]               entry_id           [DEPTH],
    output logic [PAYLOAD_WIDTH-1:0]          entry_payload      [DEPTH]
);

    // ------------------------------------------------------------------------
    // Registered storage
    // ------------------------------------------------------------------------
    logic                       r_valid   [DEPTH];
    logic [ID_WIDTH-1:0]        r_id      [DEPTH];
    logic [PAYLOAD_WIDTH-1:0]   r_payload [DEPTH];

    // ------------------------------------------------------------------------
    // Match and free vectors (parallel one-hot, 1 LUT per bit).
    // ------------------------------------------------------------------------
    (* keep = "true" *) logic [DEPTH-1:0] w_addr_match_oh;
    (* keep = "true" *) logic [DEPTH-1:0] w_data_match_oh;
    (* keep = "true" *) logic [DEPTH-1:0] w_resp_match_oh;
    (* keep = "true" *) logic [DEPTH-1:0] w_free_oh;

    always_comb begin
        for (int i = 0; i < DEPTH; i++) begin
            w_addr_match_oh[i] = r_valid[i] && (r_id[i] == lookup_addr_id);
            w_data_match_oh[i] = r_valid[i] && (r_id[i] == lookup_data_id);
            w_resp_match_oh[i] = r_valid[i] && (r_id[i] == lookup_resp_id);
            w_free_oh[i]       = !r_valid[i];
        end
    end

    assign addr_match_oh = w_addr_match_oh;
    assign data_match_oh = w_data_match_oh;
    assign resp_match_oh = w_resp_match_oh;
    assign free_oh       = w_free_oh;

    // ------------------------------------------------------------------------
    // First-match (lowest-index) version of data_match_oh.
    // Mirrors the AXI4-write "first hit wins" convention upstream.
    // ------------------------------------------------------------------------
    always_comb begin
        data_match_first_oh = '0;
        for (int i = 0; i < DEPTH; i++) begin
            if (w_data_match_oh[i] && (data_match_first_oh == '0)) begin
                data_match_first_oh[i] = 1'b1;
            end
        end
    end

    // ------------------------------------------------------------------------
    // Priority-encoded allocation with mutex across phases.
    //   - addr_alloc_oh:  lowest-index free slot
    //   - data_alloc_oh:  next-lowest-index free slot (excluding addr's)
    //   - resp_alloc_oh:  next-lowest-index free slot (excluding addr+data)
    // A phase whose `*_wants_alloc` is low contributes '0 and consumes
    // no slot, so the others keep their lowest-available pick.
    // ------------------------------------------------------------------------
    always_comb begin
        logic [DEPTH-1:0] remaining;
        logic             taken;

        addr_alloc_oh = '0;
        data_alloc_oh = '0;
        resp_alloc_oh = '0;
        taken         = 1'b0;
        remaining     = w_free_oh;

        if (addr_wants_alloc) begin
            taken = 1'b0;
            for (int i = 0; i < DEPTH; i++) begin
                if (!taken && remaining[i]) begin
                    addr_alloc_oh[i] = 1'b1;
                    remaining[i]     = 1'b0;
                    taken            = 1'b1;
                end
            end
        end

        if (data_wants_alloc) begin
            taken = 1'b0;
            for (int i = 0; i < DEPTH; i++) begin
                if (!taken && remaining[i]) begin
                    data_alloc_oh[i] = 1'b1;
                    remaining[i]     = 1'b0;
                    taken            = 1'b1;
                end
            end
        end

        if (resp_wants_alloc) begin
            taken = 1'b0;
            for (int i = 0; i < DEPTH; i++) begin
                if (!taken && remaining[i]) begin
                    resp_alloc_oh[i] = 1'b1;
                    remaining[i]     = 1'b0;
                    taken            = 1'b1;
                end
            end
        end
    end

    // ------------------------------------------------------------------------
    // Per-slot registered state -- one independent always_ff per slot so
    // synth cannot fuse update cones across slots. Caller drives
    // entry_we / entry_*_next; the CAM latches them on the next clock.
    // ------------------------------------------------------------------------
    generate
        for (genvar gi = 0; gi < DEPTH; gi++) begin : g_slot
            `ALWAYS_FF_RST(clk, rst_n,
                if (`RST_ASSERTED(rst_n)) begin
                    r_valid[gi]   <= 1'b0;
                    r_id[gi]      <= '0;
                    r_payload[gi] <= '0;
                end else if (entry_we[gi]) begin
                    r_valid[gi]   <= entry_valid_next[gi];
                    r_id[gi]      <= entry_id_next[gi];
                    r_payload[gi] <= entry_payload_next[gi];
                end
            )

            assign entry_valid[gi]   = r_valid[gi];
            assign entry_id[gi]      = r_id[gi];
            assign entry_payload[gi] = r_payload[gi];
        end
    endgenerate

    // ========================================================================
    // Caller-protocol assertions (simulation only)
    // ========================================================================
`ifdef SIMULATION
    // Allocation mutex: no slot is claimed by more than one phase.
    always @(posedge clk) begin
        if (rst_n) begin
            for (int i = 0; i < DEPTH; i++) begin
                int alloc_count;
                alloc_count = int'(addr_alloc_oh[i])
                            + int'(data_alloc_oh[i])
                            + int'(resp_alloc_oh[i]);
                if (alloc_count > 1) begin
                    $error("monitor_trans_cam: slot %0d allocated by %0d phases (must be 0 or 1)",
                           i, alloc_count);
                end
            end
        end
    end

    // Allocation lands only on free slots.
    always @(posedge clk) begin
        if (rst_n) begin
            for (int i = 0; i < DEPTH; i++) begin
                if ((addr_alloc_oh[i] | data_alloc_oh[i] | resp_alloc_oh[i])
                        && r_valid[i]) begin
                    $error("monitor_trans_cam: slot %0d alloc'd while still valid",
                           i);
                end
            end
        end
    end
`endif

endmodule : monitor_trans_cam
