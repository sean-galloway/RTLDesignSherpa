// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: 2024-2025 sean galloway
//
// RTL Design Sherpa - Industry-Standard RTL Design and Verification
// https://github.com/sean-galloway/RTLDesignSherpa
//
// Module: peakrdl_to_cmdrsp
// Purpose: Peakrdl To Cmdrsp module
//
// Documentation: docs/markdown/rtl-amba/index.md
// Subsystem: amba
//
// Author: sean galloway
// Created: 2025-10-18

`include "reset_defs.svh"

module peakrdl_to_cmdrsp #(
    parameter int ADDR_WIDTH = 12,  // Address width for cmd/rsp interface
    parameter int DATA_WIDTH = 32   // Must match PeakRDL generation (typically 32)
) (
    // Clock and Reset
    input  logic                    aclk,
    input  logic                    aresetn,

    // =========================================================================
    // CMD/RSP Interface (rtldesignsherpa standard)
    // =========================================================================
    // Command Channel
    input  logic                    cmd_valid,
    output logic                    cmd_ready,
    input  logic                    cmd_pwrite,         // 1=write, 0=read
    input  logic [ADDR_WIDTH-1:0]   cmd_paddr,          // Byte address
    input  logic [DATA_WIDTH-1:0]   cmd_pwdata,         // Write data
    input  logic [DATA_WIDTH/8-1:0] cmd_pstrb,          // Byte strobes

    // Response Channel
    output logic                    rsp_valid,
    input  logic                    rsp_ready,
    output logic [DATA_WIDTH-1:0]   rsp_prdata,         // Read data
    output logic                    rsp_pslverr,        // Error flag

    // =========================================================================
    // PeakRDL Passthrough Interface
    // =========================================================================
    output logic                    regblk_req,         // Request strobe
    output logic                    regblk_req_is_wr,   // Write flag
    output logic [ADDR_WIDTH-1:0]   regblk_addr,        // Address
    output logic [DATA_WIDTH-1:0]   regblk_wr_data,     // Write data
    output logic [DATA_WIDTH-1:0]   regblk_wr_biten,    // Write bit enables
    input  logic                    regblk_req_stall_wr, // Write stall
    input  logic                    regblk_req_stall_rd, // Read stall
    input  logic                    regblk_rd_ack,      // Read acknowledge
    input  logic                    regblk_rd_err,      // Read error
    input  logic [DATA_WIDTH-1:0]   regblk_rd_data,     // Read data
    input  logic                    regblk_wr_ack,      // Write acknowledge
    input  logic                    regblk_wr_err       // Write error
);

    // =========================================================================
    // Local Parameters
    // =========================================================================
    localparam int STRB_WIDTH = DATA_WIDTH / 8;

    // =========================================================================
    // Command Channel State Machine
    // =========================================================================
    typedef enum logic [1:0] {
        CMD_IDLE       = 2'b00,  // Ready to accept command
        CMD_WAIT_ACK   = 2'b01,  // Waiting for register block ack
        CMD_STALLED    = 2'b10   // Stalled, retry when stall clears
    } cmd_state_t;

    cmd_state_t cmd_state, cmd_state_next;

    // Registered command
    logic                    r_cmd_pwrite;
    logic [ADDR_WIDTH-1:0]   r_cmd_paddr;
    logic [DATA_WIDTH-1:0]   r_cmd_pwdata;
    logic [DATA_WIDTH-1:0]   r_cmd_wr_biten;

    // =========================================================================
    // Response Channel State Machine
    // =========================================================================
    typedef enum logic {
        RSP_IDLE  = 1'b0,       // No response pending
        RSP_VALID = 1'b1        // Response valid, waiting for ready
    } rsp_state_t;

    rsp_state_t rsp_state, rsp_state_next;

    logic [DATA_WIDTH-1:0] r_rsp_prdata;
    logic                  r_rsp_pslverr;

    // =========================================================================
    // Helper Function: Convert byte strobes to bit enables
    // =========================================================================
    function automatic logic [DATA_WIDTH-1:0] strb_to_biten(
        input logic [STRB_WIDTH-1:0] strb
    );
        logic [DATA_WIDTH-1:0] biten;
        for (int i = 0; i < STRB_WIDTH; i++) begin
            biten[i*8 +: 8] = {8{strb[i]}};
        end
        return biten;
    endfunction

    // =========================================================================
    // Command State Machine (Sequential)
    // =========================================================================
    `ALWAYS_FF_RST(aclk, aresetn,
        if (`RST_ASSERTED(aresetn)) begin
            cmd_state <= CMD_IDLE;
        end else begin
            cmd_state <= cmd_state_next;
        end
    )


    // =========================================================================
    // Command State Machine (Combinational)
    // =========================================================================
    always_comb begin
        cmd_state_next = cmd_state;

        case (cmd_state)
            CMD_IDLE: begin
                if (cmd_valid) begin
                    // Check if register block can accept request
                    if (cmd_pwrite && !regblk_req_stall_wr) begin
                        // Write accepted immediately
                        cmd_state_next = CMD_WAIT_ACK;
                    end else if (!cmd_pwrite && !regblk_req_stall_rd) begin
                        // Read accepted immediately
                        cmd_state_next = CMD_WAIT_ACK;
                    end else begin
                        // Stalled - need to retry
                        cmd_state_next = CMD_STALLED;
                    end
                end
            end

            CMD_WAIT_ACK: begin
                // Wait for register block to acknowledge
                if (regblk_wr_ack || regblk_rd_ack) begin
                    cmd_state_next = CMD_IDLE;
                end
            end

            CMD_STALLED: begin
                // Re-check stall conditions with registered command
                if (r_cmd_pwrite && !regblk_req_stall_wr) begin
                    cmd_state_next = CMD_WAIT_ACK;
                end else if (!r_cmd_pwrite && !regblk_req_stall_rd) begin
                    cmd_state_next = CMD_WAIT_ACK;
                end
                // Stay in STALLED if still blocked
            end

            default: cmd_state_next = CMD_IDLE;
        endcase
    end

    // =========================================================================
    // Command ready - can accept new command when idle
    // =========================================================================
    assign cmd_ready = (cmd_state == CMD_IDLE);

    // =========================================================================
    // Register command when accepted
    // =========================================================================
    `ALWAYS_FF_RST(aclk, aresetn,
        if (`RST_ASSERTED(aresetn)) begin
            r_cmd_pwrite   <= '0;
            r_cmd_paddr    <= '0;
            r_cmd_pwdata   <= '0;
            r_cmd_wr_biten <= '0;
        end else if (cmd_valid && cmd_ready) begin
            r_cmd_pwrite   <= cmd_pwrite;
            r_cmd_paddr    <= cmd_paddr;
            r_cmd_pwdata   <= cmd_pwdata;
            r_cmd_wr_biten <= strb_to_biten(cmd_pstrb);
        end
)

    // =========================================================================
    // Generate request to register block
    // =========================================================================
    // ONE-CYCLE STROBE, per the documented contract.
    //
    // This used to include (cmd_state == CMD_WAIT_ACK), so req stayed high for
    // the accept cycle AND every cycle spent waiting for ack -- two cycles
    // minimum against a strobe the interface documents as one. Whether the
    // PeakRDL passthrough cpuif re-executes per held cycle is not something to
    // leave to chance: a plain idempotent register masks a double-access in
    // every test, while a counter, a write-1-to-clear field or a self-clearing
    // KICK bit would double-count and only show up on hardware.
    //
    // The request is asserted only in the accept cycle. CMD_WAIT_ACK still
    // holds the ADDRESS and DATA muxes steady (below) so the register block
    // sees stable payload while it completes.
    // HELD until ack -- do NOT reduce this to a one-cycle strobe.
    //
    // TASK-064 item 2 observes that the interface DOCUMENTS a one-cycle
    // strobe while this holds req through CMD_WAIT_ACK. Reducing it to one
    // cycle (2026-08-17) BROKE every register read through this bridge: the
    // observers' obs_apb window returned nothing and test_stream_mon failed
    // with `uart_read: bad response ''`. Reverting it restored 2 passed /
    // rd_prod=16 wr_prod=16 on a clean rebuild, one variable changed.
    //
    // The generated PeakRDL passthrough regblock evidently needs the request
    // held until it acks, so the DOC is what is wrong here, not the RTL. The
    // converter's own suite cannot see this -- it hangs a plain idempotent
    // register off the interface, which is exactly the case that masks a
    // request-timing change -- so any future attempt must be validated
    // through an INTEGRATED path (stream build-mon's obs_apb window), not
    // the standalone converter tests.
    assign regblk_req = (cmd_state == CMD_WAIT_ACK) ||
                        ((cmd_state == CMD_IDLE) && cmd_valid);

    // Mux between current command and registered command
    assign regblk_req_is_wr = (cmd_state == CMD_IDLE) ? cmd_pwrite : r_cmd_pwrite;
    assign regblk_addr      = (cmd_state == CMD_IDLE) ? cmd_paddr : r_cmd_paddr;
    assign regblk_wr_data   = (cmd_state == CMD_IDLE) ? cmd_pwdata : r_cmd_pwdata;
    assign regblk_wr_biten  = (cmd_state == CMD_IDLE) ?
                                strb_to_biten(cmd_pstrb) :
                                r_cmd_wr_biten;

    // =========================================================================
    // Response State Machine (Sequential)
    // =========================================================================
    `ALWAYS_FF_RST(aclk, aresetn,
        if (`RST_ASSERTED(aresetn)) begin
            rsp_state <= RSP_IDLE;
        end else begin
            rsp_state <= rsp_state_next;
        end
    )

    // =========================================================================
    // Response State Machine (Combinational)
    // =========================================================================
    always_comb begin
        rsp_state_next = rsp_state;

        case (rsp_state)
            RSP_IDLE: begin
                // Capture response when register block acknowledges
                if (regblk_wr_ack || regblk_rd_ack) begin
                    rsp_state_next = RSP_VALID;
                end
            end

            RSP_VALID: begin
                // Wait for downstream to accept response
                if (rsp_ready) begin
                    rsp_state_next = RSP_IDLE;
                end
            end

            default: rsp_state_next = RSP_IDLE;
        endcase
    end

    // =========================================================================
    // Capture response data from register block
    // =========================================================================
    `ALWAYS_FF_RST(aclk, aresetn,
        if (`RST_ASSERTED(aresetn)) begin
            r_rsp_prdata  <= '0;
            r_rsp_pslverr <= '0;
        end else if (rsp_state == RSP_IDLE) begin
            if (regblk_rd_ack) begin
                r_rsp_prdata  <= regblk_rd_data;
                r_rsp_pslverr <= regblk_rd_err;
            end else if (regblk_wr_ack) begin
                r_rsp_prdata  <= '0;  // Write responses don't return data
                r_rsp_pslverr <= regblk_wr_err;
            end
        end
    )


    // =========================================================================
    // Response outputs
    // =========================================================================
    assign rsp_valid   = (rsp_state == RSP_VALID);
    assign rsp_prdata  = r_rsp_prdata;
    assign rsp_pslverr = r_rsp_pslverr;

    // =========================================================================
    // Assertions
    // =========================================================================
    
endmodule
