//      // verilator_coverage annotation
        // SPDX-License-Identifier: MIT
        // SPDX-FileCopyrightText: 2024-2025 sean galloway
        //
        // RTL Design Sherpa - Industry-Standard RTL Design and Verification
        // https://github.com/sean-galloway/RTLDesignSherpa
        //
        // Module: peakrdl_to_cmdrsp
        // Purpose: Peakrdl To Cmdrsp module
        //
        // Documentation: rtl/amba/PRD.md
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
 004646     input  logic                    aclk,
%000002     input  logic                    aresetn,
        
            // =========================================================================
            // CMD/RSP Interface (rtldesignsherpa standard)
            // =========================================================================
            // Command Channel
 000040     input  logic                    cmd_valid,
 000042     output logic                    cmd_ready,
 000028     input  logic                    cmd_pwrite,         // 1=write, 0=read
%000000     input  logic [ADDR_WIDTH-1:0]   cmd_paddr,          // Byte address
%000000     input  logic [DATA_WIDTH-1:0]   cmd_pwdata,         // Write data
%000002     input  logic [DATA_WIDTH/8-1:0] cmd_pstrb,          // Byte strobes
        
            // Response Channel
 000040     output logic                    rsp_valid,
 000040     input  logic                    rsp_ready,
%000000     output logic [DATA_WIDTH-1:0]   rsp_prdata,         // Read data
%000000     output logic                    rsp_pslverr,        // Error flag
        
            // =========================================================================
            // PeakRDL Passthrough Interface
            // =========================================================================
 000040     output logic                    regblk_req,         // Request strobe
 000028     output logic                    regblk_req_is_wr,   // Write flag
%000000     output logic [ADDR_WIDTH-1:0]   regblk_addr,        // Address
%000000     output logic [DATA_WIDTH-1:0]   regblk_wr_data,     // Write data
%000002     output logic [DATA_WIDTH-1:0]   regblk_wr_biten,    // Write bit enables
%000000     input  logic                    regblk_req_stall_wr, // Write stall
%000000     input  logic                    regblk_req_stall_rd, // Read stall
 000020     input  logic                    regblk_rd_ack,      // Read acknowledge
%000000     input  logic                    regblk_rd_err,      // Read error
%000000     input  logic [DATA_WIDTH-1:0]   regblk_rd_data,     // Read data
 000020     input  logic                    regblk_wr_ack,      // Write acknowledge
%000000     input  logic                    regblk_wr_err       // Write error
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
        
%000000     cmd_state_t cmd_state, cmd_state_next;
        
            // Registered command
%000008     logic                    r_cmd_pwrite;
%000000     logic [ADDR_WIDTH-1:0]   r_cmd_paddr;
%000000     logic [DATA_WIDTH-1:0]   r_cmd_pwdata;
%000002     logic [DATA_WIDTH-1:0]   r_cmd_wr_biten;
        
            // =========================================================================
            // Response Channel State Machine
            // =========================================================================
            typedef enum logic {
                RSP_IDLE  = 1'b0,       // No response pending
                RSP_VALID = 1'b1        // Response valid, waiting for ready
            } rsp_state_t;
        
 000040     rsp_state_t rsp_state, rsp_state_next;
        
%000000     logic [DATA_WIDTH-1:0] r_rsp_prdata;
%000000     logic                  r_rsp_pslverr;
        
            // =========================================================================
            // Helper Function: Convert byte strobes to bit enables
            // =========================================================================
 021774     function automatic logic [DATA_WIDTH-1:0] strb_to_biten(
                input logic [STRB_WIDTH-1:0] strb
            );
                logic [DATA_WIDTH-1:0] biten;
 021774         for (int i = 0; i < STRB_WIDTH; i++) begin
 087096             biten[i*8 +: 8] = {8{strb[i]}};
                end
 021774         return biten;
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
 000022     )
        
        
            // =========================================================================
            // Command State Machine (Combinational)
            // =========================================================================
%000000     always_comb begin
%000000         cmd_state_next = cmd_state;
        
%000000         case (cmd_state)
%000000             CMD_IDLE: begin
%000000                 if (cmd_valid) begin
                            // Check if register block can accept request
%000000                     if (cmd_pwrite && !regblk_req_stall_wr) begin
                                // Write accepted immediately
%000000                         cmd_state_next = CMD_WAIT_ACK;
%000000                     end else if (!cmd_pwrite && !regblk_req_stall_rd) begin
                                // Read accepted immediately
%000000                         cmd_state_next = CMD_WAIT_ACK;
%000000                     end else begin
                                // Stalled - need to retry
%000000                         cmd_state_next = CMD_STALLED;
                            end
                        end
                    end
        
%000000             CMD_WAIT_ACK: begin
                        // Wait for register block to acknowledge
%000000                 if (regblk_wr_ack || regblk_rd_ack) begin
%000000                     cmd_state_next = CMD_IDLE;
                        end
                    end
        
%000000             CMD_STALLED: begin
                        // Re-check stall conditions with registered command
%000000                 if (r_cmd_pwrite && !regblk_req_stall_wr) begin
%000000                     cmd_state_next = CMD_WAIT_ACK;
%000000                 end else if (!r_cmd_pwrite && !regblk_req_stall_rd) begin
%000000                     cmd_state_next = CMD_WAIT_ACK;
                        end
                        // Stay in STALLED if still blocked
                    end
        
%000000             default: cmd_state_next = CMD_IDLE;
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
 000020 )
        
            // =========================================================================
            // Generate request to register block
            // =========================================================================
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
 000022     )
        
            // =========================================================================
            // Response State Machine (Combinational)
            // =========================================================================
 021934     always_comb begin
 021934         rsp_state_next = rsp_state;
        
 021934         case (rsp_state)
 021754             RSP_IDLE: begin
                        // Capture response when register block acknowledges
 000180                 if (regblk_wr_ack || regblk_rd_ack) begin
 000180                     rsp_state_next = RSP_VALID;
                        end
                    end
        
 000180             RSP_VALID: begin
                        // Wait for downstream to accept response
%000000                 if (rsp_ready) begin
 000180                     rsp_state_next = RSP_IDLE;
                        end
                    end
        
%000000             default: rsp_state_next = RSP_IDLE;
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
 000010     )
        
        
            // =========================================================================
            // Response outputs
            // =========================================================================
            assign rsp_valid   = (rsp_state == RSP_VALID);
            assign rsp_prdata  = r_rsp_prdata;
            assign rsp_pslverr = r_rsp_pslverr;
        
            // =========================================================================
            // Assertions
            // =========================================================================
            `ifndef SYNTHESIS
                // Command channel protocol checks
%000000         property p_cmd_valid_stable;
%000000             @(posedge aclk) disable iff (!aresetn)
%000000             (cmd_valid && !cmd_ready) |=> $stable(cmd_valid);
                endproperty
                assert_cmd_valid_stable: assert property (p_cmd_valid_stable)
                    else $error("cmd_valid deasserted before cmd_ready");
        
%000000         property p_cmd_data_stable;
%000000             @(posedge aclk) disable iff (!aresetn)
%000000             (cmd_valid && !cmd_ready) |=> (
%000000                 $stable(cmd_pwrite) &&
%000000                 $stable(cmd_paddr) &&
%000000                 $stable(cmd_pwdata) &&
%000000                 $stable(cmd_pstrb)
                    );
                endproperty
                assert_cmd_data_stable: assert property (p_cmd_data_stable)
                    else $error("cmd data changed before cmd_ready");
        
                // Response channel protocol checks
%000000         property p_rsp_valid_stable;
%000000             @(posedge aclk) disable iff (!aresetn)
%000000             (rsp_valid && !rsp_ready) |=> $stable(rsp_valid);
                endproperty
                assert_rsp_valid_stable: assert property (p_rsp_valid_stable)
                    else $error("rsp_valid deasserted before rsp_ready");
        
%000000         property p_rsp_data_stable;
%000000             @(posedge aclk) disable iff (!aresetn)
%000000             (rsp_valid && !rsp_ready) |=> (
%000000                 $stable(rsp_prdata) &&
%000000                 $stable(rsp_pslverr)
                    );
                endproperty
                assert_rsp_data_stable: assert property (p_rsp_data_stable)
                    else $error("rsp data changed before rsp_ready");
            `endif
        
        endmodule
        
