//      // verilator_coverage annotation
        // SPDX-License-Identifier: MIT
        // SPDX-FileCopyrightText: 2024-2025 sean galloway
        //
        // RTL Design Sherpa - Industry-Standard RTL Design and Verification
        // https://github.com/sean-galloway/RTLDesignSherpa
        //
        // Module: apb_slave
        // Purpose: Apb Slave module
        //
        // Documentation: rtl/amba/PRD.md
        // Subsystem: amba
        //
        // Author: sean galloway
        // Created: 2025-10-18
        
        `timescale 1ns / 1ps
        
        `include "reset_defs.svh"
        
        module apb_slave #(
            parameter int ADDR_WIDTH      = 32,
            parameter int DATA_WIDTH      = 32,
            parameter int STRB_WIDTH      = 32 / 8,
            parameter int PROT_WIDTH      = 3,
            parameter int DEPTH      = 2,
            // Short Parameters
            parameter int DW  = DATA_WIDTH,
            parameter int AW  = ADDR_WIDTH,
            parameter int SW  = STRB_WIDTH,
            parameter int PW  = PROT_WIDTH,
            parameter int CPW = AW + DW + SW + PW + 1, // verilog_lint: waive line-length
            parameter int RPW = DW + 1
        ) (
            // Clock and Reset
 002323     input  logic              pclk,
%000001     input  logic              presetn,
        
            // APB interface
 000024     input  logic              s_apb_PSEL,
 000024     input  logic              s_apb_PENABLE,
 000024     output logic              s_apb_PREADY,
%000000     input  logic [AW-1:0]     s_apb_PADDR,
 000014     input  logic              s_apb_PWRITE,
%000000     input  logic [DW-1:0]     s_apb_PWDATA,
 000024     input  logic [SW-1:0]     s_apb_PSTRB,
%000000     input  logic [PW-1:0]     s_apb_PPROT,
%000000     output logic [DW-1:0]     s_apb_PRDATA,
%000000     output logic              s_apb_PSLVERR,
        
            // Command Interface
 000024     output logic              cmd_valid,
%000005     input  logic              cmd_ready,
 000014     output logic              cmd_pwrite,
%000000     output logic [AW-1:0]     cmd_paddr,
%000000     output logic [DW-1:0]     cmd_pwdata,
 000024     output logic [SW-1:0]     cmd_pstrb,
%000000     output logic [PW-1:0]     cmd_pprot,
        
            // Response Interface
 000024     input  logic              rsp_valid,
%000001     output logic              rsp_ready,
%000000     input  logic [DW-1:0]     rsp_prdata,
%000000     input  logic              rsp_pslverr
        );
        
            // Load command packet signals
 000024     logic                r_cmd_valid;
%000001     logic                r_cmd_ready;
%000000     logic                r_cmd_ready_pre;
%000000     logic [CPW-1:0]      r_cmd_data_in;
%000000     logic [CPW-1:0]      r_cmd_data_out;
%000000     logic [3:0]          r_cmd_count;
        
            assign r_cmd_data_in = { s_apb_PWRITE, s_apb_PPROT, s_apb_PSTRB, s_apb_PADDR, s_apb_PWDATA};
            assign {cmd_pwrite, cmd_pprot, cmd_pstrb, cmd_paddr, cmd_pwdata} = r_cmd_data_out;
        
            gaxi_skid_buffer #(
                .DEPTH(DEPTH),
                .DATA_WIDTH(CPW)
            ) cmd_skid_buffer_inst (
                .axi_aclk     (pclk),
                .axi_aresetn  (presetn),
                .wr_valid     (r_cmd_valid),
                .wr_ready     (r_cmd_ready),
                .wr_data      (r_cmd_data_in),
                .rd_valid     (cmd_valid),
                .rd_ready     (cmd_ready),
                .rd_data      (r_cmd_data_out),
                .count        (r_cmd_count),
                /* verilator lint_off PINCONNECTEMPTY */
                .rd_count     ()
                /* verilator lint_on PINCONNECTEMPTY */
            );
        
            // Extract response packet signals
 000024     logic                r_rsp_valid;
 000024     logic                r_rsp_ready;
%000000     logic [RPW-1:0]      r_rsp_data_in;
%000000     logic [DW-1:0]       r_rsp_prdata;
%000000     logic                r_rsp_pslverr;
%000000     logic [RPW-1:0]      r_rsp_data_out;
%000000     logic [3:0]          r_rsp_count;
        
            assign {r_rsp_pslverr, r_rsp_prdata} = r_rsp_data_out;
            assign r_rsp_data_in = {rsp_pslverr, rsp_prdata};
        
            gaxi_skid_buffer #(
                .DEPTH(DEPTH),
                .DATA_WIDTH(RPW)
            ) resp_skid_buffer_inst (
                .axi_aclk     (pclk),
                .axi_aresetn  (presetn),
                .wr_valid     (rsp_valid),
                .wr_ready     (rsp_ready),
                .wr_data      (r_rsp_data_in),
                .rd_valid     (r_rsp_valid),
                .rd_ready     (r_rsp_ready),
                .rd_data      (r_rsp_data_out),
                .count        (r_rsp_count),
                /* verilator lint_off PINCONNECTEMPTY */
                .rd_count     ()
                /* verilator lint_on PINCONNECTEMPTY */
            );
        
            // APB FSM
            typedef enum logic [2:0] {
                IDLE = 3'b001,
                BUSY = 3'b010,
                WAIT = 3'b100
            } apb_state_t;
        
 000024     apb_state_t r_apb_state;
 000024     logic r_penable_prev;  // Track previous PENABLE to detect rising edge
        
            `ALWAYS_FF_RST(pclk, presetn,
                if (`RST_ASSERTED(presetn)) begin
                    r_apb_state   <= IDLE;
                    s_apb_PREADY  <= 'b0;
                    s_apb_PSLVERR <= 'b0;
                    s_apb_PRDATA  <= 'b0;
                    r_cmd_valid   <= 1'b0;
                    r_rsp_ready   <= 1'b0;
                    r_penable_prev <= 1'b0;
                end else begin
                    // default states
                    r_apb_state <= r_apb_state;
                    s_apb_PREADY  <= 'b0;
                    s_apb_PSLVERR <= 'b0;
                    // s_apb_PRDATA  <= 'b0;  // Don't clear - APB requires it to be stable
                    r_cmd_valid   <= 1'b0;
                    r_rsp_ready   <= 1'b0;
                    r_penable_prev <= s_apb_PENABLE;
        
                    casez (r_apb_state)
        
                        IDLE: begin
                            // Only capture on rising edge of PENABLE (SETUP->ACCESS transition)
                            if (s_apb_PSEL && s_apb_PENABLE && !r_penable_prev && r_cmd_ready) begin
                                r_cmd_valid <= 1'b1;
                                r_apb_state <= BUSY;
                            end
                        end
        
                        BUSY: begin
                            if (r_rsp_valid) begin
                                s_apb_PREADY   <= 1'b1;
                                s_apb_PRDATA   <= r_rsp_prdata;
                                s_apb_PSLVERR  <= r_rsp_pslverr;
                                r_rsp_ready    <= 1'b1;
                                r_apb_state    <= WAIT;
                            end
                        end
                        WAIT: r_apb_state <= IDLE;
        
                        // verilator coverage_off
                        // DEFENSIVE: Illegal FSM state recovery
                        default: r_apb_state <= IDLE;
                        // verilator coverage_on
        
                    endcase
                end
 000011     )
        
        
        endmodule : apb_slave
        
