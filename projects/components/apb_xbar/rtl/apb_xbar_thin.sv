// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: 2024-2025 sean galloway
//
// RTL Design Sherpa - Industry-Standard RTL Design and Verification
// https://github.com/sean-galloway/RTLDesignSherpa
//
// Module: apb_xbar_thin
// Purpose: Apb Xbar Thin module
//
// Documentation: rtl/amba/PRD.md
// Subsystem: amba
//
// Author: sean galloway
// Created: 2025-10-18

`timescale 1ns / 1ps

`include "reset_defs.svh"

module apb_xbar_thin #(
    // Number of APB masters (from the master))
    parameter int M = 2,
    // Number of APB slaves (to the dest)
    parameter int S = 4,
    // Address width
    parameter int ADDR_WIDTH = 32,
    // Data widthMAX_THRESH_WIDTH
    parameter int DATA_WIDTH = 32,
    // Strobe width
    parameter int STRB_WIDTH = DATA_WIDTH/8,
    parameter int MAX_THRESH = 16,
    // local abbreviations
    parameter int DW    = DATA_WIDTH,
    parameter int AW    = ADDR_WIDTH,
    parameter int SW    = STRB_WIDTH,
    parameter int MTW   = $clog2(MAX_THRESH),
    parameter int MXMTW = M * MTW
) (
    input  logic                         pclk,
    input  logic                         presetn,

    // Slave enable for addr decoding
    input  logic [S-1:0]                 SLAVE_ENABLE,
    // Slave address base
    input  logic [S-1:0][ADDR_WIDTH-1:0] SLAVE_ADDR_BASE,
    // Slave address limit
    input  logic [S-1:0][ADDR_WIDTH-1:0] SLAVE_ADDR_LIMIT,
    // Thresholds for the Weighted Round Robin Arbiter
    input  logic [MXMTW-1:0]             THRESHOLDS,

    // Master interfaces - These are from the APB master
    input  logic [M-1:0]                 m_apb_psel,
    input  logic [M-1:0]                 m_apb_penable,
    input  logic [M-1:0]                 m_apb_pwrite,
    input  logic [M-1:0][2:0]            m_apb_pprot,
    input  logic [M-1:0][ADDR_WIDTH-1:0] m_apb_paddr,
    input  logic [M-1:0][DATA_WIDTH-1:0] m_apb_pwdata,
    input  logic [M-1:0][STRB_WIDTH-1:0] m_apb_pstrb,
    output logic [M-1:0]                 m_apb_pready,
    output logic [M-1:0][DATA_WIDTH-1:0] m_apb_prdata,
    output logic [M-1:0]                 m_apb_pslverr,

    // Slave interfaces - these are to the APB destinations
    output logic [S-1:0]                 s_apb_psel,
    output logic [S-1:0]                 s_apb_penable,
    output logic [S-1:0]                 s_apb_pwrite,
    output logic [S-1:0][2:0]            s_apb_pprot,
    output logic [S-1:0][ADDR_WIDTH-1:0] s_apb_paddr,
    output logic [S-1:0][DATA_WIDTH-1:0] s_apb_pwdata,
    output logic [S-1:0][STRB_WIDTH-1:0] s_apb_pstrb,
    input  logic [S-1:0]                 s_apb_pready,
    input  logic [S-1:0][DATA_WIDTH-1:0] s_apb_prdata,
    input  logic [S-1:0]                 s_apb_pslverr
);

    // synopsys translate_off
    integer file;

    initial begin
        file = $fopen("debug_log.txt", "w");
        if (file == 0) begin
            $display("Error: could not open file.");
            $finish;
        end
    end
    // synopsys translate_on

    ////////////////////////////////////////////////////////////////////////////////////////////////
    // Address decoding logic
    logic [S-1:0][M-1:0]             master_sel;

    generate
        for (genvar s_dec = 0; s_dec < S; s_dec++) begin : gen_decoder
            always_comb begin
                for (int m_dec = 0; m_dec < M; m_dec++) begin
                    master_sel[s_dec][m_dec] = 1'b0;
                    if (m_apb_psel[m_dec] && SLAVE_ENABLE[s_dec] &&
                            (m_apb_paddr[m_dec] >= SLAVE_ADDR_BASE[s_dec]) &&
                            (m_apb_paddr[m_dec] <= SLAVE_ADDR_LIMIT[s_dec])) begin
                        master_sel[s_dec][m_dec] = 1'b1;
                        // synopsys translate_off
                        $fdisplay(file, "Decode: Time=%0t s_dec=%0h m_dec=%0h", $realtime/1e3, s_dec, m_dec); // verilog_lint: waive line-length
                        // synopsys translate_on
                    end
                end
            end
        end
    endgenerate

    ////////////////////////////////////////////////////////////////////////////////////////////////
    // Instantiate arbiters for each slave
    logic [S-1:0]                arb_gnt_valid;
    logic [S-1:0][M-1:0]         arb_gnt;

    // Fix: Ensure the size of arb_gnt_id matches the arbiter module's output width
    // Using $clog2(M) instead of $clog2(M):0
    logic [S-1:0][$clog2(M)-1:0] arb_gnt_id;

    // Generate per-slave, per-master ACK signals
    logic [S-1:0][M-1:0] arb_gnt_ack;

    // Generate ACK logic
    generate
        for (genvar s_ack = 0; s_ack < S; s_ack++) begin : gen_ack_logic
            for (genvar m_ack = 0; m_ack < M; m_ack++) begin : gen_master_ack
                `ALWAYS_FF_RST(pclk, presetn,
                    if (~presetn)
                        arb_gnt_ack[s_ack][m_ack] <= 1'b0;
                    else begin
                        // ACK only if:
                        // 1. This slave arbiter granted access to this master
                        // 2. The transaction on this slave completed
                        arb_gnt_ack[s_ack][m_ack] <= arb_gnt[s_ack][m_ack] &&
                                                    s_apb_pready[s_ack] &&
                                                    s_apb_psel[s_ack] &&
                                                    s_apb_penable[s_ack];
                    end
                )

            end
        end
    endgenerate

    // Connect each arbiter to its ACK signals
    generate
        for (genvar s_arb = 0; s_arb < S; s_arb++) begin : gen_arbiters
            arbiter_round_robin_weighted #(
                .MAX_LEVELS  (16),
                .CLIENTS     (M),
                .WAIT_GNT_ACK(1)
            ) arbiter_inst(
                .clk         (pclk),
                .rst_n       (presetn),
                .block_arb   (1'b0),
                .max_thresh  (THRESHOLDS),
                .request     (master_sel[s_arb]),
                .grant_valid (arb_gnt_valid[s_arb]),
                .grant       (arb_gnt[s_arb]),
                .grant_id    (arb_gnt_id[s_arb]),
                .grant_ack   (arb_gnt_ack[s_arb])  // ← Now [M-1:0] per slave
            );
        end
    endgenerate

    // synopsys translate_off
    always_comb begin
        for (int s_loop=0; s_loop<S; s_loop++) begin
            $fdisplay(file, "Arbiter outputs @ %0t", $realtime/1e3);
            $fdisplay(file, "s_loop=%0d arb_gnt_valid=%0b", s_loop, arb_gnt_valid[s_loop]);
            $fdisplay(file, "s_loop=%0d arb_gnt=%0b", s_loop, arb_gnt[s_loop]);
            $fdisplay(file, "s_loop=%0d arb_gnt_id=%0d", s_loop, arb_gnt_id[s_loop]);
        end
    end

    always_comb begin
        for (int m_loop=0; m_loop<M; m_loop++) begin
            $fdisplay(file, "Time=%0t m_loop=%0d: psel=%0b penable=%0b pready=%0b pwrite=%0b pprot=%0h paddr=%0h pwdata=%0h pstrb=%0h", // verilog_lint: waive line-length
                    $realtime/1e3, m_loop,
                    m_apb_psel[m_loop], m_apb_pready[m_loop], m_apb_penable[m_loop], m_apb_pwrite[m_loop], // verilog_lint: waive line-length
                    m_apb_pprot[m_loop], m_apb_paddr[m_loop], m_apb_pwdata[m_loop],
                    m_apb_pstrb[m_loop]);

        end
    end
    // synopsys translate_on

    ////////////////////////////////////////////////////////////////////////////////////////////////
    // Slave interface multiplexing
    generate
        for (genvar s_mux = 0; s_mux < S; s_mux++) begin : gen_slave_mux
            always_comb begin
                // Fix: Ensure proper width for mst_id to match array indexing
                logic [$clog2(M)-1:0] mst_id;
                mst_id = arb_gnt_id[s_mux];

                s_apb_psel[s_mux]    = arb_gnt_valid[s_mux] ? m_apb_psel[mst_id] : 1'b0;
                s_apb_penable[s_mux] = arb_gnt_valid[s_mux] ? m_apb_penable[mst_id] : 1'b0;
                s_apb_pwrite[s_mux]  = arb_gnt_valid[s_mux] ? m_apb_pwrite[mst_id] : 1'b0;
                s_apb_pprot[s_mux]   = arb_gnt_valid[s_mux] ? m_apb_pprot[mst_id] : '0;
                s_apb_paddr[s_mux]   = arb_gnt_valid[s_mux] ? m_apb_paddr[mst_id] : '0;
                s_apb_pwdata[s_mux]  = arb_gnt_valid[s_mux] ? m_apb_pwdata[mst_id] : '0;
                s_apb_pstrb[s_mux]   = arb_gnt_valid[s_mux] ? m_apb_pstrb[mst_id] : '0;
    // synopsys translate_off
                $fdisplay(file, "Master Sel: mst_id=%0d s_mux=%0d arb_gnt_valid=%0b @ %0t ns",
                    mst_id, s_mux, arb_gnt_valid, $realtime / 1e3);
    // synopsys translate_on
            end
        end
    endgenerate

    ////////////////////////////////////////////////////////////////////////////////////////////////
    // Master interface
    // Declare the new array with swapped dimensions
    logic [M-1:0][S-1:0] arb_gnt_mst;

    // Generate block to swap indices
    generate
        for (genvar m = 0; m < M; m++) begin : gen_arb_gnt_mst_m
            for (genvar s = 0; s < S; s++) begin : gen_arb_gnt_mst_s
                always_comb begin
                    arb_gnt_mst[m][s] = arb_gnt[s][m];
                end
            end
        end
    endgenerate

    generate
        for (genvar m_demux = 0; m_demux < M; m_demux++) begin : gen_demux
            always_comb begin
                m_apb_pready[m_demux]  = 1'b0;  // default value
                m_apb_prdata[m_demux]  = '0;    // default value
                m_apb_pslverr[m_demux] = 1'b0;  // default value
                for (int s_demux = 0; s_demux < S; s_demux++) begin
                    if (arb_gnt_mst[m_demux][s_demux]) begin
                        m_apb_pready[m_demux]  = s_apb_pready[s_demux];
                        m_apb_prdata[m_demux]  = s_apb_prdata[s_demux];
                        m_apb_pslverr[m_demux] = s_apb_pslverr[s_demux];
    // synopsys translate_off
                        $fdisplay(file, "DeMux Sel: m_demux=%0d s_demux=%0d @ %0t ns",
                            m_demux, s_demux, $realtime / 1e3);
    // synopsys translate_on
                    end
                end
            end
        end
    endgenerate

endmodule : apb_xbar_thin
