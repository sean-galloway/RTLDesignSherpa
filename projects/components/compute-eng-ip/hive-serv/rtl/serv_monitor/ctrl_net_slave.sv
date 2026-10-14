// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: 2024-2025 sean galloway
//
// RTL Design Sherpa - Industry-Standard RTL Design and Verification
// https://github.com/sean-galloway/RTLDesignSherpa
//
// Module: ctrl_net_slave
// Purpose: Control-network slave: decode 32-bit AXIS frames, update config,
//          queue 32-bit read responses over the uplink AXIS master.
//
// Documentation: projects/components/compute-eng-ip/hive-serv/docs/hive_mas/ch02_blocks/03_serv_monitor.md
// Subsystem: hive-serv
//
// Author: sean galloway
// Created: 2026-10-13

`timescale 1ns / 1ps

module ctrl_net_slave #(
    parameter int TILE_ID = 0
)(
    input  logic        clk,
    input  logic        rst_n,

    // AXIS slave: control commands from HIVE-C
    input  logic        s_axis_tvalid,
    output logic        s_axis_tready,
    input  logic [31:0] s_axis_tdata,

    // AXIS master: responses toward HIVE-C
    output logic        m_axis_tvalid,
    input  logic        m_axis_tready,
    output logic [31:0] m_axis_tdata,
    output logic [1:0]  m_axis_tuser,

    // Register read inputs (32-bit)
    input  logic [31:0] reg_rdata,

    // Generic register write port (for injector data words)
    output logic        reg_wr_en,
    output logic [7:0]  reg_wr_addr,
    output logic [15:0] reg_wr_data,

    // Dedicated command outputs
    output logic        thr_update,
    output logic [7:0]  thr_value,
    output logic        reset_stats,
    output logic        clear_errors,
    output logic        inj_commit,
    output logic [1:0]  inj_commit_tuser,
    output logic [7:0]  inj_commit_tdest
);

    // Opcodes (must match testbench)
    localparam logic [7:0] OP_WRITE_THR   = 8'h01;
    localparam logic [7:0] OP_RESET_STATS = 8'h02;
    localparam logic [7:0] OP_CLEAR_ERR   = 8'h03;
    localparam logic [7:0] OP_READ_REG    = 8'h10;
    localparam logic [7:0] OP_INJ_WORD0_L = 8'h20;
    localparam logic [7:0] OP_INJ_WORD0_H = 8'h21;
    localparam logic [7:0] OP_INJ_WORD1_L = 8'h22;
    localparam logic [7:0] OP_INJ_WORD1_H = 8'h23;
    localparam logic [7:0] OP_INJ_WORD2_L = 8'h24;
    localparam logic [7:0] OP_INJ_WORD2_H = 8'h25;
    localparam logic [7:0] OP_INJ_WORD3_L = 8'h26;
    localparam logic [7:0] OP_INJ_WORD3_H = 8'h27;
    localparam logic [7:0] OP_INJ_COMMIT  = 8'h28;
    localparam logic [7:0] OP_RESP_HI     = 8'h90;
    localparam logic [7:0] OP_RESP_LO     = 8'h91;

    // Frame fields
    logic [7:0]  frame_op;
    logic [7:0]  frame_target;
    logic [15:0] frame_payload;

    assign frame_op     = s_axis_tdata[31:24];
    assign frame_target = s_axis_tdata[23:16];
    assign frame_payload= s_axis_tdata[15:0];

    // State machine for read responses
    typedef enum logic [1:0] {
        ST_IDLE,
        ST_RESP_HI,
        ST_RESP_LO
    } state_t;
    state_t r_state;

    logic [31:0] r_read_data;
    logic [7:0]  r_read_addr;

    // Addressable to this tile or broadcast
    wire frame_for_me = (frame_target == TILE_ID[7:0]) || (frame_target == 8'hFF);

    // Command decode + read response state machine
    always_ff @(posedge clk or negedge rst_n) begin
        if (!rst_n) begin
            r_state       <= ST_IDLE;
            r_read_data   <= '0;
            r_read_addr   <= '0;
            reg_wr_en     <= 1'b0;
            reg_wr_addr   <= '0;
            reg_wr_data   <= '0;
            thr_update    <= 1'b0;
            thr_value     <= '0;
            reset_stats   <= 1'b0;
            clear_errors  <= 1'b0;
            inj_commit    <= 1'b0;
            inj_commit_tuser <= '0;
            inj_commit_tdest <= '0;
        end else begin
            // Default: single-cycle pulses
            reg_wr_en    <= 1'b0;
            thr_update   <= 1'b0;
            reset_stats  <= 1'b0;
            clear_errors <= 1'b0;
            inj_commit   <= 1'b0;

            case (r_state)
                ST_IDLE: begin
                    if (s_axis_tvalid && s_axis_tready && frame_for_me) begin
                        case (frame_op)
                            OP_WRITE_THR: begin
                                thr_update <= 1'b1;
                                thr_value  <= frame_payload[7:0];
                            end
                            OP_RESET_STATS: reset_stats <= 1'b1;
                            OP_CLEAR_ERR:   clear_errors <= 1'b1;
                            OP_READ_REG: begin
                                r_read_addr <= frame_payload[7:0];
                                r_read_data <= reg_rdata;
                                r_state     <= ST_RESP_HI;
                            end
                            OP_INJ_WORD0_L: begin reg_wr_en <= 1'b1; reg_wr_addr <= 8'h04; reg_wr_data <= frame_payload; end
                            OP_INJ_WORD0_H: begin reg_wr_en <= 1'b1; reg_wr_addr <= 8'h84; reg_wr_data <= frame_payload; end
                            OP_INJ_WORD1_L: begin reg_wr_en <= 1'b1; reg_wr_addr <= 8'h05; reg_wr_data <= frame_payload; end
                            OP_INJ_WORD1_H: begin reg_wr_en <= 1'b1; reg_wr_addr <= 8'h85; reg_wr_data <= frame_payload; end
                            OP_INJ_WORD2_L: begin reg_wr_en <= 1'b1; reg_wr_addr <= 8'h06; reg_wr_data <= frame_payload; end
                            OP_INJ_WORD2_H: begin reg_wr_en <= 1'b1; reg_wr_addr <= 8'h86; reg_wr_data <= frame_payload; end
                            OP_INJ_WORD3_L: begin reg_wr_en <= 1'b1; reg_wr_addr <= 8'h07; reg_wr_data <= frame_payload; end
                            OP_INJ_WORD3_H: begin reg_wr_en <= 1'b1; reg_wr_addr <= 8'h87; reg_wr_data <= frame_payload; end
                            OP_INJ_COMMIT: begin
                                inj_commit    <= 1'b1;
                                inj_commit_tuser <= frame_payload[9:8];
                                inj_commit_tdest <= frame_payload[7:0];
                            end
                            default: ;
                        endcase
                    end
                end
                ST_RESP_HI: begin
                    if (m_axis_tready) begin
                        r_state <= ST_RESP_LO;
                    end
                end
                ST_RESP_LO: begin
                    if (m_axis_tready) begin
                        r_state <= ST_IDLE;
                    end
                end
            endcase
        end
    end

    // s_axis_tready only in IDLE
    assign s_axis_tready = (r_state == ST_IDLE);

    // m_axis output
    always_comb begin
        case (r_state)
            ST_RESP_HI: begin
                m_axis_tvalid = 1'b1;
                m_axis_tdata  = {OP_RESP_HI, TILE_ID[7:0], r_read_data[31:16]};
                m_axis_tuser  = 2'b00;
            end
            ST_RESP_LO: begin
                m_axis_tvalid = 1'b1;
                m_axis_tdata  = {OP_RESP_LO, TILE_ID[7:0], r_read_data[15:0]};
                m_axis_tuser  = 2'b00;
            end
            default: begin
                m_axis_tvalid = 1'b0;
                m_axis_tdata  = '0;
                m_axis_tuser  = '0;
            end
        endcase
    end

endmodule : ctrl_net_slave
