// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: 2026 sean galloway
//
// RTL Design Sherpa - Industry-Standard RTL Design and Verification
// https://github.com/sean-galloway/RTLDesignSherpa
//
// Module: rapids_g_equiv_tb_top
// Purpose: rapids-g equivalence bench (rapids TASK-034).  NUM_CHANNELS FSM
//          schedulers (fub/scheduler, side "f") and NUM_CHANNELS
//          gatling-sequenced schedulers (fub_g/scheduler_g + one
//          rapids_seq_g, side "g") side by side.  The testbench drives both
//          sides with the same descriptors and its own engine model per
//          side, and compares what each side asks of its engines: every
//          (address, beats) command, every packet record, the MonBus event
//          stream and the final state.  The latency differs; the sequences
//          may not.
//
// Every per-channel signal is a packed [NUM_CHANNELS-1:0] array; wide ones
// are [NUM_CHANNELS-1:0][W-1:0].  The control engines are not modelled here
// (ctrl ready/idle tied to 1): the macro suites cover them.
//
// Author: sean galloway
// Created: 2026-10-21

`timescale 1ns / 1ps

module rapids_g_equiv_tb_top #(
    parameter int NUM_CHANNELS = 4,
    parameter int NUM_HARTS    = NUM_CHANNELS,   // rapids_seq_g's harts: NUM_CHANNELS / NUM_HARTS slots each
    parameter int ADDR_WIDTH   = 64,
    parameter int DATA_WIDTH   = 256,
    parameter int OFF_W        = $clog2(DATA_WIDTH / 8)
) (
    input  logic                                 clk,
    input  logic                                 rst_n,

    input  logic [NUM_CHANNELS-1:0]              cfg_channel_enable,
    // per side, so a reset can land in the same state on both
    input  logic [NUM_CHANNELS-1:0]              f_cfg_channel_reset,
    input  logic [NUM_CHANNELS-1:0]              g_cfg_channel_reset,
    input  logic [31:0]                          cfg_sched_timeout_cycles,
    input  logic [7:0]                           cfg_sched_timeout_limit,
    input  logic                                 cfg_sched_timeout_enable,

    // ---- side f: the FSM scheduler -------------------------------------
    input  logic [NUM_CHANNELS-1:0]              f_desc_valid,
    output logic [NUM_CHANNELS-1:0]              f_desc_ready,
    input  logic [NUM_CHANNELS-1:0][255:0]       f_desc_packet,
    input  logic [NUM_CHANNELS-1:0][255:0]       f_desc_ext,
    output logic [NUM_CHANNELS-1:0]              f_rd_valid,
    output logic [NUM_CHANNELS-1:0][ADDR_WIDTH-1:0] f_rd_addr,
    output logic [NUM_CHANNELS-1:0][31:0]        f_rd_beats,
    output logic [NUM_CHANNELS-1:0]              f_rd_pkt_valid,
    input  logic [NUM_CHANNELS-1:0]              f_rd_pkt_ready,
    output logic [NUM_CHANNELS-1:0][31:0]        f_rd_pkt_bytes,
    output logic [NUM_CHANNELS-1:0][OFF_W-1:0]   f_rd_pkt_offset,
    output logic [NUM_CHANNELS-1:0]              f_wr_valid,
    input  logic [NUM_CHANNELS-1:0]              f_wr_ready,
    output logic [NUM_CHANNELS-1:0][ADDR_WIDTH-1:0] f_wr_addr,
    output logic [NUM_CHANNELS-1:0][31:0]        f_wr_beats,
    output logic [NUM_CHANNELS-1:0]              f_wr_pkt_valid,
    input  logic [NUM_CHANNELS-1:0]              f_wr_pkt_ready,
    output logic [NUM_CHANNELS-1:0][31:0]        f_wr_pkt_bytes,
    output logic [NUM_CHANNELS-1:0][OFF_W-1:0]   f_wr_pkt_offset,
    input  logic [NUM_CHANNELS-1:0]              f_rd_done,
    input  logic [NUM_CHANNELS-1:0][31:0]        f_rd_done_beats,
    input  logic [NUM_CHANNELS-1:0]              f_wr_done,
    input  logic [NUM_CHANNELS-1:0][31:0]        f_wr_done_beats,
    input  logic [NUM_CHANNELS-1:0]              f_wr_commit,
    input  logic [NUM_CHANNELS-1:0][31:0]        f_wr_commit_beats,
    input  logic [NUM_CHANNELS-1:0]              f_rd_error,
    input  logic [NUM_CHANNELS-1:0]              f_wr_error,
    output logic [NUM_CHANNELS-1:0]              f_mon_valid,
    output logic [NUM_CHANNELS-1:0][127:0]       f_mon_packet,
    output logic [NUM_CHANNELS-1:0][6:0]         f_state,
    output logic [NUM_CHANNELS-1:0]              f_idle,

    // ---- side g: scheduler_g + rapids_seq_g -----------------------------
    input  logic [NUM_CHANNELS-1:0]              g_desc_valid,
    output logic [NUM_CHANNELS-1:0]              g_desc_ready,
    input  logic [NUM_CHANNELS-1:0][255:0]       g_desc_packet,
    input  logic [NUM_CHANNELS-1:0][255:0]       g_desc_ext,
    output logic [NUM_CHANNELS-1:0]              g_rd_valid,
    output logic [NUM_CHANNELS-1:0][ADDR_WIDTH-1:0] g_rd_addr,
    output logic [NUM_CHANNELS-1:0][31:0]        g_rd_beats,
    output logic [NUM_CHANNELS-1:0]              g_rd_pkt_valid,
    input  logic [NUM_CHANNELS-1:0]              g_rd_pkt_ready,
    output logic [NUM_CHANNELS-1:0][31:0]        g_rd_pkt_bytes,
    output logic [NUM_CHANNELS-1:0][OFF_W-1:0]   g_rd_pkt_offset,
    output logic [NUM_CHANNELS-1:0]              g_wr_valid,
    input  logic [NUM_CHANNELS-1:0]              g_wr_ready,
    output logic [NUM_CHANNELS-1:0][ADDR_WIDTH-1:0] g_wr_addr,
    output logic [NUM_CHANNELS-1:0][31:0]        g_wr_beats,
    output logic [NUM_CHANNELS-1:0]              g_wr_pkt_valid,
    input  logic [NUM_CHANNELS-1:0]              g_wr_pkt_ready,
    output logic [NUM_CHANNELS-1:0][31:0]        g_wr_pkt_bytes,
    output logic [NUM_CHANNELS-1:0][OFF_W-1:0]   g_wr_pkt_offset,
    input  logic [NUM_CHANNELS-1:0]              g_rd_done,
    input  logic [NUM_CHANNELS-1:0][31:0]        g_rd_done_beats,
    input  logic [NUM_CHANNELS-1:0]              g_wr_done,
    input  logic [NUM_CHANNELS-1:0][31:0]        g_wr_done_beats,
    input  logic [NUM_CHANNELS-1:0]              g_wr_commit,
    input  logic [NUM_CHANNELS-1:0][31:0]        g_wr_commit_beats,
    input  logic [NUM_CHANNELS-1:0]              g_rd_error,
    input  logic [NUM_CHANNELS-1:0]              g_wr_error,
    output logic [NUM_CHANNELS-1:0]              g_mon_valid,
    output logic [NUM_CHANNELS-1:0][127:0]       g_mon_packet,
    output logic [NUM_CHANNELS-1:0][6:0]         g_state,
    output logic [NUM_CHANNELS-1:0]              g_idle,
    output logic [7:0]                           g_alg_max,      // the image's highest next-address selector
    output logic [NUM_HARTS-1:0]                 g_hart_halted
);

    // The sequencer's buses (side g)
    logic [NUM_CHANNELS-1:0]        s_wr_en, s_attn, s_fault;
    logic [4:0]                     s_wr_addr, s_rd_addr;
    logic [31:0]                    s_wr_data;
    logic [7:0]                     s_alg_max;
    assign g_alg_max = s_alg_max;
    logic [NUM_CHANNELS-1:0][31:0]  s_rd_data;

    rapids_seq_g #(
        .NUM_CHANNELS (NUM_CHANNELS),
        .NUM_HARTS    (NUM_HARTS)
    ) u_seq (
        .clk               (clk),
        .rst_n             (rst_n),
        .cfg_channel_reset (g_cfg_channel_reset),
        .seq_restart       (1'b0),               // no restart: the board harness's GO alone pulses it
        .seq_wr_en         (s_wr_en),
        .seq_wr_addr       (s_wr_addr),
        .seq_wr_data       (s_wr_data),
        .seq_rd_addr       (s_rd_addr),
        .seq_rd_data       (s_rd_data),
        .seq_attn          (s_attn),
        .seq_fault         (s_fault),
        .seq_alg_max       (s_alg_max),
        // the register mailbox is idle here: the scheduler firmware never uses it
        .reg_cmd_valid     (),
        .reg_cmd_ready     (1'b0),
        .reg_cmd_pwrite    (),
        .reg_cmd_paddr     (),
        .reg_cmd_pwdata    (),
        .reg_rsp_valid     (1'b0),
        .reg_rsp_ready     (),
        .reg_rsp_prdata    (32'h0),
        .reg_rsp_pslverr   (1'b0),
        .hart_halted       (g_hart_halted)
    );

    // The two sides' common port list, by side prefix
    `define RAPIDS_G_EQUIV_PORTS(P)                                  \
        .clk                      (clk),                             \
        .rst_n                    (rst_n),                           \
        .cfg_channel_enable       (cfg_channel_enable[ch]),          \
        .cfg_channel_reset        (P``_cfg_channel_reset[ch]),       \
        .cfg_sched_timeout_cycles (cfg_sched_timeout_cycles),        \
        .cfg_sched_timeout_limit  (cfg_sched_timeout_limit),         \
        .cfg_sched_timeout_enable (cfg_sched_timeout_enable),        \
        .tile_adv_done            (1'b1),                            \
        .tile_dest_legal          ('1),                              \
        .scheduler_idle           (P``_idle[ch]),                    \
        .scheduler_state          (P``_state[ch]),                   \
        .descriptor_valid         (P``_desc_valid[ch]),              \
        .descriptor_ready         (P``_desc_ready[ch]),              \
        .descriptor_packet        (P``_desc_packet[ch]),             \
        .descriptor_ext_packet    (P``_desc_ext[ch]),                \
        .descriptor_error         (1'b0),                            \
        .sched_rd_valid           (P``_rd_valid[ch]),                \
        .sched_rd_addr            (P``_rd_addr[ch]),                 \
        .sched_rd_beats           (P``_rd_beats[ch]),                \
        .sched_rd_pkt_valid       (P``_rd_pkt_valid[ch]),            \
        .sched_rd_pkt_ready       (P``_rd_pkt_ready[ch]),            \
        .sched_rd_pkt_bytes       (P``_rd_pkt_bytes[ch]),            \
        .sched_rd_pkt_offset      (P``_rd_pkt_offset[ch]),           \
        .sched_rd_pkt_tile        (),                                \
        .sched_wr_valid           (P``_wr_valid[ch]),                \
        .sched_wr_ready           (P``_wr_ready[ch]),                \
        .sched_wr_addr            (P``_wr_addr[ch]),                 \
        .sched_wr_beats           (P``_wr_beats[ch]),                \
        .sched_wr_pkt_valid       (P``_wr_pkt_valid[ch]),            \
        .sched_wr_pkt_ready       (P``_wr_pkt_ready[ch]),            \
        .sched_wr_pkt_bytes       (P``_wr_pkt_bytes[ch]),            \
        .sched_wr_pkt_offset      (P``_wr_pkt_offset[ch]),           \
        .sched_rd_done_strobe     (P``_rd_done[ch]),                 \
        .sched_rd_beats_done      (P``_rd_done_beats[ch]),           \
        .sched_wr_done_strobe     (P``_wr_done[ch]),                 \
        .sched_wr_beats_done      (P``_wr_done_beats[ch]),           \
        .sched_wr_commit_strobe   (P``_wr_commit[ch]),               \
        .sched_wr_commit_beats    (P``_wr_commit_beats[ch]),         \
        .ctrlrd_valid             (),                                \
        .ctrlrd_ready             (1'b1),                            \
        .ctrlrd_addr              (),                                \
        .ctrlrd_data              (),                                \
        .ctrlrd_mask              (),                                \
        .ctrlrd_error             (1'b0),                            \
        .ctrlrd_idle              (1'b1),                            \
        .ctrlwr_valid             (),                                \
        .ctrlwr_ready             (1'b1),                            \
        .ctrlwr_addr              (),                                \
        .ctrlwr_data              (),                                \
        .ctrlwr_error             (1'b0),                            \
        .ctrlwr_idle              (1'b1),                            \
        .sched_rd_error           (P``_rd_error[ch]),                \
        .sched_wr_error           (P``_wr_error[ch]),                \
        .sched_error              (),                                \
        .dbg_descriptor_error     (),                                \
        .dbg_read_error_sticky    (),                                \
        .dbg_write_error_sticky   (),                                \
        .dbg_timeout_expired      (),                                \
        .i_mon_time               ('0),                              \
        .mon_valid                (P``_mon_valid[ch]),               \
        .mon_ready                (1'b1),                            \
        .mon_packet               (P``_mon_packet[ch]),              \
        .mon_timestamp            ()

    /* verilator lint_off PINCONNECTEMPTY */
    for (genvar ch = 0; ch < NUM_CHANNELS; ch++) begin : gen_ch
        scheduler #(
            .CHANNEL_ID     (ch),
            .NUM_CHANNELS   (NUM_CHANNELS),
            .ADDR_WIDTH     (ADDR_WIDTH),
            .DATA_WIDTH     (DATA_WIDTH),
            .MON_CHANNEL_ID (9'(ch))
        ) u_f (
            `RAPIDS_G_EQUIV_PORTS(f)
        );

        scheduler_g #(
            .CHANNEL_ID     (ch),
            .NUM_CHANNELS   (NUM_CHANNELS),
            .ADDR_WIDTH     (ADDR_WIDTH),
            .DATA_WIDTH     (DATA_WIDTH),
            .MON_CHANNEL_ID (9'(ch))
        ) u_g (
            .seq_wr_en   (s_wr_en[ch]),
            .seq_wr_addr (s_wr_addr),
            .seq_wr_data (s_wr_data),
            .seq_rd_addr (s_rd_addr),
            .seq_rd_data (s_rd_data[ch]),
            .seq_attn    (s_attn[ch]),
            .seq_fault   (s_fault[ch]),
            .seq_alg_max (s_alg_max),
            `RAPIDS_G_EQUIV_PORTS(g)
        );
    end
    /* verilator lint_on PINCONNECTEMPTY */

    `undef RAPIDS_G_EQUIV_PORTS

endmodule : rapids_g_equiv_tb_top
