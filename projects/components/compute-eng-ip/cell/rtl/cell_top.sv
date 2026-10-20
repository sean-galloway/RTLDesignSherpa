// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: 2024-2025 sean galloway
//
// RTL Design Sherpa - Industry-Standard RTL Design and Verification
// https://github.com/sean-galloway/RTLDesignSherpa
//
// Module: cell_top
// Purpose: Compute cell top-level: delta node + rx demux + registers + memories
//
// Documentation: projects/components/compute-eng-ip/cell/docs/PRD.md
// Subsystem: cell
//
// Author: sean galloway
// Created: 2026-10-18
//
// NOTE: Slice 1 wires the delta node's local port (P_LOCAL = 8) into the cell's
//       rx demux.  The eight mesh-facing ports (P_X_NEG/POS, P_Y_NEG/POS,
//       P_Z_NEG/POS, P_DIA, P_DIA2) pass straight through to the cell boundary.
//       Credit logic, packetizer, and execution FSM are placeholders.

`timescale 1ns / 1ps

`include "reset_defs.svh"

module cell_top #(
    parameter int LINE_W          = 32,
    parameter int COORD_W         = 4,
    parameter int POS_X           = 0,
    parameter int POS_Y           = 0,
    parameter int POS_Z           = 0,
    parameter int IN_DEPTH        = 32,
    parameter int OUT_DEPTH       = 32,
    parameter int AXIL_ADDR_WIDTH = 32,
    parameter int AXIL_DATA_WIDTH = 32,
    parameter int DATA_WIDTH      = 64,
    parameter int USER_WIDTH      = 64,
    parameter int NUM_VC          = 2
) (
    input  logic              aclk,
    input  logic              aresetn,

    // Mesh-facing AXI4-Stream ports (indices 0..7 correspond to delta ports
    // P_X_NEG, P_X_POS, P_Y_NEG, P_Y_POS, P_Z_NEG, P_Z_POS, P_DIA, P_DIA2).
    input  logic [DATA_WIDTH-1:0] s_axis_tdata  [8],
    input  logic                  s_axis_tvalid [8],
    output logic                  s_axis_tready [8],
    input  logic                  s_axis_tlast  [8],
    input  logic [USER_WIDTH-1:0] s_axis_tuser  [8],

    output logic [DATA_WIDTH-1:0] m_axis_tdata  [8],
    output logic                  m_axis_tvalid [8],
    input  logic                  m_axis_tready [8],
    output logic                  m_axis_tlast  [8],
    output logic [USER_WIDTH-1:0] m_axis_tuser  [8],

    // Per-VC credit sidebands (mesh ports only)
    input  logic [NUM_VC-1:0]     s_credit      [8],
    output logic [NUM_VC-1:0]     m_credit      [8],

    // AXI4-Lite register interface
    input  logic [AXIL_ADDR_WIDTH-1:0] s_axil_awaddr,
    input  logic                       s_axil_awvalid,
    output logic                       s_axil_awready,
    input  logic [AXIL_DATA_WIDTH-1:0] s_axil_wdata,
    input  logic [AXIL_DATA_WIDTH/8-1:0] s_axil_wstrb,
    input  logic                       s_axil_wvalid,
    output logic                       s_axil_wready,
    output logic [1:0]                 s_axil_bresp,
    output logic                       s_axil_bvalid,
    input  logic                       s_axil_bready,

    input  logic [AXIL_ADDR_WIDTH-1:0] s_axil_araddr,
    input  logic                       s_axil_arvalid,
    output logic                       s_axil_arready,
    output logic [AXIL_DATA_WIDTH-1:0] s_axil_rdata,
    output logic [1:0]                 s_axil_rresp,
    output logic                       s_axil_rvalid,
    input  logic                       s_axil_rready,

    // Observability / status
    output logic [31:0]           o_err_drop_cnt,
    output logic [31:0]           o_todo_credit_drop_cnt,
    output logic [31:0]           o_todo_cfg_read_drop_cnt,
    output logic                  o_irq,

    // Test-mode local rx injection (slice-1 verification hook)
    input  logic                  test_rx_valid,
    input  logic [DATA_WIDTH-1:0] test_rx_data,
    input  logic                  test_rx_last,
    input  logic [USER_WIDTH-1:0] test_rx_user,
    input  logic                  test_mode
);

    import cell_pkg::*;

    localparam int NUM_PORTS  = 9;
    localparam int NUM_MESH   = 8;
    localparam int IN_ADDR_W  = $clog2(IN_DEPTH);
    localparam int IN_OCC_W   = $clog2(IN_DEPTH + 1);
    localparam int OUT_ADDR_W = $clog2(OUT_DEPTH);
    localparam int OUT_OCC_W  = $clog2(OUT_DEPTH + 1);

    // -------------------------------------------------------------------------
    // Delta node arrays (9 ports: 0..7 mesh, 8 local)
    // -------------------------------------------------------------------------
    logic [DATA_WIDTH-1:0] delta_s_axis_tdata  [NUM_PORTS];
    logic                  delta_s_axis_tvalid [NUM_PORTS];
    logic                  delta_s_axis_tready [NUM_PORTS];
    logic                  delta_s_axis_tlast  [NUM_PORTS];
    logic [USER_WIDTH-1:0] delta_s_axis_tuser  [NUM_PORTS];
    logic [DATA_WIDTH-1:0] delta_m_axis_tdata  [NUM_PORTS];
    logic                  delta_m_axis_tvalid [NUM_PORTS];
    logic                  delta_m_axis_tready [NUM_PORTS];
    logic                  delta_m_axis_tlast  [NUM_PORTS];
    logic [USER_WIDTH-1:0] delta_m_axis_tuser  [NUM_PORTS];
    logic [NUM_VC-1:0]     delta_s_credit      [NUM_PORTS];
    logic [NUM_VC-1:0]     delta_m_credit      [NUM_PORTS];

    // -------------------------------------------------------------------------
    // Boundary-to-array wiring (mesh ports)
    // -------------------------------------------------------------------------
    generate
        for (genvar p = 0; p < NUM_MESH; p++) begin : gen_mesh_map
            assign delta_s_axis_tdata[p]  = s_axis_tdata[p];
            assign delta_s_axis_tvalid[p] = s_axis_tvalid[p];
            assign s_axis_tready[p]       = delta_s_axis_tready[p];
            assign delta_s_axis_tlast[p]  = s_axis_tlast[p];
            assign delta_s_axis_tuser[p]  = s_axis_tuser[p];

            assign m_axis_tdata[p]        = delta_m_axis_tdata[p];
            assign m_axis_tvalid[p]       = delta_m_axis_tvalid[p];
            assign delta_m_axis_tready[p] = m_axis_tready[p];
            assign m_axis_tlast[p]        = delta_m_axis_tlast[p];
            assign m_axis_tuser[p]        = delta_m_axis_tuser[p];

            assign delta_s_credit[p]      = s_credit[p];
            assign m_credit[p]            = delta_m_credit[p];
        end
    endgenerate

    // -------------------------------------------------------------------------
    // Local port wiring: delta P_LOCAL (8) <-> cell_rx
    // -------------------------------------------------------------------------
    logic [DATA_WIDTH-1:0] local_rx_data;
    logic                  local_rx_valid;
    logic                  local_rx_ready;
    logic                  local_rx_last;
    logic [USER_WIDTH-1:0] local_rx_user;

    assign delta_s_axis_tdata[NUM_MESH]  = '0;
    assign delta_s_axis_tvalid[NUM_MESH] = 1'b0;
    assign delta_s_axis_tlast[NUM_MESH]  = 1'b0;
    assign delta_s_axis_tuser[NUM_MESH]  = '0;
    assign delta_s_credit[NUM_MESH]      = '0;

    assign local_rx_data  = test_mode ? test_rx_data  : delta_m_axis_tdata[NUM_MESH];
    assign local_rx_valid = test_mode ? test_rx_valid : delta_m_axis_tvalid[NUM_MESH];
    assign delta_m_axis_tready[NUM_MESH] = local_rx_ready;
    assign local_rx_last  = test_mode ? test_rx_last  : delta_m_axis_tlast[NUM_MESH];
    assign local_rx_user  = test_mode ? test_rx_user  : delta_m_axis_tuser[NUM_MESH];

    // -------------------------------------------------------------------------
    // Delta node instance
    // -------------------------------------------------------------------------
    delta_mesh_cell #(
        .DATA_WIDTH     (DATA_WIDTH),
        .USER_WIDTH     (USER_WIDTH),
        .COORD_W        (COORD_W),
        .POS_X          (POS_X),
        .POS_Y          (POS_Y),
        .POS_Z          (POS_Z),
        .GRID_X         (4),
        .GRID_Y         (4),
        .GRID_Z         (1),
        .NUM_VC         (NUM_VC)
    ) u_delta (
        .aclk           (aclk),
        .aresetn        (aresetn),
        .s_axis_tdata   (delta_s_axis_tdata),
        .s_axis_tvalid  (delta_s_axis_tvalid),
        .s_axis_tready  (delta_s_axis_tready),
        .s_axis_tlast   (delta_s_axis_tlast),
        .s_axis_tuser   (delta_s_axis_tuser),
        .m_axis_tdata   (delta_m_axis_tdata),
        .m_axis_tvalid  (delta_m_axis_tvalid),
        .m_axis_tready  (delta_m_axis_tready),
        .m_axis_tlast   (delta_m_axis_tlast),
        .m_axis_tuser   (delta_m_axis_tuser),
        .s_credit       (delta_s_credit),
        .m_credit       (delta_m_credit),
        .wrap_mask      (9'b0),
        .o_err_drop_cnt (o_err_drop_cnt),
        .o_mode_acks    (),
        .o_bulk_starved (),
        .o_spec_active  (),
        .o_dft_active   ()
    );

    // -------------------------------------------------------------------------
    // RX demux
    // -------------------------------------------------------------------------
    logic              mem_wr_valid;
    logic              mem_wr_ready;
    logic [IN_ADDR_W-1:0] mem_wr_addr;
    logic [LINE_W-1:0]    mem_wr_data;
    logic [COORD_BITS-1:0] mem_wr_src_coord;

    logic              cfg_wr_valid;
    logic              cfg_wr_ready;
    logic [7:0]        cfg_wr_addr;
    logic [31:0]       cfg_wr_data;

    logic              cfg_rd_valid;
    logic [7:0]        cfg_rd_addr;

    logic              inc_lines_in;
    logic              inc_err_drop;

    cell_rx #(
        .LINE_W  (LINE_W),
        .COORD_W (COORD_W),
        .IN_DEPTH(IN_DEPTH),
        .POS_X   (POS_X),
        .POS_Y   (POS_Y),
        .POS_Z   (POS_Z)
    ) u_rx (
        .aclk                     (aclk),
        .aresetn                  (aresetn),
        .s_valid                  (local_rx_valid),
        .s_ready                  (local_rx_ready),
        .s_data                   (local_rx_data),
        .s_last                   (local_rx_last),
        .s_user                   (local_rx_user),
        .mem_wr_valid             (mem_wr_valid),
        .mem_wr_ready             (mem_wr_ready),
        .mem_wr_addr              (mem_wr_addr),
        .mem_wr_data              (mem_wr_data),
        .mem_wr_src_coord         (mem_wr_src_coord),
        .cfg_wr_valid             (cfg_wr_valid),
        .cfg_wr_ready             (cfg_wr_ready),
        .cfg_wr_addr              (cfg_wr_addr),
        .cfg_wr_data              (cfg_wr_data),
        .cfg_rd_valid             (cfg_rd_valid),
        .cfg_rd_addr              (cfg_rd_addr),
        .inc_lines_in             (inc_lines_in),
        .inc_err_drop             (inc_err_drop),
        .o_todo_credit_drop_cnt   (o_todo_credit_drop_cnt),
        .o_todo_cfg_read_drop_cnt (o_todo_cfg_read_drop_cnt)
    );

    // -------------------------------------------------------------------------
    // Memory status signals (declared early so the register file can read them)
    // -------------------------------------------------------------------------
    logic              mem_in_empty;
    logic              mem_in_full;
    logic [IN_OCC_W-1:0]  mem_in_occupancy;

    logic              mem_out_empty;
    logic              mem_out_full;
    logic [OUT_OCC_W-1:0] mem_out_occupancy;

    // -------------------------------------------------------------------------
    // Register file
    // -------------------------------------------------------------------------
    logic [31:0] r_ctrl;
    logic [31:0] r_func_sel;
    logic [31:0] r_op_lines;
    logic [31:0] r_emit_batch_x;
    logic [31:0] r_credit_batch_n;
    logic [31:0] r_irq_en;
    logic [31:0] r_irq_status;
    logic [31:0] r_a, r_b, r_c, r_d, r_t;
    logic [31:0] r_op_src;
    logic [31:0] r_dest;
    logic [31:0] r_ip;
    logic [31:0] r_op;

    logic soft_rst;

    cell_cfg_regs #(
        .AXIL_ADDR_WIDTH(AXIL_ADDR_WIDTH),
        .AXIL_DATA_WIDTH(AXIL_DATA_WIDTH)
    ) u_cfg (
        .aclk                   (aclk),
        .aresetn                (aresetn),
        .s_axil_awaddr          (s_axil_awaddr),
        .s_axil_awvalid         (s_axil_awvalid),
        .s_axil_awready         (s_axil_awready),
        .s_axil_wdata           (s_axil_wdata),
        .s_axil_wstrb           (s_axil_wstrb),
        .s_axil_wvalid          (s_axil_wvalid),
        .s_axil_wready          (s_axil_wready),
        .s_axil_bresp           (s_axil_bresp),
        .s_axil_bvalid          (s_axil_bvalid),
        .s_axil_bready          (s_axil_bready),
        .s_axil_araddr          (s_axil_araddr),
        .s_axil_arvalid         (s_axil_arvalid),
        .s_axil_arready         (s_axil_arready),
        .s_axil_rdata           (s_axil_rdata),
        .s_axil_rresp           (s_axil_rresp),
        .s_axil_rvalid          (s_axil_rvalid),
        .s_axil_rready          (s_axil_rready),
        .cfg_wr_valid           (cfg_wr_valid),
        .cfg_wr_addr            (cfg_wr_addr),
        .cfg_wr_data            (cfg_wr_data),
        .cfg_wr_ready           (cfg_wr_ready),
        .cfg_rd_valid           (cfg_rd_valid),
        .cfg_rd_addr            (cfg_rd_addr),
        .cfg_rd_data            (),
        .cfg_rd_ready           (),
        .inc_lines_in           (inc_lines_in),
        .inc_lines_out          (1'b0),
        .inc_credits            (1'b0),
        .inc_pkts               (1'b0),
        .status_input_empty     (mem_in_empty),
        .status_result_nonempty (!mem_out_empty),
        .status_grant_nonzero   (1'b0),
        .r_ctrl                 (r_ctrl),
        .r_func_sel             (r_func_sel),
        .r_op_lines             (r_op_lines),
        .r_emit_batch_x         (r_emit_batch_x),
        .r_credit_batch_n       (r_credit_batch_n),
        .r_irq_en               (r_irq_en),
        .r_irq_status           (r_irq_status),
        .r_a                    (r_a),
        .r_b                    (r_b),
        .r_c                    (r_c),
        .r_d                    (r_d),
        .r_t                    (r_t),
        .r_op_src               (r_op_src),
        .r_dest                 (r_dest),
        .r_ip                   (r_ip),
        .r_op                   (r_op),
        .o_soft_rst             (soft_rst),
        .o_irq                  (o_irq)
    );

    // -------------------------------------------------------------------------
    // Input memory
    // -------------------------------------------------------------------------
    logic [IN_ADDR_W-1:0] mem_in_rd_addr;
    logic              mem_in_rd_valid;
    logic              mem_in_rd_ready;
    logic [LINE_W-1:0] mem_in_rd_data;
    logic [COORD_BITS-1:0] mem_in_rd_src_coord;

    cell_mem_in #(
        .LINE_W  (LINE_W),
        .COORD_W (COORD_W),
        .IN_DEPTH(IN_DEPTH)
    ) u_mem_in (
        .aclk          (aclk),
        .aresetn       (aresetn),
        .wr_valid      (mem_wr_valid),
        .wr_ready      (mem_wr_ready),
        .wr_addr       (mem_wr_addr),
        .wr_data       (mem_wr_data),
        .wr_src_coord  (mem_wr_src_coord),
        .rd_valid      (mem_in_rd_valid),
        .rd_ready      (mem_in_rd_ready),
        .rd_addr       (mem_in_rd_addr),
        .rd_data       (mem_in_rd_data),
        .rd_src_coord  (mem_in_rd_src_coord),
        .o_empty       (mem_in_empty),
        .o_full        (mem_in_full),
        .o_occupancy   (mem_in_occupancy)
    );

    // -------------------------------------------------------------------------
    // Result memory
    // -------------------------------------------------------------------------
    cell_mem_out #(
        .LINE_W   (LINE_W),
        .OUT_DEPTH(OUT_DEPTH)
    ) u_mem_out (
        .aclk        (aclk),
        .aresetn     (aresetn),
        .wr_valid    (1'b0),
        .wr_ready    (),
        .wr_addr     ('0),
        .wr_data     ('0),
        .rd_valid    (1'b0),
        .rd_ready    (),
        .rd_addr     ('0),
        .rd_data     (),
        .o_empty     (mem_out_empty),
        .o_full      (mem_out_full),
        .o_occupancy (mem_out_occupancy)
    );

    // -------------------------------------------------------------------------
    // Slice-3 FSM read-side tie-off: the FSM does not exist yet, so the read
    // port is held idle.  The memory still exposes its read data for probes.
    // -------------------------------------------------------------------------
    assign mem_in_rd_valid = 1'b0;
    assign mem_in_rd_addr  = '0;

endmodule : cell_top
