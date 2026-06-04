// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: 2026 sean galloway
//
// Module: axil_to_axi4_wide_align_rd
// Purpose: Drop-in replacement for axi4_dwidth_converter_rd when the
//          slave-side master is effectively AXIL (single-beat, narrow).
//
// Mirror of axil_to_axi4_wide_align_wr — for sub-row narrow reads
// from a wider slave, the wide R beat has the requested slot at byte
// offset (araddr & wide_mask)*8. The generic narrow→wide dnsize
// emits multiple narrow beats by beat counter, not the slot the
// master asked for. This module:
//   - Accepts one AXI4 single-beat narrow AR (awlen/awsize ignored).
//   - Emits one wide AXI4 single-beat AR at the row-aligned address.
//   - On the wide R beat, extracts the narrow slot via araddr's low
//     bits and returns it as the narrow R.

`timescale 1ns / 1ps

`include "reset_defs.svh"

module axil_to_axi4_wide_align_rd #(
    parameter int S_AXI_DATA_WIDTH  = 32,
    parameter int M_AXI_DATA_WIDTH  = 256,
    parameter int AXI_ID_WIDTH      = 8,
    parameter int AXI_ADDR_WIDTH    = 32,
    parameter int AXI_USER_WIDTH    = 1,
    parameter int SKID_DEPTH_AR     = 2,
    parameter int SKID_DEPTH_R      = 4
) (
    input  logic                                  aclk,
    input  logic                                  aresetn,

    // -------- AXI4 slave (from master via wrapper) --------
    input  logic [AXI_ID_WIDTH-1:0]               s_axi_arid,
    input  logic [AXI_ADDR_WIDTH-1:0]             s_axi_araddr,
    input  logic [7:0]                            s_axi_arlen,
    input  logic [2:0]                            s_axi_arsize,
    input  logic [1:0]                            s_axi_arburst,
    input  logic                                  s_axi_arlock,
    input  logic [3:0]                            s_axi_arcache,
    input  logic [2:0]                            s_axi_arprot,
    input  logic [3:0]                            s_axi_arqos,
    input  logic [3:0]                            s_axi_arregion,
    input  logic [AXI_USER_WIDTH-1:0]             s_axi_aruser,
    input  logic                                  s_axi_arvalid,
    output logic                                  s_axi_arready,

    output logic [AXI_ID_WIDTH-1:0]               s_axi_rid,
    output logic [S_AXI_DATA_WIDTH-1:0]           s_axi_rdata,
    output logic [1:0]                            s_axi_rresp,
    output logic                                  s_axi_rlast,
    output logic [AXI_USER_WIDTH-1:0]             s_axi_ruser,
    output logic                                  s_axi_rvalid,
    input  logic                                  s_axi_rready,

    // -------- AXI4 master (to crossbar / wide slave) --------
    output logic [AXI_ID_WIDTH-1:0]               m_axi_arid,
    output logic [AXI_ADDR_WIDTH-1:0]             m_axi_araddr,
    output logic [7:0]                            m_axi_arlen,
    output logic [2:0]                            m_axi_arsize,
    output logic [1:0]                            m_axi_arburst,
    output logic                                  m_axi_arlock,
    output logic [3:0]                            m_axi_arcache,
    output logic [2:0]                            m_axi_arprot,
    output logic [3:0]                            m_axi_arqos,
    output logic [3:0]                            m_axi_arregion,
    output logic [AXI_USER_WIDTH-1:0]             m_axi_aruser,
    output logic                                  m_axi_arvalid,
    input  logic                                  m_axi_arready,

    input  logic [AXI_ID_WIDTH-1:0]               m_axi_rid,
    input  logic [M_AXI_DATA_WIDTH-1:0]           m_axi_rdata,
    input  logic [1:0]                            m_axi_rresp,
    input  logic                                  m_axi_rlast,
    input  logic [AXI_USER_WIDTH-1:0]             m_axi_ruser,
    input  logic                                  m_axi_rvalid,
    output logic                                  m_axi_rready
);

    localparam int M_STRB_W       = M_AXI_DATA_WIDTH / 8;
    localparam int S_STRB_W       = S_AXI_DATA_WIDTH / 8;
    localparam int RATIO          = M_AXI_DATA_WIDTH / S_AXI_DATA_WIDTH;
    localparam int SLOT_W         = $clog2(RATIO);
    localparam int ROW_LSB        = $clog2(M_STRB_W);
    localparam int SLOT_LSB       = $clog2(S_STRB_W);
    localparam int WIDE_SIZE_LOG2 = $clog2(M_STRB_W);

    // ----------------------------------------------------------------
    // 1-deep AR latch
    // ----------------------------------------------------------------
    logic [AXI_ID_WIDTH-1:0]      r_ar_id;
    logic [AXI_ADDR_WIDTH-1:0]    r_ar_addr;
    logic [2:0]                   r_ar_prot;
    logic [3:0]                   r_ar_cache;
    logic [AXI_USER_WIDTH-1:0]    r_ar_user;
    logic                         r_ar_full;
    logic                         consume_ar;

    assign s_axi_arready = !r_ar_full;

    `ALWAYS_FF_RST(aclk, aresetn,
        if (`RST_ASSERTED(aresetn)) begin
            r_ar_full  <= 1'b0;
            r_ar_id    <= '0;
            r_ar_addr  <= '0;
            r_ar_prot  <= '0;
            r_ar_cache <= '0;
            r_ar_user  <= '0;
        end else begin
            if (s_axi_arvalid && s_axi_arready) begin
                r_ar_full  <= 1'b1;
                r_ar_id    <= s_axi_arid;
                r_ar_addr  <= s_axi_araddr;
                r_ar_prot  <= s_axi_arprot;
                r_ar_cache <= s_axi_arcache;
                r_ar_user  <= s_axi_aruser;
            end else if (consume_ar) begin
                r_ar_full <= 1'b0;
            end
        end
    )

    // ----------------------------------------------------------------
    // Forwarder FSM
    //   IDLE → AR: latch ready → emit wide AR
    //   AR   → R:  m_axi_arvalid/arready done
    //   R    → S:  wide R captured → drive narrow R
    //   S    → IDLE: narrow R handshake completes
    // ----------------------------------------------------------------
    typedef enum logic [1:0] {
        S_IDLE = 2'd0,
        S_AR   = 2'd1,
        S_R    = 2'd2,
        S_S    = 2'd3
    } state_e;

    state_e r_state, w_next_state;

    always_comb begin
        w_next_state = r_state;
        consume_ar   = 1'b0;
        case (r_state)
            S_IDLE: if (r_ar_full) begin
                consume_ar   = 1'b1;
                w_next_state = S_AR;
            end
            S_AR: if (m_axi_arvalid && m_axi_arready) w_next_state = S_R;
            S_R:  if (m_axi_rvalid  && m_axi_rready)  w_next_state = S_S;
            S_S:  if (s_axi_rvalid  && s_axi_rready)  w_next_state = S_IDLE;
            default: w_next_state = S_IDLE;
        endcase
    end

    `ALWAYS_FF_RST(aclk, aresetn,
        if (`RST_ASSERTED(aresetn)) begin
            r_state <= S_IDLE;
        end else begin
            r_state <= w_next_state;
        end
    )

    // ----------------------------------------------------------------
    // Held AR + the wide R beat we just got back.
    // ----------------------------------------------------------------
    logic [AXI_ID_WIDTH-1:0]      r_held_id;
    logic [AXI_ADDR_WIDTH-1:0]    r_held_addr;
    logic [2:0]                   r_held_prot;
    logic [3:0]                   r_held_cache;
    logic [AXI_USER_WIDTH-1:0]    r_held_aruser;
    logic [M_AXI_DATA_WIDTH-1:0]  r_wide_rdata;
    logic [1:0]                   r_wide_rresp;
    logic [AXI_USER_WIDTH-1:0]    r_wide_ruser;

    `ALWAYS_FF_RST(aclk, aresetn,
        if (`RST_ASSERTED(aresetn)) begin
            r_held_id     <= '0;
            r_held_addr   <= '0;
            r_held_prot   <= '0;
            r_held_cache  <= '0;
            r_held_aruser <= '0;
            r_wide_rdata  <= '0;
            r_wide_rresp  <= 2'b00;
            r_wide_ruser  <= '0;
        end else begin
            if (consume_ar) begin
                r_held_id     <= r_ar_id;
                r_held_addr   <= r_ar_addr;
                r_held_prot   <= r_ar_prot;
                r_held_cache  <= r_ar_cache;
                r_held_aruser <= r_ar_user;
            end
            if (r_state == S_R && m_axi_rvalid && m_axi_rready) begin
                r_wide_rdata <= m_axi_rdata;
                r_wide_rresp <= m_axi_rresp;
                r_wide_ruser <= m_axi_ruser;
            end
        end
    )

    wire [SLOT_W-1:0]         held_slot = r_held_addr[SLOT_LSB +: SLOT_W];
    wire [AXI_ADDR_WIDTH-1:0] row_addr_mask =
        ~({{(AXI_ADDR_WIDTH-ROW_LSB){1'b0}}, {ROW_LSB{1'b1}}});

    // ----------------------------------------------------------------
    // Wide-side AXI4 master drives
    // ----------------------------------------------------------------
    assign m_axi_arid     = r_held_id;
    assign m_axi_araddr   = r_held_addr & row_addr_mask;
    assign m_axi_arlen    = 8'd0;
    assign m_axi_arsize   = WIDE_SIZE_LOG2[2:0];
    assign m_axi_arburst  = 2'b01;
    assign m_axi_arlock   = 1'b0;
    assign m_axi_arcache  = r_held_cache;
    assign m_axi_arprot   = r_held_prot;
    assign m_axi_arqos    = 4'b0;
    assign m_axi_arregion = 4'b0;
    assign m_axi_aruser   = r_held_aruser;
    assign m_axi_arvalid  = (r_state == S_AR);
    assign m_axi_rready   = (r_state == S_R);

    // ----------------------------------------------------------------
    // Narrow R: extract the slot from the wide R data.
    // ----------------------------------------------------------------
    assign s_axi_rid    = r_held_id;
    assign s_axi_rdata  = r_wide_rdata[held_slot * S_AXI_DATA_WIDTH
                                       +: S_AXI_DATA_WIDTH];
    assign s_axi_rresp  = r_wide_rresp;
    assign s_axi_rlast  = (r_state == S_S);   // single beat → last on the only beat
    assign s_axi_ruser  = r_wide_ruser;
    assign s_axi_rvalid = (r_state == S_S);

    /* verilator lint_off UNUSED */
    wire _unused = &{1'b0, s_axi_arlen, s_axi_arsize, s_axi_arburst,
                     s_axi_arlock, s_axi_arqos, s_axi_arregion,
                     m_axi_rid, m_axi_rlast,
                     SKID_DEPTH_AR, SKID_DEPTH_R};
    /* verilator lint_on UNUSED */

endmodule : axil_to_axi4_wide_align_rd
