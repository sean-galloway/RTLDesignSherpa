// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: 2026 sean galloway
//
// Module: axil_to_axi4_wide_align_wr
// Purpose: Drop-in replacement for axi4_dwidth_converter_wr when the
//          slave-side master is effectively AXIL (single-beat, narrow).
//
// Why this exists:
//   The narrow→wide upsize converter `axi_data_upsize` aggregates N
//   narrow beats into one wide beat by beat counter. For an AXIL
//   master (every transfer is single-beat at a sub-row address),
//   every beat lands at lane 0 of the wide bus regardless of awaddr.
//   The bridge generator wraps AXIL masters with `axi4_slave_wr`
//   which presents fub_axi_* with awlen=0/awsize=narrow/awburst=01 —
//   and this module replaces the buggy upsize in that path.
//
//   Per AXI4 spec for single-beat narrow writes on a wide bus:
//     - awaddr's low bits identify the byte offset within the wide row
//     - wstrb[b]=1 enables wdata[8*b +: 8] (byte lane b carries data)
//   So the master is responsible for placing its narrow data and
//   strobes at the correct byte lanes. This module does that
//   master-side alignment.
//
// Interface: AXI4 slave (matches axi4_dwidth_converter_wr's slave
// port) on the master-side; emits a single-beat wide AXI4 write.
// awlen/awsize on the slave side are ignored (always treated as
// single-beat narrow → single-beat wide aligned).

`timescale 1ns / 1ps

`include "reset_defs.svh"

module axil_to_axi4_wide_align_wr #(
    parameter int S_AXI_DATA_WIDTH  = 32,
    parameter int M_AXI_DATA_WIDTH  = 256,
    parameter int AXI_ID_WIDTH      = 8,
    parameter int AXI_ADDR_WIDTH    = 32,
    parameter int AXI_USER_WIDTH    = 1,
    parameter int SKID_DEPTH_AW     = 2,   // accepted for API parity
    parameter int SKID_DEPTH_W      = 2,
    parameter int SKID_DEPTH_B      = 2
) (
    input  logic                                  aclk,
    input  logic                                  aresetn,

    // -------- AXI4 slave (from master via wrapper) --------
    input  logic [AXI_ID_WIDTH-1:0]               s_axi_awid,
    input  logic [AXI_ADDR_WIDTH-1:0]             s_axi_awaddr,
    input  logic [7:0]                            s_axi_awlen,
    input  logic [2:0]                            s_axi_awsize,
    input  logic [1:0]                            s_axi_awburst,
    input  logic                                  s_axi_awlock,
    input  logic [3:0]                            s_axi_awcache,
    input  logic [2:0]                            s_axi_awprot,
    input  logic [3:0]                            s_axi_awqos,
    input  logic [3:0]                            s_axi_awregion,
    input  logic [AXI_USER_WIDTH-1:0]             s_axi_awuser,
    input  logic                                  s_axi_awvalid,
    output logic                                  s_axi_awready,

    input  logic [S_AXI_DATA_WIDTH-1:0]           s_axi_wdata,
    input  logic [S_AXI_DATA_WIDTH/8-1:0]         s_axi_wstrb,
    input  logic                                  s_axi_wlast,
    input  logic [AXI_USER_WIDTH-1:0]             s_axi_wuser,
    input  logic                                  s_axi_wvalid,
    output logic                                  s_axi_wready,

    output logic [AXI_ID_WIDTH-1:0]               s_axi_bid,
    output logic [1:0]                            s_axi_bresp,
    output logic [AXI_USER_WIDTH-1:0]             s_axi_buser,
    output logic                                  s_axi_bvalid,
    input  logic                                  s_axi_bready,

    // -------- AXI4 master (to crossbar / wide slave) --------
    output logic [AXI_ID_WIDTH-1:0]               m_axi_awid,
    output logic [AXI_ADDR_WIDTH-1:0]             m_axi_awaddr,
    output logic [7:0]                            m_axi_awlen,
    output logic [2:0]                            m_axi_awsize,
    output logic [1:0]                            m_axi_awburst,
    output logic                                  m_axi_awlock,
    output logic [3:0]                            m_axi_awcache,
    output logic [2:0]                            m_axi_awprot,
    output logic [3:0]                            m_axi_awqos,
    output logic [3:0]                            m_axi_awregion,
    output logic [AXI_USER_WIDTH-1:0]             m_axi_awuser,
    output logic                                  m_axi_awvalid,
    input  logic                                  m_axi_awready,

    output logic [M_AXI_DATA_WIDTH-1:0]           m_axi_wdata,
    output logic [M_AXI_DATA_WIDTH/8-1:0]         m_axi_wstrb,
    output logic                                  m_axi_wlast,
    output logic [AXI_USER_WIDTH-1:0]             m_axi_wuser,
    output logic                                  m_axi_wvalid,
    input  logic                                  m_axi_wready,

    input  logic [AXI_ID_WIDTH-1:0]               m_axi_bid,
    input  logic [1:0]                            m_axi_bresp,
    input  logic [AXI_USER_WIDTH-1:0]             m_axi_buser,
    input  logic                                  m_axi_bvalid,
    output logic                                  m_axi_bready
);

    localparam int M_STRB_W       = M_AXI_DATA_WIDTH / 8;
    localparam int S_STRB_W       = S_AXI_DATA_WIDTH / 8;
    localparam int RATIO          = M_AXI_DATA_WIDTH / S_AXI_DATA_WIDTH;
    localparam int SLOT_W         = $clog2(RATIO);
    localparam int ROW_LSB        = $clog2(M_STRB_W);
    localparam int SLOT_LSB       = $clog2(S_STRB_W);
    localparam int WIDE_SIZE_LOG2 = $clog2(M_STRB_W);

    // ----------------------------------------------------------------
    // 1-deep independent AW and W latches.
    // ----------------------------------------------------------------
    logic [AXI_ID_WIDTH-1:0]       r_aw_id;
    logic [AXI_ADDR_WIDTH-1:0]     r_aw_addr;
    logic [2:0]                    r_aw_prot;
    logic [3:0]                    r_aw_cache;
    logic [AXI_USER_WIDTH-1:0]     r_aw_user;
    logic                          r_aw_full;
    logic [S_AXI_DATA_WIDTH-1:0]   r_w_data;
    logic [S_STRB_W-1:0]           r_w_strb;
    logic [AXI_USER_WIDTH-1:0]     r_w_user;
    logic                          r_w_full;

    logic consume_beat;
    wire  beat_pair_ready = r_aw_full && r_w_full;

    assign s_axi_awready = !r_aw_full;
    assign s_axi_wready  = !r_w_full;

    `ALWAYS_FF_RST(aclk, aresetn,
        if (`RST_ASSERTED(aresetn)) begin
            r_aw_full  <= 1'b0;
            r_aw_id    <= '0;
            r_aw_addr  <= '0;
            r_aw_prot  <= '0;
            r_aw_cache <= '0;
            r_aw_user  <= '0;
            r_w_full   <= 1'b0;
            r_w_data   <= '0;
            r_w_strb   <= '0;
            r_w_user   <= '0;
        end else begin
            if (s_axi_awvalid && s_axi_awready) begin
                r_aw_full  <= 1'b1;
                r_aw_id    <= s_axi_awid;
                r_aw_addr  <= s_axi_awaddr;
                r_aw_prot  <= s_axi_awprot;
                r_aw_cache <= s_axi_awcache;
                r_aw_user  <= s_axi_awuser;
            end else if (consume_beat) begin
                r_aw_full <= 1'b0;
            end

            if (s_axi_wvalid && s_axi_wready) begin
                r_w_full <= 1'b1;
                r_w_data <= s_axi_wdata;
                r_w_strb <= s_axi_wstrb;
                r_w_user <= s_axi_wuser;
            end else if (consume_beat) begin
                r_w_full <= 1'b0;
            end
        end
    )

    // ----------------------------------------------------------------
    // Forwarder FSM
    // ----------------------------------------------------------------
    typedef enum logic [1:0] {
        S_IDLE = 2'd0,
        S_AW   = 2'd1,
        S_W    = 2'd2,
        S_B    = 2'd3
    } state_e;

    state_e r_state, w_next_state;

    always_comb begin
        w_next_state = r_state;
        consume_beat = 1'b0;
        case (r_state)
            S_IDLE: if (beat_pair_ready) begin
                consume_beat = 1'b1;
                w_next_state = S_AW;
            end
            S_AW: if (m_axi_awvalid && m_axi_awready) w_next_state = S_W;
            S_W:  if (m_axi_wvalid  && m_axi_wready)  w_next_state = S_B;
            S_B:  if (m_axi_bvalid  && m_axi_bready)  w_next_state = S_IDLE;
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
    // Held (matched) beat — drives m_axi_* through multi-cycle handshakes.
    // ----------------------------------------------------------------
    logic [AXI_ID_WIDTH-1:0]     r_held_id;
    logic [AXI_ADDR_WIDTH-1:0]   r_held_addr;
    logic [2:0]                  r_held_prot;
    logic [3:0]                  r_held_cache;
    logic [AXI_USER_WIDTH-1:0]   r_held_awuser;
    logic [S_AXI_DATA_WIDTH-1:0] r_held_data;
    logic [S_STRB_W-1:0]         r_held_strb;
    logic [AXI_USER_WIDTH-1:0]   r_held_wuser;

    `ALWAYS_FF_RST(aclk, aresetn,
        if (`RST_ASSERTED(aresetn)) begin
            r_held_id     <= '0;
            r_held_addr   <= '0;
            r_held_prot   <= '0;
            r_held_cache  <= '0;
            r_held_awuser <= '0;
            r_held_data   <= '0;
            r_held_strb   <= '0;
            r_held_wuser  <= '0;
        end else if (consume_beat) begin
            r_held_id     <= r_aw_id;
            r_held_addr   <= r_aw_addr;
            r_held_prot   <= r_aw_prot;
            r_held_cache  <= r_aw_cache;
            r_held_awuser <= r_aw_user;
            r_held_data   <= r_w_data;
            r_held_strb   <= r_w_strb;
            r_held_wuser  <= r_w_user;
        end
    )

    // ----------------------------------------------------------------
    // Alignment — slot = held_addr[SLOT_LSB +: SLOT_W]
    //   m_axi_wdata: place S_AXI_DATA_WIDTH bits at slot*S_AXI_DATA_WIDTH
    //   m_axi_wstrb: place S_STRB_W bits at slot*S_STRB_W
    //   m_axi_awaddr: row-aligned (addr & ~(M_STRB_W-1))
    // ----------------------------------------------------------------
    wire [SLOT_W-1:0]         held_slot = r_held_addr[SLOT_LSB +: SLOT_W];
    wire [AXI_ADDR_WIDTH-1:0] row_addr_mask =
        ~({{(AXI_ADDR_WIDTH-ROW_LSB){1'b0}}, {ROW_LSB{1'b1}}});

    logic [M_AXI_DATA_WIDTH-1:0] aligned_wdata;
    logic [M_STRB_W-1:0]         aligned_wstrb;
    always_comb begin
        aligned_wdata = '0;
        aligned_wstrb = '0;
        aligned_wdata[held_slot * S_AXI_DATA_WIDTH +: S_AXI_DATA_WIDTH]
            = r_held_data;
        aligned_wstrb[held_slot * S_STRB_W +: S_STRB_W]
            = r_held_strb;
    end

    // ----------------------------------------------------------------
    // Wide-side master drives
    // ----------------------------------------------------------------
    assign m_axi_awid     = r_held_id;
    assign m_axi_awaddr   = r_held_addr & row_addr_mask;
    assign m_axi_awlen    = 8'd0;                       // single beat
    assign m_axi_awsize   = WIDE_SIZE_LOG2[2:0];
    assign m_axi_awburst  = 2'b01;                      // INCR
    assign m_axi_awlock   = 1'b0;
    assign m_axi_awcache  = r_held_cache;
    assign m_axi_awprot   = r_held_prot;
    assign m_axi_awqos    = 4'b0;
    assign m_axi_awregion = 4'b0;
    assign m_axi_awuser   = r_held_awuser;
    assign m_axi_awvalid  = (r_state == S_AW);
    assign m_axi_wdata    = aligned_wdata;
    assign m_axi_wstrb    = aligned_wstrb;
    assign m_axi_wlast    = 1'b1;
    assign m_axi_wuser    = r_held_wuser;
    assign m_axi_wvalid   = (r_state == S_W);
    assign m_axi_bready   = (r_state == S_B);

    // ----------------------------------------------------------------
    // B response back to slave-side. Forward bid/bresp/buser.
    // ----------------------------------------------------------------
    logic                       r_s_bvalid;
    logic [AXI_ID_WIDTH-1:0]    r_s_bid;
    logic [1:0]                 r_s_bresp;
    logic [AXI_USER_WIDTH-1:0]  r_s_buser;
    `ALWAYS_FF_RST(aclk, aresetn,
        if (`RST_ASSERTED(aresetn)) begin
            r_s_bvalid <= 1'b0;
            r_s_bid    <= '0;
            r_s_bresp  <= 2'b00;
            r_s_buser  <= '0;
        end else begin
            if (r_state == S_B && m_axi_bvalid && m_axi_bready) begin
                r_s_bvalid <= 1'b1;
                r_s_bid    <= m_axi_bid;
                r_s_bresp  <= m_axi_bresp;
                r_s_buser  <= m_axi_buser;
            end else if (r_s_bvalid && s_axi_bready) begin
                r_s_bvalid <= 1'b0;
            end
        end
    )
    assign s_axi_bvalid = r_s_bvalid;
    assign s_axi_bid    = r_s_bid;
    assign s_axi_bresp  = r_s_bresp;
    assign s_axi_buser  = r_s_buser;

    /* verilator lint_off UNUSED */
    wire _unused = &{1'b0, s_axi_awlen, s_axi_awsize, s_axi_awburst,
                     s_axi_awlock, s_axi_awqos, s_axi_awregion,
                     s_axi_wlast,
                     SKID_DEPTH_AW, SKID_DEPTH_W, SKID_DEPTH_B};
    /* verilator lint_on UNUSED */

endmodule : axil_to_axi4_wide_align_wr
