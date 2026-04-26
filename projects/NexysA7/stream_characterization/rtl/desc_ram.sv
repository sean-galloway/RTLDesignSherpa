// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: 2025 sean galloway
//
// Module: desc_ram
// Purpose: Dual-port descriptor RAM with AXI4-Lite write and AXI4 read.
//
// Host loads STREAM descriptors via AXI4-Lite writes (32-bit word at a time).
// STREAM fetches descriptors via AXI4 reads (256-bit wide, single beat).
//
// Protocol logic is hand-rolled for simplicity; every upstream channel is
// isolated by a gaxi_skid_buffer for timing closure. Five skid buffers total:
//   - AXIL AW (host -> internal write engine)
//   - AXIL W  (host -> internal write engine)
//   - AXIL B  (internal -> host)
//   - AXI4 AR (STREAM -> internal read engine)
//   - AXI4 R  (internal -> STREAM)
//
// Storage is a dual-port BRAM organized as DEPTH_256 x 256-bit. The AXIL
// write path does read-modify-write because the BRAM is 256-bit wide and
// the AXIL writes are 32-bit.

`timescale 1ns / 1ps

`include "reset_defs.svh"

module desc_ram #(
    parameter int AXI_ID_WIDTH   = 8,
    parameter int AXI_USER_WIDTH = 3,
    parameter int AXI_ADDR_WIDTH = 32,
    parameter int DEPTH_256      = 2048,  // 2048 x 256 = 512 Kbits = 64 KB

    parameter int SKID_DEPTH_AW = 2,
    parameter int SKID_DEPTH_W  = 2,
    parameter int SKID_DEPTH_B  = 2,
    parameter int SKID_DEPTH_AR = 2,
    parameter int SKID_DEPTH_R  = 4
) (
    input  logic                        aclk,
    input  logic                        aresetn,

    // =====================================================================
    // AXI4-Lite slave: host writes descriptors (32-bit)
    // =====================================================================
    input  logic [31:0]                 s_axil_awaddr,
    input  logic [2:0]                  s_axil_awprot,
    input  logic                        s_axil_awvalid,
    output logic                        s_axil_awready,

    input  logic [31:0]                 s_axil_wdata,
    input  logic [3:0]                  s_axil_wstrb,
    input  logic                        s_axil_wvalid,
    output logic                        s_axil_wready,

    output logic [1:0]                  s_axil_bresp,
    output logic                        s_axil_bvalid,
    input  logic                        s_axil_bready,

    // Read side of AXIL is unused (desc RAM is write-only from host)
    input  logic [31:0]                 s_axil_araddr,
    input  logic [2:0]                  s_axil_arprot,
    input  logic                        s_axil_arvalid,
    output logic                        s_axil_arready,
    output logic [31:0]                 s_axil_rdata,
    output logic [1:0]                  s_axil_rresp,
    output logic                        s_axil_rvalid,
    input  logic                        s_axil_rready,

    // =====================================================================
    // AXI4 slave: STREAM fetches descriptors (256-bit, single-beat)
    // =====================================================================
    input  logic [AXI_ID_WIDTH-1:0]     s_axi_arid,
    input  logic [AXI_ADDR_WIDTH-1:0]   s_axi_araddr,
    input  logic [7:0]                  s_axi_arlen,
    input  logic [2:0]                  s_axi_arsize,
    input  logic [1:0]                  s_axi_arburst,
    input  logic                        s_axi_arlock,
    input  logic [3:0]                  s_axi_arcache,
    input  logic [2:0]                  s_axi_arprot,
    input  logic [3:0]                  s_axi_arqos,
    input  logic [3:0]                  s_axi_arregion,
    input  logic [AXI_USER_WIDTH-1:0]   s_axi_aruser,
    input  logic                        s_axi_arvalid,
    output logic                        s_axi_arready,

    output logic [AXI_ID_WIDTH-1:0]     s_axi_rid,
    output logic [255:0]                s_axi_rdata,
    output logic [1:0]                  s_axi_rresp,
    output logic                        s_axi_rlast,
    output logic [AXI_USER_WIDTH-1:0]   s_axi_ruser,
    output logic                        s_axi_rvalid,
    input  logic                        s_axi_rready
);

    localparam int ADDR_BITS_256 = $clog2(DEPTH_256);

    // Packed widths for skid buffer payloads
    localparam int AWL_PKT_W   = 32 + 3;           // axil awaddr + awprot
    localparam int WL_PKT_W    = 32 + 4;           // axil wdata + wstrb
    localparam int BL_PKT_W    = 2;                // axil bresp
    localparam int AR4_PKT_W   = AXI_ID_WIDTH + AXI_ADDR_WIDTH + 8 + 3 + 2 + 1 + 4 + 3 + 4 + 4 + AXI_USER_WIDTH;
    localparam int R4_PKT_W    = AXI_ID_WIDTH + 256 + 2 + 1 + AXI_USER_WIDTH;

    // =========================================================================
    // Descriptor storage (256-bit wide, dual-port inferred from separate
    // clocked writes/reads). The byte-strobed RMW write path below forces
    // Vivado to infer one RAM per byte lane (32 lanes × 8 bits = 256 bits).
    // With ram_style = "block" and this width, Vivado allocates one RAMB18
    // per bit → 256 RAMB18 = 128 tiles regardless of DEPTH_256, which blows
    // the Artix-7 100T budget. Use "auto" so Vivado picks distributed LUTRAM
    // for small depths (FPGA build at DEPTH_256=128 fits easily in ~512 LUT-
    // as-memory cells) and block RAM only for the big ASIC-sim depths.
    // "distributed" forces LUTRAM inference; at DEPTH_256=128 this costs
    // about 512 LUT-as-memory cells (we have 19000 available). For the big
    // ASIC simulation depths (2048+), switch this back to "auto" or "block".
    (* ram_style = "distributed" *)
    logic [255:0] r_mem [DEPTH_256];

    // =========================================================================
    // AXIL AW skid buffer (host -> internal)
    // =========================================================================
    logic                 int_awvalid, int_awready;
    logic [AWL_PKT_W-1:0] int_aw_pkt;
    logic [31:0]          int_awaddr;
    logic [2:0]           int_awprot;
    assign {int_awaddr, int_awprot} = int_aw_pkt;

    gaxi_skid_buffer #(
        .DEPTH     (SKID_DEPTH_AW),
        .DATA_WIDTH(AWL_PKT_W)
    ) u_skid_aw (
        .axi_aclk   (aclk),
        .axi_aresetn(aresetn),
        .wr_valid   (s_axil_awvalid),
        .wr_ready   (s_axil_awready),
        .wr_data    ({s_axil_awaddr, s_axil_awprot}),
        .count      (),
        .rd_valid   (int_awvalid),
        .rd_ready   (int_awready),
        .rd_count   (),
        .rd_data    (int_aw_pkt)
    );

    // =========================================================================
    // AXIL W skid buffer (host -> internal)
    // =========================================================================
    logic                 int_wvalid, int_wready;
    logic [WL_PKT_W-1:0]  int_w_pkt;
    logic [31:0]          int_wdata;
    logic [3:0]           int_wstrb;
    assign {int_wdata, int_wstrb} = int_w_pkt;

    gaxi_skid_buffer #(
        .DEPTH     (SKID_DEPTH_W),
        .DATA_WIDTH(WL_PKT_W)
    ) u_skid_w (
        .axi_aclk   (aclk),
        .axi_aresetn(aresetn),
        .wr_valid   (s_axil_wvalid),
        .wr_ready   (s_axil_wready),
        .wr_data    ({s_axil_wdata, s_axil_wstrb}),
        .count      (),
        .rd_valid   (int_wvalid),
        .rd_ready   (int_wready),
        .rd_count   (),
        .rd_data    (int_w_pkt)
    );

    // =========================================================================
    // AXIL B skid buffer (internal -> host)
    // =========================================================================
    logic                int_bvalid, int_bready;
    logic [BL_PKT_W-1:0] int_b_pkt;

    gaxi_skid_buffer #(
        .DEPTH     (SKID_DEPTH_B),
        .DATA_WIDTH(BL_PKT_W)
    ) u_skid_b (
        .axi_aclk   (aclk),
        .axi_aresetn(aresetn),
        .wr_valid   (int_bvalid),
        .wr_ready   (int_bready),
        .wr_data    (int_b_pkt),
        .count      (),
        .rd_valid   (s_axil_bvalid),
        .rd_ready   (s_axil_bready),
        .rd_count   (),
        .rd_data    (s_axil_bresp)
    );

    // =========================================================================
    // AXIL write engine: consume AW+W from skid buffers, RMW the BRAM, emit B
    // =========================================================================
    typedef enum logic [1:0] {
        AW_IDLE  = 2'd0,
        AW_RMW   = 2'd1,
        AW_BRESP = 2'd2
    } aw_state_t;

    aw_state_t r_aw_state;
    logic [ADDR_BITS_256-1:0] r_aw_word_idx;
    logic [2:0]               r_aw_slice;
    logic [31:0]              r_aw_data;
    logic [3:0]               r_aw_strb;

    `ALWAYS_FF_RST(aclk, aresetn,
        if (`RST_ASSERTED(aresetn)) begin
            r_aw_state    <= AW_IDLE;
            r_aw_word_idx <= '0;
            r_aw_slice    <= '0;
            r_aw_data     <= '0;
            r_aw_strb     <= '0;
        end else begin
            case (r_aw_state)
                AW_IDLE: begin
                    if (int_awvalid && int_wvalid) begin
                        r_aw_word_idx <= int_awaddr[ADDR_BITS_256+4:5];
                        r_aw_slice    <= int_awaddr[4:2];
                        r_aw_data     <= int_wdata;
                        r_aw_strb     <= int_wstrb;
                        r_aw_state    <= AW_RMW;
                    end
                end
                AW_RMW: begin
                    for (int b = 0; b < 4; b++) begin
                        if (r_aw_strb[b]) begin
                            r_mem[r_aw_word_idx][
                                (32*int'(r_aw_slice) + 8*b) +: 8
                            ] <= r_aw_data[8*b +: 8];
                        end
                    end
                    r_aw_state <= AW_BRESP;
                end
                AW_BRESP: begin
                    if (int_bready) r_aw_state <= AW_IDLE;
                end
                default: r_aw_state <= AW_IDLE;
            endcase
        end
    )

    assign int_awready = (r_aw_state == AW_IDLE) && int_wvalid;
    assign int_wready  = (r_aw_state == AW_IDLE) && int_awvalid;
    assign int_bvalid  = (r_aw_state == AW_BRESP);
    assign int_b_pkt   = 2'b00;  // OKAY

    // =========================================================================
    // AXIL read side (desc RAM is write-only from host) -- tie off with DECERR
    // =========================================================================
    assign s_axil_arready = 1'b1;
    logic r_ar_latch;
    `ALWAYS_FF_RST(aclk, aresetn,
        if (`RST_ASSERTED(aresetn)) begin
            r_ar_latch <= 1'b0;
        end else begin
            if (s_axil_arvalid && s_axil_arready)    r_ar_latch <= 1'b1;
            else if (s_axil_rvalid && s_axil_rready) r_ar_latch <= 1'b0;
        end
    )
    assign s_axil_rvalid = r_ar_latch;
    assign s_axil_rdata  = 32'hDEAD_DEAD;
    assign s_axil_rresp  = 2'b11;  // DECERR

    // =========================================================================
    // AXI4 AR skid buffer (STREAM -> internal)
    // =========================================================================
    logic                  int4_arvalid, int4_arready;
    logic [AR4_PKT_W-1:0]  int4_ar_pkt;
    logic [AXI_ID_WIDTH-1:0]    int4_arid;
    logic [AXI_ADDR_WIDTH-1:0]  int4_araddr;
    logic [7:0]                 int4_arlen;
    logic [2:0]                 int4_arsize;
    logic [1:0]                 int4_arburst;
    logic                       int4_arlock;
    logic [3:0]                 int4_arcache;
    logic [2:0]                 int4_arprot;
    logic [3:0]                 int4_arqos;
    logic [3:0]                 int4_arregion;
    logic [AXI_USER_WIDTH-1:0]  int4_aruser;
    assign {int4_arid, int4_araddr, int4_arlen, int4_arsize, int4_arburst,
            int4_arlock, int4_arcache, int4_arprot, int4_arqos, int4_arregion,
            int4_aruser} = int4_ar_pkt;

    gaxi_skid_buffer #(
        .DEPTH     (SKID_DEPTH_AR),
        .DATA_WIDTH(AR4_PKT_W)
    ) u_skid_ar (
        .axi_aclk   (aclk),
        .axi_aresetn(aresetn),
        .wr_valid   (s_axi_arvalid),
        .wr_ready   (s_axi_arready),
        .wr_data    ({s_axi_arid, s_axi_araddr, s_axi_arlen, s_axi_arsize,
                      s_axi_arburst, s_axi_arlock, s_axi_arcache, s_axi_arprot,
                      s_axi_arqos, s_axi_arregion, s_axi_aruser}),
        .count      (),
        .rd_valid   (int4_arvalid),
        .rd_ready   (int4_arready),
        .rd_count   (),
        .rd_data    (int4_ar_pkt)
    );

    // =========================================================================
    // AXI4 R skid buffer (internal -> STREAM)
    // =========================================================================
    logic                 int4_rvalid, int4_rready;
    logic [R4_PKT_W-1:0]  int4_r_pkt;

    gaxi_skid_buffer #(
        .DEPTH     (SKID_DEPTH_R),
        .DATA_WIDTH(R4_PKT_W)
    ) u_skid_r (
        .axi_aclk   (aclk),
        .axi_aresetn(aresetn),
        .wr_valid   (int4_rvalid),
        .wr_ready   (int4_rready),
        .wr_data    (int4_r_pkt),
        .count      (),
        .rd_valid   (s_axi_rvalid),
        .rd_ready   (s_axi_rready),
        .rd_count   (),
        .rd_data    ({s_axi_rid, s_axi_rdata, s_axi_rresp, s_axi_rlast, s_axi_ruser})
    );

    // =========================================================================
    // AXI4 read engine: single-beat read from BRAM (arlen ignored)
    // =========================================================================
    typedef enum logic [1:0] {
        AR_IDLE = 2'd0,
        AR_READ = 2'd1,
        AR_RESP = 2'd2
    } ar_state_t;

    ar_state_t r_ar_state;
    logic [AXI_ID_WIDTH-1:0]    r_ar_id;
    logic [AXI_USER_WIDTH-1:0]  r_ar_user;
    logic [ADDR_BITS_256-1:0]   r_ar_word_idx;
    logic [255:0]               r_ar_data;

    `ALWAYS_FF_RST(aclk, aresetn,
        if (`RST_ASSERTED(aresetn)) begin
            r_ar_state    <= AR_IDLE;
            r_ar_id       <= '0;
            r_ar_user     <= '0;
            r_ar_word_idx <= '0;
            r_ar_data     <= '0;
        end else begin
            case (r_ar_state)
                AR_IDLE: begin
                    if (int4_arvalid) begin
                        r_ar_id       <= int4_arid;
                        r_ar_user     <= int4_aruser;
                        r_ar_word_idx <= int4_araddr[ADDR_BITS_256+4:5];
                        r_ar_state    <= AR_READ;
                    end
                end
                AR_READ: begin
                    r_ar_data  <= r_mem[r_ar_word_idx];
                    r_ar_state <= AR_RESP;
                end
                AR_RESP: begin
                    if (int4_rready) r_ar_state <= AR_IDLE;
                end
                default: r_ar_state <= AR_IDLE;
            endcase
        end
    )

    assign int4_arready = (r_ar_state == AR_IDLE);
    assign int4_rvalid  = (r_ar_state == AR_RESP);
    // {rid, rdata, rresp, rlast, ruser}
    assign int4_r_pkt   = {r_ar_id, r_ar_data, 2'b00, 1'b1, r_ar_user};

    // Prevent unused signal warnings (skid buffers pass these through untouched)
    /* verilator lint_off UNUSED */
    wire _unused_ok = &{1'b0,
        int_awprot,
        int4_arlen, int4_arsize, int4_arburst, int4_arlock, int4_arcache,
        int4_arprot, int4_arqos, int4_arregion,
        1'b0};
    /* verilator lint_on UNUSED */

endmodule : desc_ram
