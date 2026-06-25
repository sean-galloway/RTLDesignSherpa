// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: 2024-2026 sean galloway
//
// TB wrapper for the axi4_master_wr_pattern_gen / axi4_master_rd_crc_check
// pair. Both DUTs share clock + reset. Each has its own slave-side stub
// backed by a single shared SystemVerilog memory array, so the writer's
// W beats land in mem[idx] and the reader's R beats sample mem[idx]. End
// to end this lets the TB confirm:
//
//   - `o_expected_crc` (writer) == `o_actual_crc` (reader)
//   - `o_data_error == 0` and `o_beats_mismatched == 0` on a clean run
//
// Both DUTs are programmed with the same workload (start_addr, strides,
// burst_len, txn_count, lfsr_seed) so the reader walks the same address
// sequence the writer just populated.

`timescale 1ns / 1ps

module tb_axi4_master_pat_crc_pair #(
    parameter int AXI_ADDR_WIDTH = 32,
    parameter int AXI_DATA_WIDTH = 64,
    parameter int AXI_ID_WIDTH   = 8,
    parameter int AXI_USER_WIDTH = 1,
    parameter int MEM_DEPTH_LOG2 = 12,  // 4096 beat-words backing storage

    parameter int AW = AXI_ADDR_WIDTH,
    parameter int DW = AXI_DATA_WIDTH,
    parameter int IW = AXI_ID_WIDTH,
    parameter int SW = AXI_DATA_WIDTH / 8
) (
    input  logic                       aclk,
    input  logic                       aresetn,

    // Shared CSR (programmed identically into both blocks)
    input  logic [AW-1:0]              cfg_start_addr,
    input  logic signed [23:0]         cfg_addr_stride_0,
    input  logic signed [23:0]         cfg_addr_stride_1,
    input  logic [AW-1:0]              cfg_addr_wrap_mask_0,
    input  logic [AW-1:0]              cfg_addr_wrap_mask_1,
    input  logic [7:0]                 cfg_burst_len,
    input  logic [15:0]                cfg_txn_count,
    input  logic [IW-1:0]              cfg_axi_id,
    input  logic [2:0]                 cfg_axi_size,
    input  logic [1:0]                 cfg_axi_burst,
    input  logic [31:0]                cfg_lfsr_seed,

    // Separate start/done so the TB can run wr -> rd sequentially.
    input  logic                       cfg_start_wr,
    output logic                       cfg_done_wr,
    input  logic                       cfg_start_rd,
    output logic                       cfg_done_rd,

    // Telemetry
    output logic [31:0]                o_expected_crc,
    output logic                       o_expected_crc_valid,
    output logic                       o_bresp_error,
    output logic [31:0]                o_actual_crc,
    output logic                       o_actual_crc_valid,
    output logic                       o_data_error,
    output logic                       o_rresp_error,
    output logic [15:0]                o_beats_mismatched
);

    //==========================================================================
    // M-side AXI for the writer DUT
    //==========================================================================
    logic [IW-1:0] wr_awid;
    logic [AW-1:0] wr_awaddr;
    logic [7:0]    wr_awlen;
    logic [2:0]    wr_awsize;
    logic [1:0]    wr_awburst;
    logic          wr_awlock;
    logic [3:0]    wr_awcache, wr_awqos, wr_awregion;
    logic [2:0]    wr_awprot;
    logic [AXI_USER_WIDTH-1:0] wr_awuser, wr_wuser;
    logic          wr_awvalid;
    logic          wr_awready;
    logic [DW-1:0] wr_wdata;
    logic [SW-1:0] wr_wstrb;
    logic          wr_wlast, wr_wvalid, wr_wready;
    logic [IW-1:0] wr_bid;
    logic [1:0]    wr_bresp;
    logic [AXI_USER_WIDTH-1:0] wr_buser;
    logic          wr_bvalid, wr_bready;

    axi4_master_wr_pattern_gen #(
        .AXI_ID_WIDTH  (AXI_ID_WIDTH),
        .AXI_ADDR_WIDTH(AXI_ADDR_WIDTH),
        .AXI_DATA_WIDTH(AXI_DATA_WIDTH),
        .AXI_USER_WIDTH(AXI_USER_WIDTH)
    ) u_wr (
        .aclk                 (aclk),
        .aresetn              (aresetn),
        .cfg_start_addr       (cfg_start_addr),
        .cfg_addr_stride_0    (cfg_addr_stride_0),
        .cfg_addr_stride_1    (cfg_addr_stride_1),
        .cfg_addr_wrap_mask_0 (cfg_addr_wrap_mask_0),
        .cfg_addr_wrap_mask_1 (cfg_addr_wrap_mask_1),
        .cfg_burst_len        (cfg_burst_len),
        .cfg_txn_count        (cfg_txn_count),
        .cfg_axi_id           (cfg_axi_id),
        .cfg_axi_size         (cfg_axi_size),
        .cfg_axi_burst        (cfg_axi_burst),
        .cfg_lfsr_seed        (cfg_lfsr_seed),
        .cfg_start            (cfg_start_wr),
        .cfg_done             (cfg_done_wr),
        .o_expected_crc       (o_expected_crc),
        .o_expected_crc_valid (o_expected_crc_valid),
        .o_bresp_error        (o_bresp_error),
        .m_axi_awid           (wr_awid),
        .m_axi_awaddr         (wr_awaddr),
        .m_axi_awlen          (wr_awlen),
        .m_axi_awsize         (wr_awsize),
        .m_axi_awburst        (wr_awburst),
        .m_axi_awlock         (wr_awlock),
        .m_axi_awcache        (wr_awcache),
        .m_axi_awprot         (wr_awprot),
        .m_axi_awqos          (wr_awqos),
        .m_axi_awregion       (wr_awregion),
        .m_axi_awuser         (wr_awuser),
        .m_axi_awvalid        (wr_awvalid),
        .m_axi_awready        (wr_awready),
        .m_axi_wdata          (wr_wdata),
        .m_axi_wstrb          (wr_wstrb),
        .m_axi_wlast          (wr_wlast),
        .m_axi_wuser          (wr_wuser),
        .m_axi_wvalid         (wr_wvalid),
        .m_axi_wready         (wr_wready),
        .m_axi_bid            (wr_bid),
        .m_axi_bresp          (wr_bresp),
        .m_axi_buser          (wr_buser),
        .m_axi_bvalid         (wr_bvalid),
        .m_axi_bready         (wr_bready)
    );

    //==========================================================================
    // M-side AXI for the reader DUT
    //==========================================================================
    logic [IW-1:0] rd_arid;
    logic [AW-1:0] rd_araddr;
    logic [7:0]    rd_arlen;
    logic [2:0]    rd_arsize;
    logic [1:0]    rd_arburst;
    logic          rd_arlock;
    logic [3:0]    rd_arcache, rd_arqos, rd_arregion;
    logic [2:0]    rd_arprot;
    logic [AXI_USER_WIDTH-1:0] rd_aruser, rd_ruser;
    logic          rd_arvalid, rd_arready;
    logic [IW-1:0] rd_rid;
    logic [DW-1:0] rd_rdata;
    logic [1:0]    rd_rresp;
    logic          rd_rlast, rd_rvalid, rd_rready;

    axi4_master_rd_crc_check #(
        .AXI_ID_WIDTH  (AXI_ID_WIDTH),
        .AXI_ADDR_WIDTH(AXI_ADDR_WIDTH),
        .AXI_DATA_WIDTH(AXI_DATA_WIDTH),
        .AXI_USER_WIDTH(AXI_USER_WIDTH)
    ) u_rd (
        .aclk                 (aclk),
        .aresetn              (aresetn),
        .cfg_start_addr       (cfg_start_addr),
        .cfg_addr_stride_0    (cfg_addr_stride_0),
        .cfg_addr_stride_1    (cfg_addr_stride_1),
        .cfg_addr_wrap_mask_0 (cfg_addr_wrap_mask_0),
        .cfg_addr_wrap_mask_1 (cfg_addr_wrap_mask_1),
        .cfg_burst_len        (cfg_burst_len),
        .cfg_txn_count        (cfg_txn_count),
        .cfg_axi_id           (cfg_axi_id),
        .cfg_axi_size         (cfg_axi_size),
        .cfg_axi_burst        (cfg_axi_burst),
        .cfg_lfsr_seed        (cfg_lfsr_seed),
        .cfg_start            (cfg_start_rd),
        .cfg_done             (cfg_done_rd),
        .o_actual_crc         (o_actual_crc),
        .o_actual_crc_valid   (o_actual_crc_valid),
        .o_data_error         (o_data_error),
        .o_rresp_error        (o_rresp_error),
        .o_beats_mismatched   (o_beats_mismatched),
        .m_axi_arid           (rd_arid),
        .m_axi_araddr         (rd_araddr),
        .m_axi_arlen          (rd_arlen),
        .m_axi_arsize         (rd_arsize),
        .m_axi_arburst        (rd_arburst),
        .m_axi_arlock         (rd_arlock),
        .m_axi_arcache        (rd_arcache),
        .m_axi_arprot         (rd_arprot),
        .m_axi_arqos          (rd_arqos),
        .m_axi_arregion       (rd_arregion),
        .m_axi_aruser         (rd_aruser),
        .m_axi_arvalid        (rd_arvalid),
        .m_axi_arready        (rd_arready),
        .m_axi_rid            (rd_rid),
        .m_axi_rdata          (rd_rdata),
        .m_axi_rresp          (rd_rresp),
        .m_axi_rlast          (rd_rlast),
        .m_axi_ruser          (rd_ruser),
        .m_axi_rvalid         (rd_rvalid),
        .m_axi_rready         (rd_rready)
    );

    //==========================================================================
    // Shared memory model — beat-word addressed. Byte address ÷ (DW/8) is
    // the index. Sized via MEM_DEPTH_LOG2 (default 4096 beats = 32 KiB at
    // 64-bit beats; plenty for the test workloads).
    //==========================================================================
    localparam int MEM_DEPTH      = 1 << MEM_DEPTH_LOG2;
    localparam int BYTES_PER_BEAT = DW / 8;
    localparam int BYTE_OFF_LOG2  = $clog2(BYTES_PER_BEAT);

    logic [DW-1:0] mem [0:MEM_DEPTH-1];

    function automatic [MEM_DEPTH_LOG2-1:0] beat_idx(input [AW-1:0] byte_addr);
        return (byte_addr >> BYTE_OFF_LOG2) & ((1 << MEM_DEPTH_LOG2) - 1);
    endfunction

    //==========================================================================
    // Writer-side slave stub — captures W beats into mem.
    // - Always ready on AW + W.
    // - Tracks the active burst's running byte address + remaining beats.
    // - Drives B-OKAY after wlast.
    //==========================================================================
    logic [AW-1:0]  wr_active_addr;
    logic [IW-1:0]  wr_active_id;
    logic [8:0]     wr_active_left;  // 9 bits to hold 256+
    logic           wr_active_busy;

    assign wr_awready = !wr_active_busy;
    assign wr_wready  = wr_active_busy;

    always_ff @(posedge aclk or negedge aresetn) begin
        if (!aresetn) begin
            wr_active_addr <= '0;
            wr_active_id   <= '0;
            wr_active_left <= '0;
            wr_active_busy <= 1'b0;
            wr_bvalid      <= 1'b0;
            wr_bid         <= '0;
            wr_bresp       <= 2'b00;
            wr_buser       <= '0;
        end else begin
            // B response handshake
            if (wr_bvalid && wr_bready) wr_bvalid <= 1'b0;

            // AW accepted -> start the burst
            if (wr_awvalid && wr_awready) begin
                wr_active_addr <= wr_awaddr;
                wr_active_id   <= wr_awid;
                wr_active_left <= 9'(wr_awlen) + 9'd1;
                wr_active_busy <= 1'b1;
            end

            // W beat -> commit + advance
            if (wr_wvalid && wr_wready) begin
                mem[beat_idx(wr_active_addr)] <= wr_wdata;
                wr_active_addr <= wr_active_addr + AW'(BYTES_PER_BEAT);
                wr_active_left <= wr_active_left - 9'd1;
                if (wr_wlast) begin
                    wr_active_busy <= 1'b0;
                    // Schedule B
                    wr_bvalid <= 1'b1;
                    wr_bid    <= wr_active_id;
                    wr_bresp  <= 2'b00;
                end
            end
        end
    end

    //==========================================================================
    // Reader-side slave stub — returns mem[idx] per R beat.
    // - Always ready on AR.
    // - Streams (arlen+1) R beats with rid + rlast on the last.
    //==========================================================================
    logic [AW-1:0]  rd_active_addr;
    logic [IW-1:0]  rd_active_id;
    logic [8:0]     rd_active_left;
    logic           rd_active_busy;

    assign rd_arready = !rd_active_busy;

    always_ff @(posedge aclk or negedge aresetn) begin
        if (!aresetn) begin
            rd_active_addr <= '0;
            rd_active_id   <= '0;
            rd_active_left <= '0;
            rd_active_busy <= 1'b0;
            rd_rvalid      <= 1'b0;
            rd_rid         <= '0;
            rd_rdata       <= '0;
            rd_rresp       <= 2'b00;
            rd_rlast       <= 1'b0;
            rd_ruser       <= '0;
        end else begin
            // R handshake retires the current beat
            if (rd_rvalid && rd_rready) begin
                rd_active_addr <= rd_active_addr + AW'(BYTES_PER_BEAT);
                rd_active_left <= rd_active_left - 9'd1;
                if (rd_rlast) begin
                    rd_rvalid      <= 1'b0;
                    rd_rlast       <= 1'b0;
                    rd_active_busy <= 1'b0;
                end else begin
                    rd_rdata <= mem[beat_idx(rd_active_addr + AW'(BYTES_PER_BEAT))];
                    rd_rlast <= (rd_active_left == 9'd2);
                end
            end

            // AR accepted -> start streaming R beats
            if (rd_arvalid && rd_arready) begin
                rd_active_addr <= rd_araddr;
                rd_active_id   <= rd_arid;
                rd_active_left <= 9'(rd_arlen) + 9'd1;
                rd_active_busy <= 1'b1;
                rd_rvalid      <= 1'b1;
                rd_rid         <= rd_arid;
                rd_rresp       <= 2'b00;
                rd_rdata       <= mem[beat_idx(rd_araddr)];
                rd_rlast       <= (rd_arlen == 8'd0);
            end
        end
    end

endmodule : tb_axi4_master_pat_crc_pair
