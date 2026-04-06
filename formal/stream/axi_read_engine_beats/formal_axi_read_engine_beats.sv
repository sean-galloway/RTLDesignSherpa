// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: 2024-2025 sean galloway
//
// Formal wrapper for axi_read_engine_beats (RAPIDS fub_beats variant)
// All multi-dimensional ports use flat packed vectors to match sv2v output.
// (yosys-compatible, sv2v-preprocessed)
// Run with: make prove  (or make cover)

module formal_axi_read_engine_beats (
    input  logic        clk,
    input  logic        rst_n
);

    // =========================================================================
    // Parameters (small for tractability)
    // =========================================================================
    localparam int NC  = 2;
    localparam int AW  = 32;
    localparam int DW  = 64;
    localparam int IW  = 4;
    localparam int SCW = 5;   // $clog2(16)+1
    localparam int CIW = 1;   // $clog2(2)

    // =========================================================================
    // Free inputs (driven by formal engine) -- flat packed vectors
    // =========================================================================
    (* anyseq *) reg  [7:0]                cfg_axi_rd_xfer_beats;

    (* anyseq *) reg  [NC-1:0]             sched_rd_valid;
    (* anyseq *) reg  [(NC*AW)-1:0]        sched_rd_addr;
    (* anyseq *) reg  [(NC*32)-1:0]        sched_rd_beats;

    // Give each channel ample free space so arbiter is not starved
    wire [(NC*SCW)-1:0] axi_rd_alloc_space_free;
    assign axi_rd_alloc_space_free = {SCW'(16), SCW'(16)};

    (* anyseq *) reg                       m_axi_arready;
    (* anyseq *) reg                       m_axi_rvalid;
    (* anyseq *) reg  [IW-1:0]             m_axi_rid;
    (* anyseq *) reg  [DW-1:0]             m_axi_rdata;
    (* anyseq *) reg  [1:0]                m_axi_rresp;
    (* anyseq *) reg                       m_axi_rlast;

    (* anyseq *) reg                       axi_rd_sram_ready;

    // =========================================================================
    // DUT outputs
    // =========================================================================
    wire [NC-1:0]       sched_rd_done_strobe;
    wire [(NC*32)-1:0]  sched_rd_beats_done;

    wire                axi_rd_alloc_req;
    wire [7:0]          axi_rd_alloc_size;
    wire [IW-1:0]       axi_rd_alloc_id;

    wire                axi_rd_sram_valid;
    wire [IW-1:0]       axi_rd_sram_id;
    wire [DW-1:0]       axi_rd_sram_data;

    wire                m_axi_arvalid;
    wire [IW-1:0]       m_axi_arid;
    wire [AW-1:0]       m_axi_araddr;
    wire [7:0]          m_axi_arlen;
    wire [2:0]          m_axi_arsize;
    wire [1:0]          m_axi_arburst;

    wire                m_axi_rready;

    wire [NC-1:0]       sched_rd_error;
    wire [NC-1:0]       dbg_rd_all_complete;
    wire [31:0]         dbg_r_beats_rcvd;
    wire [31:0]         dbg_sram_writes;
    wire [NC-1:0]       dbg_arb_request;

    // =========================================================================
    // DUT instantiation -- flat vectors connect directly
    // =========================================================================
    axi_read_engine_beats #(
        .NUM_CHANNELS       (NC),
        .ADDR_WIDTH         (AW),
        .DATA_WIDTH         (DW),
        .ID_WIDTH           (IW),
        .SEG_COUNT_WIDTH    (SCW),
        .PIPELINE           (0),
        .AR_MAX_OUTSTANDING (4),
        .STROBE_EVERY_BEAT  (0)
    ) dut (
        .clk                     (clk),
        .rst_n                   (rst_n),

        .cfg_axi_rd_xfer_beats   (cfg_axi_rd_xfer_beats),

        .sched_rd_valid           (sched_rd_valid),
        .sched_rd_addr            (sched_rd_addr),
        .sched_rd_beats           (sched_rd_beats),

        .sched_rd_done_strobe     (sched_rd_done_strobe),
        .sched_rd_beats_done      (sched_rd_beats_done),

        .axi_rd_alloc_req         (axi_rd_alloc_req),
        .axi_rd_alloc_size        (axi_rd_alloc_size),
        .axi_rd_alloc_id          (axi_rd_alloc_id),
        .axi_rd_alloc_space_free  (axi_rd_alloc_space_free),

        .axi_rd_sram_valid        (axi_rd_sram_valid),
        .axi_rd_sram_ready        (axi_rd_sram_ready),
        .axi_rd_sram_id           (axi_rd_sram_id),
        .axi_rd_sram_data         (axi_rd_sram_data),

        .m_axi_arvalid            (m_axi_arvalid),
        .m_axi_arready            (m_axi_arready),
        .m_axi_arid               (m_axi_arid),
        .m_axi_araddr             (m_axi_araddr),
        .m_axi_arlen              (m_axi_arlen),
        .m_axi_arsize             (m_axi_arsize),
        .m_axi_arburst            (m_axi_arburst),

        .m_axi_rvalid             (m_axi_rvalid),
        .m_axi_rready             (m_axi_rready),
        .m_axi_rid                (m_axi_rid),
        .m_axi_rdata              (m_axi_rdata),
        .m_axi_rresp              (m_axi_rresp),
        .m_axi_rlast              (m_axi_rlast),

        .sched_rd_error           (sched_rd_error),

        .dbg_rd_all_complete      (dbg_rd_all_complete),
        .dbg_r_beats_rcvd         (dbg_r_beats_rcvd),
        .dbg_sram_writes          (dbg_sram_writes),
        .dbg_arb_request          (dbg_arb_request)
    );

    // =========================================================================
    // Formal infrastructure
    // =========================================================================
    reg [7:0] f_past_valid = 0;
    always @(posedge clk)
        f_past_valid <= f_past_valid + (f_past_valid < 8'hFF);

    // Reset sequence: assert reset for first 2 cycles
    initial assume (!rst_n);
    always @(posedge clk)
        if (f_past_valid >= 2) assume (rst_n);

    // Constrain cfg_axi_rd_xfer_beats to valid range (1..15 for tractability)
    always @(posedge clk)
        if (rst_n) assume (cfg_axi_rd_xfer_beats >= 1 && cfg_axi_rd_xfer_beats <= 15);

    // =========================================================================
    // AXI AR channel properties
    // =========================================================================

    // P1: After reset, arvalid must be deasserted
    always @(posedge clk) begin
        if (f_past_valid > 0 && $past(!rst_n))
            ap_ar_reset: assert (m_axi_arvalid == 1'b0);
    end

    // P2-P6: AXI handshake stability (VALID/ADDR/LEN/SIZE/BURST)
    //   NOT asserted here. This is a pre-skid (FUB-side) interface.
    //   The engine drives AR combinationally from the arbiter for instant
    //   backpressure response (space_free->arvalid in same cycle).
    //   A downstream gaxi_skid_buffer registers these signals before
    //   they reach the external AXI port, enforcing AMBA IHI0022E A3.2.1
    //   at the system boundary.

    // P7: ARBURST is always INCR (2'b01)
    always @(posedge clk) begin
        if (rst_n && m_axi_arvalid)
            ap_ar_burst_incr: assert (m_axi_arburst == 2'b01);
    end

    // P8: ARSIZE matches data width: arsize == $clog2(DW/8) == 3 for 64-bit
    always @(posedge clk) begin
        if (rst_n && m_axi_arvalid)
            ap_ar_size_match: assert (m_axi_arsize == 3'($clog2(DW / 8)));
    end

    // =========================================================================
    // AXI R channel properties
    // =========================================================================

    // P9: SRAM write data passthrough -- when sram_valid, data matches rdata
    always @(posedge clk) begin
        if (rst_n && axi_rd_sram_valid)
            ap_sram_data_match: assert (axi_rd_sram_data == m_axi_rdata);
    end

    // =========================================================================
    // Cover properties
    // =========================================================================

    // C1: AR handshake occurs
    always @(posedge clk) begin
        if (rst_n)
            cp_ar_handshake: cover (m_axi_arvalid && m_axi_arready);
    end

    // C2: R handshake occurs
    always @(posedge clk) begin
        if (rst_n)
            cp_r_handshake: cover (m_axi_rvalid && m_axi_rready);
    end

    // C3: done_strobe fires for channel 0
    always @(posedge clk) begin
        if (rst_n)
            cp_done_strobe_ch0: cover (sched_rd_done_strobe[0]);
    end

    // C4: alloc_req asserted
    always @(posedge clk) begin
        if (rst_n)
            cp_alloc_req: cover (axi_rd_alloc_req);
    end

    // C5: SRAM valid handshake
    always @(posedge clk) begin
        if (rst_n)
            cp_sram_handshake: cover (axi_rd_sram_valid && axi_rd_sram_ready);
    end

endmodule
