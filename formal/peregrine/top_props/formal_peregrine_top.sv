// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: 2026 sean galloway
//
// RTL Design Sherpa - Industry-Standard RTL Design and Verification
// https://github.com/sean-galloway/RTLDesignSherpa
//
// Module: formal_peregrine_top (and an amber_top stub)
// Purpose: Harness for peregrine_top (riscv-ip/peregrine-rv32im TASK-001
//          stage 5): the D-side wrapper properties spliced into
//          peregrine_top (peregrine_top_props.svh), and here the fetch
//          property:
//
//            ap_i_fetch_word: an instruction that retires from address X
//            is the word the fabric memory holds at X.
//
//          X and its word V are free constants (anyconst), so the check
//          holds for every address; the fabric slave below answers a read
//          beat that covers X with V in X's lane and free data everywhere
//          else, and never changes it (a ROM: D-side stores land in the
//          amber stub, uncached stores are dropped).  It catches an I$ that
//          returns the wrong word, a stale line, a line filled from the
//          wrong beat, or a held fetch that replays the wrong address
//          (TASK-001 stage 7's I$ hold changes).
//
//          Environment:
//          - amber_top is replaced by the stub at the end of this file
//            (the Makefile excludes amber's filelist): it accepts when free
//            (ready is a free input, and only with nothing outstanding or in
//            the response cycle -- amber is blocking), answers each accept
//            at least one cycle later, and drives a FREE response beat on
//            every cycle, so a wrapper that reads it outside the valid
//            cycle reads noise.  Its AXI master is idle.  amber itself is
//            proved in cache-ip; here only its CPU-port contract matters;
//          - the fabric slave takes one read and one write at a time
//            (AxREADY only when idle, W after AW), returns INCR bursts with
//            correct RID / RLAST and OKAY, and free valid timing;
//          - interrupts (irq_external, the TB hooks) are free; the CLINT's
//            own interrupts are live; dc_clean_req is tied low;
//          - reset is held two cycles.
//          Geometry is shrunk for the solver: I$ 64 B with 16 B lines
//          (4 sets, 2 beats per line), BTB 2, BHT 2.  Nothing in the
//          wrapper or the I$ depends on the size beyond the index width;
//          the short fill brings every cover in by step 21 (it was 28
//          with 32 B lines), and BMC cost doubles with each step.
//
// Documentation: projects/components/riscv-ip/peregrine-rv32im/PRD.md
// Subsystem: riscv-ip/peregrine-rv32im
//
// Author: sean galloway
// Created: 2026-11-25

`timescale 1ns / 1ps

module formal_peregrine_top (
    input  logic        clk,
    input  logic        irq_external,
    input  logic        tb_irq_software,
    input  logic        tb_irq_timer
);

    localparam int AXI_DW = 64;
    localparam int AXI_IW = 4;
    localparam int FIW    = AXI_IW + 2;
    localparam int STRBW  = AXI_DW / 8;

    logic [1:0] r_rst_cnt = 2'd0;
    logic       rst_n;
    always_ff @(posedge clk) begin
        if (r_rst_cnt != 2'd2) r_rst_cnt <= r_rst_cnt + 2'd1;
    end
    assign rst_n = (r_rst_cnt == 2'd2);

    // Free slave timing and data.
    (* anyseq *)   logic              f_arready, f_rvalid, f_awready, f_wready, f_bvalid;
    (* anyseq *)   logic [AXI_DW-1:0] f_rdata;
    (* anyconst *) logic [31:0]       f_x;
    (* anyconst *) logic [31:0]       f_v;

    logic [FIW-1:0]    arid, rid, awid, bid;
    logic [31:0]       araddr, awaddr;
    logic [7:0]        arlen, awlen;
    logic [2:0]        arsize, awsize;
    logic [1:0]        arburst, awburst;
    logic              arvalid, arready, rvalid, rready, rlast;
    logic              awvalid, awready, wvalid, wready, wlast, bvalid, bready;
    logic [AXI_DW-1:0] rdata, wdata;
    logic [STRBW-1:0]  wstrb;

    logic              rvfi_valid;
    logic [31:0]       rvfi_pc_rdata;
    logic [31:0]       rvfi_insn;

    peregrine_top #(
        .RESET_ADDR   (32'h0000_0000),
        .MUL_DSP      (1'b0),
        .BP_EN        (1'b1),
        .BTB_ENTRIES  (2),
        .BHT_ENTRIES  (2),
        .ICACHE_BYTES (64),
        .ICACHE_LINE  (16),
        .AXI_DW       (AXI_DW),
        .AXI_IW       (AXI_IW),
        .MTIME_DIV    (1)
    ) u_top (
        .clk             (clk),
        .rst_n           (rst_n),
        .irq_external    (irq_external),
        .tb_irq_software (tb_irq_software),
        .tb_irq_timer    (tb_irq_timer),
        .dc_clean_req    (1'b0),
        .dc_clean_done   (),
        .m_axi_arid      (arid),
        .m_axi_araddr    (araddr),
        .m_axi_arlen     (arlen),
        .m_axi_arsize    (arsize),
        .m_axi_arburst   (arburst),
        .m_axi_arlock    (),
        .m_axi_arcache   (),
        .m_axi_arprot    (),
        .m_axi_arqos     (),
        .m_axi_arregion  (),
        .m_axi_arvalid   (arvalid),
        .m_axi_arready   (arready),
        .m_axi_rid       (rid),
        .m_axi_rdata     (rdata),
        .m_axi_rresp     (2'b00),
        .m_axi_rlast     (rlast),
        .m_axi_rvalid    (rvalid),
        .m_axi_rready    (rready),
        .m_axi_awid      (awid),
        .m_axi_awaddr    (awaddr),
        .m_axi_awlen     (awlen),
        .m_axi_awsize    (awsize),
        .m_axi_awburst   (awburst),
        .m_axi_awlock    (),
        .m_axi_awcache   (),
        .m_axi_awprot    (),
        .m_axi_awqos     (),
        .m_axi_awregion  (),
        .m_axi_awvalid   (awvalid),
        .m_axi_awready   (awready),
        .m_axi_wdata     (wdata),
        .m_axi_wstrb     (wstrb),
        .m_axi_wlast     (wlast),
        .m_axi_wvalid    (wvalid),
        .m_axi_wready    (wready),
        .m_axi_bid       (bid),
        .m_axi_bresp     (2'b00),
        .m_axi_bvalid    (bvalid),
        .m_axi_bready    (bready),
        .dobs_valid      (),
        .dobs_addr       (),
        .dobs_wstrb      (),
        .dobs_wdata      (),
        .rvfi_valid      (rvfi_valid),
        .rvfi_order      (),
        .rvfi_pc_rdata   (rvfi_pc_rdata),
        .rvfi_pc_wdata   (),
        .rvfi_insn       (rvfi_insn),
        .rvfi_trap       (),
        .rvfi_rs1_addr   (),
        .rvfi_rs2_addr   (),
        .rvfi_rs1_rdata  (),
        .rvfi_rs2_rdata  (),
        .rvfi_rd_addr    (),
        .rvfi_rd_wdata   (),
        .rvfi_mem_addr   (),
        .rvfi_mem_rmask  (),
        .rvfi_mem_wmask  (),
        .rvfi_mem_rdata  (),
        .rvfi_mem_wdata  (),
        .rvfi_trap_cause (),
        .rvfi_bp_pred_taken  (),
        .rvfi_bp_pred_target (),
        .rvfi_bp_mispredict  ()
    );

    // -----------------------------------------------------------------
    // Fabric slave: one read burst at a time
    // -----------------------------------------------------------------
    logic           r_rd_busy;
    logic [FIW-1:0] r_rid;
    logic [31:0]    r_raddr;
    logic [2:0]     r_rsize;
    logic [7:0]     r_rleft;

    assign arready = f_arready & ~r_rd_busy;
    assign rvalid  = r_rd_busy & f_rvalid;
    assign rid     = r_rid;
    assign rlast   = (r_rleft == 8'd0);
    // The beat covering X carries V in X's lane; everything else is free.
    assign rdata   = (r_raddr[31:3] == f_x[31:3])
                     ? (f_x[2] ? {f_v, f_rdata[31:0]} : {f_rdata[63:32], f_v})
                     : f_rdata;

    always_ff @(posedge clk) begin
        if (!rst_n) begin
            r_rd_busy <= 1'b0;
        end else if (arvalid && arready) begin
            r_rd_busy <= 1'b1;
            r_rid     <= arid;
            r_raddr   <= araddr;
            r_rsize   <= arsize;
            r_rleft   <= arlen;
        end else if (rvalid && rready) begin
            if (rlast) r_rd_busy <= 1'b0;
            r_rleft <= r_rleft - 8'd1;
            r_raddr <= (r_raddr & ~((32'd1 << r_rsize) - 32'd1)) + (32'd1 << r_rsize);
        end
    end

    // -----------------------------------------------------------------
    // Fabric slave: one write at a time, W after AW, then B
    // -----------------------------------------------------------------
    logic           r_wr_busy;
    logic           r_w_done;
    logic [FIW-1:0] r_bid;

    assign awready = f_awready & ~r_wr_busy;
    assign wready  = f_wready & r_wr_busy & ~r_w_done;
    assign bvalid  = f_bvalid & r_wr_busy & r_w_done;
    assign bid     = r_bid;

    always_ff @(posedge clk) begin
        if (!rst_n) begin
            r_wr_busy <= 1'b0;
            r_w_done  <= 1'b0;
        end else if (awvalid && awready) begin
            r_wr_busy <= 1'b1;
            r_w_done  <= 1'b0;
            r_bid     <= awid;
        end else begin
            if (wvalid && wready && wlast) r_w_done  <= 1'b1;
            if (bvalid && bready)          r_wr_busy <= 1'b0;
        end
    end

    // -----------------------------------------------------------------
    // The fetch property
    // -----------------------------------------------------------------
    always_comb begin
        assume (f_x[1:0] == 2'b00);
        if (rst_n && rvfi_valid && (rvfi_pc_rdata == f_x))
            ap_i_fetch_word: assert (rvfi_insn == f_v);
    end

    always_comb begin
        if (rst_n) begin
            cp_i_retire_x:      cover (rvfi_valid && (rvfi_pc_rdata == f_x));
            cp_i_retire_x_hi:   cover (rvfi_valid && (rvfi_pc_rdata == f_x) && f_x[2]);
        end
    end

    logic w_unused;
    assign w_unused = &{1'b0, awaddr, awlen, awsize, awburst, wdata, wstrb, arburst};

endmodule : formal_peregrine_top

// ---------------------------------------------------------------------
// amber_top stub: the CPU-port contract only (see the header)
// ---------------------------------------------------------------------
module amber_top #(
    parameter int ADDR_WIDTH     = 32,
    parameter int SETS           = 128,
    parameter int WAYS           = 4,
    parameter int LINE_BYTES     = 64,
    parameter int BUS_WIDTH      = 64,
    parameter int REPL_POLICY    = 0,
    parameter int AXI_ID_WIDTH   = 8,
    parameter int AXI_USER_WIDTH = 1,
    parameter bit USE_MONITOR    = 1'b1,
    parameter bit MAINT_EN       = 1'b0,
    parameter bit READ_FILL_E    = 1'b0,   // amber TASK-006; CPU-port contract unchanged
    localparam int STRB_W        = BUS_WIDTH / 8,
    localparam int IW            = AXI_ID_WIDTH,
    localparam int UW            = AXI_USER_WIDTH,
    localparam int CPU_REQ_W     = int'(MAINT_EN) + ADDR_WIDTH + 1 + STRB_W + BUS_WIDTH,
    localparam int CPU_RSP_W     = BUS_WIDTH
) (
    input  logic                  aclk,
    input  logic                  aresetn,
    input  logic                  cpu_req_wr_valid,
    output logic                  cpu_req_wr_ready,
    input  logic [CPU_REQ_W-1:0]  cpu_req_wr_data,
    output logic                  cpu_rsp_rd_valid,
    input  logic                  cpu_rsp_rd_ready,
    output logic [CPU_RSP_W-1:0]  cpu_rsp_rd_data,
    output logic [IW-1:0]         m_axi_arid,
    output logic [ADDR_WIDTH-1:0] m_axi_araddr,
    output logic [7:0]            m_axi_arlen,
    output logic [2:0]            m_axi_arsize,
    output logic [1:0]            m_axi_arburst,
    output logic                  m_axi_arlock,
    output logic [3:0]            m_axi_arcache,
    output logic [2:0]            m_axi_arprot,
    output logic [3:0]            m_axi_arqos,
    output logic [3:0]            m_axi_arregion,
    output logic [UW-1:0]         m_axi_aruser,
    output logic                  m_axi_arvalid,
    input  logic                  m_axi_arready,
    input  logic [IW-1:0]         m_axi_rid,
    input  logic [BUS_WIDTH-1:0]  m_axi_rdata,
    input  logic [1:0]            m_axi_rresp,
    input  logic                  m_axi_rlast,
    input  logic [UW-1:0]         m_axi_ruser,
    input  logic                  m_axi_rvalid,
    output logic                  m_axi_rready,
    output logic [IW-1:0]         m_axi_awid,
    output logic [ADDR_WIDTH-1:0] m_axi_awaddr,
    output logic [7:0]            m_axi_awlen,
    output logic [2:0]            m_axi_awsize,
    output logic [1:0]            m_axi_awburst,
    output logic                  m_axi_awlock,
    output logic [3:0]            m_axi_awcache,
    output logic [2:0]            m_axi_awprot,
    output logic [3:0]            m_axi_awqos,
    output logic [3:0]            m_axi_awregion,
    output logic [UW-1:0]         m_axi_awuser,
    output logic                  m_axi_awvalid,
    input  logic                  m_axi_awready,
    output logic [BUS_WIDTH-1:0]  m_axi_wdata,
    output logic [STRB_W-1:0]     m_axi_wstrb,
    output logic                  m_axi_wlast,
    output logic [UW-1:0]         m_axi_wuser,
    output logic                  m_axi_wvalid,
    input  logic                  m_axi_wready,
    input  logic [IW-1:0]         m_axi_bid,
    input  logic [1:0]            m_axi_bresp,
    input  logic [UW-1:0]         m_axi_buser,
    input  logic                  m_axi_bvalid,
    output logic                  m_axi_bready,
    input  logic [ADDR_WIDTH-1:0] m_axi_acaddr,
    input  logic [3:0]            m_axi_acsnoop,
    input  logic [2:0]            m_axi_acprot,
    input  logic                  m_axi_acvalid,
    output logic                  m_axi_acready,
    output logic [4:0]            m_axi_crresp,
    output logic                  m_axi_crvalid,
    input  logic                  m_axi_crready,
    output logic [BUS_WIDTH-1:0]  m_axi_cddata,
    output logic                  m_axi_cdlast,
    output logic                  m_axi_cdvalid,
    input  logic                  m_axi_cdready,
    output logic                  coh_req_valid,
    output logic [ADDR_WIDTH-1:0] coh_req_addr,
    output logic [2:0]            coh_req_type,
    input  logic [63:0]           i_mon_time,
    output logic                  mon_valid,
    input  logic                  mon_ready,
    output logic [127:0]          mon_packet,
    output logic [63:0]           mon_timestamp,
    output logic                  init_busy,
    output logic [3:0]            ctrl_state
);

    (* anyseq *) logic                 f_ready;
    (* anyseq *) logic                 f_rsp_go;
    (* anyseq *) logic [BUS_WIDTH-1:0] f_beat;

    logic r_out;

    assign cpu_rsp_rd_valid = r_out & f_rsp_go;
    assign cpu_rsp_rd_data  = f_beat;           // free on every cycle
    assign cpu_req_wr_ready = f_ready & (~r_out | cpu_rsp_rd_valid);

    always_ff @(posedge aclk) begin
        if (!aresetn) begin
            r_out <= 1'b0;
        end else if (cpu_req_wr_valid && cpu_req_wr_ready) begin
            r_out <= 1'b1;
        end else if (cpu_rsp_rd_valid) begin
            r_out <= 1'b0;
        end
    end

    // The AXI master is idle; no snoop port activity; no monitor.
    assign m_axi_arid     = '0;
    assign m_axi_araddr   = '0;
    assign m_axi_arlen    = '0;
    assign m_axi_arsize   = '0;
    assign m_axi_arburst  = '0;
    assign m_axi_arlock   = 1'b0;
    assign m_axi_arcache  = '0;
    assign m_axi_arprot   = '0;
    assign m_axi_arqos    = '0;
    assign m_axi_arregion = '0;
    assign m_axi_aruser   = '0;
    assign m_axi_arvalid  = 1'b0;
    assign m_axi_rready   = 1'b1;
    assign m_axi_awid     = '0;
    assign m_axi_awaddr   = '0;
    assign m_axi_awlen    = '0;
    assign m_axi_awsize   = '0;
    assign m_axi_awburst  = '0;
    assign m_axi_awlock   = 1'b0;
    assign m_axi_awcache  = '0;
    assign m_axi_awprot   = '0;
    assign m_axi_awqos    = '0;
    assign m_axi_awregion = '0;
    assign m_axi_awuser   = '0;
    assign m_axi_awvalid  = 1'b0;
    assign m_axi_wdata    = '0;
    assign m_axi_wstrb    = '0;
    assign m_axi_wlast    = 1'b0;
    assign m_axi_wuser    = '0;
    assign m_axi_wvalid   = 1'b0;
    assign m_axi_bready   = 1'b1;
    assign m_axi_acready  = 1'b1;
    assign m_axi_crresp   = '0;
    assign m_axi_crvalid  = 1'b0;
    assign m_axi_cddata   = '0;
    assign m_axi_cdlast   = 1'b0;
    assign m_axi_cdvalid  = 1'b0;
    assign coh_req_valid  = 1'b0;
    assign coh_req_addr   = '0;
    assign coh_req_type   = '0;
    assign mon_valid      = 1'b0;
    assign mon_packet     = '0;
    assign mon_timestamp  = '0;
    assign init_busy      = 1'b0;
    assign ctrl_state     = '0;

endmodule : amber_top
