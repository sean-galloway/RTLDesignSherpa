// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: 2026 sean galloway
//
// RTL Design Sherpa - Industry-Standard RTL Design and Verification
// https://github.com/sean-galloway/RTLDesignSherpa
//
// Module: peregrine_top
// Purpose: The cached peregrine (PRD §4.5, P4, P7, P9, P10; TASK-001 stage
//          4): peregrine_core at CACHE_EN=1 with its I$, the D-side
//          decode, the CLINT, the uncached port, and the house AXI4 arbiter
//          onto one fabric port.  The cacheless build (PRD P12) is
//          peregrine_core itself at CACHE_EN=0.
//
//          Address map (PRD P7):
//            0x0200_0000 - 0x0200_FFFF  CLINT (msip, mtimecmp, mtime)
//            0x1000_0000 - 0x1FFF_FFFF  uncached I/O (tohost, board UART)
//            everything else            RAM, cacheable
//          The I/O window is bounded at 0x1FFF_FFFF (the PRD says "0x1000_0000
//          and up"): the riscv-tests and arch-test images link at
//          0x8000_0000 and must stay cacheable.  Recorded in TASK-001.
//
//          Fetch: every fetch goes through peregrine_icache.  A miss holds
//          the whole core (mem_wait) until the line is in.
//
//          D side: the core issues a load or store in MEM from its EX/MEM
//          register (the address is a flop, not the ALU) and takes load
//          data in WB, the stage-1 registered-read contract.  A 1-cycle D$
//          hit (amber TASK-005) fits it with no added stall: the request is
//          accepted in MEM, the response is valid in the next cycle, which
//          is WB.  The wrapper:
//          - presents the request (valid) when MEM has one, no other hold
//            is active, and the previous response is in or arriving;
//          - holds the core while MEM has a request not yet accepted, and
//            while WB waits for its response;
//          - captures a response that arrives while the core is held, and
//            gives it to WB until WB retires.
//          One access is in flight at a time (amber is blocking; the
//          uncached port is single-transaction).
//
//          D$ slot: the cacheable window goes to the D$ port.  Until amber
//          is wired (needs cache-ip/amber-mesi-l1 TASK-004 for fence.i)
//          the D$ is a STUB that routes the cacheable window through the
//          uncached port; arbiter port 1 (the D$ AXI master) is idle.  See
//          "TODO(TASK-004)" below for the interface amber takes.
//
//          fence.i (PRD P10): while the core holds fence.i in MEM
//          (fencei_req) the wrapper (1) cleans the D$ (TODO(TASK-004): the
//          stub has no dirty state, so it is done at once), (2) invalidates
//          the I$, then releases the hold; the core redirects to pc + 4.
//
// Documentation: projects/components/riscv-ip/peregrine-rv32im/PRD.md
// Subsystem: riscv-ip/peregrine-rv32im
//
// Author: sean galloway
// Created: 2026-11-24
//
// Parameters:
//   - RESET_ADDR, MUL_DSP, BP_EN, BTB_ENTRIES, BHT_ENTRIES: peregrine_core's.
//   - ICACHE_BYTES, ICACHE_LINE: I$ geometry (PRD P9: 4096, 64).
//   - AXI_DW: fabric data width (64, amber's BUS_WIDTH default).
//   - AXI_IW: per-master id width; the fabric id is AXI_IW + 2.
//   - MTIME_DIV: CLINT clocks per mtime tick.
//
// Notes:
//   - tb_irq_software / tb_irq_timer are a TB hook (see the ports); a
//     system ties them to 0.
//   - dobs_* observe the D side at the handshake (one beat per accepted
//     load or store), for the TB: the tohost detector and the
//     memory-side-effect count.
//
// Related Modules:
//   - peregrine_core, peregrine_icache, peregrine_clint, peregrine_uc_axi,
//     peregrine_axi4_arb

`timescale 1ns / 1ps

`include "reset_defs.svh"

module peregrine_top #(
    parameter logic [31:0] RESET_ADDR   = 32'h0000_0000,
    parameter bit          MUL_DSP      = 1'b0,
    parameter bit          BP_EN        = 1'b1,
    parameter int          BTB_ENTRIES  = 32,
    parameter int          BHT_ENTRIES  = 256,
    parameter int          ICACHE_BYTES = 4096,
    parameter int          ICACHE_LINE  = 64,
    parameter int          AXI_DW       = 64,
    parameter int          AXI_IW       = 4,
    parameter int          MTIME_DIV    = 1,
    localparam int         FIW          = AXI_IW + 2,
    localparam int         STRBW        = AXI_DW / 8
) (
    input  logic                clk,
    input  logic                rst_n,
    input  logic                irq_external,
    // Test hook: ORed into the CLINT's software / timer interrupts so the
    // TB-driven interrupt suite runs on the cached build.  Tie to 0.
    input  logic                tb_irq_software,
    input  logic                tb_irq_timer,

    // Fabric AXI4 master
    output logic [FIW-1:0]      m_axi_arid,
    output logic [31:0]         m_axi_araddr,
    output logic [7:0]          m_axi_arlen,
    output logic [2:0]          m_axi_arsize,
    output logic [1:0]          m_axi_arburst,
    output logic                m_axi_arlock,
    output logic [3:0]          m_axi_arcache,
    output logic [2:0]          m_axi_arprot,
    output logic [3:0]          m_axi_arqos,
    output logic [3:0]          m_axi_arregion,
    output logic                m_axi_arvalid,
    input  logic                m_axi_arready,
    input  logic [FIW-1:0]      m_axi_rid,
    input  logic [AXI_DW-1:0]   m_axi_rdata,
    input  logic [1:0]          m_axi_rresp,
    input  logic                m_axi_rlast,
    input  logic                m_axi_rvalid,
    output logic                m_axi_rready,
    output logic [FIW-1:0]      m_axi_awid,
    output logic [31:0]         m_axi_awaddr,
    output logic [7:0]          m_axi_awlen,
    output logic [2:0]          m_axi_awsize,
    output logic [1:0]          m_axi_awburst,
    output logic                m_axi_awlock,
    output logic [3:0]          m_axi_awcache,
    output logic [2:0]          m_axi_awprot,
    output logic [3:0]          m_axi_awqos,
    output logic [3:0]          m_axi_awregion,
    output logic                m_axi_awvalid,
    input  logic                m_axi_awready,
    output logic [AXI_DW-1:0]   m_axi_wdata,
    output logic [STRBW-1:0]    m_axi_wstrb,
    output logic                m_axi_wlast,
    output logic                m_axi_wvalid,
    input  logic                m_axi_wready,
    input  logic [FIW-1:0]      m_axi_bid,
    input  logic [1:0]          m_axi_bresp,
    input  logic                m_axi_bvalid,
    output logic                m_axi_bready,

    // D-side observation (TB): one beat per accepted load or store
    output logic                dobs_valid,
    output logic [31:0]         dobs_addr,
    output logic [3:0]          dobs_wstrb,
    output logic [31:0]         dobs_wdata,

    // RVFI
    output logic        rvfi_valid,
    output logic [63:0] rvfi_order,
    output logic [31:0] rvfi_pc_rdata,
    output logic [31:0] rvfi_pc_wdata,
    output logic [31:0] rvfi_insn,
    output logic        rvfi_trap,
    output logic [4:0]  rvfi_rs1_addr,
    output logic [4:0]  rvfi_rs2_addr,
    output logic [31:0] rvfi_rs1_rdata,
    output logic [31:0] rvfi_rs2_rdata,
    output logic [4:0]  rvfi_rd_addr,
    output logic [31:0] rvfi_rd_wdata,
    output logic [31:0] rvfi_mem_addr,
    output logic [3:0]  rvfi_mem_rmask,
    output logic [3:0]  rvfi_mem_wmask,
    output logic [31:0] rvfi_mem_rdata,
    output logic [31:0] rvfi_mem_wdata,
    output logic [31:0] rvfi_trap_cause,
    output logic        rvfi_bp_pred_taken,
    output logic [31:0] rvfi_bp_pred_target,
    output logic        rvfi_bp_mispredict
);

    localparam int NM       = 3;
    localparam int M_IC     = 0;     // arbiter port: I$ refill
    localparam int M_DC     = 1;     // arbiter port: D$ (amber), idle while stubbed
    localparam int M_UC     = 2;     // arbiter port: uncached

    localparam logic [15:0] CLINT_HI = 16'h0200;
    localparam logic [3:0]  IO_HI    = 4'h1;

    // -----------------------------------------------------------------
    // Core
    // -----------------------------------------------------------------
    logic        w_mem_wait;
    logic [31:0] w_imem_addr;
    logic [31:0] w_imem_addr_next;
    logic [31:0] w_imem_rdata;
    logic        w_dreq_pre;
    logic [31:0] w_daddr;
    logic [3:0]  w_dwstrb;
    logic [31:0] w_dwdata;
    logic [31:0] w_drdata;
    logic        w_fencei_req;
    logic        w_irq_software;
    logic        w_irq_timer;

    peregrine_core #(
        .RESET_ADDR  (RESET_ADDR),
        .MUL_DSP     (MUL_DSP),
        .BP_EN       (BP_EN),
        .BTB_ENTRIES (BTB_ENTRIES),
        .BHT_ENTRIES (BHT_ENTRIES),
        .CACHE_EN    (1'b1)
    ) u_core (
        .clk                 (clk),
        .rst_n               (rst_n),
        .mem_wait            (w_mem_wait),
        .imem_addr           (w_imem_addr),
        .imem_addr_next      (w_imem_addr_next),
        .imem_rdata          (w_imem_rdata),
        .dmem_req            (),
        .dmem_addr           (w_daddr),
        .dmem_rdata          (w_drdata),
        .dmem_wstrb          (w_dwstrb),
        .dmem_wdata          (w_dwdata),
        .dmem_req_pre        (w_dreq_pre),
        .fencei_req          (w_fencei_req),
        .irq_software        (w_irq_software | tb_irq_software),
        .irq_timer           (w_irq_timer | tb_irq_timer),
        .irq_external        (irq_external),
        .rvfi_valid          (rvfi_valid),
        .rvfi_order          (rvfi_order),
        .rvfi_pc_rdata       (rvfi_pc_rdata),
        .rvfi_pc_wdata       (rvfi_pc_wdata),
        .rvfi_insn           (rvfi_insn),
        .rvfi_trap           (rvfi_trap),
        .rvfi_rs1_addr       (rvfi_rs1_addr),
        .rvfi_rs2_addr       (rvfi_rs2_addr),
        .rvfi_rs1_rdata      (rvfi_rs1_rdata),
        .rvfi_rs2_rdata      (rvfi_rs2_rdata),
        .rvfi_rd_addr        (rvfi_rd_addr),
        .rvfi_rd_wdata       (rvfi_rd_wdata),
        .rvfi_mem_addr       (rvfi_mem_addr),
        .rvfi_mem_rmask      (rvfi_mem_rmask),
        .rvfi_mem_wmask      (rvfi_mem_wmask),
        .rvfi_mem_rdata      (rvfi_mem_rdata),
        .rvfi_mem_wdata      (rvfi_mem_wdata),
        .rvfi_trap_cause     (rvfi_trap_cause),
        .rvfi_bp_pred_taken  (rvfi_bp_pred_taken),
        .rvfi_bp_pred_target (rvfi_bp_pred_target),
        .rvfi_bp_mispredict  (rvfi_bp_mispredict)
    );

    // Same synchronized reset the core uses internally, for the wrapper's
    // own state.
    logic w_aresetn;
    reset_sync #(
        .N             (3),
        .KEEP_ATTRS    (1'b1),
        .IN_ACTIVE_LOW (1'b1),
        .OUT_ACTIVE_LOW(1'b1),
        .ASYNC_ASSERT  (1'b1)
    ) u_rst_sync (
        .clk     (clk),
        .rst_n   (rst_n),
        .sync_rst_n (w_aresetn)
    );

    // -----------------------------------------------------------------
    // Fabric master ports (flattened for the arbiter)
    // -----------------------------------------------------------------
    logic [NM*AXI_IW-1:0] s_arid, s_rid, s_awid, s_bid;
    logic [NM*32-1:0]     s_araddr, s_awaddr;
    logic [NM*8-1:0]      s_arlen, s_awlen;
    logic [NM*3-1:0]      s_arsize, s_awsize;
    logic [NM*2-1:0]      s_arburst, s_awburst, s_rresp, s_bresp;
    logic [NM-1:0]        s_arvalid, s_arready, s_rlast, s_rvalid, s_rready;
    logic [NM-1:0]        s_awvalid, s_awready, s_wlast, s_wvalid, s_wready;
    logic [NM-1:0]        s_bvalid, s_bready;
    logic [NM*AXI_DW-1:0] s_rdata, s_wdata;
    logic [NM*STRBW-1:0]  s_wstrb;

    // -----------------------------------------------------------------
    // I$
    // -----------------------------------------------------------------
    logic w_ic_stall;
    logic w_ic_inv_req;
    logic w_ic_inv_ack;

    peregrine_icache #(
        .SIZE_BYTES (ICACHE_BYTES),
        .LINE_BYTES (ICACHE_LINE),
        .AXI_DW     (AXI_DW),
        .AXI_IW     (AXI_IW)
    ) u_icache (
        .clk             (clk),
        .rst_n           (w_aresetn),
        .fetch_addr      (w_imem_addr),
        .fetch_addr_next (w_imem_addr_next),
        .fetch_rdata     (w_imem_rdata),
        .stall           (w_ic_stall),
        .inv_req         (w_ic_inv_req),
        .inv_ack         (w_ic_inv_ack),
        .m_axi_arid      (s_arid[M_IC*AXI_IW +: AXI_IW]),
        .m_axi_araddr    (s_araddr[M_IC*32 +: 32]),
        .m_axi_arlen     (s_arlen[M_IC*8 +: 8]),
        .m_axi_arsize    (s_arsize[M_IC*3 +: 3]),
        .m_axi_arburst   (s_arburst[M_IC*2 +: 2]),
        .m_axi_arvalid   (s_arvalid[M_IC]),
        .m_axi_arready   (s_arready[M_IC]),
        .m_axi_rid       (s_rid[M_IC*AXI_IW +: AXI_IW]),
        .m_axi_rdata     (s_rdata[M_IC*AXI_DW +: AXI_DW]),
        .m_axi_rresp     (s_rresp[M_IC*2 +: 2]),
        .m_axi_rlast     (s_rlast[M_IC]),
        .m_axi_rvalid    (s_rvalid[M_IC]),
        .m_axi_rready    (s_rready[M_IC])
    );

    // The I$ never writes.
    assign s_awid[M_IC*AXI_IW +: AXI_IW] = '0;
    assign s_awaddr[M_IC*32 +: 32]       = '0;
    assign s_awlen[M_IC*8 +: 8]          = '0;
    assign s_awsize[M_IC*3 +: 3]         = '0;
    assign s_awburst[M_IC*2 +: 2]        = '0;
    assign s_awvalid[M_IC]               = 1'b0;
    assign s_wdata[M_IC*AXI_DW +: AXI_DW] = '0;
    assign s_wstrb[M_IC*STRBW +: STRBW]  = '0;
    assign s_wlast[M_IC]                 = 1'b0;
    assign s_wvalid[M_IC]                = 1'b0;
    assign s_bready[M_IC]                = 1'b1;

    // -----------------------------------------------------------------
    // fence.i sequence: D$ clean, then I$ invalidate, then release
    // -----------------------------------------------------------------
    // TODO(TASK-004): with amber, the clean is amber's CPU-side clean-all
    // request (an op on the GAXI request; amber answers after the last
    // write-back's B).  The stub has no dirty line, so its clean is done
    // the cycle it is asked for.
    logic r_fi_clean_done;
    logic r_fi_done;
    logic w_fi_busy;
    logic w_dc_clean_req;
    logic w_dc_clean_done;

    assign w_dc_clean_req  = w_fencei_req & ~r_fi_clean_done;
    assign w_dc_clean_done = w_dc_clean_req;                 // stub
    assign w_ic_inv_req    = w_fencei_req & r_fi_clean_done & ~r_fi_done;
    assign w_fi_busy       = w_fencei_req & ~r_fi_done;

    // -----------------------------------------------------------------
    // D side: decode, request, hold, response capture
    // -----------------------------------------------------------------
    logic w_to_clint;
    logic w_to_io;
    logic w_to_ram;

    assign w_to_clint = (w_daddr[31:16] == CLINT_HI);
    assign w_to_io    = (w_daddr[31:28] == IO_HI);
    assign w_to_ram   = ~w_to_clint & ~w_to_io;

    // Holds that do not depend on the D side's ready (all from flops).
    logic w_other_hold;
    assign w_other_hold = w_ic_stall | w_fi_busy;

    logic        r_outstanding;   // an accepted access whose response is due
    logic        r_have;          // a response captured while the core held
    logic [31:0] r_have_data;
    logic        w_rsp_valid;
    logic [31:0] w_rsp_rdata;
    logic        w_dvalid;
    logic        w_dready;
    logic        w_dhs;

    assign w_dvalid = w_dreq_pre & ~w_other_hold & (~r_outstanding | w_rsp_valid);
    assign w_dhs    = w_dvalid & w_dready;

    // The core holds while MEM's access is not accepted, while WB waits for
    // its response, and for the I$ and fence.i.
    assign w_mem_wait = w_other_hold |
                        (w_dreq_pre & ~w_dhs) |
                        (r_outstanding & ~w_rsp_valid);

    assign w_drdata = r_have ? r_have_data : w_rsp_rdata;

    // Target of the access in flight (for the response mux)
    typedef enum logic [1:0] { T_CLINT = 2'd0, T_UC = 2'd1, T_DC = 2'd2 } tgt_e;
    tgt_e r_tgt;
    tgt_e w_tgt;

    // TODO(TASK-004): T_DC routes to amber's CPU GAXI port.  Until then the
    // RAM window goes through the uncached port (T_UC).
    assign w_tgt = w_to_clint ? T_CLINT : T_UC;

    // CLINT
    logic        w_clint_req;
    logic        w_clint_rsp_valid;
    logic [31:0] w_clint_rsp_rdata;
    assign w_clint_req = w_dhs & (w_tgt == T_CLINT);

    peregrine_clint #(
        .MTIME_DIV (MTIME_DIV)
    ) u_clint (
        .clk          (clk),
        .rst_n        (w_aresetn),
        .req_valid    (w_clint_req),
        .req_addr     (w_daddr[15:0]),
        .req_we       (|w_dwstrb),
        .req_wstrb    (w_dwstrb),
        .req_wdata    (w_dwdata),
        .rsp_valid    (w_clint_rsp_valid),
        .rsp_rdata    (w_clint_rsp_rdata),
        .irq_software (w_irq_software),
        .irq_timer    (w_irq_timer)
    );

    // Uncached port
    logic        w_uc_req_valid;
    logic        w_uc_req_ready;
    logic        w_uc_rsp_valid;
    logic [31:0] w_uc_rsp_rdata;
    assign w_uc_req_valid = w_dvalid & (w_tgt == T_UC);

    peregrine_uc_axi #(
        .AXI_DW (AXI_DW),
        .AXI_IW (AXI_IW)
    ) u_uc (
        .clk           (clk),
        .rst_n         (w_aresetn),
        .req_valid     (w_uc_req_valid),
        .req_ready     (w_uc_req_ready),
        .req_addr      (w_daddr),
        .req_we        (|w_dwstrb),
        .req_wstrb     (w_dwstrb),
        .req_wdata     (w_dwdata),
        .rsp_valid     (w_uc_rsp_valid),
        .rsp_rdata     (w_uc_rsp_rdata),
        .m_axi_arid    (s_arid[M_UC*AXI_IW +: AXI_IW]),
        .m_axi_araddr  (s_araddr[M_UC*32 +: 32]),
        .m_axi_arlen   (s_arlen[M_UC*8 +: 8]),
        .m_axi_arsize  (s_arsize[M_UC*3 +: 3]),
        .m_axi_arburst (s_arburst[M_UC*2 +: 2]),
        .m_axi_arvalid (s_arvalid[M_UC]),
        .m_axi_arready (s_arready[M_UC]),
        .m_axi_rid     (s_rid[M_UC*AXI_IW +: AXI_IW]),
        .m_axi_rdata   (s_rdata[M_UC*AXI_DW +: AXI_DW]),
        .m_axi_rresp   (s_rresp[M_UC*2 +: 2]),
        .m_axi_rlast   (s_rlast[M_UC]),
        .m_axi_rvalid  (s_rvalid[M_UC]),
        .m_axi_rready  (s_rready[M_UC]),
        .m_axi_awid    (s_awid[M_UC*AXI_IW +: AXI_IW]),
        .m_axi_awaddr  (s_awaddr[M_UC*32 +: 32]),
        .m_axi_awlen   (s_awlen[M_UC*8 +: 8]),
        .m_axi_awsize  (s_awsize[M_UC*3 +: 3]),
        .m_axi_awburst (s_awburst[M_UC*2 +: 2]),
        .m_axi_awvalid (s_awvalid[M_UC]),
        .m_axi_awready (s_awready[M_UC]),
        .m_axi_wdata   (s_wdata[M_UC*AXI_DW +: AXI_DW]),
        .m_axi_wstrb   (s_wstrb[M_UC*STRBW +: STRBW]),
        .m_axi_wlast   (s_wlast[M_UC]),
        .m_axi_wvalid  (s_wvalid[M_UC]),
        .m_axi_wready  (s_wready[M_UC]),
        .m_axi_bid     (s_bid[M_UC*AXI_IW +: AXI_IW]),
        .m_axi_bresp   (s_bresp[M_UC*2 +: 2]),
        .m_axi_bvalid  (s_bvalid[M_UC]),
        .m_axi_bready  (s_bready[M_UC])
    );

    // TODO(TASK-004): the D$ (amber_top) on arbiter port M_DC.  amber's
    // m_axi read and write masters connect here; its snoop port is tied
    // idle (one core, PRD §4.5).  Until then the port is idle.
    assign s_arid[M_DC*AXI_IW +: AXI_IW]  = '0;
    assign s_araddr[M_DC*32 +: 32]        = '0;
    assign s_arlen[M_DC*8 +: 8]           = '0;
    assign s_arsize[M_DC*3 +: 3]          = '0;
    assign s_arburst[M_DC*2 +: 2]         = '0;
    assign s_arvalid[M_DC]                = 1'b0;
    assign s_rready[M_DC]                 = 1'b1;
    assign s_awid[M_DC*AXI_IW +: AXI_IW]  = '0;
    assign s_awaddr[M_DC*32 +: 32]        = '0;
    assign s_awlen[M_DC*8 +: 8]           = '0;
    assign s_awsize[M_DC*3 +: 3]          = '0;
    assign s_awburst[M_DC*2 +: 2]         = '0;
    assign s_awvalid[M_DC]                = 1'b0;
    assign s_wdata[M_DC*AXI_DW +: AXI_DW] = '0;
    assign s_wstrb[M_DC*STRBW +: STRBW]   = '0;
    assign s_wlast[M_DC]                  = 1'b0;
    assign s_wvalid[M_DC]                 = 1'b0;
    assign s_bready[M_DC]                 = 1'b1;

    // Ready and response, by target
    always_comb begin
        unique case (w_tgt)
            T_CLINT: w_dready = 1'b1;
            default: w_dready = w_uc_req_ready;
        endcase
        unique case (r_tgt)
            T_CLINT: begin
                w_rsp_valid = w_clint_rsp_valid;
                w_rsp_rdata = w_clint_rsp_rdata;
            end
            default: begin
                w_rsp_valid = w_uc_rsp_valid;
                w_rsp_rdata = w_uc_rsp_rdata;
            end
        endcase
    end

    `ALWAYS_FF_RST(clk, w_aresetn,
        if (`RST_ASSERTED(w_aresetn)) begin
            r_outstanding   <= 1'b0;
            r_have          <= 1'b0;
            r_have_data     <= '0;
            r_tgt           <= T_CLINT;
            r_fi_clean_done <= 1'b0;
            r_fi_done       <= 1'b0;
        end else begin
            // One access in flight: set on accept, cleared by its response
            // (a new accept in the response's cycle keeps it set).
            if (w_dhs) begin
                r_outstanding <= 1'b1;
                r_tgt         <= w_tgt;
            end else if (w_rsp_valid) begin
                r_outstanding <= 1'b0;
            end
            // A response that arrives while the core holds waits here for
            // WB; WB retires on the first cycle without a hold.
            if (w_rsp_valid && r_outstanding && w_mem_wait) begin
                r_have      <= 1'b1;
                r_have_data <= w_rsp_rdata;
            end else if (!w_mem_wait) begin
                r_have      <= 1'b0;
            end
            // fence.i progress, cleared when the core commits it.
            if (!w_fencei_req || !w_mem_wait) begin
                r_fi_clean_done <= 1'b0;
                r_fi_done       <= 1'b0;
            end else begin
                if (w_dc_clean_done) r_fi_clean_done <= 1'b1;
                if (w_ic_inv_ack)    r_fi_done       <= 1'b1;
            end
        end
    )

    assign dobs_valid = w_dhs;
    assign dobs_addr  = w_daddr;
    assign dobs_wstrb = w_dwstrb;
    assign dobs_wdata = w_dwdata;

    // -----------------------------------------------------------------
    // Arbiter onto the fabric
    // -----------------------------------------------------------------
    peregrine_axi4_arb #(
        .NM     (NM),
        .AXI_DW (AXI_DW),
        .AXI_IW (AXI_IW)
    ) u_arb (
        .clk            (clk),
        .rst_n          (w_aresetn),
        .s_axi_arid     (s_arid),
        .s_axi_araddr   (s_araddr),
        .s_axi_arlen    (s_arlen),
        .s_axi_arsize   (s_arsize),
        .s_axi_arburst  (s_arburst),
        .s_axi_arvalid  (s_arvalid),
        .s_axi_arready  (s_arready),
        .s_axi_rid      (s_rid),
        .s_axi_rdata    (s_rdata),
        .s_axi_rresp    (s_rresp),
        .s_axi_rlast    (s_rlast),
        .s_axi_rvalid   (s_rvalid),
        .s_axi_rready   (s_rready),
        .s_axi_awid     (s_awid),
        .s_axi_awaddr   (s_awaddr),
        .s_axi_awlen    (s_awlen),
        .s_axi_awsize   (s_awsize),
        .s_axi_awburst  (s_awburst),
        .s_axi_awvalid  (s_awvalid),
        .s_axi_awready  (s_awready),
        .s_axi_wdata    (s_wdata),
        .s_axi_wstrb    (s_wstrb),
        .s_axi_wlast    (s_wlast),
        .s_axi_wvalid   (s_wvalid),
        .s_axi_wready   (s_wready),
        .s_axi_bid      (s_bid),
        .s_axi_bresp    (s_bresp),
        .s_axi_bvalid   (s_bvalid),
        .s_axi_bready   (s_bready),
        .m_axi_arid     (m_axi_arid),
        .m_axi_araddr   (m_axi_araddr),
        .m_axi_arlen    (m_axi_arlen),
        .m_axi_arsize   (m_axi_arsize),
        .m_axi_arburst  (m_axi_arburst),
        .m_axi_arlock   (m_axi_arlock),
        .m_axi_arcache  (m_axi_arcache),
        .m_axi_arprot   (m_axi_arprot),
        .m_axi_arqos    (m_axi_arqos),
        .m_axi_arregion (m_axi_arregion),
        .m_axi_arvalid  (m_axi_arvalid),
        .m_axi_arready  (m_axi_arready),
        .m_axi_rid      (m_axi_rid),
        .m_axi_rdata    (m_axi_rdata),
        .m_axi_rresp    (m_axi_rresp),
        .m_axi_rlast    (m_axi_rlast),
        .m_axi_rvalid   (m_axi_rvalid),
        .m_axi_rready   (m_axi_rready),
        .m_axi_awid     (m_axi_awid),
        .m_axi_awaddr   (m_axi_awaddr),
        .m_axi_awlen    (m_axi_awlen),
        .m_axi_awsize   (m_axi_awsize),
        .m_axi_awburst  (m_axi_awburst),
        .m_axi_awlock   (m_axi_awlock),
        .m_axi_awcache  (m_axi_awcache),
        .m_axi_awprot   (m_axi_awprot),
        .m_axi_awqos    (m_axi_awqos),
        .m_axi_awregion (m_axi_awregion),
        .m_axi_awvalid  (m_axi_awvalid),
        .m_axi_awready  (m_axi_awready),
        .m_axi_wdata    (m_axi_wdata),
        .m_axi_wstrb    (m_axi_wstrb),
        .m_axi_wlast    (m_axi_wlast),
        .m_axi_wvalid   (m_axi_wvalid),
        .m_axi_wready   (m_axi_wready),
        .m_axi_bid      (m_axi_bid),
        .m_axi_bresp    (m_axi_bresp),
        .m_axi_bvalid   (m_axi_bvalid),
        .m_axi_bready   (m_axi_bready)
    );

    logic w_unused;
    assign w_unused = &{1'b0, w_to_ram, w_dc_clean_req};

endmodule : peregrine_top
