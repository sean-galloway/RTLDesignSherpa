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
//          The I/O window is bounded at 0x1FFF_FFFF (P7 as amended
//          2026-11-24): the riscv-tests and arch-test images link at
//          0x8000_0000 and must stay cacheable.
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
//          - presents the request (valid) when MEM has one not yet
//            accepted, no fence.i / clean hold is active, and the previous
//            response is in or arriving.  An I$ stall does not gate it
//            (TASK-001 stage 7): the I$ hit is late, and amber's accept-
//            cycle lookup sits behind the valid.  So an access can be
//            accepted while the core is held for the I$; r_mem_done then
//            marks MEM's access as done until MEM moves on;
//          - holds the core while MEM has a request not yet accepted, and
//            while an accepted access waits for its response;
//          - captures a response that arrives while the core is held: WB's
//            in r_have (given to WB until WB retires), MEM's in r_mem_have
//            (moved to r_have when MEM moves to WB).
//          One access is in flight at a time (amber is blocking; the
//          uncached port is single-transaction).
//
//          D$: amber (cache-ip/amber-mesi-l1 amber_top, MAINT_EN=1) on the
//          cacheable window, its AXI4 master on arbiter port 1.  The CPU
//          word is 32 bits and amber's beat is BUS_WIDTH = AXI_DW (64): no
//          width converter; a request carries the word in its lane
//          (be = wstrb << 4*lane, wdata replicated) and the response lane
//          is selected by the accepted address's lane bit, registered at
//          the accept.  amber's ACE snoop port is tied idle: one core, no
//          other cache, so no snoop ever arrives (amber MAS ch03/04).
//          amber installs every read fill Shared (its AXI4 plane sees no
//          IsShared), so the first store to a line a load brought in pays a
//          CleanUnique upgrade: a 1-beat AR the memory answers.  Correct on
//          any AXI4 memory; a cost recorded in TASK-001.
//
//          D$ clean (amber TASK-004): one engine issues amber's clean-all
//          ({maint=1, we=0}) when no access is in flight, and waits for its
//          response, which amber gives after the last WriteClean's B.  Two
//          sources: fence.i, and the dc_clean_req port (a TB/debug hook:
//          the arch-test signature is read from memory, so the TB cleans
//          first).  The core is held while either source is pending.
//
//          fence.i (PRD P10): while the core holds fence.i in MEM
//          (fencei_req) the wrapper (1) cleans the D$, (2) invalidates the
//          I$, then releases the hold; the core redirects to pc + 4.
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
//   - AXI_DW: fabric data width, and amber's BUS_WIDTH (64, its default;
//     32 also legal: one lane).
//   - DC_SETS, DC_WAYS, DC_LINE: amber geometry (l1_pkg default 128 / 4 /
//     64 = 32 KiB, the geometry PRD P13 was measured at).
//   - AXI_IW: per-master id width; the fabric id is AXI_IW + 2.
//   - MTIME_DIV: CLINT clocks per mtime tick.
//
// Notes:
//   - tb_irq_software / tb_irq_timer are a TB hook (see the ports); a
//     system ties them to 0.  dc_clean_req likewise (tie 0 for no use).
//   - dobs_* observe the D side at the handshake (one beat per accepted
//     load or store), for the TB: the tohost detector and the
//     memory-side-effect count.
//
// Related Modules:
//   - peregrine_core, peregrine_icache, peregrine_clint, peregrine_uc_axi,
//     peregrine_axi4_arb, amber_top (cache-ip/amber-mesi-l1)

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
    parameter int          DC_SETS      = 128,
    parameter int          DC_WAYS      = 4,
    parameter int          DC_LINE      = 64,
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
    // D$ clean hook (TB / debug): hold high to clean amber; dc_clean_done
    // is high from the clean's completion until dc_clean_req drops.  The
    // core is held while it is pending.  Tie to 0.
    input  logic                dc_clean_req,
    output logic                dc_clean_done,

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
    localparam int M_DC     = 1;     // arbiter port: D$ (amber)
    localparam int M_UC     = 2;     // arbiter port: uncached

    localparam logic [15:0] CLINT_HI = 16'h0200;
    localparam logic [3:0]  IO_HI    = 4'h1;

    // -----------------------------------------------------------------
    // Core
    // -----------------------------------------------------------------
    logic        w_mem_wait;
    logic [31:0] w_imem_addr;
    logic [31:0] w_imem_addr_next_nw;
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
        .imem_addr_next      (),
        .imem_addr_next_nw   (w_imem_addr_next_nw),
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
        .fetch_addr_next_nw (w_imem_addr_next_nw),
        .hold            (w_mem_wait),
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
    // The clean is amber's clean-all (TASK-004), issued by the clean engine
    // below; w_cl_done pulses on its response.
    logic r_fi_clean_done;
    logic r_fi_done;
    logic w_fi_busy;
    logic w_fi_clean_want;
    logic r_ext_done;
    logic w_ext_busy;
    logic w_cl_done;

    assign w_fi_clean_want = w_fencei_req & ~r_fi_clean_done;
    assign w_ic_inv_req    = w_fencei_req & r_fi_clean_done & ~r_fi_done;
    assign w_fi_busy       = w_fencei_req & ~r_fi_done;
    assign w_ext_busy      = dc_clean_req & ~r_ext_done;
    assign dc_clean_done   = dc_clean_req & r_ext_done;

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
    assign w_other_hold = w_ic_stall | w_fi_busy | w_ext_busy;

    logic        r_outstanding;   // an accepted access whose response is due
    logic        r_have;          // WB's response, captured while the core held
    logic [31:0] r_have_data;
    logic        r_mem_done;      // MEM's access accepted while the core held
    logic        r_mem_have;      // MEM's response, captured while the core held
    logic [31:0] r_mem_data;
    logic        w_rsp_valid;
    logic [31:0] w_rsp_rdata;
    logic        w_dvalid;
    logic        w_dready;
    logic        w_dhs;

    assign w_dvalid = w_dreq_pre & ~r_mem_done & ~w_fi_busy & ~w_ext_busy &
                      (~r_outstanding | w_rsp_valid);
    assign w_dhs    = w_dvalid & w_dready;

    // The core holds while MEM's access is not accepted, while an accepted
    // access waits for its response, and for the I$ and fence.i.  After an
    // accept under a hold, the outstanding access is MEM's (r_mem_done):
    // the previous one's response was in or arriving at the accept.
    assign w_mem_wait = w_other_hold |
                        (w_dreq_pre & ~r_mem_done & ~w_dhs) |
                        (r_outstanding & ~w_rsp_valid);

    assign w_drdata = r_have ? r_have_data : w_rsp_rdata;

    // Target of the access in flight (for the response mux)
    typedef enum logic [1:0] { T_CLINT = 2'd0, T_UC = 2'd1, T_DC = 2'd2 } tgt_e;
    tgt_e r_tgt;
    tgt_e w_tgt;

    assign w_tgt = w_to_clint ? T_CLINT : (w_to_io ? T_UC : T_DC);

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

    // -----------------------------------------------------------------
    // D$: amber
    // -----------------------------------------------------------------
    localparam int DC_REQ_W = 1 + 32 + 1 + STRBW + AXI_DW;   // MAINT_EN=1
    localparam int LANES    = AXI_DW / 32;
    localparam int LANE_W   = (LANES > 1) ? $clog2(LANES) : 1;

    logic                 w_dc_req_valid;
    logic                 w_dc_req_ready;
    logic [DC_REQ_W-1:0]  w_dc_req_data;
    logic                 w_dc_rsp_valid_raw;
    logic [AXI_DW-1:0]    w_dc_rsp_data;
    logic                 w_dc_rsp_valid;
    logic [31:0]          w_dc_rsp_word;

    // Clean engine: issue when wanted and nothing is in flight; done on
    // amber's response to it.  (amber is blocking, so it could not accept
    // the clean before answering an access in flight anyway; the
    // ~r_outstanding term keeps the engine correct without relying on it.)
    logic r_cl_wait;
    logic w_cl_want;
    logic w_cl_valid;
    assign w_cl_want  = w_fi_clean_want | w_ext_busy;
    assign w_cl_valid = w_cl_want & ~r_cl_wait & ~r_outstanding;
    assign w_cl_done  = r_cl_wait & w_dc_rsp_valid_raw;

    // Lane placement of the 32-bit word on amber's beat.
    logic [LANE_W-1:0]    w_lane;
    logic [LANE_W-1:0]    r_lane;
    logic [STRBW-1:0]     w_dc_be;
    logic [AXI_DW-1:0]    w_dc_wdata;
    if (LANES > 1) begin : g_lanes
        assign w_lane = w_daddr[2 +: LANE_W];
    end else begin : g_one_lane
        assign w_lane = '0;
    end
    assign w_dc_be    = STRBW'(w_dwstrb) << (4 * w_lane);
    assign w_dc_wdata = {LANES{w_dwdata}};
    assign w_dc_rsp_word = w_dc_rsp_data[32 * r_lane +: 32];

    // The clean and a data access never coincide: the clean's sources hold
    // the core (w_other_hold), so w_dvalid is low while w_cl_valid is up.
    assign w_dc_req_valid = w_cl_valid | (w_dvalid & (w_tgt == T_DC));
    assign w_dc_req_data  = w_cl_valid
        ? {1'b1, 32'd0, 1'b0, {STRBW{1'b0}}, {AXI_DW{1'b0}}}
        : {1'b0, w_daddr, (|w_dwstrb), w_dc_be, w_dc_wdata};
    // amber's response to the clean needs no masking here: the clean is
    // issued only with nothing outstanding, and a response counts (capture,
    // r_outstanding, mem_wait) only while r_outstanding is set.
    assign w_dc_rsp_valid = w_dc_rsp_valid_raw;

    amber_top #(
        .ADDR_WIDTH     (32),
        .SETS           (DC_SETS),
        .WAYS           (DC_WAYS),
        .LINE_BYTES     (DC_LINE),
        .BUS_WIDTH      (AXI_DW),
        .AXI_ID_WIDTH   (AXI_IW),
        .AXI_USER_WIDTH (1),
        .USE_MONITOR    (1'b0),
        .MAINT_EN       (1'b1)
    ) u_dcache (
        .aclk             (clk),
        .aresetn          (w_aresetn),
        .cpu_req_wr_valid (w_dc_req_valid),
        .cpu_req_wr_ready (w_dc_req_ready),
        .cpu_req_wr_data  (w_dc_req_data),
        .cpu_rsp_rd_valid (w_dc_rsp_valid_raw),
        .cpu_rsp_rd_ready (1'b1),
        .cpu_rsp_rd_data  (w_dc_rsp_data),
        .m_axi_arid       (s_arid[M_DC*AXI_IW +: AXI_IW]),
        .m_axi_araddr     (s_araddr[M_DC*32 +: 32]),
        .m_axi_arlen      (s_arlen[M_DC*8 +: 8]),
        .m_axi_arsize     (s_arsize[M_DC*3 +: 3]),
        .m_axi_arburst    (s_arburst[M_DC*2 +: 2]),
        .m_axi_arlock     (),
        .m_axi_arcache    (),
        .m_axi_arprot     (),
        .m_axi_arqos      (),
        .m_axi_arregion   (),
        .m_axi_aruser     (),
        .m_axi_arvalid    (s_arvalid[M_DC]),
        .m_axi_arready    (s_arready[M_DC]),
        .m_axi_rid        (s_rid[M_DC*AXI_IW +: AXI_IW]),
        .m_axi_rdata      (s_rdata[M_DC*AXI_DW +: AXI_DW]),
        .m_axi_rresp      (s_rresp[M_DC*2 +: 2]),
        .m_axi_rlast      (s_rlast[M_DC]),
        .m_axi_ruser      (1'b0),
        .m_axi_rvalid     (s_rvalid[M_DC]),
        .m_axi_rready     (s_rready[M_DC]),
        .m_axi_awid       (s_awid[M_DC*AXI_IW +: AXI_IW]),
        .m_axi_awaddr     (s_awaddr[M_DC*32 +: 32]),
        .m_axi_awlen      (s_awlen[M_DC*8 +: 8]),
        .m_axi_awsize     (s_awsize[M_DC*3 +: 3]),
        .m_axi_awburst    (s_awburst[M_DC*2 +: 2]),
        .m_axi_awlock     (),
        .m_axi_awcache    (),
        .m_axi_awprot     (),
        .m_axi_awqos      (),
        .m_axi_awregion   (),
        .m_axi_awuser     (),
        .m_axi_awvalid    (s_awvalid[M_DC]),
        .m_axi_awready    (s_awready[M_DC]),
        .m_axi_wdata      (s_wdata[M_DC*AXI_DW +: AXI_DW]),
        .m_axi_wstrb      (s_wstrb[M_DC*STRBW +: STRBW]),
        .m_axi_wlast      (s_wlast[M_DC]),
        .m_axi_wuser      (),
        .m_axi_wvalid     (s_wvalid[M_DC]),
        .m_axi_wready     (s_wready[M_DC]),
        .m_axi_bid        (s_bid[M_DC*AXI_IW +: AXI_IW]),
        .m_axi_bresp      (s_bresp[M_DC*2 +: 2]),
        .m_axi_buser      (1'b0),
        .m_axi_bvalid     (s_bvalid[M_DC]),
        .m_axi_bready     (s_bready[M_DC]),
        // ACE snoop: one core, no snoop ever arrives
        .m_axi_acaddr     (32'd0),
        .m_axi_acsnoop    (4'd0),
        .m_axi_acprot     (3'd0),
        .m_axi_acvalid    (1'b0),
        .m_axi_acready    (),
        .m_axi_crresp     (),
        .m_axi_crvalid    (),
        .m_axi_crready    (1'b1),
        .m_axi_cddata     (),
        .m_axi_cdlast     (),
        .m_axi_cdvalid    (),
        .m_axi_cdready    (1'b1),
        .coh_req_valid    (),
        .coh_req_addr     (),
        .coh_req_type     (),
        .i_mon_time       (64'd0),
        .mon_valid        (),
        .mon_ready        (1'b1),
        .mon_packet       (),
        .mon_timestamp    (),
        .init_busy        (),
        .ctrl_state       ()
    );

    // Ready and response, by target
    always_comb begin
        unique case (w_tgt)
            T_CLINT: w_dready = 1'b1;
            T_DC:    w_dready = w_dc_req_ready;
            default: w_dready = w_uc_req_ready;
        endcase
        unique case (r_tgt)
            T_CLINT: begin
                w_rsp_valid = w_clint_rsp_valid;
                w_rsp_rdata = w_clint_rsp_rdata;
            end
            T_DC: begin
                w_rsp_valid = w_dc_rsp_valid;
                w_rsp_rdata = w_dc_rsp_word;
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
            r_mem_done      <= 1'b0;
            r_mem_have      <= 1'b0;
            r_mem_data      <= '0;
            r_tgt           <= T_CLINT;
            r_fi_clean_done <= 1'b0;
            r_fi_done       <= 1'b0;
            r_ext_done      <= 1'b0;
            r_cl_wait       <= 1'b0;
            r_lane          <= '0;
        end else begin
            // One access in flight: set on accept, cleared by its response
            // (a new accept in the response's cycle keeps it set).
            if (w_dhs) begin
                r_outstanding <= 1'b1;
                r_tgt         <= w_tgt;
                r_lane        <= w_lane;
            end else if (w_rsp_valid) begin
                r_outstanding <= 1'b0;
            end
            // Responses.  WB retires and MEM moves to WB on the first cycle
            // without a hold.  WB's response that arrives under a hold waits
            // in r_have; MEM's (an access accepted under a hold) waits in
            // r_mem_have and becomes WB's when MEM moves.  One access is in
            // flight, so a response is MEM's exactly when r_mem_done.
            if (!w_mem_wait) begin
                r_mem_done <= 1'b0;
                r_mem_have <= 1'b0;
                if (r_mem_have) begin
                    r_have      <= 1'b1;
                    r_have_data <= r_mem_data;
                end else if (w_rsp_valid && r_outstanding && r_mem_done) begin
                    r_have      <= 1'b1;
                    r_have_data <= w_rsp_rdata;
                end else begin
                    r_have      <= 1'b0;
                end
            end else begin
                if (w_dhs) begin
                    r_mem_done <= 1'b1;
                end
                if (w_rsp_valid && r_outstanding && r_mem_done) begin
                    r_mem_have <= 1'b1;
                    r_mem_data <= w_rsp_rdata;
                end else if (w_rsp_valid && r_outstanding) begin
                    r_have      <= 1'b1;
                    r_have_data <= w_rsp_rdata;
                end
            end
            // fence.i progress, cleared when the core commits it.
            if (!w_fencei_req || !w_mem_wait) begin
                r_fi_clean_done <= 1'b0;
                r_fi_done       <= 1'b0;
            end else begin
                if (w_cl_done && w_fencei_req) r_fi_clean_done <= 1'b1;
                if (w_ic_inv_ack)               r_fi_done       <= 1'b1;
            end
            // The clean engine: one clean-all in flight.  A clean finishing
            // satisfies every source pending at the time (the core has been
            // held since each one rose, so nothing was stored after it).
            if (w_cl_valid && w_dc_req_ready) begin
                r_cl_wait <= 1'b1;
            end else if (w_cl_done) begin
                r_cl_wait <= 1'b0;
            end
            if (!dc_clean_req) begin
                r_ext_done <= 1'b0;
            end else if (w_cl_done) begin
                r_ext_done <= 1'b1;
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
    // The I$ never writes, so its B channel is unused.
    assign w_unused = &{1'b0, w_to_ram, s_bid[M_IC*AXI_IW +: AXI_IW], s_bresp[M_IC*2 +: 2]};

endmodule : peregrine_top
