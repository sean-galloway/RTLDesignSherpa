// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: 2026 sean galloway
//
// RTL Design Sherpa - Industry-Standard RTL Design and Verification
// https://github.com/sean-galloway/RTLDesignSherpa
//
// Module: gatling_mem_bram
// Purpose: Block-RAM memory system for gatling_core: one private program/data
//          bank per context in one true-dual-port array (port A fetches,
//          port B serves loads/stores or the AXIL loader), per-context run
//          control, and per-context status registers
//
// Documentation: projects/components/riscv-ip/gatling-rv32itetrad/docs/gatling_mas
// Subsystem: riscv-ip/gatling-rv32itetrad
//
// Author: sean galloway
// Created: 2026-10-21
//
// Notes:
//   - Derived from kestrel_mem_bram (same AXIL leaves, same load/run
//     discipline, same register semantics), widened to four contexts.
//   - Program placement (PRD 7 item 3, owner 2026-10-21): each context has
//     its own program/data region -- bank {ctx} of the array, MEM_WORDS
//     words (16 KB) -- and sees it at every address (the bank index is
//     the context, never an address bit, so all four run images linked at
//     the same base).  The cell's POP input memory is separate and arrives
//     with Xcell.
//   - Port A fetches: the core presents {ctx, pc} in F and reads the word in
//     D.  Port B is the core's data port while a context's load/store is in
//     X (word in W), and the loader's otherwise.  The core always wins port
//     B; the loader waits a cycle.  The barrel has no wait signal: every
//     latency here is the one stage the core already allows.
//   - A store and a fetch can never touch the same word on one edge: they
//     belong to different contexts (X and F), and so to different banks.
//   - The loader writes a bank only while that context is held (run = 0);
//     a write to a running context's bank is acknowledged and dropped, as
//     kestrel's loader drops writes while running.  Reads are accepted any
//     time port B is free.
//
//     s_axil addr[17] = 0: memory.  addr[15:14] = context bank,
//                          addr[13:0] = byte within it (addr[16] aliases)
//     s_axil addr[17] = 1: registers
//       0x2_0000  CTRL      W: bits[3:0] run per context (1 = release,
//                           0 = hold at RESET_ADDR).  R: {halted[7:4], run[3:0]}
//       0x2_0004  BUILD_ID  ASCII "GATL"
//       0x2_0100 + 0x10*c   context c:
//         +0x0  STATUS   {cause[7:4], 2'b0, halted[1], run[0]}
//         +0x4  CYCLES   clocks since its run was set, frozen at its halt
//         +0x8  INSTRET  its retired instructions (RVFI beats)
//         +0xC  GP       the last value it wrote to x3 (the riscv-tests
//                        verdict, since a context halts on its final ecall)
//     halted/cause/cycles/instret/gp hold their values after the context is
//     stopped and clear when its run bit rises, as kestrel_mem_bram's.

`timescale 1ns / 1ps

`include "reset_defs.svh"

module gatling_mem_bram #(
    parameter int AXIL_ADDR_WIDTH = 18,
    parameter int AXIL_DATA_WIDTH = 32,
    parameter int MEM_WORDS       = 4096,    // per context: 16 KB (rv32ui images end below 12.3 KB)
    parameter int SKID_DEPTH_AW   = 2,
    parameter int SKID_DEPTH_W    = 2,
    parameter int SKID_DEPTH_B    = 2,
    parameter int SKID_DEPTH_AR   = 2,
    parameter int SKID_DEPTH_R    = 4
) (
    input  logic                         aclk,
    input  logic                         aresetn,

    // AXIL slave (loader + registers)
    input  logic [AXIL_ADDR_WIDTH-1:0]   s_axil_awaddr,
    input  logic [2:0]                   s_axil_awprot,
    input  logic                         s_axil_awvalid,
    output logic                         s_axil_awready,
    input  logic [AXIL_DATA_WIDTH-1:0]   s_axil_wdata,
    input  logic [AXIL_DATA_WIDTH/8-1:0] s_axil_wstrb,
    input  logic                         s_axil_wvalid,
    output logic                         s_axil_wready,
    output logic [1:0]                   s_axil_bresp,
    output logic                         s_axil_bvalid,
    input  logic                         s_axil_bready,
    input  logic [AXIL_ADDR_WIDTH-1:0]   s_axil_araddr,
    input  logic [2:0]                   s_axil_arprot,
    input  logic                         s_axil_arvalid,
    output logic                         s_axil_arready,
    output logic [AXIL_DATA_WIDTH-1:0]   s_axil_rdata,
    output logic [1:0]                   s_axil_rresp,
    output logic                         s_axil_rvalid,
    input  logic                         s_axil_rready,

    // Core side (gatling_core's memory ports)
    input  logic [1:0]                   imem_ctx,
    input  logic [31:0]                  imem_addr,
    output logic [31:0]                  imem_rdata,
    input  logic                         dmem_req,
    input  logic [1:0]                   dmem_ctx,
    input  logic [31:0]                  dmem_addr,
    output logic [31:0]                  dmem_rdata,
    input  logic [3:0]                   dmem_wstrb,
    input  logic [31:0]                  dmem_wdata,
    output logic [3:0]                   hart_run,

    // Core status, for the registers
    input  logic [3:0]                   halted,
    input  logic [3:0][3:0]              halt_cause,
    input  logic                         rvfi_valid,
    input  logic [1:0]                   rvfi_ctx,
    input  logic [4:0]                   rvfi_rd_addr,
    input  logic [31:0]                  rvfi_rd_wdata,

    output logic [3:0]                   o_run,
    output logic [3:0]                   o_halted
);

    localparam int NH       = 4;
    localparam int STRB_W   = AXIL_DATA_WIDTH / 8;
    localparam int IDX_W    = $clog2(MEM_WORDS);
    localparam int REG_BIT  = 17;
    localparam int BANK_LSB = 14;              // byte address of the bank field
    localparam int HREG_BIT = 8;               // 0x2_0100: per-context block
    localparam logic [31:0] BUILD_ID  = 32'h4741_544C;   // "GATL"
    localparam logic [1:0]  RESP_OKAY = 2'b00;
    localparam logic [4:0]  REG_GP    = 5'd3;

    // =========================================================================
    // The array: NH banks of MEM_WORDS, indexed {ctx, word}.  Port A
    // read-only (fetch), port B byte writes; registered read on both
    // =========================================================================
`ifdef XILINX
    (* ram_style = "block" *)
`elsif SYNTH_PRAGMA
    /* synthesis ramstyle = "M10K" */
`endif
    logic [31:0] r_mem [NH*MEM_WORDS];

    logic               a_en, b_en;
    logic [IDX_W+1:0]   a_idx, b_idx;
    logic [3:0]         b_we;
    logic [31:0]        b_din, a_dout, b_dout;

    always_ff @(posedge aclk) begin
        if (a_en) a_dout <= r_mem[a_idx];
    end

    always_ff @(posedge aclk) begin
        if (b_en) begin
            for (int b = 0; b < 4; b++)
                if (b_we[b]) r_mem[b_idx][b*8 +: 8] <= b_din[b*8 +: 8];
            b_dout <= r_mem[b_idx];
        end
    end

    // =========================================================================
    // Run/status state, per context
    // =========================================================================
    logic [NH-1:0]       run_q, halted_q;
    logic [NH-1:0][3:0]  cause_q;
    logic [NH-1:0][31:0] cycles_q, instret_q, gp_q;

    assign hart_run = run_q;
    assign o_run    = run_q;
    assign o_halted = halted_q;

    // =========================================================================
    // Port A: fetch.  Port B: the core's data access (wins the port)
    // =========================================================================
    logic core_b;

    assign a_en       = 1'b1;
    assign a_idx      = {imem_ctx, imem_addr[IDX_W+1:2]};
    assign imem_rdata = a_dout;
    assign core_b     = dmem_req;
    assign dmem_rdata = b_dout;

    // =========================================================================
    // AXIL leaf slaves
    // =========================================================================
    logic [AXIL_ADDR_WIDTH-1:0] fub_awaddr, fub_araddr;
    logic [2:0]                 fub_awprot, fub_arprot;
    logic                       fub_awvalid, fub_awready, fub_wvalid, fub_wready;
    logic [AXIL_DATA_WIDTH-1:0] fub_wdata, fub_rdata;
    logic [STRB_W-1:0]          fub_wstrb;
    logic [1:0]                 fub_bresp, fub_rresp;
    logic                       fub_bvalid, fub_bready, fub_arvalid, fub_arready;
    logic                       fub_rvalid, fub_rready;

    axil4_slave_wr #(
        .AXIL_ADDR_WIDTH(AXIL_ADDR_WIDTH), .AXIL_DATA_WIDTH(AXIL_DATA_WIDTH),
        .SKID_DEPTH_AW(SKID_DEPTH_AW), .SKID_DEPTH_W(SKID_DEPTH_W), .SKID_DEPTH_B(SKID_DEPTH_B)
    ) u_axil_wr (
        .aclk(aclk), .aresetn(aresetn),
        .s_axil_awaddr(s_axil_awaddr), .s_axil_awprot(s_axil_awprot),
        .s_axil_awvalid(s_axil_awvalid), .s_axil_awready(s_axil_awready),
        .s_axil_wdata(s_axil_wdata), .s_axil_wstrb(s_axil_wstrb),
        .s_axil_wvalid(s_axil_wvalid), .s_axil_wready(s_axil_wready),
        .s_axil_bresp(s_axil_bresp), .s_axil_bvalid(s_axil_bvalid), .s_axil_bready(s_axil_bready),
        .fub_awaddr(fub_awaddr), .fub_awprot(fub_awprot),
        .fub_awvalid(fub_awvalid), .fub_awready(fub_awready),
        .fub_wdata(fub_wdata), .fub_wstrb(fub_wstrb),
        .fub_wvalid(fub_wvalid), .fub_wready(fub_wready),
        .fub_bresp(fub_bresp), .fub_bvalid(fub_bvalid), .fub_bready(fub_bready),
        .busy());

    axil4_slave_rd #(
        .AXIL_ADDR_WIDTH(AXIL_ADDR_WIDTH), .AXIL_DATA_WIDTH(AXIL_DATA_WIDTH),
        .SKID_DEPTH_AR(SKID_DEPTH_AR), .SKID_DEPTH_R(SKID_DEPTH_R)
    ) u_axil_rd (
        .aclk(aclk), .aresetn(aresetn),
        .s_axil_araddr(s_axil_araddr), .s_axil_arprot(s_axil_arprot),
        .s_axil_arvalid(s_axil_arvalid), .s_axil_arready(s_axil_arready),
        .s_axil_rdata(s_axil_rdata), .s_axil_rresp(s_axil_rresp),
        .s_axil_rvalid(s_axil_rvalid), .s_axil_rready(s_axil_rready),
        .fub_araddr(fub_araddr), .fub_arprot(fub_arprot),
        .fub_arvalid(fub_arvalid), .fub_arready(fub_arready),
        .fub_rdata(fub_rdata), .fub_rresp(fub_rresp),
        .fub_rvalid(fub_rvalid), .fub_rready(fub_rready),
        .busy());

    // ---- write side: AW holding register + B holding bit (loader pattern) ----
    // W is held off while the core owns port B, so a loader memory write
    // never collides with a running context's store.
    logic [AXIL_ADDR_WIDTH-1:0] wr_addr_q;
    logic                       wr_pend_q, b_pend_q;
    logic                       aw_fire, w_fire, b_fire;
    logic [1:0]                 wr_bank;

    assign aw_fire     = fub_awvalid && fub_awready;
    assign w_fire      = fub_wvalid  && fub_wready;
    assign b_fire      = fub_bvalid  && fub_bready;
    assign fub_awready = !wr_pend_q || w_fire;
    assign fub_wready  = wr_pend_q && !b_pend_q && !core_b;
    assign fub_bvalid  = b_pend_q;
    assign fub_bresp   = RESP_OKAY;
    assign wr_bank     = wr_addr_q[BANK_LSB +: 2];

    logic ld_wr, ctrl_wr;
    assign ld_wr   = w_fire && !wr_addr_q[REG_BIT] && !run_q[wr_bank];
    assign ctrl_wr = w_fire &&  wr_addr_q[REG_BIT] && !wr_addr_q[HREG_BIT]
                            && (wr_addr_q[3:2] == 2'd0) && fub_wstrb[0];

    `ALWAYS_FF_RST(aclk, aresetn,
        if (`RST_ASSERTED(aresetn)) begin
            wr_addr_q <= '0;
            wr_pend_q <= 1'b0;
            b_pend_q  <= 1'b0;
        end else begin
            if (aw_fire) wr_addr_q <= fub_awaddr;
            case ({aw_fire, w_fire})
                2'b10:   wr_pend_q <= 1'b1;
                2'b01:   wr_pend_q <= 1'b0;
                default: ;
            endcase
            if (w_fire)      b_pend_q <= 1'b1;
            else if (b_fire) b_pend_q <= 1'b0;
        end
    )

    // ---- read side: two stages (address -> block RAM -> holding register) ----
    // Port B takes one access per cycle: AR is accepted only when neither a
    // loader write nor the core wants it.
    logic                       rd_wait_q, rd_full_q, rd_reg_q, rd_hreg_q;
    logic [1:0]                 rd_ctx_q, rd_sel_q;
    logic [AXIL_DATA_WIDTH-1:0] rd_data_q, reg_rdata;
    logic                       ar_fire;

    assign fub_arready = !rd_wait_q && !rd_full_q && !ld_wr && !core_b;
    assign ar_fire     = fub_arvalid && fub_arready;
    assign fub_rvalid  = rd_full_q;
    assign fub_rdata   = rd_data_q;
    assign fub_rresp   = RESP_OKAY;

    always_comb begin
        reg_rdata = '0;
        if (rd_hreg_q) begin
            case (rd_sel_q)
                2'd0: reg_rdata = {24'd0, cause_q[rd_ctx_q], 2'b00,
                                   halted_q[rd_ctx_q], run_q[rd_ctx_q]};
                2'd1: reg_rdata = cycles_q[rd_ctx_q];
                2'd2: reg_rdata = instret_q[rd_ctx_q];
                default: reg_rdata = gp_q[rd_ctx_q];
            endcase
        end else begin
            case (rd_sel_q)
                2'd0:    reg_rdata = {24'd0, halted_q, run_q};
                2'd1:    reg_rdata = BUILD_ID;
                default: reg_rdata = '0;
            endcase
        end
    end

    `ALWAYS_FF_RST(aclk, aresetn,
        if (`RST_ASSERTED(aresetn)) begin
            rd_wait_q <= 1'b0;
            rd_full_q <= 1'b0;
            rd_reg_q  <= 1'b0;
            rd_hreg_q <= 1'b0;
            rd_ctx_q  <= '0;
            rd_sel_q  <= '0;
            rd_data_q <= '0;
        end else begin
            if (ar_fire) begin
                rd_wait_q <= 1'b1;
                rd_reg_q  <= fub_araddr[REG_BIT];
                rd_hreg_q <= fub_araddr[HREG_BIT];
                rd_ctx_q  <= fub_araddr[5:4];
                rd_sel_q  <= fub_araddr[3:2];
            end else if (rd_wait_q) begin
                rd_wait_q <= 1'b0;
                rd_full_q <= 1'b1;
                rd_data_q <= rd_reg_q ? reg_rdata : b_dout;
            end else if (rd_full_q && fub_rready) begin
                rd_full_q <= 1'b0;
            end
        end
    )

    always_comb begin
        if (core_b) begin
            b_en  = 1'b1;
            b_we  = dmem_wstrb;
            b_din = dmem_wdata;
            b_idx = {dmem_ctx, dmem_addr[IDX_W+1:2]};
        end else begin
            b_en  = ld_wr || ar_fire;
            b_we  = ld_wr ? fub_wstrb : 4'b0000;
            b_din = fub_wdata;
            b_idx = ld_wr ? {wr_bank, wr_addr_q[IDX_W+1:2]}
                          : {fub_araddr[BANK_LSB +: 2], fub_araddr[IDX_W+1:2]};
        end
    end

    // =========================================================================
    // Run control and status, per context
    // =========================================================================
    `ALWAYS_FF_RST(aclk, aresetn,
        if (`RST_ASSERTED(aresetn)) begin
            run_q     <= '0;
            halted_q  <= '0;
            cause_q   <= '0;
            cycles_q  <= '0;
            instret_q <= '0;
            gp_q      <= '0;
        end else begin
            for (int c = 0; c < NH; c++) begin
                if (ctrl_wr) run_q[c] <= fub_wdata[c];
                if (ctrl_wr && fub_wdata[c] && !run_q[c]) begin
                    halted_q[c]  <= 1'b0;
                    cause_q[c]   <= '0;
                    cycles_q[c]  <= '0;
                    instret_q[c] <= '0;
                    gp_q[c]      <= '0;
                end else if (run_q[c] && !halted_q[c]) begin
                    cycles_q[c] <= cycles_q[c] + 1'b1;
                    if (rvfi_valid && (rvfi_ctx == 2'(c))) begin
                        instret_q[c] <= instret_q[c] + 1'b1;
                        if (rvfi_rd_addr == REG_GP) gp_q[c] <= rvfi_rd_wdata;
                    end
                    if (halted[c]) begin
                        halted_q[c] <= 1'b1;
                        cause_q[c]  <= halt_cause[c];
                    end
                end
            end
        end
    )

endmodule : gatling_mem_bram
