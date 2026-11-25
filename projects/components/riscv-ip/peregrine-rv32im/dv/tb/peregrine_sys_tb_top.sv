// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: 2026 sean galloway
//
// RTL Design Sherpa - Industry-Standard RTL Design and Verification
// https://github.com/sean-galloway/RTLDesignSherpa
//
// Module: peregrine_sys_tb_top
// Purpose: TB harness for the cached peregrine (peregrine_top, TASK-001
//          stage 4): the wrapper on a behavioral AXI4 memory.
//
//          The port list matches peregrine_tb_top so PeregrineTB and the
//          battery runner drive both unchanged:
//          - dmem_req / dmem_addr / dmem_wstrb / dmem_wdata are the
//            wrapper's D-side observation, one beat per accepted access;
//          - mem_wait stalls the memory (no AR/AW/W accept, no R/B beat) for
//            the cycle, instead of holding the core directly;
//          - irq_software and irq_timer are ORed with the CLINT's (the
//            wrapper's TB hook), so the pin-driven interrupt suite runs
//            here too; tie them 0 to test the CLINT alone.
//          - tb_mem_* is the same reset-time backdoor loader; the
//            +imem / +dmem plusargs load the same array.
//          - tb_dc_clean_req / _done clean the D$ (amber) so results the
//            TB reads from mem (an arch-test signature) are in memory.
//
//          Memory model: one word array, aliased modulo MEM_WORDS; reads
//          serve INCR bursts beat by beat, writes apply strobes per beat.
//          One read and one write transaction at a time (every master in
//          peregrine_top issues one at a time per channel).  Behavioral,
//          not synthesizable.
//
//          RSP_SCRAMBLE=1 (TASK-001 stage 7): amber's response data
//          (u_top.w_dc_rsp_data, its cpu_rsp_rd_data) is forced to an LFSR
//          value on every cycle its response valid is low.  amber keeps its
//          last response on cpu_rsp_rd_data, so a wrapper that reads the
//          data outside its valid cycle (instead of the copy it captured)
//          passes by luck without this.  The force is on amber's whole beat,
//          upstream of peregrine_top's lane select, so every wrapper stage
//          stays the RTL under test; in the valid cycle it passes amber's
//          own value, re-derived from its frontend's response mux
//          (l1_cpu_frontend, RSP_BYPASS=1: the staged beat if one is
//          staged, else the bypassed one) because the port net itself is
//          the forced one.  The uncached port and the CLINT already drive 0
//          outside their valid.  A TB force, not RTL: peregrine_top and
//          amber are unchanged.
//
// Documentation: projects/components/riscv-ip/peregrine-rv32im/PRD.md
// Subsystem: riscv-ip/peregrine-rv32im
//
// Author: sean galloway
// Created: 2026-11-24

`timescale 1ns / 1ps

`include "reset_defs.svh"

module peregrine_sys_tb_top #(
    parameter logic [31:0] RESET_ADDR = 32'h0000_0000,
    parameter int          MEM_WORDS  = 65536,
    parameter bit          MUL_DSP    = 1'b0,
    parameter bit          BP_EN      = 1'b1,
    parameter int          MTIME_DIV  = 1,
    parameter bit          RSP_SCRAMBLE = 1'b0
) (
    input  logic        clk,
    input  logic        rst_n,
    input  logic        mem_wait,
    input  logic        irq_software,
    input  logic        irq_timer,
    input  logic        irq_external,
    output logic        dmem_req,
    output logic [31:0] dmem_addr,
    output logic [3:0]  dmem_wstrb,
    output logic [31:0] dmem_wdata,
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
    output logic        rvfi_bp_mispredict,
    input  logic        tb_mem_we,
    input  logic [31:0] tb_mem_addr,
    input  logic [31:0] tb_mem_wdata,
    // D$ clean hook (peregrine_top dc_clean_req / dc_clean_done): the TB
    // cleans amber before reading results from memory.
    input  logic        tb_dc_clean_req,
    output logic        tb_dc_clean_done,
    // Fabric observation for the TB (I$ refills, uncached accesses)
    output logic        fab_ar_hs,
    output logic [31:0] fab_araddr,
    output logic        fab_aw_hs
);

    localparam int AXI_DW = 64;
    localparam int AXI_IW = 4;
    localparam int FIW    = AXI_IW + 2;
    localparam int MEM_ADDR_MSB = $clog2(MEM_WORDS) + 1;

    logic [31:0] mem [MEM_WORDS];

    string imem_file;
    string dmem_file;

    initial begin
        for (int i = 0; i < MEM_WORDS; i++) mem[i] = '0;
        if ($value$plusargs("imem=%s", imem_file)) $readmemh(imem_file, mem);
        if ($value$plusargs("dmem=%s", dmem_file)) $readmemh(dmem_file, mem);
    end

    // AXI wires
    logic [FIW-1:0]    arid, rid, awid, bid;
    logic [31:0]       araddr, awaddr;
    logic [7:0]        arlen, awlen;
    logic [2:0]        arsize, awsize;
    logic [1:0]        arburst, awburst, rresp, bresp;
    logic              arvalid, arready, rlast, rvalid, rready;
    logic              awvalid, awready, wlast, wvalid, wready, bvalid, bready;
    logic [AXI_DW-1:0] rdata, wdata;
    logic [7:0]        wstrb;

    peregrine_top #(
        .RESET_ADDR (RESET_ADDR),
        .MUL_DSP    (MUL_DSP),
        .BP_EN      (BP_EN),
        .AXI_DW     (AXI_DW),
        .AXI_IW     (AXI_IW),
        .MTIME_DIV  (MTIME_DIV)
    ) u_top (
        .clk                 (clk),
        .rst_n               (rst_n),
        .irq_external        (irq_external),
        .tb_irq_software     (irq_software),
        .tb_irq_timer        (irq_timer),
        .dc_clean_req        (tb_dc_clean_req),
        .dc_clean_done       (tb_dc_clean_done),
        .m_axi_arid          (arid),
        .m_axi_araddr        (araddr),
        .m_axi_arlen         (arlen),
        .m_axi_arsize        (arsize),
        .m_axi_arburst       (arburst),
        .m_axi_arlock        (),
        .m_axi_arcache       (),
        .m_axi_arprot        (),
        .m_axi_arqos         (),
        .m_axi_arregion      (),
        .m_axi_arvalid       (arvalid),
        .m_axi_arready       (arready),
        .m_axi_rid           (rid),
        .m_axi_rdata         (rdata),
        .m_axi_rresp         (rresp),
        .m_axi_rlast         (rlast),
        .m_axi_rvalid        (rvalid),
        .m_axi_rready        (rready),
        .m_axi_awid          (awid),
        .m_axi_awaddr        (awaddr),
        .m_axi_awlen         (awlen),
        .m_axi_awsize        (awsize),
        .m_axi_awburst       (awburst),
        .m_axi_awlock        (),
        .m_axi_awcache       (),
        .m_axi_awprot        (),
        .m_axi_awqos         (),
        .m_axi_awregion      (),
        .m_axi_awvalid       (awvalid),
        .m_axi_awready       (awready),
        .m_axi_wdata         (wdata),
        .m_axi_wstrb         (wstrb),
        .m_axi_wlast         (wlast),
        .m_axi_wvalid        (wvalid),
        .m_axi_wready        (wready),
        .m_axi_bid           (bid),
        .m_axi_bresp         (bresp),
        .m_axi_bvalid        (bvalid),
        .m_axi_bready        (bready),
        .dobs_valid          (dmem_req),
        .dobs_addr           (dmem_addr),
        .dobs_wstrb          (dmem_wstrb),
        .dobs_wdata          (dmem_wdata),
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

    // -----------------------------------------------------------------
    // Behavioral AXI4 memory
    // -----------------------------------------------------------------
    logic             r_rd_act;
    logic [31:0]      r_rd_addr;
    logic [7:0]       r_rd_left;
    logic [FIW-1:0]   r_rd_id;
    logic             r_wr_act;
    logic             r_wr_bpend;
    logic [31:0]      r_wr_addr;
    logic [FIW-1:0]   r_wr_id;

    function automatic logic [MEM_ADDR_MSB-2:0] widx(input logic [31:0] a);
        return a[MEM_ADDR_MSB:2];
    endfunction

    assign arready = ~r_rd_act & ~mem_wait;
    assign rvalid  = r_rd_act & ~mem_wait;
    assign rid     = r_rd_id;
    assign rresp   = 2'b00;
    assign rlast   = (r_rd_left == 8'd0);
    assign rdata   = {mem[widx({r_rd_addr[31:3], 3'b100})], mem[widx({r_rd_addr[31:3], 3'b000})]};

    assign awready = ~r_wr_act & ~r_wr_bpend & ~mem_wait;
    assign wready  = r_wr_act & ~mem_wait;
    assign bvalid  = r_wr_bpend & ~mem_wait;
    assign bid     = r_wr_id;
    assign bresp   = 2'b00;

    assign fab_ar_hs  = arvalid & arready;
    assign fab_araddr = araddr;
    assign fab_aw_hs  = awvalid & awready;

    always_ff @(posedge clk) begin
        if (!rst_n) begin
            r_rd_act   <= 1'b0;
            r_rd_addr  <= '0;
            r_rd_left  <= '0;
            r_rd_id    <= '0;
            r_wr_act   <= 1'b0;
            r_wr_bpend <= 1'b0;
            r_wr_addr  <= '0;
            r_wr_id    <= '0;
        end else begin
            if (arvalid && arready) begin
                r_rd_act  <= 1'b1;
                r_rd_addr <= araddr;
                r_rd_left <= arlen;
                r_rd_id   <= arid;
            end else if (rvalid && rready) begin
                r_rd_addr <= r_rd_addr + 32'd8;
                r_rd_left <= r_rd_left - 8'd1;
                if (rlast) r_rd_act <= 1'b0;
            end
            if (awvalid && awready) begin
                r_wr_act  <= 1'b1;
                r_wr_addr <= awaddr;
                r_wr_id   <= awid;
            end else if (wvalid && wready) begin
                for (int b = 0; b < 8; b++) begin
                    if (wstrb[b]) begin
                        mem[widx({r_wr_addr[31:3], b[2], 2'b00})][(b % 4) * 8 +: 8] = wdata[b * 8 +: 8];
                    end
                end
                r_wr_addr <= r_wr_addr + 32'd8;
                if (wlast) begin
                    r_wr_act   <= 1'b0;
                    r_wr_bpend <= 1'b1;
                end
            end else if (bvalid && bready) begin
                r_wr_bpend <= 1'b0;
            end
        end
        if (tb_mem_we) begin
            mem[widx(tb_mem_addr)] = tb_mem_wdata;
        end
    end

    // D$ response scrambler (see the header).
    if (RSP_SCRAMBLE) begin : g_rsp_scramble
        logic [31:0] r_scr;
        always_ff @(posedge clk) begin
            if (!rst_n) r_scr <= 32'hACE1_5EED;
            else        r_scr <= {r_scr[30:0], r_scr[31] ^ r_scr[21] ^ r_scr[1] ^ r_scr[0]};
        end
        initial begin
            force u_top.w_dc_rsp_data = !u_top.w_dc_rsp_valid_raw ? {2{r_scr}} :
                u_top.u_dcache.u_cpu.u_frontend.stage_rd_valid
                    ? u_top.u_dcache.u_cpu.u_frontend.stage_rd_data
                    : u_top.u_dcache.u_cpu.u_frontend.ctrl_rsp_data;
        end
    end

    logic w_unused;
    assign w_unused = &{1'b0, arsize, arburst, awlen, awsize, awburst};

endmodule : peregrine_sys_tb_top
