// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: 2026 sean galloway
//
// Module: bstress_slv_csr
// Purpose: One stress slave's register block: APB (cfg clock) ->
//          bstress_slv_regs (the slave's clock) -> stress_sdir_cfg_t /
//          stress_sdir_sts_t.
//
// Documentation: projects/fpga-systems/Genesys2/bridge-stress/PRD.md
// Author: sean galloway
// Created: 2026-10-19
//==============================================================================

`timescale 1ns / 1ps

module bstress_slv_csr
    import axi_stress_pkg::*;
#(
    parameter int INDEX    = 0,
    parameter int PROTOCOL = 0,
    parameter int DW       = 64,
    parameter int IW       = 8,
    parameter int DEPTH    = 16,
    parameter bit HAS_RD   = 1'b1,
    parameter bit HAS_WR   = 1'b1
) (
    input  logic             aclk,
    input  logic             aresetn,
    input  logic             pclk,
    input  logic             presetn,

    input  logic             s_apb_PSEL,
    input  logic             s_apb_PENABLE,
    output logic             s_apb_PREADY,
    input  logic [11:0]      s_apb_PADDR,
    input  logic             s_apb_PWRITE,
    input  logic [31:0]      s_apb_PWDATA,
    input  logic [3:0]       s_apb_PSTRB,
    input  logic [2:0]       s_apb_PPROT,
    output logic [31:0]      s_apb_PRDATA,
    output logic             s_apb_PSLVERR,

    output stress_sdir_cfg_t cfg_rd,
    output stress_sdir_cfg_t cfg_wr,
    input  stress_sdir_sts_t sts_rd,
    input  stress_sdir_sts_t sts_wr
);

    logic        req, req_is_wr, stall_wr, stall_rd, rd_ack, rd_err, wr_ack, wr_err;
    logic [11:0] addr;
    logic [31:0] wr_data, wr_biten, rd_data;

    apb4_to_peakrdl #(.ADDR_WIDTH(12), .DATA_WIDTH(32), .PROT_WIDTH(3)) u_shim (
        .aclk, .aresetn, .pclk, .presetn,
        .s_apb_PSEL, .s_apb_PENABLE, .s_apb_PREADY, .s_apb_PADDR, .s_apb_PWRITE,
        .s_apb_PWDATA, .s_apb_PSTRB, .s_apb_PPROT, .s_apb_PRDATA, .s_apb_PSLVERR,
        .cpuif_req (req), .cpuif_req_is_wr (req_is_wr), .cpuif_addr (addr),
        .cpuif_wr_data (wr_data), .cpuif_wr_biten (wr_biten),
        .cpuif_req_stall_wr (stall_wr), .cpuif_req_stall_rd (stall_rd),
        .cpuif_rd_ack (rd_ack), .cpuif_rd_err (rd_err), .cpuif_rd_data (rd_data),
        .cpuif_wr_ack (wr_ack), .cpuif_wr_err (wr_err)
    );

    bstress_slv_regs_pkg::bstress_slv_regs__in_t  hi;
    bstress_slv_regs_pkg::bstress_slv_regs__out_t ho;

    bstress_slv_regs u_regs (
        .clk (aclk), .rst (~aresetn),
        .s_cpuif_req (req), .s_cpuif_req_is_wr (req_is_wr), .s_cpuif_addr (addr[9:0]),
        .s_cpuif_wr_data (wr_data), .s_cpuif_wr_biten (wr_biten),
        .s_cpuif_req_stall_wr (stall_wr), .s_cpuif_req_stall_rd (stall_rd),
        .s_cpuif_rd_ack (rd_ack), .s_cpuif_rd_err (rd_err), .s_cpuif_rd_data (rd_data),
        .s_cpuif_wr_ack (wr_ack), .s_cpuif_wr_err (wr_err),
        .hwif_in (hi), .hwif_out (ho)
    );
    wire unused_addr = ^addr[11:10];

    always_comb begin
        cfg_rd = '0;
        cfg_rd.base          = ho.RD_BASE.VALUE.value;
        cfg_rd.size_lg2      = ho.RD_CTRL.SIZE_LG2.value;
        cfg_rd.offset_mode   = ho.RD_CTRL.OFFSET_MODE.value;
        cfg_rd.err_en        = ho.RD_CTRL.ERR_EN.value;
        cfg_rd.tag           = ho.RD_CTRL.TAG.value;
        cfg_rd.inorder       = ho.RD_CTRL.INORDER.value;
        cfg_rd.interleave    = ho.RD_CTRL.INTERLEAVE.value;
        cfg_rd.req_throttle  = ho.RD_CTRL.REQ_THROTTLE.value;
        cfg_rd.data_throttle = ho.RD_CTRL.DATA_THROTTLE.value;
        cfg_rd.err_base      = ho.RD_ERR_BASE.VALUE.value;
        cfg_rd.err_mask      = ho.RD_ERR_MASK.VALUE.value;
        cfg_rd.lat_min       = ho.RD_TIMING.LAT_MIN.value;
        cfg_rd.lat_mask      = ho.RD_TIMING.LAT_MASK.value;
        cfg_rd.max_out       = ho.RD_TIMING.MAX_OUT.value;
        cfg_rd.seed          = ho.RD_SEED.VALUE.value;
        cfg_rd.sb_src        = ho.RD_SB.SRC.value;
        cfg_rd.poison_lg2    = ho.RD_SB.POISON_LG2.value;

        cfg_wr = '0;
        cfg_wr.base          = ho.WR_BASE.VALUE.value;
        cfg_wr.size_lg2      = ho.WR_CTRL.SIZE_LG2.value;
        cfg_wr.offset_mode   = ho.WR_CTRL.OFFSET_MODE.value;
        cfg_wr.err_en        = ho.WR_CTRL.ERR_EN.value;
        cfg_wr.tag           = ho.WR_CTRL.TAG.value;
        cfg_wr.inorder       = ho.WR_CTRL.INORDER.value;
        cfg_wr.interleave    = ho.WR_CTRL.INTERLEAVE.value;
        cfg_wr.req_throttle  = ho.WR_CTRL.REQ_THROTTLE.value;
        cfg_wr.data_throttle = ho.WR_CTRL.DATA_THROTTLE.value;
        cfg_wr.err_base      = ho.WR_ERR_BASE.VALUE.value;
        cfg_wr.err_mask      = ho.WR_ERR_MASK.VALUE.value;
        cfg_wr.lat_min       = ho.WR_TIMING.LAT_MIN.value;
        cfg_wr.lat_mask      = ho.WR_TIMING.LAT_MASK.value;
        cfg_wr.max_out       = ho.WR_TIMING.MAX_OUT.value;
        cfg_wr.seed          = ho.WR_SEED.VALUE.value;
        cfg_wr.sb_src        = ho.WR_SB.SRC.value;
        cfg_wr.poison_lg2    = ho.WR_SB.POISON_LG2.value;
        cfg_wr.w_first       = ho.WR_CTRL.W_FIRST.value;
    end

    always_comb begin
        hi.ID.BUS_BYTES.next  = 8'(DW / 8);
        hi.ID.ID_WIDTH.next   = 5'(IW);
        hi.ID.PROTOCOL.next   = 3'(PROTOCOL);
        hi.ID.MAGIC.next      = 16'h5353;
        hi.PARAMS.DEPTH.next  = 8'(DEPTH);
        hi.PARAMS.HAS_RD.next = HAS_RD;
        hi.PARAMS.HAS_WR.next = HAS_WR;
        hi.PARAMS.INDEX.next  = 4'(INDEX);
        hi.RD_BURSTS.VALUE.next = sts_rd.bursts;
        hi.RD_BEATS.VALUE.next  = sts_rd.beats;
        hi.RD_ERR.MASK.next     = sts_rd.err_mask;
        hi.RD_ERR.COUNT.next    = sts_rd.err_cnt;
        hi.RD_FE.FE_VALID.next  = sts_rd.fe_valid;
        hi.RD_FE.FE_KIND.next   = sts_rd.fe_kind;
        hi.RD_FE.FE_ID.next     = sts_rd.fe_id;
        hi.RD_FE_ADDR.VALUE.next = sts_rd.fe_addr;
        hi.RD_FE_EXP.VALUE.next = sts_rd.fe_exp;
        hi.RD_FE_ACT.VALUE.next = sts_rd.fe_act;
        hi.RD_OUT.OUT_NOW.next  = sts_rd.out_now;
        hi.RD_OUT.OUT_MAX.next  = sts_rd.out_max;
        hi.RD_OUT.RUNS.next     = sts_rd.runs;
        hi.WR_BURSTS.VALUE.next = sts_wr.bursts;
        hi.WR_BEATS.VALUE.next  = sts_wr.beats;
        hi.WR_ERR.MASK.next     = sts_wr.err_mask;
        hi.WR_ERR.COUNT.next    = sts_wr.err_cnt;
        hi.WR_FE.FE_VALID.next  = sts_wr.fe_valid;
        hi.WR_FE.FE_KIND.next   = sts_wr.fe_kind;
        hi.WR_FE.FE_ID.next     = sts_wr.fe_id;
        hi.WR_FE_ADDR.VALUE.next = sts_wr.fe_addr;
        hi.WR_FE_EXP.VALUE.next = sts_wr.fe_exp;
        hi.WR_FE_ACT.VALUE.next = sts_wr.fe_act;
        hi.WR_OUT.OUT_NOW.next  = sts_wr.out_now;
        hi.WR_OUT.OUT_MAX.next  = sts_wr.out_max;
        hi.WR_OUT.RUNS.next     = sts_wr.runs;
    end

endmodule : bstress_slv_csr
