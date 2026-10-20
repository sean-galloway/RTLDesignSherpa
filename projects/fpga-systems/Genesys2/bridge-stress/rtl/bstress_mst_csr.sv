// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: 2026 sean galloway
//
// Module: bstress_mst_csr
// Purpose: One stress master's register block: APB (cfg clock) ->
//          bstress_mst_regs (the master's clock) -> the axi_stress_pkg
//          cfg / status structures its protocol shell takes.
//
// Documentation: projects/fpga-systems/Genesys2/bridge-stress/PRD.md
// Author: sean galloway
// Created: 2026-10-19
//==============================================================================
// The register file runs on the MASTER's clock (aclk); apb4_to_peakrdl
// carries the APB access across from pclk, so a master in its own clock
// domain needs no other crossing for its configuration. Field-for-field
// mapping only -- no state of its own.
//==============================================================================

`timescale 1ns / 1ps

module bstress_mst_csr
    import axi_stress_pkg::*;
#(
    parameter int INDEX    = 0,
    parameter int PROTOCOL = 0,   // bstress_mst_regs.ID.PROTOCOL encoding
    parameter int DW       = 64,
    parameter int IW       = 8,
    parameter int DEPTH    = 16,
    parameter int NWIN     = 8,
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

    output stress_mdir_cfg_t cfg_rd,
    output stress_mdir_cfg_t cfg_wr,
    output stress_win_t      cfg_win [NWIN],
    input  stress_mdir_sts_t sts_rd,
    input  stress_mdir_sts_t sts_wr
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

    bstress_mst_regs_pkg::bstress_mst_regs__in_t  hi;
    bstress_mst_regs_pkg::bstress_mst_regs__out_t ho;

    bstress_mst_regs u_regs (
        .clk (aclk), .rst (~aresetn),
        .s_cpuif_req (req), .s_cpuif_req_is_wr (req_is_wr), .s_cpuif_addr (addr[9:0]),
        .s_cpuif_wr_data (wr_data), .s_cpuif_wr_biten (wr_biten),
        .s_cpuif_req_stall_wr (stall_wr), .s_cpuif_req_stall_rd (stall_rd),
        .s_cpuif_rd_ack (rd_ack), .s_cpuif_rd_err (rd_err), .s_cpuif_rd_data (rd_data),
        .s_cpuif_wr_ack (wr_ack), .s_cpuif_wr_err (wr_err),
        .hwif_in (hi), .hwif_out (ho)
    );
    wire unused_addr = ^addr[11:10];

    // ---- config out ---------------------------------------------------------
    always_comb begin
        cfg_rd = '0;
        cfg_rd.enable        = ho.RD_CTRL.ENABLE.value;
        cfg_rd.qos_rand      = ho.RD_CTRL.QOS_RAND.value;
        cfg_rd.idunq         = ho.RD_CTRL.IDUNQ.value;
        cfg_rd.timeout_lg2   = ho.RD_CTRL.TIMEOUT_LG2.value;
        cfg_rd.resp_throttle = ho.RD_CTRL.RESP_THROTTLE.value;
        cfg_rd.data_throttle = ho.RD_CTRL.DATA_THROTTLE.value;
        cfg_rd.gap_mask      = ho.RD_CTRL.GAP_MASK.value;
        cfg_rd.max_out       = ho.RD_CTRL.MAX_OUT.value;
        cfg_rd.txn_count     = ho.RD_TXN_COUNT.VALUE.value;
        cfg_rd.seed          = ho.RD_SEED.VALUE.value;
        cfg_rd.id_base       = ho.RD_ID_CFG.BASE.value;
        cfg_rd.id_mask       = ho.RD_ID_CFG.MASK.value;

        cfg_wr = '0;
        cfg_wr.enable        = ho.WR_CTRL.ENABLE.value;
        cfg_wr.qos_rand      = ho.WR_CTRL.QOS_RAND.value;
        cfg_wr.idunq         = ho.WR_CTRL.IDUNQ.value;
        cfg_wr.atom_lg2      = ho.WR_ATOM.LG2.value;
        cfg_wr.timeout_lg2   = ho.WR_CTRL.TIMEOUT_LG2.value;
        cfg_wr.resp_throttle = ho.WR_CTRL.RESP_THROTTLE.value;
        cfg_wr.data_throttle = ho.WR_CTRL.DATA_THROTTLE.value;
        cfg_wr.gap_mask      = ho.WR_CTRL.GAP_MASK.value;
        cfg_wr.max_out       = ho.WR_CTRL.MAX_OUT.value;
        cfg_wr.txn_count     = ho.WR_TXN_COUNT.VALUE.value;
        cfg_wr.seed          = ho.WR_SEED.VALUE.value;
        cfg_wr.id_base       = ho.WR_ID_CFG.BASE.value;
        cfg_wr.id_mask       = ho.WR_ID_CFG.MASK.value;

        for (int i = 0; i < NWIN; i++) begin
            cfg_win[i]            = '0;
            cfg_win[i].base       = ho.WIN[i].BASE.VALUE.value;
            cfg_win[i].size_lg2   = ho.WIN[i].CFG0.SIZE_LG2.value;
            cfg_win[i].resp       = ho.WIN[i].CFG0.RESP.value;
            cfg_win[i].tag        = ho.WIN[i].CFG0.TAG.value;
            cfg_win[i].len_mask   = ho.WIN[i].CFG0.LEN_MASK.value;
            cfg_win[i].size_min   = ho.WIN[i].CFG1.SIZE_MIN.value;
            cfg_win[i].size_max   = ho.WIN[i].CFG1.SIZE_MAX.value;
            cfg_win[i].burst_mask = ho.WIN[i].CFG1.BURST_MASK.value;
            cfg_win[i].unaligned  = ho.WIN[i].CFG1.UNALIGNED.value;
            cfg_win[i].strb_rand  = ho.WIN[i].CFG1.STRB_RAND.value;
            cfg_win[i].sb         = ho.WIN[i].CFG1.SB.value;
            cfg_win[i].poison_lg2 = ho.WIN[i].CFG1.POISON_LG2.value;
            cfg_win[i].atomic     = ho.WIN[i].CFG1.ATOMIC.value;
            cfg_win[i].rd_en      = ho.WIN[i].CFG1.RD_EN.value && HAS_RD;
            cfg_win[i].wr_en      = ho.WIN[i].CFG1.WR_EN.value && HAS_WR;
        end
    end

    // ---- status in ------------------------------------------------------------
    always_comb begin
        hi.ID.BUS_BYTES.next = 8'(DW / 8);
        hi.ID.ID_WIDTH.next  = 5'(IW);
        hi.ID.PROTOCOL.next  = 3'(PROTOCOL);
        hi.ID.MAGIC.next     = 16'h5354;
        hi.PARAMS.DEPTH.next  = 8'(DEPTH);
        hi.PARAMS.NWIN.next   = 4'(NWIN);
        hi.PARAMS.HAS_RD.next = HAS_RD;
        hi.PARAMS.HAS_WR.next = HAS_WR;
        hi.PARAMS.INDEX.next  = 4'(INDEX);

        hi.RD_STATUS.BUSY.next     = sts_rd.busy;
        hi.RD_STATUS.DONE.next     = sts_rd.done;
        hi.RD_STATUS.FE_VALID.next = sts_rd.fe_valid;
        hi.RD_STATUS.FE_KIND.next  = sts_rd.fe_kind;
        hi.RD_STATUS.RUNS.next     = sts_rd.runs;
        hi.RD_STATUS.OUT_NOW.next  = sts_rd.out_now;
        hi.RD_STATUS.OUT_MAX.next  = sts_rd.out_max;
        hi.RD_ISSUED.VALUE.next    = sts_rd.issued;
        hi.RD_COMPLETED.VALUE.next = sts_rd.completed;
        hi.RD_BEATS.VALUE.next     = sts_rd.beats;
        hi.RD_ERR.MASK.next        = sts_rd.err_mask;
        hi.RD_ERR.COUNT.next       = sts_rd.err_cnt;
        hi.RD_FE_ID.VALUE.next     = sts_rd.fe_id;
        hi.RD_FE_ADDR.VALUE.next   = sts_rd.fe_addr;
        hi.RD_FE_EXP.VALUE.next    = sts_rd.fe_exp;
        hi.RD_FE_ACT.VALUE.next    = sts_rd.fe_act;
        hi.RD_LAT_MAX.VALUE.next   = sts_rd.lat_max;
        hi.RD_LAT_SUM.VALUE.next   = sts_rd.lat_sum;

        hi.WR_STATUS.BUSY.next     = sts_wr.busy;
        hi.WR_STATUS.DONE.next     = sts_wr.done;
        hi.WR_STATUS.FE_VALID.next = sts_wr.fe_valid;
        hi.WR_STATUS.FE_KIND.next  = sts_wr.fe_kind;
        hi.WR_STATUS.RUNS.next     = sts_wr.runs;
        hi.WR_STATUS.OUT_NOW.next  = sts_wr.out_now;
        hi.WR_STATUS.OUT_MAX.next  = sts_wr.out_max;
        hi.WR_ISSUED.VALUE.next    = sts_wr.issued;
        hi.WR_COMPLETED.VALUE.next = sts_wr.completed;
        hi.WR_BEATS.VALUE.next     = sts_wr.beats;
        hi.WR_ERR.MASK.next        = sts_wr.err_mask;
        hi.WR_ERR.COUNT.next       = sts_wr.err_cnt;
        hi.WR_FE_ID.VALUE.next     = sts_wr.fe_id;
        hi.WR_FE_ADDR.VALUE.next   = sts_wr.fe_addr;
        hi.WR_FE_EXP.VALUE.next    = sts_wr.fe_exp;
        hi.WR_FE_ACT.VALUE.next    = sts_wr.fe_act;
        hi.WR_LAT_MAX.VALUE.next   = sts_wr.lat_max;
        hi.WR_LAT_SUM.VALUE.next   = sts_wr.lat_sum;
    end

endmodule : bstress_mst_csr
