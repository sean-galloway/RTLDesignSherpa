// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: 2026 sean galloway
//
// RTL Design Sherpa - Industry-Standard RTL Design and Verification
// https://github.com/sean-galloway/RTLDesignSherpa
//
// Module: ref_cva6_dcache_top
// Purpose:
//   The OpenHW CVA6 write-back data cache (std_nbdcache, vendor/cva6-dcache)
//   behind the cache-ip pair rig's CPU port and memory port (cache-ip
//   common-ip TASK-003): the blocking reference, amber's peer. Port shape is
//   jet_top's memory half: a GAXI cpu_req / cpu_rsp pair in, one AXI4
//   master out. No snoop side -- the CVA6 cache is not coherent.
//
//   CVA6 drives this cache from separate load and store units on separate
//   request ports, and its controller assumes that (a port that sees both
//   would double-grant a store presented behind a load hit), so the wrapper
//   does the same: loads on port 0, stores on port 1, never both in flight.
//     load : data_req with the index; data_gnt accepts it; the next cycle
//            presents tag_valid with the tag (the controller samples the tag
//            one cycle behind the index, and a hit returns data_rvalid in
//            that same cycle); a further load may be presented in that cycle
//            (the controller's WAIT_TAG re-grant), so hits stream one per
//            cycle. A load is presented only while no store is pending.
//     store: data_req held until data_gnt, which the controller gives when
//            the store has landed in the array (its second array access);
//            presented only when no load is in the pipe, so a load after a
//            store to the same word reads the stored bytes.
//   Acceptance on the GAXI port is the cache's grant for both kinds, so the
//   injector's STALL_CYCLES counts the time a request waited at the port
//   and its latency counts grant-to-response (a load hit: 2 cycles; a store:
//   1). Responses leave in accept order by construction (loads and stores
//   never overlap, loads answer in order on one port); a store answers with
//   zero data. Memory side: the cache's own axi_adapter (refills, write-
//   backs) onto the rig's flat AXI4 master; the bypass master is unused
//   (the cache is enabled from reset and nothing is uncacheable) and tied
//   off.
//
// Configuration: ref_cva6_cfg_pkg -- upstream's cv64a6 write-back point
//   with the geometry set to the pair rig's (32 KB, 4 ways, 64 B lines,
//   64-bit AXI, ID width 8).
//
// Documentation: vault/tracking/projects/components/cache-ip/common-ip/task/active/TASK-003.md
// Subsystem: cache-ip pair rig (reference variant)
//
// Author: sean galloway
// Created: 2026-11-11
`timescale 1ns / 1ps

`include "axi/typedef.svh"

module ref_cva6_dcache_top
    import ariane_pkg::*;
#(
    parameter int ADDR_WIDTH     = 32,
    parameter int BUS_WIDTH      = 64,
    parameter int AXI_ID_WIDTH   = 8,
    parameter int AXI_USER_WIDTH = 1,
    parameter config_pkg::cva6_cfg_t CVA6Cfg = ref_cva6_cfg_pkg::CVA6Cfg
) (
    input  logic aclk,
    input  logic aresetn,

    // GAXI CPU port (packet: {addr, we, be, wdata})
    input  logic                                   cpu_req_wr_valid,
    output logic                                   cpu_req_wr_ready,
    input  logic [ADDR_WIDTH+1+BUS_WIDTH/8+BUS_WIDTH-1:0] cpu_req_wr_data,
    output logic                                   cpu_rsp_rd_valid,
    input  logic                                   cpu_rsp_rd_ready,
    output logic [BUS_WIDTH-1:0]                   cpu_rsp_rd_data,

    // AXI4 master (memory side)
    output logic [AXI_ID_WIDTH-1:0]   m_axi_arid,
    output logic [ADDR_WIDTH-1:0]     m_axi_araddr,
    output logic [7:0]                m_axi_arlen,
    output logic [2:0]                m_axi_arsize,
    output logic [1:0]                m_axi_arburst,
    output logic                      m_axi_arlock,
    output logic [3:0]                m_axi_arcache,
    output logic [2:0]                m_axi_arprot,
    output logic [3:0]                m_axi_arqos,
    output logic [3:0]                m_axi_arregion,
    output logic [AXI_USER_WIDTH-1:0] m_axi_aruser,
    output logic                      m_axi_arvalid,
    input  logic                      m_axi_arready,
    input  logic [AXI_ID_WIDTH-1:0]   m_axi_rid,
    input  logic [BUS_WIDTH-1:0]      m_axi_rdata,
    input  logic [1:0]                m_axi_rresp,
    input  logic                      m_axi_rlast,
    input  logic [AXI_USER_WIDTH-1:0] m_axi_ruser,
    input  logic                      m_axi_rvalid,
    output logic                      m_axi_rready,
    output logic [AXI_ID_WIDTH-1:0]   m_axi_awid,
    output logic [ADDR_WIDTH-1:0]     m_axi_awaddr,
    output logic [7:0]                m_axi_awlen,
    output logic [2:0]                m_axi_awsize,
    output logic [1:0]                m_axi_awburst,
    output logic                      m_axi_awlock,
    output logic [3:0]                m_axi_awcache,
    output logic [2:0]                m_axi_awprot,
    output logic [3:0]                m_axi_awqos,
    output logic [3:0]                m_axi_awregion,
    output logic [AXI_USER_WIDTH-1:0] m_axi_awuser,
    output logic                      m_axi_awvalid,
    input  logic                      m_axi_awready,
    output logic [BUS_WIDTH-1:0]      m_axi_wdata,
    output logic [BUS_WIDTH/8-1:0]    m_axi_wstrb,
    output logic                      m_axi_wlast,
    output logic [AXI_USER_WIDTH-1:0] m_axi_wuser,
    output logic                      m_axi_wvalid,
    input  logic                      m_axi_wready,
    input  logic [AXI_ID_WIDTH-1:0]   m_axi_bid,
    input  logic [1:0]                m_axi_bresp,
    input  logic [AXI_USER_WIDTH-1:0] m_axi_buser,
    input  logic                      m_axi_bvalid,
    output logic                      m_axi_bready,

    // Observability
    output logic                      o_miss,
    output logic                      o_rsp_error        // sticky: a load response carried data_error
);

    localparam int STRB_W  = BUS_WIDTH / 8;
    localparam int IW      = AXI_ID_WIDTH;
    localparam int UW      = AXI_USER_WIDTH;
    localparam int IDX_W   = CVA6Cfg.DCACHE_INDEX_WIDTH;
    localparam int TAG_W   = CVA6Cfg.DCACHE_TAG_WIDTH;
    localparam int LD_PORT = 0;
    localparam int ST_PORT = 1;

    // ------------------------------------------------------------------
    // CVA6 dcache request / response port types (cva6.sv's definitions;
    // cbo_t is cva6.sv's 8-bit cache-block-operation code, unused by the
    // write-back cache)
    // ------------------------------------------------------------------
    typedef logic [7:0] cbo_t;
    typedef struct packed {
        logic [IDX_W-1:0]                      address_index;
        logic [TAG_W-1:0]                      address_tag;
        logic [CVA6Cfg.XLEN-1:0]               data_wdata;
        logic [CVA6Cfg.DCACHE_USER_WIDTH-1:0]  data_wuser;
        logic                                  data_req;
        logic                                  data_we;
        logic [(CVA6Cfg.XLEN/8)-1:0]           data_be;
        logic [1:0]                            data_size;
        logic [CVA6Cfg.DcacheIdWidth-1:0]      data_id;
        logic                                  kill_req;
        logic                                  tag_valid;
        cbo_t                                  cbo_op;
    } dcache_req_i_t;

    typedef struct packed {
        logic                                 data_gnt;
        logic                                 data_rvalid;
        logic [CVA6Cfg.DcacheIdWidth-1:0]     data_rid;
        logic [CVA6Cfg.XLEN-1:0]              data_rdata;
        logic [CVA6Cfg.DCACHE_USER_WIDTH-1:0] data_ruser;
        logic                                 data_error;
    } dcache_req_o_t;

    // AXI request / response structs in the PULP field vocabulary the
    // cache's axi_adapter uses
    typedef logic [CVA6Cfg.AxiAddrWidth-1:0] axi_addr_t;
    typedef logic [IW-1:0]                   axi_id_t;
    typedef logic [BUS_WIDTH-1:0]            axi_data_t;
    typedef logic [STRB_W-1:0]               axi_strb_t;
    typedef logic [UW-1:0]                   axi_user_t;
    `AXI_TYPEDEF_ALL(ref_axi, axi_addr_t, axi_id_t, axi_data_t, axi_strb_t, axi_user_t)

    // ------------------------------------------------------------------
    // CPU request unpack
    // ------------------------------------------------------------------
    logic [ADDR_WIDTH-1:0] w_req_addr;
    logic                  w_req_we;
    logic [STRB_W-1:0]     w_req_be;
    logic [BUS_WIDTH-1:0]  w_req_wdata;
    assign {w_req_addr, w_req_we, w_req_be, w_req_wdata} = cpu_req_wr_data;

    // word-aligned index (the rig addresses the 64-bit word; the strobes
    // say which bytes) and the tag zero-extended to the cache's PLEN
    logic [IDX_W-1:0] w_req_index;
    logic [TAG_W-1:0] w_req_tag;
    assign w_req_index = {w_req_addr[IDX_W-1:$clog2(STRB_W)], {$clog2(STRB_W){1'b0}}};
    assign w_req_tag   = TAG_W'(w_req_addr[ADDR_WIDTH-1:IDX_W]);

    // ------------------------------------------------------------------
    // Port scheduling
    // ------------------------------------------------------------------
    dcache_req_i_t [1:0] req_ports_i;   // packed, as std_nbdcache declares its ports
    dcache_req_o_t [1:0] req_ports_o;

    logic [TAG_W-1:0] r_ld_tag;        // tag of the load granted last cycle
    logic             r_ld_tag_pend;   // present it this cycle (tag_valid)
    logic [1:0]       r_ld_outst;      // loads granted, data not yet returned
    logic             w_ld_gnt, w_st_gnt, w_ld_rvalid;
    logic             w_loads_quiet;

    assign w_loads_quiet = (r_ld_outst == 2'd0) & ~r_ld_tag_pend;

    // a load may be presented whenever the head is a load (stores are only
    // ever presented when the load pipe is empty, and block until granted,
    // so the head cannot be a load while a store is pending); a store only
    // when the load pipe is empty
    logic w_present_ld, w_present_st;
    assign w_present_ld = cpu_req_wr_valid & ~w_req_we;
    assign w_present_st = cpu_req_wr_valid &  w_req_we & w_loads_quiet;

    always_comb begin
        req_ports_i[LD_PORT]               = '0;
        req_ports_i[LD_PORT].address_index = w_req_index;
        req_ports_i[LD_PORT].address_tag   = r_ld_tag;      // the previous load's tag
        req_ports_i[LD_PORT].data_req      = w_present_ld;
        req_ports_i[LD_PORT].data_we       = 1'b0;
        req_ports_i[LD_PORT].data_be       = {STRB_W{1'b1}};
        req_ports_i[LD_PORT].data_size     = 2'b11;         // 8 bytes
        req_ports_i[LD_PORT].tag_valid     = r_ld_tag_pend;
        req_ports_i[LD_PORT].cbo_op        = '0;

        req_ports_i[ST_PORT]               = '0;
        req_ports_i[ST_PORT].address_index = w_req_index;
        req_ports_i[ST_PORT].address_tag   = w_req_tag;     // sampled the cycle after the request is taken
        req_ports_i[ST_PORT].data_wdata    = w_req_wdata;
        req_ports_i[ST_PORT].data_req      = w_present_st;
        req_ports_i[ST_PORT].data_we       = 1'b1;
        req_ports_i[ST_PORT].data_be       = w_req_be;
        req_ports_i[ST_PORT].data_size     = 2'b11;
        req_ports_i[ST_PORT].tag_valid     = 1'b1;
        req_ports_i[ST_PORT].cbo_op        = '0;
    end

    assign w_ld_gnt    = w_present_ld & req_ports_o[LD_PORT].data_gnt;
    assign w_st_gnt    = w_present_st & req_ports_o[ST_PORT].data_gnt;
    assign w_ld_rvalid = req_ports_o[LD_PORT].data_rvalid;
    assign cpu_req_wr_ready = w_req_we ? (w_loads_quiet & req_ports_o[ST_PORT].data_gnt)
                                       : req_ports_o[LD_PORT].data_gnt;

    always_ff @(posedge aclk or negedge aresetn) begin
        if (!aresetn) begin
            r_ld_tag      <= '0;
            r_ld_tag_pend <= 1'b0;
            r_ld_outst    <= 2'd0;
            o_rsp_error   <= 1'b0;
        end else begin
            r_ld_tag_pend <= w_ld_gnt;
            if (w_ld_gnt) r_ld_tag <= w_req_tag;
            r_ld_outst <= r_ld_outst + 2'(w_ld_gnt) - 2'(w_ld_rvalid);
            if (w_ld_rvalid & req_ports_o[LD_PORT].data_error) o_rsp_error <= 1'b1;
        end
    end

    // ------------------------------------------------------------------
    // Responses, in accept order: a store answers at its grant with zero
    // data, a load at data_rvalid. Four entries cover the two loads the
    // controller can hold plus a store landing while they drain.
    // ------------------------------------------------------------------
    logic                 w_rsp_push;
    logic [BUS_WIDTH-1:0] w_rsp_data;
    assign w_rsp_push = w_st_gnt | w_ld_rvalid;
    assign w_rsp_data = w_ld_rvalid ? req_ports_o[LD_PORT].data_rdata : '0;

    logic [BUS_WIDTH-1:0] r_rsp_q [4];
    logic [1:0]           r_rsp_wr, r_rsp_rd;
    logic [2:0]           r_rsp_cnt;
    assign cpu_rsp_rd_valid = (r_rsp_cnt != 3'd0);
    assign cpu_rsp_rd_data  = r_rsp_q[r_rsp_rd];

    logic w_rsp_pop;
    assign w_rsp_pop = cpu_rsp_rd_valid & cpu_rsp_rd_ready;

    always_ff @(posedge aclk or negedge aresetn) begin
        if (!aresetn) begin
            r_rsp_wr  <= '0;
            r_rsp_rd  <= '0;
            r_rsp_cnt <= '0;
        end else begin
            if (w_rsp_push) begin
                r_rsp_q[r_rsp_wr] <= w_rsp_data;
                r_rsp_wr          <= r_rsp_wr + 2'd1;
            end
            if (w_rsp_pop) r_rsp_rd <= r_rsp_rd + 2'd1;
            r_rsp_cnt <= r_rsp_cnt + 3'(w_rsp_push) - 3'(w_rsp_pop);
        end
    end

    // ------------------------------------------------------------------
    // The cache
    // ------------------------------------------------------------------
    ref_axi_req_t  axi_data_req, axi_bypass_req;
    ref_axi_resp_t axi_data_rsp, axi_bypass_rsp;
    /* verilator lint_off UNUSEDSIGNAL */
    logic      flush_ack_unused;
    amo_resp_t amo_resp_unused;
    /* verilator lint_on UNUSEDSIGNAL */

    std_nbdcache #(
        .CVA6Cfg       (CVA6Cfg),
        .dcache_req_i_t(dcache_req_i_t),
        .dcache_req_o_t(dcache_req_o_t),
        .NumPorts      (2),
        .axi_req_t     (ref_axi_req_t),
        .axi_rsp_t     (ref_axi_resp_t)
    ) u_dcache (
        .clk_i        (aclk),
        .rst_ni       (aresetn),
        .enable_i     (1'b1),
        .flush_i      (1'b0),
        .flush_ack_o  (flush_ack_unused),
        .miss_o       (o_miss),
        .amo_req_i    ('0),
        .amo_resp_o   (amo_resp_unused),
        .req_ports_i  (req_ports_i),
        .req_ports_o  (req_ports_o),
        .axi_data_o   (axi_data_req),
        .axi_data_i   (axi_data_rsp),
        .axi_bypass_o (axi_bypass_req),
        .axi_bypass_i (axi_bypass_rsp)
    );

    // the bypass master never issues (enable_i is high, nothing is
    // uncacheable, no AMOs): no readies, no responses
    assign axi_bypass_rsp = '0;
    /* verilator lint_off UNUSEDSIGNAL */
    ref_axi_req_t w_bypass_unused;
    assign w_bypass_unused = axi_bypass_req;
    /* verilator lint_on UNUSEDSIGNAL */

    // ------------------------------------------------------------------
    // AXI structs -> the rig's flat AXI4 master
    // ------------------------------------------------------------------
    assign m_axi_arid     = axi_data_req.ar.id;
    assign m_axi_araddr   = axi_data_req.ar.addr[ADDR_WIDTH-1:0];
    assign m_axi_arlen    = axi_data_req.ar.len;
    assign m_axi_arsize   = axi_data_req.ar.size;
    assign m_axi_arburst  = axi_data_req.ar.burst;
    assign m_axi_arlock   = axi_data_req.ar.lock;
    assign m_axi_arcache  = axi_data_req.ar.cache;
    assign m_axi_arprot   = axi_data_req.ar.prot;
    assign m_axi_arqos    = axi_data_req.ar.qos;
    assign m_axi_arregion = axi_data_req.ar.region;
    assign m_axi_aruser   = axi_data_req.ar.user;
    assign m_axi_arvalid  = axi_data_req.ar_valid;
    assign m_axi_rready   = axi_data_req.r_ready;
    assign m_axi_awid     = axi_data_req.aw.id;
    assign m_axi_awaddr   = axi_data_req.aw.addr[ADDR_WIDTH-1:0];
    assign m_axi_awlen    = axi_data_req.aw.len;
    assign m_axi_awsize   = axi_data_req.aw.size;
    assign m_axi_awburst  = axi_data_req.aw.burst;
    assign m_axi_awlock   = axi_data_req.aw.lock;
    assign m_axi_awcache  = axi_data_req.aw.cache;
    assign m_axi_awprot   = axi_data_req.aw.prot;
    assign m_axi_awqos    = axi_data_req.aw.qos;
    assign m_axi_awregion = axi_data_req.aw.region;
    assign m_axi_awuser   = axi_data_req.aw.user;
    assign m_axi_awvalid  = axi_data_req.aw_valid;
    assign m_axi_wdata    = axi_data_req.w.data;
    assign m_axi_wstrb    = axi_data_req.w.strb;
    assign m_axi_wlast    = axi_data_req.w.last;
    assign m_axi_wuser    = axi_data_req.w.user;
    assign m_axi_wvalid   = axi_data_req.w_valid;
    assign m_axi_bready   = axi_data_req.b_ready;

    always_comb begin
        axi_data_rsp          = '0;
        axi_data_rsp.aw_ready = m_axi_awready;
        axi_data_rsp.ar_ready = m_axi_arready;
        axi_data_rsp.w_ready  = m_axi_wready;
        axi_data_rsp.b_valid  = m_axi_bvalid;
        axi_data_rsp.b.id     = m_axi_bid;
        axi_data_rsp.b.resp   = m_axi_bresp;
        axi_data_rsp.b.user   = m_axi_buser;
        axi_data_rsp.r_valid  = m_axi_rvalid;
        axi_data_rsp.r.id     = m_axi_rid;
        axi_data_rsp.r.data   = m_axi_rdata;
        axi_data_rsp.r.resp   = m_axi_rresp;
        axi_data_rsp.r.last   = m_axi_rlast;
        axi_data_rsp.r.user   = m_axi_ruser;
    end

endmodule : ref_cva6_dcache_top
