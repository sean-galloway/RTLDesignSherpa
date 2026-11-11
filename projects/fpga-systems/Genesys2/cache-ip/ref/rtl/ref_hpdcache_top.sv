// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: 2026 sean galloway
//
// RTL Design Sherpa - Industry-Standard RTL Design and Verification
// https://github.com/sean-galloway/RTLDesignSherpa
//
// Module: ref_hpdcache_top
// Purpose:
//   The CEA / OpenHW HPDcache (vendor/cv-hpdcache) behind the cache-ip pair
//   rig's CPU port and memory port, so the reference L1 sees exactly the
//   stimulus amber and jet see (cache-ip common-ip TASK-003). Port shape is
//   jet_top's memory half: a GAXI cpu_req / cpu_rsp pair in, one AXI4
//   master out. No snoop side -- HPDcache is not coherent.
//
//   cpu_req {addr, we, be, wdata} -> one HPDcache requester (sid 0),
//   physically indexed (the tag rides in the request, so no second-cycle
//   tag/pma), LOAD or STORE, need_rsp on both. HPDcache answers loads and
//   stores to non-overlapping addresses OUT OF ORDER (tid-tagged); the rig's
//   injector counts responses in accept order (its latency ring and read
//   CRC assume it), so a REORDER_DEPTH-deep slot ring allocates the tid in
//   accept order and releases responses in that order. Memory side: the
//   upstream hpdcache_mem_to_axi_{read,write} adapters onto the rig's flat
//   AXI4 master signals (ID width AXI_ID_WIDTH; HPDcache tags reads by MSHR
//   entry and writes by write-buffer entry, both well inside 8 bits).
//
// Configuration (fixed here, mirrors the pair rig's geometry): SETS x WAYS
//   x LINE_BYTES with BUS_WIDTH words, PLRU victim, MSHR_WAYS outstanding
//   misses (one MSHR set, register bank), WBUF_ENTRIES write-buffer entries,
//   write-back policy (wbEn, cfg_default_wb), fast loads (lowLatency), no
//   ECC. The cache is enabled from reset.
//
// Documentation: vault/tracking/projects/components/cache-ip/common-ip/task/active/TASK-003.md
// Subsystem: cache-ip pair rig (reference variant)
//
// Author: sean galloway
// Created: 2026-11-11
`timescale 1ns / 1ps

`include "hpdcache_typedef.svh"

module ref_hpdcache_top
    import hpdcache_pkg::*;
#(
    parameter int ADDR_WIDTH     = 32,
    parameter int SETS           = 128,
    parameter int WAYS           = 4,
    parameter int LINE_BYTES     = 64,
    parameter int BUS_WIDTH      = 64,
    parameter int AXI_ID_WIDTH   = 8,
    parameter int AXI_USER_WIDTH = 1,
    parameter int MSHR_WAYS      = 8,    // outstanding misses (one MSHR set)
    parameter int WBUF_ENTRIES   = 8,    // write-buffer directory and data entries
    parameter int REORDER_DEPTH  = 16    // in-flight requests the response ring holds (power of 2)
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

    // Observability (no CSR behind these; the harness may tap them)
    output logic                      o_evt_read_miss,
    output logic                      o_evt_write_miss,
    output logic                      o_rsp_error        // sticky: a response carried error
);

    // ------------------------------------------------------------------
    // Geometry and HPDcache configuration
    // ------------------------------------------------------------------
    localparam int STRB_W   = BUS_WIDTH / 8;
    localparam int IW       = AXI_ID_WIDTH;
    localparam int UW       = AXI_USER_WIDTH;
    localparam int TID_W    = $clog2(REORDER_DEPTH);
    localparam int CL_WORDS = LINE_BYTES / (BUS_WIDTH / 8);

    localparam hpdcache_user_cfg_t UserCfg = '{
        nRequesters:              1,
        paWidth:                  ADDR_WIDTH,
        wordWidth:                BUS_WIDTH,
        sets:                     SETS,
        ways:                     WAYS,
        clWords:                  CL_WORDS,
        reqWords:                 1,
        reqTransIdWidth:          TID_W,
        reqSrcIdWidth:            1,
        victimSel:                HPDCACHE_VICTIM_PLRU,
        dataWaysPerRamWord:       (WAYS < 2) ? WAYS : 2,
        dataSetsPerRam:           SETS,
        accessWords:              1,      // one 64-bit word per data-array access and refill beat
        mshrSets:                 1,
        mshrWays:                 MSHR_WAYS,
        mshrWaysPerRamWord:       MSHR_WAYS,
        mshrSetsPerRam:           1,
        mshrRamByteEnable:        1'b1,
        mshrUseRegbank:           1'b1,
        cbufEntries:              4,
        refillCoreRspFeedthrough: 1'b1,
        refillFifoDepth:          2 * CL_WORDS,   // must hold a full line of 64-bit refill beats (upstream $fatal)
        wbufDirEntries:           WBUF_ENTRIES,
        wbufDataEntries:          WBUF_ENTRIES,
        wbufWords:                1,
        wbufTimecntWidth:         3,
        rtabEntries:              4,
        flushEntries:             4,
        flushFifoDepth:           2,
        memAddrWidth:             ADDR_WIDTH,
        memIdWidth:               IW,
        memDataWidth:             BUS_WIDTH,
        wtEn:                     1'b0,
        wbEn:                     1'b1,
        lowLatency:               1'b1,
        eccEn:                    1'b0,
        eccScrubberEn:            1'b0
    };
    localparam hpdcache_cfg_t Cfg = hpdcacheBuildConfig(UserCfg);

    typedef logic unsigned [Cfg.u.wbufTimecntWidth-1:0] wbuf_timecnt_t;
    `HPDCACHE_TYPEDEF_REQ_ATTR_T(hpdcache_req_offset_t, hpdcache_data_word_t,
                                 hpdcache_data_be_t, hpdcache_req_data_t,
                                 hpdcache_req_be_t, hpdcache_req_sid_t,
                                 hpdcache_req_tid_t, hpdcache_tag_t, Cfg);
    `HPDCACHE_TYPEDEF_REQ_T(hpdcache_req_t, hpdcache_req_offset_t, hpdcache_req_data_t,
                            hpdcache_req_be_t, hpdcache_req_sid_t, hpdcache_req_tid_t,
                            hpdcache_tag_t);
    `HPDCACHE_TYPEDEF_RSP_T(hpdcache_rsp_t, hpdcache_req_data_t, hpdcache_req_sid_t,
                            hpdcache_req_tid_t);
    `HPDCACHE_TYPEDEF_MEM_ATTR_T(hpdcache_mem_addr_t, hpdcache_mem_id_t,
                                 hpdcache_mem_data_t, hpdcache_mem_be_t, Cfg);
    `HPDCACHE_TYPEDEF_MEM_REQ_T(hpdcache_mem_req_t, hpdcache_mem_addr_t, hpdcache_mem_id_t);
    `HPDCACHE_TYPEDEF_MEM_RESP_R_T(hpdcache_mem_resp_r_t, hpdcache_mem_id_t, hpdcache_mem_data_t);
    `HPDCACHE_TYPEDEF_MEM_REQ_W_T(hpdcache_mem_req_w_t, hpdcache_mem_data_t, hpdcache_mem_be_t);
    `HPDCACHE_TYPEDEF_MEM_RESP_W_T(hpdcache_mem_resp_w_t, hpdcache_mem_id_t);
    typedef logic [Cfg.nlineWidth-1:0] hpdcache_nline_t;

    // AXI channel structs in the field vocabulary the upstream adapters use
    typedef struct packed {
        logic [IW-1:0]         id;
        logic [ADDR_WIDTH-1:0] addr;
        logic [7:0]            len;
        logic [2:0]            size;
        logic [1:0]            burst;
        logic                  lock;
        logic [3:0]            cache;
        logic [2:0]            prot;
        logic [3:0]            qos;
        logic [3:0]            region;
        logic [UW-1:0]         user;
    } ar_chan_t;
    typedef struct packed {
        logic [IW-1:0]         id;
        logic [ADDR_WIDTH-1:0] addr;
        logic [7:0]            len;
        logic [2:0]            size;
        logic [1:0]            burst;
        logic                  lock;
        logic [3:0]            cache;
        logic [2:0]            prot;
        logic [3:0]            qos;
        logic [3:0]            region;
        logic [5:0]            atop;
        logic [UW-1:0]         user;
    } aw_chan_t;
    typedef struct packed {
        logic [BUS_WIDTH-1:0] data;
        logic [STRB_W-1:0]    strb;
        logic                 last;
        logic [UW-1:0]        user;
    } w_chan_t;
    typedef struct packed {
        logic [IW-1:0] id;
        logic [1:0]    resp;
    } b_chan_t;
    typedef struct packed {
        logic [IW-1:0]        id;
        logic [BUS_WIDTH-1:0] data;
        logic [1:0]           resp;
        logic                 last;
        logic [UW-1:0]        user;
    } r_chan_t;

    // ------------------------------------------------------------------
    // CPU request unpack -> HPDcache request
    // ------------------------------------------------------------------
    logic [ADDR_WIDTH-1:0] w_req_addr;
    logic                  w_req_we;
    logic [STRB_W-1:0]     w_req_be;
    logic [BUS_WIDTH-1:0]  w_req_wdata;
    assign {w_req_addr, w_req_we, w_req_be, w_req_wdata} = cpu_req_wr_data;

    // response slot ring: tid = slot index, allocated in accept order
    logic [REORDER_DEPTH-1:0] r_slot_busy;   // allocated, response not yet released
    logic [REORDER_DEPTH-1:0] r_slot_done;   // response landed
    logic [REORDER_DEPTH-1:0] r_slot_store;  // the request was a store: its response carries no data
    logic [BUS_WIDTH-1:0]     r_slot_data [REORDER_DEPTH];
    logic [TID_W-1:0]         r_alloc_ptr, r_free_ptr;

    logic          core_req_valid [1];
    logic          core_req_ready [1];
    hpdcache_req_t core_req       [1];
    logic          core_req_abort [1];
    hpdcache_tag_t core_req_tag   [1];
    hpdcache_pma_t core_req_pma   [1];
    logic          core_rsp_valid [1];
    hpdcache_rsp_t core_rsp       [1];

    logic w_slot_free;
    assign w_slot_free      = ~r_slot_busy[r_alloc_ptr];
    assign cpu_req_wr_ready = w_slot_free & core_req_ready[0];
    assign core_req_valid[0] = cpu_req_wr_valid & w_slot_free;

    always_comb begin
        core_req[0]              = '0;
        // amber and jet address the 64-bit word (addr[2:0] is ignored, the
        // byte enables say which bytes); HPDcache requires the byte enables
        // to sit at or above the address offset within the word, so the
        // word-aligned offset carries the same request
        core_req[0].addr_offset  = {w_req_addr[Cfg.reqOffsetWidth-1:$clog2(STRB_W)],
                                    {$clog2(STRB_W){1'b0}}};
        core_req[0].addr_tag     = w_req_addr[ADDR_WIDTH-1 -: Cfg.tagWidth];
        core_req[0].wdata        = w_req_wdata;
        core_req[0].op           = w_req_we ? HPDCACHE_REQ_STORE : HPDCACHE_REQ_LOAD;
        // a load returns the whole word (amber/jet semantics); a store
        // writes the strobed bytes
        core_req[0].be           = w_req_we ? w_req_be : {STRB_W{1'b1}};
        core_req[0].size         = hpdcache_req_size_t'($clog2(STRB_W));
        core_req[0].sid          = '0;
        core_req[0].tid          = r_alloc_ptr;
        core_req[0].need_rsp     = 1'b1;
        core_req[0].phys_indexed = 1'b1;
        core_req[0].pma          = '{uncacheable: 1'b0, io: 1'b0,
                                     wr_policy_hint: HPDCACHE_WR_POLICY_WB};
    end
    assign core_req_abort[0] = 1'b0;
    assign core_req_tag[0]   = '0;   // phys_indexed: the tag rides in the request
    assign core_req_pma[0]   = '0;

    logic w_accept, w_release;
    assign w_accept  = cpu_req_wr_valid & cpu_req_wr_ready;
    assign w_release = cpu_rsp_rd_valid & cpu_rsp_rd_ready;

    assign cpu_rsp_rd_valid = r_slot_done[r_free_ptr];
    // HPDcache's store response leaves rdata unspecified (it differs between
    // the hit and the miss path); the rig's read CRC covers every response,
    // so a store answers with zero, which keeps the CRC a function of the
    // issued stream alone (amber and jet are deterministic here too).
    assign cpu_rsp_rd_data  = r_slot_store[r_free_ptr] ? '0 : r_slot_data[r_free_ptr];

    always_ff @(posedge aclk or negedge aresetn) begin
        if (!aresetn) begin
            r_slot_busy <= '0;
            r_slot_done <= '0;
            r_slot_store <= '0;
            r_alloc_ptr <= '0;
            r_free_ptr  <= '0;
            o_rsp_error <= 1'b0;
        end else begin
            if (w_accept) begin
                r_slot_busy[r_alloc_ptr]  <= 1'b1;
                r_slot_store[r_alloc_ptr] <= w_req_we;
                r_alloc_ptr              <= r_alloc_ptr + TID_W'(1);
            end
            if (core_rsp_valid[0]) begin
                r_slot_done[core_rsp[0].tid] <= 1'b1;
                r_slot_data[core_rsp[0].tid] <= core_rsp[0].rdata;
                if (core_rsp[0].error) o_rsp_error <= 1'b1;
            end
            if (w_release) begin
                r_slot_busy[r_free_ptr] <= 1'b0;
                r_slot_done[r_free_ptr] <= 1'b0;
                r_free_ptr              <= r_free_ptr + TID_W'(1);
            end
        end
    end

    // ------------------------------------------------------------------
    // The cache
    // ------------------------------------------------------------------
    logic                 mem_req_read_ready, mem_req_read_valid;
    hpdcache_mem_req_t    mem_req_read;
    logic                 mem_resp_read_ready, mem_resp_read_valid;
    hpdcache_mem_resp_r_t mem_resp_read;
    logic                 mem_req_write_ready, mem_req_write_valid;
    hpdcache_mem_req_t    mem_req_write;
    logic                 mem_req_write_data_ready, mem_req_write_data_valid;
    hpdcache_mem_req_w_t  mem_req_write_data;
    logic                 mem_resp_write_ready, mem_resp_write_valid;
    hpdcache_mem_resp_w_t mem_resp_write;

    hpdcache #(
        .HPDcacheCfg           (Cfg),
        .wbuf_timecnt_t        (wbuf_timecnt_t),
        .hpdcache_tag_t        (hpdcache_tag_t),
        .hpdcache_data_word_t  (hpdcache_data_word_t),
        .hpdcache_data_be_t    (hpdcache_data_be_t),
        .hpdcache_req_offset_t (hpdcache_req_offset_t),
        .hpdcache_req_data_t   (hpdcache_req_data_t),
        .hpdcache_req_be_t     (hpdcache_req_be_t),
        .hpdcache_req_sid_t    (hpdcache_req_sid_t),
        .hpdcache_req_tid_t    (hpdcache_req_tid_t),
        .hpdcache_req_t        (hpdcache_req_t),
        .hpdcache_rsp_t        (hpdcache_rsp_t),
        .hpdcache_mem_addr_t   (hpdcache_mem_addr_t),
        .hpdcache_mem_id_t     (hpdcache_mem_id_t),
        .hpdcache_mem_data_t   (hpdcache_mem_data_t),
        .hpdcache_mem_be_t     (hpdcache_mem_be_t),
        .hpdcache_mem_req_t    (hpdcache_mem_req_t),
        .hpdcache_mem_req_w_t  (hpdcache_mem_req_w_t),
        .hpdcache_mem_resp_r_t (hpdcache_mem_resp_r_t),
        .hpdcache_mem_resp_w_t (hpdcache_mem_resp_w_t)
    ) u_hpdcache (
        .clk_i                       (aclk),
        .rst_ni                      (aresetn),
        .wbuf_flush_i                (1'b0),
        .core_req_valid_i            (core_req_valid),
        .core_req_ready_o            (core_req_ready),
        .core_req_i                  (core_req),
        .core_req_abort_i            (core_req_abort),
        .core_req_tag_i              (core_req_tag),
        .core_req_pma_i              (core_req_pma),
        .core_rsp_valid_o            (core_rsp_valid),
        .core_rsp_o                  (core_rsp),
        .mem_req_read_ready_i        (mem_req_read_ready),
        .mem_req_read_valid_o        (mem_req_read_valid),
        .mem_req_read_o              (mem_req_read),
        .mem_resp_read_ready_o       (mem_resp_read_ready),
        .mem_resp_read_valid_i       (mem_resp_read_valid),
        .mem_resp_read_i             (mem_resp_read),
        .mem_resp_read_inval_i       (1'b0),
        .mem_resp_read_inval_nline_i ('0),
        .mem_req_write_ready_i       (mem_req_write_ready),
        .mem_req_write_valid_o       (mem_req_write_valid),
        .mem_req_write_o             (mem_req_write),
        .mem_req_write_data_ready_i  (mem_req_write_data_ready),
        .mem_req_write_data_valid_o  (mem_req_write_data_valid),
        .mem_req_write_data_o        (mem_req_write_data),
        .mem_resp_write_ready_o      (mem_resp_write_ready),
        .mem_resp_write_valid_i      (mem_resp_write_valid),
        .mem_resp_write_i            (mem_resp_write),
        .evt_cache_write_miss_o      (o_evt_write_miss),
        .evt_cache_read_miss_o       (o_evt_read_miss),
        .evt_cache_dir_unc_err_o     (),
        .evt_cache_dir_cor_err_o     (),
        .evt_cache_dat_unc_err_o     (),
        .evt_cache_dat_cor_err_o     (),
        .evt_scrub_complete_o        (),
        .evt_uncached_req_o          (),
        .evt_cmo_req_o               (),
        .evt_write_req_o             (),
        .evt_read_req_o              (),
        .evt_prefetch_req_o          (),
        .evt_req_on_hold_o           (),
        .evt_rtab_rollback_o         (),
        .evt_stall_refill_o          (),
        .evt_stall_o                 (),
        .wbuf_empty_o                (),
        .cfg_enable_i                        (1'b1),
        .cfg_wbuf_threshold_i                (wbuf_timecnt_t'(2)),
        .cfg_wbuf_reset_timecnt_on_write_i   (1'b1),
        .cfg_wbuf_sequential_waw_i           (1'b0),
        .cfg_wbuf_inhibit_write_coalescing_i (1'b0),
        .cfg_prefetch_updt_plru_i            (1'b1),
        .cfg_error_on_cacheable_amo_i        (1'b0),
        .cfg_rtab_single_entry_i             (1'b0),
        .cfg_default_wb_i                    (1'b1),
        .cfg_scrub_enable_i                  (1'b0),
        .cfg_scrub_period_i                  (6'd0),
        .cfg_scrub_restart_i                 (1'b0)
    );

    // ------------------------------------------------------------------
    // Memory side: HPDcache request/response channels -> AXI4
    // ------------------------------------------------------------------
    ar_chan_t axi_ar;
    r_chan_t  axi_r;
    aw_chan_t axi_aw;
    w_chan_t  axi_w;
    b_chan_t  axi_b;

    hpdcache_mem_to_axi_read #(
        .hpdcache_mem_req_t    (hpdcache_mem_req_t),
        .hpdcache_mem_resp_r_t (hpdcache_mem_resp_r_t),
        .ar_chan_t             (ar_chan_t),
        .r_chan_t              (r_chan_t)
    ) u_mem_rd (
        .req_ready_o    (mem_req_read_ready),
        .req_valid_i    (mem_req_read_valid),
        .req_i          (mem_req_read),
        .resp_ready_i   (mem_resp_read_ready),
        .resp_valid_o   (mem_resp_read_valid),
        .resp_o         (mem_resp_read),
        .axi_ar_valid_o (m_axi_arvalid),
        .axi_ar_o       (axi_ar),
        .axi_ar_ready_i (m_axi_arready),
        .axi_r_valid_i  (m_axi_rvalid),
        .axi_r_i        (axi_r),
        .axi_r_ready_o  (m_axi_rready)
    );

    hpdcache_mem_to_axi_write #(
        .hpdcache_mem_req_t    (hpdcache_mem_req_t),
        .hpdcache_mem_req_w_t  (hpdcache_mem_req_w_t),
        .hpdcache_mem_resp_w_t (hpdcache_mem_resp_w_t),
        .aw_chan_t             (aw_chan_t),
        .w_chan_t              (w_chan_t),
        .b_chan_t              (b_chan_t)
    ) u_mem_wr (
        .req_ready_o      (mem_req_write_ready),
        .req_valid_i      (mem_req_write_valid),
        .req_i            (mem_req_write),
        .req_data_ready_o (mem_req_write_data_ready),
        .req_data_valid_i (mem_req_write_data_valid),
        .req_data_i       (mem_req_write_data),
        .resp_ready_i     (mem_resp_write_ready),
        .resp_valid_o     (mem_resp_write_valid),
        .resp_o           (mem_resp_write),
        .axi_aw_valid_o   (m_axi_awvalid),
        .axi_aw_o         (axi_aw),
        .axi_aw_ready_i   (m_axi_awready),
        .axi_w_valid_o    (m_axi_wvalid),
        .axi_w_o          (axi_w),
        .axi_w_ready_i    (m_axi_wready),
        .axi_b_valid_i    (m_axi_bvalid),
        .axi_b_i          (axi_b),
        .axi_b_ready_o    (m_axi_bready)
    );

    assign m_axi_arid     = axi_ar.id;
    assign m_axi_araddr   = axi_ar.addr;
    assign m_axi_arlen    = axi_ar.len;
    assign m_axi_arsize   = axi_ar.size;
    assign m_axi_arburst  = axi_ar.burst;
    assign m_axi_arlock   = axi_ar.lock;
    assign m_axi_arcache  = axi_ar.cache;
    assign m_axi_arprot   = axi_ar.prot;
    assign m_axi_arqos    = axi_ar.qos;
    assign m_axi_arregion = axi_ar.region;
    assign m_axi_aruser   = axi_ar.user;
    assign axi_r = '{id: m_axi_rid, data: m_axi_rdata, resp: m_axi_rresp,
                     last: m_axi_rlast, user: m_axi_ruser};

    assign m_axi_awid     = axi_aw.id;
    assign m_axi_awaddr   = axi_aw.addr;
    assign m_axi_awlen    = axi_aw.len;
    assign m_axi_awsize   = axi_aw.size;
    assign m_axi_awburst  = axi_aw.burst;
    assign m_axi_awlock   = axi_aw.lock;
    assign m_axi_awcache  = axi_aw.cache;
    assign m_axi_awprot   = axi_aw.prot;
    assign m_axi_awqos    = axi_aw.qos;
    assign m_axi_awregion = axi_aw.region;
    assign m_axi_awuser   = axi_aw.user;
    assign m_axi_wdata    = axi_w.data;
    assign m_axi_wstrb    = axi_w.strb;
    assign m_axi_wlast    = axi_w.last;
    assign m_axi_wuser    = axi_w.user;
    assign axi_b = '{id: m_axi_bid, resp: m_axi_bresp};

endmodule : ref_hpdcache_top
