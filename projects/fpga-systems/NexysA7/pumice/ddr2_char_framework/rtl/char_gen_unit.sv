// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: 2024-2026 sean galloway
//
// RTL Design Sherpa - Industry-Standard RTL Design and Verification
// https://github.com/sean-galloway/RTLDesignSherpa
//
// Module: char_gen_unit
// Purpose: The characterization stimulus source -- N write and N read
//          generator blocks behind ONE AXI4 master port
//
// Documentation: ddr2-characterization/flows-litedram-uart/HARNESS_PLAN.md
//==============================================================================
// Description:
//   One generator unit, N generator blocks inside it, one AXI4 master port out
//   that hooks straight to the memory controller's s_axi:
//
//     cfg_i -> axi4_master_wr_pattern_gen [NUM_GEN] -\
//                                                     >-- m_axi_* -> the MC
//              axi4_master_rd_crc_check   [NUM_GEN] -/
//
//   Replaces the two generated 2x1 bridges (bridge_ddr2_char_wr /
//   bridge_ddr2_char_rd) that used to sit between the generators and the
//   controller on the data path. The APB config path still goes through the
//   bridge, which is the right tool there -- a real address decode across
//   several unrelated slaves. This is not that: it is N identical masters
//   merging onto one slave at one address range.
//
//   To be precise about what was actually costly, because the module names
//   mislead: the bridges' routing module is called *_xbar, but at 2x1 there is
//   nothing to cross. It is a combinational grant-lock round-robin plus one
//   address comparator -- 88 LUTs on the read side, 338 on the write side --
//   and u_aw_mux/u_ar_mux below do the same job by the same method. What cost
//   something was the four generated ADAPTERS wrapped around it (1069 of the
//   read bridge's 1123 LUTs), which carry three things a measuring instrument
//   cannot afford.
//
//   1. Outstanding depth. Each generated adapter gates the address channel on
//      a bridge_cam with DEPTH(16), so the whole engine could never have more
//      than 16 reads or 16 writes in flight no matter what the generators'
//      MAX_OUTSTANDING said. The latency curve is read bandwidth against
//      outstanding transactions; a hard 16 puts the knee inside the harness
//      for every AxLEN below 8. Here the generators' own MAX_OUTSTANDING is
//      the only limit, which is the knob the sweep is supposed to turn.
//
//   2. Latency. The master-side and slave-side adapters carry two skid stages
//      each (axi4_slave_rd and axi4_master_rd, AR out and R back), so four
//      round trip on a path whose whole purpose is to measure a ~49-cycle
//      read. Four cycles of instrument is ~8% of the reading, and it is added
//      to pumice and LiteDRAM alike, so it also flatters whichever controller
//      is slower. The routing module between them is combinational and
//      contributed none of it.
//
//   3. The CAM itself, which recovers the originating master from the
//      returning ID -- information that is already sitting in the top bits of
//      that ID, because the bridge put it there. AXI4 requires BID/RID to
//      equal the AWID/ARID that was issued, so the prefix IS the return route
//      and the demux below is combinational with no state at all.
//
//   What the merge still has to do, and does:
//     - N:1 round-robin on AW and AR, grant held across a stalled handshake
//       (char_gen_axi_mux).
//     - Master-unique IDs: {generator index, generator id}, the same
//       {BRIDGE_ID, id} shape the bridges used (BRIDGE-016), so the ID width
//       the controller sees is unchanged at NUM_GEN=2.
//     - W in AW order (char_gen_wr_order_q), which is an AXI4 requirement the
//       moment two masters share one W channel.
//     - B and R steered back by ID prefix.
//
//   What it deliberately does NOT do: address decode, protocol conversion,
//   width conversion, error injection, timeout, or monbus observation. Every
//   one of those is a reason to use the bridge generator instead, and none of
//   them applies to a generator array pointed at a single controller.
//
//   One thing genuinely went away with the bridges: the subtractive slave,
//   which absorbed accesses above 0x07FFFFFF and latched the first offending
//   address. Nothing observed it -- char_engine_block left the bridge's
//   unmapped_irq / unmapped_addr ports unconnected -- so an out-of-range
//   access was silently swallowed rather than reported. Now it reaches the
//   controller instead, which is at least a behaviour something can see. If a
//   real out-of-range trap is ever wanted here, it belongs in the generators'
//   address generation, where the bad address is produced.
//==============================================================================
`timescale 1ns / 1ps
`include "reset_defs.svh"

module char_gen_unit #(
    // ---- AXI4 ----
    parameter int AXI_ADDR_WIDTH   = 32,
    parameter int AXI_DATA_WIDTH   = 64,
    // AXI_ID_WIDTH=8 to match the pattern-gen engines' internal 8-bit LFSR
    // for the ID-picker (axi4_master_wr_pattern_gen slices cfg_axi_id[7:0]).
    parameter int AXI_ID_WIDTH     = 8,
    parameter int AXI_USER_WIDTH   = 8,
    parameter int AXI_STRB_WIDTH   = AXI_DATA_WIDTH / 8,
    parameter int BURST_LEN_MULTIPLE = 1,

    // ---- Generator array ----
    parameter int NUM_GEN          = 2,
    parameter int GEN_MAX_OUTSTANDING = 32,

    // ---- Engine workload ranges ----
    parameter int TXN_COUNT_WIDTH  = 16,
    parameter int INDEX_WIDTH      = 16,
    parameter int STRIDE_WIDTH     = 24,

    // ---- Reader-engine debug FIFO depth (0 = elide) ----
    parameter int RD_DBG_FIFO_DEPTH = 0,

    // ---- Aliases ----
    parameter int IW = AXI_ID_WIDTH,
    parameter int AW = AXI_ADDR_WIDTH,
    parameter int DW = AXI_DATA_WIDTH,
    parameter int UW = AXI_USER_WIDTH,
    parameter int SW = AXI_STRB_WIDTH,
    // Generator-select field carried in the top bits of the outgoing ID. Zero
    // bits when there is only one generator, so a single-generator build
    // presents exactly the generator's own ID and the merge disappears.
    parameter int GSELW = (NUM_GEN > 1) ? $clog2(NUM_GEN) : 0,
    parameter int PIW   = IW + GSELW
) (
    input  logic aclk,
    input  logic aresetn,

    //---- Config (chargen_regs hwif) --------------------------------------
    // The register block stays outside: it is one APB window shared with the
    // roll-up and identity registers, and those are not this module's
    // business. What arrives here is the per-generator workload description.
    input  chargen_regs_pkg::chargen_regs__out_t cfg_i,

    // Launch, one bit per generator. Gathered by the caller from the GO
    // register's singlepulse fields so every generator starts on one host
    // write -- see char_engine_block for why the skew matters.
    input  logic [NUM_GEN-1:0] wr_go_i,
    input  logic [NUM_GEN-1:0] rd_go_i,

    //---- Per-generator status --------------------------------------------
    output logic [NUM_GEN-1:0]        wr_done_o,
    output logic [NUM_GEN-1:0]        wr_crc_valid_o,
    output logic [NUM_GEN-1:0]        wr_bresp_err_o,
    output logic [31:0]               wr_crc_o [NUM_GEN],

    output logic [NUM_GEN-1:0]        rd_done_o,
    output logic [NUM_GEN-1:0]        rd_crc_valid_o,
    output logic [NUM_GEN-1:0]        rd_data_err_o,
    output logic [NUM_GEN-1:0]        rd_rresp_err_o,
    output logic [NUM_GEN-1:0]        rd_stray_err_o,
    output logic [31:0]               rd_crc_o [NUM_GEN],
    output logic [TXN_COUNT_WIDTH-1:0] rd_beats_mism_o [NUM_GEN],
    output logic [TXN_COUNT_WIDTH-1:0] rd_stray_cnt_o  [NUM_GEN],

    //---- Reader debug FIFO drain (generator 0 only) ----------------------
    output logic          rd_dbg_valid,
    input  logic          rd_dbg_ready,
    output logic [DW-1:0] rd_dbg_actual,
    output logic [DW-1:0] rd_dbg_expected,
    output logic          rd_dbg_mismatch,

    //---- The one AXI4 master port ----------------------------------------
    output logic [PIW-1:0] m_axi_awid,
    output logic [AW-1:0]  m_axi_awaddr,
    output logic [7:0]     m_axi_awlen,
    output logic [2:0]     m_axi_awsize,
    output logic [1:0]     m_axi_awburst,
    output logic           m_axi_awlock,
    output logic [3:0]     m_axi_awcache,
    output logic [2:0]     m_axi_awprot,
    output logic [3:0]     m_axi_awqos,
    output logic [3:0]     m_axi_awregion,
    output logic [UW-1:0]  m_axi_awuser,
    output logic           m_axi_awvalid,
    input  logic           m_axi_awready,
    output logic [DW-1:0]  m_axi_wdata,
    output logic [SW-1:0]  m_axi_wstrb,
    output logic           m_axi_wlast,
    output logic [UW-1:0]  m_axi_wuser,
    output logic           m_axi_wvalid,
    input  logic           m_axi_wready,
    input  logic [PIW-1:0] m_axi_bid,
    input  logic [1:0]     m_axi_bresp,
    input  logic [UW-1:0]  m_axi_buser,
    input  logic           m_axi_bvalid,
    output logic           m_axi_bready,
    output logic [PIW-1:0] m_axi_arid,
    output logic [AW-1:0]  m_axi_araddr,
    output logic [7:0]     m_axi_arlen,
    output logic [2:0]     m_axi_arsize,
    output logic [1:0]     m_axi_arburst,
    output logic           m_axi_arlock,
    output logic [3:0]     m_axi_arcache,
    output logic [2:0]     m_axi_arprot,
    output logic [3:0]     m_axi_arqos,
    output logic [3:0]     m_axi_arregion,
    output logic [UW-1:0]  m_axi_aruser,
    output logic           m_axi_arvalid,
    input  logic           m_axi_arready,
    input  logic [PIW-1:0] m_axi_rid,
    input  logic [DW-1:0]  m_axi_rdata,
    input  logic [1:0]     m_axi_rresp,
    input  logic           m_axi_rlast,
    input  logic [UW-1:0]  m_axi_ruser,
    input  logic           m_axi_rvalid,
    output logic           m_axi_rready
);

    // Index width for the mux's own select port. GSELW is zero when NUM_GEN
    // is 1 and a zero-width net is not legal, so the mux keeps its own
    // minimum-one-bit alias and this module ignores it in that case.
    localparam int SELW = (NUM_GEN > 1) ? $clog2(NUM_GEN) : 1;
    localparam bit SEL_EXACT = (NUM_GEN == (1 << SELW));

    // Every AW that can be in flight at once needs a slot in the order queue,
    // or AW stalls behind it and the outstanding count the sweep is trying to
    // reach is unreachable for a second time.
    // Width of the engines' runtime outstanding dial. The CSR field is six
    // bits so a 32-deep build is reachable; the engines clamp anything above
    // their own ceiling, so narrowing here would hide a host mistake instead
    // of letting the RTL saturate it visibly.
    localparam int OSW = $clog2(GEN_MAX_OUTSTANDING + 1);

    localparam int WR_ORDER_DEPTH = 1 << $clog2(NUM_GEN * GEN_MAX_OUTSTANDING);

    // Address-channel payloads, packed for the mux. Order is fixed here and
    // undone in the unpack below; nothing else may assume it.
    localparam int AX_W = IW + AW + 8 + 3 + 2 + 1 + 4 + 3 + 4 + 4 + 1;

    initial begin
        if (NUM_GEN < 1) begin
            $error("char_gen_unit: NUM_GEN (%0d) must be at least 1", NUM_GEN);
        end
    end

    //=========================================================================
    // Per-generator AXI nets
    //=========================================================================
    logic [IW-1:0] gw_awid    [NUM_GEN];
    logic [AW-1:0] gw_awaddr  [NUM_GEN];
    logic [7:0]    gw_awlen   [NUM_GEN];
    logic [2:0]    gw_awsize  [NUM_GEN];
    logic [1:0]    gw_awburst [NUM_GEN];
    logic          gw_awlock  [NUM_GEN];
    logic [3:0]    gw_awcache [NUM_GEN], gw_awqos [NUM_GEN], gw_awregion [NUM_GEN];
    logic [2:0]    gw_awprot  [NUM_GEN];
    logic [UW-1:0] gw_awuser  [NUM_GEN], gw_wuser [NUM_GEN];
    logic          gw_awvalid [NUM_GEN], gw_awready [NUM_GEN];
    logic [DW-1:0] gw_wdata   [NUM_GEN];
    logic [SW-1:0] gw_wstrb   [NUM_GEN];
    logic          gw_wlast   [NUM_GEN], gw_wvalid [NUM_GEN], gw_wready [NUM_GEN];
    logic [IW-1:0] gw_bid     [NUM_GEN];
    logic [1:0]    gw_bresp   [NUM_GEN];
    logic [UW-1:0] gw_buser   [NUM_GEN];
    logic          gw_bvalid  [NUM_GEN], gw_bready [NUM_GEN];

    logic [IW-1:0] gr_arid    [NUM_GEN];
    logic [AW-1:0] gr_araddr  [NUM_GEN];
    logic [7:0]    gr_arlen   [NUM_GEN];
    logic [2:0]    gr_arsize  [NUM_GEN];
    logic [1:0]    gr_arburst [NUM_GEN];
    logic          gr_arlock  [NUM_GEN];
    logic [3:0]    gr_arcache [NUM_GEN], gr_arqos [NUM_GEN], gr_arregion [NUM_GEN];
    logic [2:0]    gr_arprot  [NUM_GEN];
    logic [UW-1:0] gr_aruser  [NUM_GEN], gr_ruser [NUM_GEN];
    logic          gr_arvalid [NUM_GEN], gr_arready [NUM_GEN];
    logic [IW-1:0] gr_rid     [NUM_GEN];
    logic [DW-1:0] gr_rdata   [NUM_GEN];
    logic [1:0]    gr_rresp   [NUM_GEN];
    logic          gr_rlast   [NUM_GEN], gr_rvalid [NUM_GEN], gr_rready [NUM_GEN];

    // Debug-FIFO drain nets; only generator 0's are wired out (see below).
    logic          w_dbg_valid    [NUM_GEN];
    logic          w_dbg_ready    [NUM_GEN];
    logic [DW-1:0] w_dbg_actual   [NUM_GEN];
    logic [DW-1:0] w_dbg_expected [NUM_GEN];
    logic          w_dbg_mismatch [NUM_GEN];

    // Status, gathered per generator and handed up as vectors/arrays.
    logic [NUM_GEN-1:0] w_wr_done, w_wr_crc_valid, w_wr_bresp_err;
    logic [NUM_GEN-1:0] w_rd_done, w_rd_crc_valid, w_rd_data_err;
    logic [NUM_GEN-1:0] w_rd_rresp_err, w_rd_stray_err;
    logic [TXN_COUNT_WIDTH-1:0] w_rd_beats_mism [NUM_GEN];
    logic [TXN_COUNT_WIDTH-1:0] w_rd_stray_cnt  [NUM_GEN];
    logic [31:0]                w_wr_crc        [NUM_GEN];
    logic [31:0]                w_rd_crc        [NUM_GEN];

    assign wr_done_o      = w_wr_done;
    assign wr_crc_valid_o = w_wr_crc_valid;
    assign wr_bresp_err_o = w_wr_bresp_err;
    assign rd_done_o      = w_rd_done;
    assign rd_crc_valid_o = w_rd_crc_valid;
    assign rd_data_err_o  = w_rd_data_err;
    assign rd_rresp_err_o = w_rd_rresp_err;
    assign rd_stray_err_o = w_rd_stray_err;

    generate
    for (genvar g = 0; g < NUM_GEN; g++) begin : g_status
        assign wr_crc_o[g]       = w_wr_crc[g];
        assign rd_crc_o[g]       = w_rd_crc[g];
        assign rd_beats_mism_o[g] = w_rd_beats_mism[g];
        assign rd_stray_cnt_o[g]  = w_rd_stray_cnt[g];
    end
    endgenerate

    //=========================================================================
    // Runtime outstanding dial: CSR field -> per-engine limit
    //=========================================================================
    // The CSR field is a fixed six bits; the engines' port is sized from
    // GEN_MAX_OUTSTANDING. Saturating the comparison in full width before
    // narrowing is the whole point of this block: a plain cast would alias a
    // host value of 33 down to 1 on an 8-deep build, which reads as a
    // legitimate measurement rather than as the mistake it is. Zero passes
    // through untouched -- the engines read it as "as built".
    logic [OSW-1:0] w_wr_os_limit [NUM_GEN];
    logic [OSW-1:0] w_rd_os_limit [NUM_GEN];

    generate
    for (genvar g = 0; g < NUM_GEN; g++) begin : g_os_limit
        assign w_wr_os_limit[g] =
            (32'(cfg_i.WR_GEN[g].AXI_ATTR.max_outstanding.value) > 32'(GEN_MAX_OUTSTANDING))
                ? OSW'(GEN_MAX_OUTSTANDING)
                : OSW'(cfg_i.WR_GEN[g].AXI_ATTR.max_outstanding.value);
        assign w_rd_os_limit[g] =
            (32'(cfg_i.RD_GEN[g].AXI_ATTR.max_outstanding.value) > 32'(GEN_MAX_OUTSTANDING))
                ? OSW'(GEN_MAX_OUTSTANDING)
                : OSW'(cfg_i.RD_GEN[g].AXI_ATTR.max_outstanding.value);
    end
    endgenerate

    //=========================================================================
    // Write generator blocks
    //=========================================================================
    generate
    for (genvar g = 0; g < NUM_GEN; g++) begin : g_wr_engine
        axi4_master_wr_pattern_gen #(
            .AXI_ID_WIDTH       (AXI_ID_WIDTH),
            .AXI_ADDR_WIDTH     (AXI_ADDR_WIDTH),
            .AXI_DATA_WIDTH     (AXI_DATA_WIDTH),
            .AXI_USER_WIDTH     (AXI_USER_WIDTH),
            .AXI_WSTRB_WIDTH    (AXI_STRB_WIDTH),
            .TXN_COUNT_WIDTH    (TXN_COUNT_WIDTH),
            .INDEX_WIDTH        (INDEX_WIDTH),
            .STRIDE_WIDTH       (STRIDE_WIDTH),
            .BURST_LEN_MULTIPLE (BURST_LEN_MULTIPLE),
            .MAX_OUTSTANDING    (GEN_MAX_OUTSTANDING)
        ) u_wr_engine (
            .aclk                 (aclk),
            .aresetn              (aresetn),
            .cfg_start_addr       (AW'(cfg_i.WR_GEN[g].START_ADDR.addr.value)),
            .cfg_addr_stride_0    (signed'(cfg_i.WR_GEN[g].STRIDE_0.stride.value)),
            .cfg_addr_stride_1    (signed'(cfg_i.WR_GEN[g].STRIDE_1.stride.value)),
            .cfg_addr_wrap_mask_0 (AW'(cfg_i.WR_GEN[g].WRAP_MASK_0.mask.value)),
            .cfg_addr_wrap_mask_1 (AW'(cfg_i.WR_GEN[g].WRAP_MASK_1.mask.value)),
            .cfg_burst_len        (cfg_i.WR_GEN[g].BLEN_TXN.burst_len.value),
            .cfg_txn_count        (cfg_i.WR_GEN[g].BLEN_TXN.txn_count.value),
            .cfg_axi_id           (cfg_i.WR_GEN[g].AXI_ATTR.axi_id.value),
            .cfg_id_mode          (cfg_i.WR_GEN[g].AXI_ATTR.id_mode.value),
            .cfg_axi_size         (cfg_i.WR_GEN[g].AXI_ATTR.axi_size.value),
            .cfg_axi_burst        (cfg_i.WR_GEN[g].AXI_ATTR.axi_burst.value),
            .cfg_lfsr_seed        (cfg_i.WR_GEN[g].LFSR_SEED.seed.value),
            .cfg_data_mode        (cfg_i.WR_GEN[g].AXI_ATTR.data_mode.value),
            .cfg_hash_seed0       (cfg_i.WR_GEN[g].HASH_SEED0.seed.value),
            .cfg_hash_seed1       (cfg_i.WR_GEN[g].HASH_SEED1.seed.value),
            .cfg_hash_seed2       (cfg_i.WR_GEN[g].HASH_SEED2.seed.value),
            .cfg_wr_gap           (cfg_i.WR_GEN[g].BLEN_TXN.gap.value),
            .cfg_max_outstanding  (w_wr_os_limit[g]),
            .cfg_start            (wr_go_i[g]),
            .cfg_done             (w_wr_done[g]),
            .o_expected_crc       (w_wr_crc[g]),
            .o_expected_crc_valid (w_wr_crc_valid[g]),
            .o_bresp_error        (w_wr_bresp_err[g]),
            .m_axi_awid           (gw_awid[g]),
            .m_axi_awaddr         (gw_awaddr[g]),
            .m_axi_awlen          (gw_awlen[g]),
            .m_axi_awsize         (gw_awsize[g]),
            .m_axi_awburst        (gw_awburst[g]),
            .m_axi_awlock         (gw_awlock[g]),
            .m_axi_awcache        (gw_awcache[g]),
            .m_axi_awprot         (gw_awprot[g]),
            .m_axi_awqos          (gw_awqos[g]),
            .m_axi_awregion       (gw_awregion[g]),
            .m_axi_awuser         (gw_awuser[g]),
            .m_axi_awvalid        (gw_awvalid[g]),
            .m_axi_awready        (gw_awready[g]),
            .m_axi_wdata          (gw_wdata[g]),
            .m_axi_wstrb          (gw_wstrb[g]),
            .m_axi_wlast          (gw_wlast[g]),
            .m_axi_wuser          (gw_wuser[g]),
            .m_axi_wvalid         (gw_wvalid[g]),
            .m_axi_wready         (gw_wready[g]),
            .m_axi_bid            (gw_bid[g]),
            .m_axi_bresp          (gw_bresp[g]),
            .m_axi_buser          (gw_buser[g]),
            .m_axi_bvalid         (gw_bvalid[g]),
            .m_axi_bready         (gw_bready[g])
        );
    end
    endgenerate

    //=========================================================================
    // Read generator blocks
    //=========================================================================
    generate
    for (genvar g = 0; g < NUM_GEN; g++) begin : g_rd_engine
        axi4_master_rd_crc_check #(
            .AXI_ID_WIDTH       (AXI_ID_WIDTH),
            .AXI_ADDR_WIDTH     (AXI_ADDR_WIDTH),
            .AXI_DATA_WIDTH     (AXI_DATA_WIDTH),
            .AXI_USER_WIDTH     (AXI_USER_WIDTH),
            .TXN_COUNT_WIDTH    (TXN_COUNT_WIDTH),
            .INDEX_WIDTH        (INDEX_WIDTH),
            .STRIDE_WIDTH       (STRIDE_WIDTH),
            .BURST_LEN_MULTIPLE (BURST_LEN_MULTIPLE),
            .MAX_OUTSTANDING    (GEN_MAX_OUTSTANDING),
            // Only generator 0 carries the debug FIFO; see the note above.
            .DBG_FIFO_DEPTH     ((g == 0) ? RD_DBG_FIFO_DEPTH : 0)
        ) u_rd_engine (
            .aclk                 (aclk),
            .aresetn              (aresetn),
            .cfg_start_addr       (AW'(cfg_i.RD_GEN[g].START_ADDR.addr.value)),
            .cfg_addr_stride_0    (signed'(cfg_i.RD_GEN[g].STRIDE_0.stride.value)),
            .cfg_addr_stride_1    (signed'(cfg_i.RD_GEN[g].STRIDE_1.stride.value)),
            .cfg_addr_wrap_mask_0 (AW'(cfg_i.RD_GEN[g].WRAP_MASK_0.mask.value)),
            .cfg_addr_wrap_mask_1 (AW'(cfg_i.RD_GEN[g].WRAP_MASK_1.mask.value)),
            .cfg_burst_len        (cfg_i.RD_GEN[g].BLEN_TXN.burst_len.value),
            .cfg_txn_count        (cfg_i.RD_GEN[g].BLEN_TXN.txn_count.value),
            .cfg_axi_id           (cfg_i.RD_GEN[g].AXI_ATTR.axi_id.value),
            .cfg_id_mode          (cfg_i.RD_GEN[g].AXI_ATTR.id_mode.value),
            .cfg_axi_size         (cfg_i.RD_GEN[g].AXI_ATTR.axi_size.value),
            .cfg_axi_burst        (cfg_i.RD_GEN[g].AXI_ATTR.axi_burst.value),
            .cfg_lfsr_seed        (cfg_i.RD_GEN[g].LFSR_SEED.seed.value),
            .cfg_data_mode        (cfg_i.RD_GEN[g].AXI_ATTR.data_mode.value),
            .cfg_hash_seed0       (cfg_i.RD_GEN[g].HASH_SEED0.seed.value),
            .cfg_hash_seed1       (cfg_i.RD_GEN[g].HASH_SEED1.seed.value),
            .cfg_hash_seed2       (cfg_i.RD_GEN[g].HASH_SEED2.seed.value),
            .cfg_rd_gap           (cfg_i.RD_GEN[g].BLEN_TXN.gap.value),
            .cfg_max_outstanding  (w_rd_os_limit[g]),
            .cfg_start            (rd_go_i[g]),
            .cfg_done             (w_rd_done[g]),
            .o_actual_crc         (w_rd_crc[g]),
            .o_actual_crc_valid   (w_rd_crc_valid[g]),
            .o_data_error         (w_rd_data_err[g]),
            .o_rresp_error        (w_rd_rresp_err[g]),
            .o_stray_beat_error   (w_rd_stray_err[g]),
            .o_stray_beats        (w_rd_stray_cnt[g]),
            .o_beats_mismatched   (w_rd_beats_mism[g]),
            .m_axi_arid           (gr_arid[g]),
            .m_axi_araddr         (gr_araddr[g]),
            .m_axi_arlen          (gr_arlen[g]),
            .m_axi_arsize         (gr_arsize[g]),
            .m_axi_arburst        (gr_arburst[g]),
            .m_axi_arlock         (gr_arlock[g]),
            .m_axi_arcache        (gr_arcache[g]),
            .m_axi_arprot         (gr_arprot[g]),
            .m_axi_arqos          (gr_arqos[g]),
            .m_axi_arregion       (gr_arregion[g]),
            .m_axi_aruser         (gr_aruser[g]),
            .m_axi_arvalid        (gr_arvalid[g]),
            .m_axi_arready        (gr_arready[g]),
            .m_axi_rid            (gr_rid[g]),
            .m_axi_rdata          (gr_rdata[g]),
            .m_axi_rresp          (gr_rresp[g]),
            .m_axi_rlast          (gr_rlast[g]),
            .m_axi_ruser          (gr_ruser[g]),
            .m_axi_rvalid         (gr_rvalid[g]),
            .m_axi_rready         (gr_rready[g]),
            .dbg_valid            (w_dbg_valid[g]),
            .dbg_ready            (w_dbg_ready[g]),
            .dbg_actual           (w_dbg_actual[g]),
            .dbg_expected         (w_dbg_expected[g]),
            .dbg_mismatch         (w_dbg_mismatch[g])
        );
    end
    endgenerate

    //=========================================================================
    // Reader debug FIFO drain -- generator 0 only
    //=========================================================================
    // The FIFO is a bench aid for eyeballing a mismatching beat, not a checker
    // -- every reader's mismatch is already counted in its own BEATS_MISM
    // register, which is what the host reads. The others are held permanently
    // drained: the engine does not stall on a full debug FIFO, but a
    // never-emptied buffer is a confusing thing to meet in a waveform and
    // draining it costs one constant.
    assign rd_dbg_valid    = w_dbg_valid[0];
    assign rd_dbg_actual   = w_dbg_actual[0];
    assign rd_dbg_expected = w_dbg_expected[0];
    assign rd_dbg_mismatch = w_dbg_mismatch[0];
    assign w_dbg_ready[0]  = rd_dbg_ready;

    generate
    for (genvar g = 1; g < NUM_GEN; g++) begin : g_dbg_drain
        assign w_dbg_ready[g] = 1'b1;
    end
    endgenerate

    //=========================================================================
    // Write merge: N generators -> one AW/W/B channel group
    //=========================================================================
    // The `user` bits narrow to one on the way out. pumice's s_axi_awuser and
    // s_axi_wuser are single bits, so anything wider dies at the controller
    // regardless; taking bit 0 explicitly makes that visible at the boundary
    // instead of leaving a silent width truncation for lint to swallow.
    logic [NUM_GEN-1:0] w_aw_valid, w_aw_ready;
    logic [AX_W-1:0]    w_aw_payload [NUM_GEN];
    logic [AX_W-1:0]    w_aw_merged;
    logic [SELW-1:0]    w_aw_sel;
    logic               w_aw_mvalid, w_aw_mready;

    generate
    for (genvar g = 0; g < NUM_GEN; g++) begin : g_aw_pack
        assign w_aw_valid[g]   = gw_awvalid[g];
        assign gw_awready[g]   = w_aw_ready[g];
        assign w_aw_payload[g] = {gw_awid[g], gw_awaddr[g], gw_awlen[g], gw_awsize[g],
                                  gw_awburst[g], gw_awlock[g], gw_awcache[g], gw_awprot[g],
                                  gw_awqos[g], gw_awregion[g], gw_awuser[g][0]};
    end
    endgenerate

    logic w_wr_q_full;

    char_gen_axi_mux #(
        .N             (NUM_GEN),
        .PAYLOAD_WIDTH (AX_W)
    ) u_aw_mux (
        .clk       (aclk),
        .rst_n     (aresetn),
        .s_valid   (w_aw_valid),
        .s_ready   (w_aw_ready),
        .s_payload (w_aw_payload),
        .m_valid   (w_aw_mvalid),
        .m_ready   (w_aw_mready),
        .m_payload (w_aw_merged),
        .m_sel     (w_aw_sel),
        // Refuse a new address when the W-order queue cannot record it. The
        // queue is sized to every AW that can be outstanding, so this is a
        // guard against a parameter mistake rather than a routine stall.
        .block     (w_wr_q_full)
    );

    logic [IW-1:0] w_m_awid_raw;
    logic          w_m_awuser_raw;

    assign {w_m_awid_raw, m_axi_awaddr, m_axi_awlen, m_axi_awsize, m_axi_awburst,
            m_axi_awlock, m_axi_awcache, m_axi_awprot, m_axi_awqos, m_axi_awregion,
            w_m_awuser_raw} = w_aw_merged;

    assign m_axi_awuser  = UW'(w_m_awuser_raw);
    assign m_axi_awvalid = w_aw_mvalid;
    assign w_aw_mready   = m_axi_awready;

    //---- W ordering ------------------------------------------------------
    logic            w_wr_head_valid;
    logic [SELW-1:0] w_wr_head_sel;
    logic            w_wlast_hs;

    assign w_wlast_hs = m_axi_wvalid && m_axi_wready && m_axi_wlast;

    char_gen_wr_order_q #(
        .DEPTH (WR_ORDER_DEPTH),
        .SELW  (SELW)
    ) u_wr_order_q (
        .clk        (aclk),
        .rst_n      (aresetn),
        .push       (m_axi_awvalid && m_axi_awready),
        .push_sel   (w_aw_sel),
        .full       (w_wr_q_full),
        .head_valid (w_wr_head_valid),
        .head_sel   (w_wr_head_sel),
        .pop        (w_wlast_hs)
    );

    // W follows the head of the order queue and nobody else. A generator whose
    // AW has not been granted yet simply waits with WVALID up -- legal, and the
    // only thing that keeps the merged W stream in AW order.
    assign m_axi_wdata  = gw_wdata [w_wr_head_sel];
    assign m_axi_wstrb  = gw_wstrb [w_wr_head_sel];
    assign m_axi_wlast  = gw_wlast [w_wr_head_sel];
    assign m_axi_wuser  = UW'(gw_wuser[w_wr_head_sel][0]);
    assign m_axi_wvalid = w_wr_head_valid && gw_wvalid[w_wr_head_sel];

    generate
    for (genvar g = 0; g < NUM_GEN; g++) begin : g_w_ready
        assign gw_wready[g] = w_wr_head_valid && (w_wr_head_sel == SELW'(g)) && m_axi_wready;
    end
    endgenerate

    //---- B demux ---------------------------------------------------------
    // AXI4 requires BID to equal the AWID that was issued, and the top GSELW
    // bits of that AWID are the generator index this module put there. So the
    // return route is already in the response and no tracking structure is
    // needed to recover it.
    logic [SELW-1:0] w_b_sel;
    logic            w_b_inrange;

    generate
    for (genvar g = 0; g < NUM_GEN; g++) begin : g_b_demux
        assign gw_bid[g]    = m_axi_bid[IW-1:0];
        assign gw_bresp[g]  = m_axi_bresp;
        assign gw_buser[g]  = m_axi_buser;
        assign gw_bvalid[g] = m_axi_bvalid && w_b_inrange && (w_b_sel == SELW'(g));
    end
    endgenerate

    //---- R demux ---------------------------------------------------------
    logic [SELW-1:0] w_r_sel;
    logic            w_r_inrange;

    generate
    for (genvar g = 0; g < NUM_GEN; g++) begin : g_r_demux
        assign gr_rid[g]    = m_axi_rid[IW-1:0];
        assign gr_rdata[g]  = m_axi_rdata;
        assign gr_rresp[g]  = m_axi_rresp;
        assign gr_rlast[g]  = m_axi_rlast;
        assign gr_ruser[g]  = m_axi_ruser;
        assign gr_rvalid[g] = m_axi_rvalid && w_r_inrange && (w_r_sel == SELW'(g));
    end
    endgenerate

    generate
    if (NUM_GEN > 1) begin : g_sel_decode
        assign w_b_sel     = SELW'(m_axi_bid[PIW-1 -: GSELW]);
        assign w_r_sel     = SELW'(m_axi_rid[PIW-1 -: GSELW]);
        // NUM_GEN need not be a power of two, so a response can name a
        // generator that does not exist. That is a controller bug or a
        // corrupted ID, and the generator it was meant for will report as
        // never-done -- but the channel must not wedge while that is
        // diagnosed, so an out-of-range response is accepted and dropped.
        // When NUM_GEN is an exact power of two every encoding names a
        // real generator, and the literal NUM_GEN would wrap to zero in SELW
        // bits -- making the test constant-false and silently dropping every
        // response. Settle it at elaboration rather than write a comparison
        // that is correct for 3 generators and a deadlock for 2.
        assign w_b_inrange = SEL_EXACT ? 1'b1 : (w_b_sel < SELW'(NUM_GEN));
        assign w_r_inrange = SEL_EXACT ? 1'b1 : (w_r_sel < SELW'(NUM_GEN));
        assign m_axi_bready = w_b_inrange ? gw_bready[w_b_sel] : 1'b1;
        assign m_axi_rready = w_r_inrange ? gr_rready[w_r_sel] : 1'b1;
    end else begin : g_sel_single
        assign w_b_sel      = '0;
        assign w_r_sel      = '0;
        assign w_b_inrange  = 1'b1;
        assign w_r_inrange  = 1'b1;
        assign m_axi_bready = gw_bready[0];
        assign m_axi_rready = gr_rready[0];
    end
    endgenerate

    //=========================================================================
    // Read merge: N generators -> one AR/R channel group
    //=========================================================================
    // No W-equivalent here. Write data has to be ordered because the W channel
    // carries no ID and the slave can only match it to AW by arrival order;
    // read data carries RID on every beat, so the demux above routes beat by
    // beat and needs no ordering state. That also means it stays correct if a
    // controller ever interleaves read bursts across generators, which AXI4
    // forbids but which costs nothing to tolerate here.
    logic [NUM_GEN-1:0] w_ar_valid, w_ar_ready;
    logic [AX_W-1:0]    w_ar_payload [NUM_GEN];
    logic [AX_W-1:0]    w_ar_merged;
    logic [SELW-1:0]    w_ar_sel;
    logic               w_ar_mvalid, w_ar_mready;

    generate
    for (genvar g = 0; g < NUM_GEN; g++) begin : g_ar_pack
        assign w_ar_valid[g]   = gr_arvalid[g];
        assign gr_arready[g]   = w_ar_ready[g];
        assign w_ar_payload[g] = {gr_arid[g], gr_araddr[g], gr_arlen[g], gr_arsize[g],
                                  gr_arburst[g], gr_arlock[g], gr_arcache[g], gr_arprot[g],
                                  gr_arqos[g], gr_arregion[g], gr_aruser[g][0]};
    end
    endgenerate

    char_gen_axi_mux #(
        .N             (NUM_GEN),
        .PAYLOAD_WIDTH (AX_W)
    ) u_ar_mux (
        .clk       (aclk),
        .rst_n     (aresetn),
        .s_valid   (w_ar_valid),
        .s_ready   (w_ar_ready),
        .s_payload (w_ar_payload),
        .m_valid   (w_ar_mvalid),
        .m_ready   (w_ar_mready),
        .m_payload (w_ar_merged),
        .m_sel     (w_ar_sel),
        .block     (1'b0)
    );

    logic [IW-1:0] w_m_arid_raw;
    logic          w_m_aruser_raw;

    assign {w_m_arid_raw, m_axi_araddr, m_axi_arlen, m_axi_arsize, m_axi_arburst,
            m_axi_arlock, m_axi_arcache, m_axi_arprot, m_axi_arqos, m_axi_arregion,
            w_m_aruser_raw} = w_ar_merged;

    assign m_axi_aruser  = UW'(w_m_aruser_raw);
    assign m_axi_arvalid = w_ar_mvalid;
    assign w_ar_mready   = m_axi_arready;

    //=========================================================================
    // Master-unique IDs
    //=========================================================================
    // {generator index, generator id} -- the same shape the generated bridges
    // produced ({BRIDGE_ID, id}, BRIDGE-016), so the ID width the controller
    // sees is unchanged and no downstream parameter moves. Two generators with
    // the same cfg_axi_id stay distinguishable, which is what lets the demuxes
    // above be stateless.
    generate
    if (NUM_GEN > 1) begin : g_id_prefix
        assign m_axi_awid = {GSELW'(w_aw_sel), w_m_awid_raw};
        assign m_axi_arid = {GSELW'(w_ar_sel), w_m_arid_raw};
    end else begin : g_id_direct
        assign m_axi_awid = w_m_awid_raw;
        assign m_axi_arid = w_m_arid_raw;
    end
    endgenerate

endmodule : char_gen_unit
