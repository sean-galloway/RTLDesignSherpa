// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: 2026 sean galloway
//
// RTL Design Sherpa - Industry-Standard RTL Design and Verification
// https://github.com/sean-galloway/RTLDesignSherpa
//
// Module: amber_cycle_injector
// Purpose: Per-core stimulus engine for the cache-ip pair-rig Genesys2 harnesses
//   (amber and jet share it).  AXIL4-Lite CSR slave (32-word decode window)
//   drives a deterministic cpu_req GAXI master and measures what comes back.
//
//   Pipelined (cache-ip common-ip TASK-002, 2026-11-11).  The engine keeps up
//   to CTRL.outstanding requests in flight (1..MAX_OUTSTANDING; 0 reads as 1,
//   so the original blocking behaviour is CTRL.outstanding = 0/1):
//     - the house dma_address_gen runs full: one address request per cycle
//       while credit allows, the LFSR value riding through as the pass-through
//       tag so address, we, byte-enable and write data of a transaction all
//       derive from the same LFSR step, exactly as in the blocking version --
//       the issued sequence (and so both CRCs) is independent of the depth;
//     - issue is credit-gated at the cpu_req port: cpu_req_wr_valid is held
//       while r_inflight < credit, and r_inflight only falls on a response,
//       so a raised valid stays raised until accepted;
//     - responses are taken whenever offered (both caches return CPU responses
//       in accept order: amber is blocking, jet's jet_rsp_seq is its ordering
//       point), and per-request latency is the free-running cycle counter at
//       the response minus the accept timestamp popped from a ring in order.
//   Latency = cycles from request accept to response handshake, so a
//   next-cycle response measures 1 (unchanged convention).  Per run the block
//   records latency min/max/sum, an 8-bucket log2 histogram, run cycles, and
//   now the achieved parallelism: OUTST_MAX, OUTST_SUM (sum of in-flight count
//   over run cycles; / RUN_CYCLES = mean MLP), STALL_CYCLES (cycles the cache
//   held cpu_req_wr_ready low against a valid request) and CREDIT_STALL
//   (cycles an address was ready but the credit held it back).
//
//   Family-aligned with rtl/amba/shared/axi4_master_wr_injector:
//     - Addresses come from the house dma_address_gen using base + strided index
//       with a wrap mask, reproducing the original "base | (lfsr & mask)" pattern
//       when the base is aligned to (mask + 1).
//     - Write data and the read/write mix come from the house
//       shifter_lfsr_fibonacci (loadable seed).
//     - Response-data and issued-write-data integrity are accumulated with the
//       house dataint_crc (CRC-32, POLY=0x04C11DB7, REFIN=1, REFOUT=1,
//       POLY_INIT='1, XOROUT='1).
//
//   Divergence from the house injector (documented):
//     - This block drives a cpu_req GAXI slave, not a full AXI4 memory
//       controller: no AW/W decoupling, no address-hash data mode.
//     - The address generator is used with stride_0 = 1 and index_0 = lfsr_out,
//       so the resulting address is base + (lfsr & mask).  Software must keep
//       ADDR_BASE aligned to (ADDR_MASK + 1) to recover the original OR semantics.
//     - The dma_address_gen descriptor ports are re-sampled from CSRs on every
//       run start, preserving runtime AXIL programmability even though the house
//       module normally sees a static descriptor for a whole transfer.
//     - CTRL must not be rewritten while STATUS.busy is set: lowering the
//       credit mid-run could drop a raised cpu_req_wr_valid.

`timescale 1ns / 1ps

`include "reset_defs.svh"

module amber_cycle_injector
    import l1_pkg::*;
#(
    parameter int ADDR_WIDTH = AMBER_ADDR_WIDTH,
    parameter int BUS_WIDTH  = AMBER_BUS_WIDTH,
    parameter bit USE_MONITOR = 1'b1,
    localparam int STRB_W    = BUS_WIDTH / 8,
    localparam int CPU_REQ_W = ADDR_WIDTH + 1 + STRB_W + BUS_WIDTH,
    localparam int CPU_RSP_W = BUS_WIDTH,

    // Address generation.  INDEX_WIDTH=32 keeps the whole LFSR value as the
    // index so the address distribution matches the original 32-bit LFSR.
    parameter int INDEX_WIDTH  = 32,
    parameter int STRIDE_WIDTH = 32,

    // Depth of the accept-timestamp ring = the most requests ever in flight.
    // CTRL.outstanding is clamped to it.  Power of two.
    parameter int MAX_OUTSTANDING = 16
) (
    input  logic                    aclk,
    input  logic                    aresetn,

    // ------------------------------------------------------------------
    // AXIL slave (host config / status)
    // ------------------------------------------------------------------
    input  logic [31:0]             s_axil_awaddr,
    input  logic [2:0]              s_axil_awprot,
    input  logic                    s_axil_awvalid,
    output logic                    s_axil_awready,
    input  logic [31:0]             s_axil_wdata,
    input  logic [3:0]              s_axil_wstrb,
    input  logic                    s_axil_wvalid,
    output logic                    s_axil_wready,
    output logic [1:0]              s_axil_bresp,
    output logic                    s_axil_bvalid,
    input  logic                    s_axil_bready,

    input  logic [31:0]             s_axil_araddr,
    input  logic [2:0]              s_axil_arprot,
    input  logic                    s_axil_arvalid,
    output logic                    s_axil_arready,
    output logic [31:0]             s_axil_rdata,
    output logic [1:0]              s_axil_rresp,
    output logic                    s_axil_rvalid,
    input  logic                    s_axil_rready,

    // ------------------------------------------------------------------
    // cpu_req GAXI master (packed {addr, we, be, wdata})
    // ------------------------------------------------------------------
    output logic                    cpu_req_wr_valid,
    input  logic                    cpu_req_wr_ready,
    output logic [CPU_REQ_W-1:0]    cpu_req_wr_data,
    input  logic                    cpu_rsp_rd_valid,
    output logic                    cpu_rsp_rd_ready,
    input  logic [CPU_RSP_W-1:0]    cpu_rsp_rd_data,

    // ------------------------------------------------------------------
    // Status outputs to the harness aggregate
    // ------------------------------------------------------------------
    output logic                    o_done,
    output logic                    o_busy,
    output logic                    o_err_flag
);

    // ------------------------------------------------------------------
    // CSR map (32-bit word offsets)
    //   Decode is addr[6:2] (32-word window). Words 0x00-0x3C are the
    //   original 16-word regfile; the latency instrumentation fills the
    //   three historic holes and lives above 0x40; the parallelism counters
    //   (TASK-002) take words 26..30. All instrument registers are
    //   read-only and cleared on run start.
    // ------------------------------------------------------------------
    localparam logic [4:0] CSR_CTRL          = 5'h00;
    localparam logic [4:0] CSR_SEED          = 5'h01;
    localparam logic [4:0] CSR_ADDR_BASE     = 5'h02;
    localparam logic [4:0] CSR_ADDR_MASK     = 5'h03;
    localparam logic [4:0] CSR_TRANS_COUNT   = 5'h04;
    localparam logic [4:0] CSR_STATUS        = 5'h05;
    localparam logic [4:0] CSR_ACC_COUNT     = 5'h06;
    localparam logic [4:0] CSR_RSP_COUNT     = 5'h07;
    localparam logic [4:0] CSR_ERR_FLAG      = 5'h08;
    localparam logic [4:0] CSR_LAT_MIN       = 5'h09;   // 0x24
    localparam logic [4:0] CSR_LAT_MAX       = 5'h0A;   // 0x28
    localparam logic [4:0] CSR_RUN_CYCLES    = 5'h0B;   // 0x2C
    localparam logic [4:0] CSR_RSP_CRC_LO    = 5'h0C;   // word 12
    localparam logic [4:0] CSR_RSP_CRC_HI    = 5'h0D;   // word 13
    localparam logic [4:0] CSR_WDATA_CRC_LO  = 5'h0E;   // word 14
    localparam logic [4:0] CSR_WDATA_CRC_HI  = 5'h0F;   // word 15
    localparam logic [4:0] CSR_LAT_SUM_LO    = 5'h10;   // 0x40
    localparam logic [4:0] CSR_LAT_SUM_HI    = 5'h11;   // 0x44
    localparam logic [4:0] CSR_LAT_HIST0     = 5'h12;   // 0x48 .. 0x64 (8 buckets)
    localparam logic [4:0] CSR_OUTST_MAX     = 5'h1A;   // 0x68
    localparam logic [4:0] CSR_OUTST_SUM_LO  = 5'h1B;   // 0x6C
    localparam logic [4:0] CSR_OUTST_SUM_HI  = 5'h1C;   // 0x70
    localparam logic [4:0] CSR_STALL_CYCLES  = 5'h1D;   // 0x74
    localparam logic [4:0] CSR_CREDIT_STALL  = 5'h1E;   // 0x78

    // Histogram bucket edges are powers of two: bucket b covers latencies
    // [2^b, 2^(b+1)-1] and bucket 7 catches >= 128. Bucket 0 is latency 1.
    localparam int LAT_HIST_BUCKETS = 8;

    localparam logic [31:0] CSR_CTRL_RUN_MASK      = 32'h0000_0001;
    localparam int          CSR_CTRL_WE_MIX_SHIFT  = 8;
    localparam int          CSR_CTRL_OUTST_SHIFT   = 16;

    localparam int OUTST_W = $clog2(MAX_OUTSTANDING + 1);
    localparam int TS_AW   = (MAX_OUTSTANDING > 1) ? $clog2(MAX_OUTSTANDING) : 1;

    // Cycles the address generator is drained after an aborted run: its
    // 2-stage pipe may hold results nobody consumed.
    localparam int FLUSH_CYCLES = 4;
    localparam int FLUSH_W      = $clog2(FLUSH_CYCLES + 1);

    // ------------------------------------------------------------------
    // CSR registers
    // ------------------------------------------------------------------
    logic [31:0] r_ctrl;
    logic [31:0] r_seed;
    logic [31:0] r_addr_base;
    logic [31:0] r_addr_mask;
    logic [31:0] r_trans_count;
    logic [31:0] r_acc_count;
    logic [31:0] r_rsp_count;
    logic        r_done;
    logic        r_run;
    logic        r_err_flag;
    logic [BUS_WIDTH-1:0] r_rsp_crc;
    logic [BUS_WIDTH-1:0] r_wdata_crc;

    // Latency / parallelism instrumentation (read-only, cleared on run start)
    logic [31:0] r_lat_min;
    logic [31:0] r_lat_max;
    logic [63:0] r_lat_sum;
    logic [31:0] r_run_cycles;
    logic [31:0] r_lat_hist [LAT_HIST_BUCKETS];
    logic [31:0] r_outst_max;
    logic [63:0] r_outst_sum;
    logic [31:0] r_stall_cycles;
    logic [31:0] r_credit_stall;

    assign o_done     = r_done;
    assign o_busy     = r_run;
    assign o_err_flag = r_err_flag;

    // ------------------------------------------------------------------
    // House Fibonacci LFSR for data / we_mix / address index
    //   Width 32, taps {23,3,2,1} (maximal, verified table entry).
    //   seed_load re-seeds from the CSR so the run is deterministic.
    // ------------------------------------------------------------------
    localparam logic [47:0] LFSR_TAPS = {12'd23, 12'd3, 12'd2, 12'd1};
    localparam logic [31:0] LFSR_SEED_DEFAULT = 32'hDEAD_BEEF;

    logic [31:0] w_lfsr_out;
    logic        w_lfsr_load;
    logic        w_lfsr_advance;
    logic [31:0] w_lfsr_seed;

    // A zero seed would lock the Fibonacci LFSR.  Mirror the house injector:
    // substitute the default seed when the CSR seed is zero.
    assign w_lfsr_seed = (r_seed == '0) ? LFSR_SEED_DEFAULT : r_seed;

    shifter_lfsr_fibonacci #(
        .WIDTH          (32),
        .TAP_INDEX_WIDTH(12),
        .TAP_COUNT      (4)
    ) u_lfsr (
        .clk      (aclk),
        .rst_n    (aresetn),
        .enable   (w_lfsr_advance || w_lfsr_load),
        .seed_load(w_lfsr_load),
        .seed_data(w_lfsr_seed),
        .taps     (LFSR_TAPS),
        .lfsr_out (w_lfsr_out),
        .lfsr_done()
    );

    // ------------------------------------------------------------------
    // House address generator, run as a pipeline
    //   base  = r_addr_base
    //   stride = +1, wrap = r_addr_mask
    //   index = current LFSR output
    //   tag   = the same LFSR output, so the result carries everything the
    //           transaction needs (address, and the LFSR step for we/be/wdata)
    //   => addr = base + (lfsr & mask)
    //   Software must align base to (mask + 1) to match the old OR semantics.
    // ------------------------------------------------------------------
    logic                       w_addr_req_valid;
    logic                       w_addr_req_ready;
    logic [INDEX_WIDTH-1:0]     w_addr_index;
    logic                       w_addr_result_valid;
    logic                       w_addr_result_ready;
    logic [ADDR_WIDTH-1:0]      w_addr_result;
    logic [31:0]                w_addr_result_lfsr;

    assign w_addr_index = INDEX_WIDTH'(w_lfsr_out);

    dma_address_gen #(
        .ADDR_WIDTH  (ADDR_WIDTH),
        .INDEX_WIDTH (INDEX_WIDTH),
        .STRIDE_WIDTH(STRIDE_WIDTH),
        .TAG_WIDTH   (32)
    ) u_addr_gen (
        .i_clk             (aclk),
        .i_rst_n           (aresetn),

        .i_cfg_base_addr   (r_addr_base),
        .i_cfg_stride_0    (STRIDE_WIDTH'($signed(32'sd1))),
        .i_cfg_stride_1    ('0),
        .i_cfg_wrap_mask_0 (ADDR_WIDTH'(r_addr_mask)),
        .i_cfg_wrap_mask_1 ('0),

        .i_req_valid       (w_addr_req_valid),
        .o_req_ready       (w_addr_req_ready),
        .i_req_index_0     (w_addr_index),
        .i_req_index_1     ('0),
        .i_req_tag         (w_lfsr_out),

        .o_result_valid    (w_addr_result_valid),
        .i_result_ready    (w_addr_result_ready),
        .o_result_addr     (w_addr_result),
        .o_result_tag      (w_addr_result_lfsr)
    );

    // ------------------------------------------------------------------
    // Request fields of the transaction at the head of the address pipe
    // ------------------------------------------------------------------
    logic [7:0]            w_we_mix;
    logic                  w_do_write;
    logic [STRB_W-1:0]     w_write_be;
    logic [BUS_WIDTH-1:0]  w_wdata;
    logic [ADDR_WIDTH-1:0] w_addr;

    assign w_we_mix   = r_ctrl[15:8];
    assign w_do_write = (w_addr_result_lfsr[7:0] < w_we_mix);

    always_comb begin
        if (w_do_write) begin
            w_write_be = STRB_W'(w_addr_result_lfsr);
            if (w_write_be == '0) w_write_be = {{(STRB_W-1){1'b0}}, 1'b1};
        end else begin
            w_write_be = {STRB_W{1'b1}};
        end
    end

    assign w_wdata = BUS_WIDTH'(w_addr_result_lfsr);
    assign w_addr  = w_addr_result;

    assign cpu_req_wr_data = {w_addr, w_do_write, w_write_be, w_wdata};

    // ------------------------------------------------------------------
    // House CRC-32 over issued write data and over response read data.
    //   Same polynomial / reflection / init / xorout as axi4_master_wr_injector.
    // ------------------------------------------------------------------
    localparam int CRC_WIDTH      = 32;
    localparam int CRC_DATA_WIDTH = BUS_WIDTH;
    localparam logic [CRC_WIDTH-1:0] CRC_POLY      = 32'h04C11DB7;
    localparam logic [CRC_WIDTH-1:0] CRC_POLY_INIT = '1;
    localparam logic [CRC_WIDTH-1:0] CRC_XOROUT    = '1;
    localparam int CRC_REFIN  = 1;
    localparam int CRC_REFOUT = 1;

    logic w_crc_start;
    logic w_crc_wdata_strobe;
    logic w_crc_rsp_strobe;

    localparam int CRC_CHUNKS = CRC_DATA_WIDTH / 8;

    dataint_crc #(
        .DATA_WIDTH(CRC_DATA_WIDTH),
        .CRC_WIDTH (CRC_WIDTH),
        .REFIN     (CRC_REFIN),
        .REFOUT    (CRC_REFOUT)
    ) u_crc_wdata (
        .POLY              (CRC_POLY),
        .POLY_INIT         (CRC_POLY_INIT),
        .XOROUT            (CRC_XOROUT),
        .clk               (aclk),
        .rst_n             (aresetn),
        .load_crc_start    (w_crc_start),
        .load_from_cascade (w_crc_wdata_strobe),
        .cascade_sel       ({CRC_CHUNKS{1'b1}}),
        .data              (w_wdata),
        .crc               (r_wdata_crc[CRC_WIDTH-1:0])
    );

    dataint_crc #(
        .DATA_WIDTH(CRC_DATA_WIDTH),
        .CRC_WIDTH (CRC_WIDTH),
        .REFIN     (CRC_REFIN),
        .REFOUT    (CRC_REFOUT)
    ) u_crc_rsp (
        .POLY              (CRC_POLY),
        .POLY_INIT         (CRC_POLY_INIT),
        .XOROUT            (CRC_XOROUT),
        .clk               (aclk),
        .rst_n             (aresetn),
        .load_crc_start    (w_crc_start),
        .load_from_cascade (w_crc_rsp_strobe),
        .cascade_sel       ({CRC_CHUNKS{1'b1}}),
        .data              (cpu_rsp_rd_data),
        .crc               (r_rsp_crc[CRC_WIDTH-1:0])
    );

    // Upper halves of the 64-bit CSR readback are zero.
    assign r_wdata_crc[BUS_WIDTH-1:CRC_WIDTH] = '0;
    assign r_rsp_crc[BUS_WIDTH-1:CRC_WIDTH]   = '0;

    // ------------------------------------------------------------------
    // AXIL write handling: accept AW and W independently per AXI4-Lite spec.
    // ------------------------------------------------------------------
    logic        r_bvalid;
    logic        r_aw_done;
    logic        r_w_done;
    logic [31:0] r_awaddr;
    logic [31:0] r_wdata_reg;
    logic [3:0]  r_wstrb;

    assign s_axil_awready = ~r_bvalid & ~r_aw_done;
    assign s_axil_wready  = ~r_bvalid & ~r_w_done;
    assign s_axil_bvalid  = r_bvalid;
    assign s_axil_bresp   = 2'b00;

    `ALWAYS_FF_RST(aclk, aresetn,
        if (`RST_ASSERTED(aresetn)) begin
            r_bvalid      <= 1'b0;
            r_aw_done     <= 1'b0;
            r_w_done      <= 1'b0;
            r_ctrl        <= '0;
            r_seed        <= '0;
            r_addr_base   <= '0;
            r_addr_mask   <= '0;
            r_trans_count <= '0;
        end else begin
            if (s_axil_awvalid && s_axil_awready) begin
                r_aw_done <= 1'b1;
                r_awaddr  <= s_axil_awaddr;
            end
            if (s_axil_wvalid && s_axil_wready) begin
                r_w_done <= 1'b1;
                r_wdata_reg  <= s_axil_wdata;
                r_wstrb  <= s_axil_wstrb;
            end
            if (r_aw_done && r_w_done && ~r_bvalid) begin
                r_bvalid  <= 1'b1;
                r_aw_done <= 1'b0;
                r_w_done  <= 1'b0;
                for (int b = 0; b < 4; b++) begin
                    if (r_wstrb[b]) begin
                        case (r_awaddr[6:2])
                            CSR_CTRL:        r_ctrl[8*b +: 8]        <= r_wdata_reg[8*b +: 8];
                            CSR_SEED:        r_seed[8*b +: 8]        <= r_wdata_reg[8*b +: 8];
                            CSR_ADDR_BASE:   r_addr_base[8*b +: 8]   <= r_wdata_reg[8*b +: 8];
                            CSR_ADDR_MASK:   r_addr_mask[8*b +: 8]   <= r_wdata_reg[8*b +: 8];
                            CSR_TRANS_COUNT: r_trans_count[8*b +: 8] <= r_wdata_reg[8*b +: 8];
                            default: ;
                        endcase
                    end
                end
            end else if (s_axil_bvalid && s_axil_bready) begin
                r_bvalid <= 1'b0;
            end

            // Clear run bit when the engine starts (leaves idle) and when
            // it finishes. Software can read STATUS to observe completion.
            if (~r_run && (r_ctrl[0] == 1'b1)) begin
                r_ctrl[0] <= 1'b0;
            end
        end
    )

    // ------------------------------------------------------------------
    // AXIL read handling
    // ------------------------------------------------------------------
    logic        r_ar_done;
    logic [31:0] r_ar_addr;
    logic [31:0] r_rdata;

    assign s_axil_arready = ~r_ar_done;
    assign s_axil_rvalid  = r_ar_done;
    assign s_axil_rresp   = 2'b00;
    assign s_axil_rdata   = r_rdata;

    always_comb begin
        r_rdata = 32'hDEAD_BEEF;
        case (r_ar_addr[6:2])
            CSR_CTRL:          r_rdata = r_ctrl;
            CSR_SEED:          r_rdata = r_seed;
            CSR_ADDR_BASE:     r_rdata = r_addr_base;
            CSR_ADDR_MASK:     r_rdata = r_addr_mask;
            CSR_TRANS_COUNT:   r_rdata = r_trans_count;
            CSR_STATUS:        r_rdata = {30'b0, r_run, r_done};
            CSR_ACC_COUNT:     r_rdata = r_acc_count;
            CSR_RSP_COUNT:     r_rdata = r_rsp_count;
            CSR_ERR_FLAG:      r_rdata = {31'b0, r_err_flag};
            CSR_LAT_MIN:       r_rdata = (r_rsp_count == '0) ? 32'h0 : r_lat_min;
            CSR_LAT_MAX:       r_rdata = r_lat_max;
            CSR_RUN_CYCLES:    r_rdata = r_run_cycles;
            CSR_RSP_CRC_LO:    r_rdata = r_rsp_crc[31:0];
            CSR_RSP_CRC_HI:    r_rdata = r_rsp_crc[63:32];
            CSR_WDATA_CRC_LO:  r_rdata = r_wdata_crc[31:0];
            CSR_WDATA_CRC_HI:  r_rdata = r_wdata_crc[63:32];
            CSR_LAT_SUM_LO:    r_rdata = r_lat_sum[31:0];
            CSR_LAT_SUM_HI:    r_rdata = r_lat_sum[63:32];
            CSR_OUTST_MAX:     r_rdata = r_outst_max;
            CSR_OUTST_SUM_LO:  r_rdata = r_outst_sum[31:0];
            CSR_OUTST_SUM_HI:  r_rdata = r_outst_sum[63:32];
            CSR_STALL_CYCLES:  r_rdata = r_stall_cycles;
            CSR_CREDIT_STALL:  r_rdata = r_credit_stall;
            default: begin
                if (r_ar_addr[6:2] >= CSR_LAT_HIST0 &&
                    r_ar_addr[6:2] < CSR_LAT_HIST0 + 5'(LAT_HIST_BUCKETS)) begin
                    r_rdata = r_lat_hist[3'(r_ar_addr[6:2] - CSR_LAT_HIST0)];
                end
            end
        endcase
    end

    `ALWAYS_FF_RST(aclk, aresetn,
        if (`RST_ASSERTED(aresetn)) begin
            r_ar_done <= 1'b0;
            r_ar_addr <= '0;
        end else begin
            if (s_axil_arvalid && s_axil_arready) begin
                r_ar_addr <= s_axil_araddr;
                r_ar_done <= 1'b1;
            end else if (s_axil_rvalid && s_axil_rready) begin
                r_ar_done <= 1'b0;
            end
        end
    )

    // ------------------------------------------------------------------
    // Run control, credit and the accept-timestamp ring
    // ------------------------------------------------------------------
    logic [31:0]        r_gen_count;      // address requests handed to the generator
    logic [OUTST_W-1:0] r_inflight;       // accepted, not yet responded
    logic [OUTST_W-1:0] w_credit;         // CTRL.outstanding, 0 -> 1, clamped
    logic [7:0]         w_ctrl_outst;
    logic               w_start;
    logic               w_can_issue;
    logic               w_accept;
    logic               w_resp;
    logic               w_last_resp;
    logic               w_stray_resp;
    logic [FLUSH_W-1:0] r_flush_cnt;
    logic               w_flushing;

    // Timeout while a request is in flight (large but finite)
    localparam int TIMEOUT_BITS = 24;
    logic [TIMEOUT_BITS-1:0] r_timeout_cnt;
    logic                    w_timeout;

    // Free-running cycle counter and the per-request accept timestamps.
    logic [31:0]        r_cycle;
    logic [31:0]        r_ts [MAX_OUTSTANDING];
    logic [TS_AW-1:0]   r_ts_wr;
    logic [TS_AW-1:0]   r_ts_rd;

    assign w_ctrl_outst = r_ctrl[CSR_CTRL_OUTST_SHIFT +: 8];
    always_comb begin
        if (w_ctrl_outst == 8'd0)                     w_credit = OUTST_W'(1);
        else if (int'(w_ctrl_outst) > MAX_OUTSTANDING) w_credit = OUTST_W'(MAX_OUTSTANDING);
        else                                          w_credit = OUTST_W'(w_ctrl_outst);
    end

    assign w_start    = ~r_run & r_ctrl[0];
    assign w_flushing = (r_flush_cnt != '0);

    // The generator is fed while the run has requests left to issue; it
    // holds at most two results nobody has taken yet, which the credit gate
    // at the cpu port throttles.
    assign w_addr_req_valid = r_run & ~w_flushing & (r_gen_count < r_trans_count);
    assign w_lfsr_advance   = w_addr_req_valid & w_addr_req_ready;

    // Credit gate at the cpu port.  r_inflight only falls on a response, so
    // a raised cpu_req_wr_valid stays raised until it is accepted.
    assign w_can_issue         = r_run & ~w_flushing & (r_inflight < w_credit);
    assign cpu_req_wr_valid    = w_addr_result_valid & w_can_issue;
    assign w_addr_result_ready = w_flushing | (w_can_issue & cpu_req_wr_ready);
    assign w_accept            = cpu_req_wr_valid & cpu_req_wr_ready;

    // Responses are taken whenever something is in flight; one arriving with
    // nothing in flight is a protocol error and is flagged, not consumed.
    assign cpu_rsp_rd_ready = (r_inflight != '0);
    assign w_resp           = cpu_rsp_rd_valid & cpu_rsp_rd_ready;
    assign w_stray_resp     = cpu_rsp_rd_valid & (r_inflight == '0);
    assign w_last_resp      = w_resp & ((r_rsp_count + 32'd1) >= r_trans_count);
    assign w_timeout        = r_run & (r_inflight != '0) & (&r_timeout_cnt);

    // LFSR loads once on run start and advances once per transaction handed
    // to the address generator; the value rides the generator as the tag.
    assign w_lfsr_load = w_start;

    // CRCs reset on run start; they accumulate on accepted issue (wdata) and
    // on every response beat (rsp).
    assign w_crc_start        = w_start;
    assign w_crc_wdata_strobe = w_accept;
    assign w_crc_rsp_strobe   = w_resp;

    // ------------------------------------------------------------------
    // Latency sample: cycles from request accept to response handshake.
    // The accept stored r_cycle; the response reads it back in order, so a
    // next-cycle response measures 1.  Bucket = floor(log2(sample)) capped
    // at 7 (sample is always >= 1).
    // ------------------------------------------------------------------
    logic [31:0] w_lat_sample;
    logic [4:0]  w_lat_msb;
    logic [2:0]  w_lat_bucket;

    assign w_lat_sample = r_cycle - r_ts[r_ts_rd];

    always_comb begin
        w_lat_msb = 5'd0;
        for (int i = 1; i < 32; i++) begin
            if (w_lat_sample[i]) w_lat_msb = 5'(i);
        end
    end
    assign w_lat_bucket = (w_lat_msb > 5'd7) ? 3'd7 : w_lat_msb[2:0];

    // Timestamp ring: no reset on the storage (it is written before read).
    always_ff @(posedge aclk) begin
        if (w_accept) r_ts[r_ts_wr] <= r_cycle;
    end

    `ALWAYS_FF_RST(aclk, aresetn,
        if (`RST_ASSERTED(aresetn)) begin
            r_run          <= 1'b0;
            r_done         <= 1'b0;
            r_err_flag     <= 1'b0;
            r_gen_count    <= '0;
            r_inflight     <= '0;
            r_acc_count    <= '0;
            r_rsp_count    <= '0;
            r_timeout_cnt  <= '0;
            r_flush_cnt    <= '0;
            r_cycle        <= '0;
            r_ts_wr        <= '0;
            r_ts_rd        <= '0;
            r_lat_min      <= '1;
            r_lat_max      <= '0;
            r_lat_sum      <= '0;
            r_run_cycles   <= '0;
            r_outst_max    <= '0;
            r_outst_sum    <= '0;
            r_stall_cycles <= '0;
            r_credit_stall <= '0;
            for (int b = 0; b < LAT_HIST_BUCKETS; b++) r_lat_hist[b] <= '0;
        end else begin
            r_cycle <= r_cycle + 32'd1;

            if (w_flushing) r_flush_cnt <= r_flush_cnt - 1'b1;

            if (w_start) begin
                // A run of zero transactions completes at once.
                r_run          <= (r_trans_count != '0);
                r_done         <= (r_trans_count == '0);
                r_err_flag     <= 1'b0;
                r_gen_count    <= '0;
                r_inflight     <= '0;
                r_acc_count    <= '0;
                r_rsp_count    <= '0;
                r_timeout_cnt  <= '0;
                r_ts_wr        <= '0;
                r_ts_rd        <= '0;
                r_lat_min      <= '1;
                r_lat_max      <= '0;
                r_lat_sum      <= '0;
                r_run_cycles   <= '0;
                r_outst_max    <= '0;
                r_outst_sum    <= '0;
                r_stall_cycles <= '0;
                r_credit_stall <= '0;
                for (int b = 0; b < LAT_HIST_BUCKETS; b++) r_lat_hist[b] <= '0;
            end else if (r_run) begin
                // ---- per-cycle run statistics ----
                r_run_cycles <= (r_run_cycles == 32'hFFFF_FFFF)
                                ? r_run_cycles : r_run_cycles + 1'b1;
                r_outst_sum  <= r_outst_sum + 64'(r_inflight);
                if (32'(r_inflight) > r_outst_max) r_outst_max <= 32'(r_inflight);
                if (cpu_req_wr_valid & ~cpu_req_wr_ready) begin
                    r_stall_cycles <= r_stall_cycles + 1'b1;
                end
                if (w_addr_result_valid & ~w_flushing & ~w_can_issue) begin
                    r_credit_stall <= r_credit_stall + 1'b1;
                end

                // ---- issue side ----
                if (w_lfsr_advance) r_gen_count <= r_gen_count + 32'd1;
                if (w_accept) begin
                    r_acc_count <= (r_acc_count == 32'hFFFF_FFFF)
                                   ? r_acc_count : r_acc_count + 1'b1;
                    r_ts_wr     <= r_ts_wr + 1'b1;
                end

                // ---- response side ----
                if (w_resp) begin
                    r_rsp_count   <= (r_rsp_count == 32'hFFFF_FFFF)
                                     ? r_rsp_count : r_rsp_count + 1'b1;
                    r_ts_rd       <= r_ts_rd + 1'b1;
                    r_timeout_cnt <= '0;
                    if (w_lat_sample < r_lat_min) r_lat_min <= w_lat_sample;
                    if (w_lat_sample > r_lat_max) r_lat_max <= w_lat_sample;
                    r_lat_sum <= r_lat_sum + 64'(w_lat_sample);
                    if (r_lat_hist[w_lat_bucket] != 32'hFFFF_FFFF) begin
                        r_lat_hist[w_lat_bucket] <= r_lat_hist[w_lat_bucket] + 1'b1;
                    end
                end else if (r_inflight != '0) begin
                    r_timeout_cnt <= r_timeout_cnt + 1'b1;
                end

                r_inflight <= r_inflight + OUTST_W'(w_accept) - OUTST_W'(w_resp);

                // ---- end of run ----
                if (w_last_resp) begin
                    r_run  <= 1'b0;
                    r_done <= 1'b1;
                end else if (w_timeout) begin
                    // Abort: the generator may hold addresses nobody took;
                    // drain them so the next run starts clean.
                    r_err_flag  <= 1'b1;
                    r_run       <= 1'b0;
                    r_done      <= 1'b1;
                    r_flush_cnt <= FLUSH_W'(FLUSH_CYCLES);
                end
            end

            // A response with nothing in flight is a protocol error whenever
            // it happens; it is flagged and left unconsumed.
            if (w_stray_resp & ~w_start) r_err_flag <= 1'b1;
        end
    )

endmodule : amber_cycle_injector
