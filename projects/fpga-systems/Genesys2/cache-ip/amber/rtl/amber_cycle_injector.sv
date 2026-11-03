// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: 2026 sean galloway
//
// RTL Design Sherpa - Industry-Standard RTL Design and Verification
// https://github.com/sean-galloway/RTLDesignSherpa
//
// Module: amber_cycle_injector
// Purpose: Per-core stimulus engine for the amber pair-rig Genesys2 bring-up.
//   AXIL4-Lite CSR slave (32-word decode window; the original 16-word regfile
//   plus read-only latency/occupancy instrumentation) drives a deterministic
//   cpu_req GAXI master.  One outstanding transaction at a time; counts accepts
//   and responses; raises ERR_FLAG if a response never arrives. Being blocking,
//   per-request latency is exactly FSM_WAIT_RSP occupancy + 1, so the block
//   records latency min/max/sum, an 8-bucket log2 histogram, and a run-cycle
//   count per run (formal/amber TASK-001 item 2).
//
//   Family-aligned with rtl/amba/shared/axi4_master_wr_injector:
//     - Addresses come from the house dma_address_gen using base + strided index
//       with a wrap mask, reproducing the original "base | (lfsr & mask)" pattern
//       when the base is aligned to (mask + 1).
//     - Write data and the read/write mix come from the house
//       shifter_lfsr_fibonacci (loadable seed) rather than the old inline Galois
//       LFSR.
//     - Response-data and issued-write-data integrity are accumulated with the
//       house dataint_crc (CRC-32, POLY=0x04C11DB7, REFIN=1, REFOUT=1,
//       POLY_INIT='1, XOROUT='1) instead of the old XOR checksums.
//
//   Divergence from the house injector (documented):
//     - This block is a single-module, one-outstanding, blocking injector with
//       no pipelined outstanding transactions, no AW/W decoupling, and no
//       address-hash data mode.  It exists to drive a cpu_req GAXI slave, not a
//       full AXI4 memory controller.
//     - The address generator is used with stride_0 = 1 and index_0 = lfsr_out,
//       so the resulting address is base + (lfsr & mask).  Software must keep
//       ADDR_BASE aligned to (ADDR_MASK + 1) to recover the original OR semantics.
//     - The dma_address_gen descriptor ports are re-sampled from CSRs on every
//       run start, preserving runtime AXIL programmability even though the house
//       module normally sees a static descriptor for a whole transfer.

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
    parameter int STRIDE_WIDTH = 32
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
    //   original 16-word regfile; the latency/occupancy instrumentation
    //   (formal/amber TASK-001 item 2) fills the three historic holes and
    //   lives above 0x40. All instrument registers are read-only, cleared
    //   on run start. Latency is cycles from request accept to response
    //   handshake (FSM_WAIT_RSP occupancy + 1), one sample per request.
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

    // Histogram bucket edges are powers of two: bucket b covers latencies
    // [2^b, 2^(b+1)-1] and bucket 7 catches >= 128. Bucket 0 is latency 1.
    localparam int LAT_HIST_BUCKETS = 8;

    localparam logic [31:0] CSR_CTRL_RUN_MASK     = 32'h0000_0001;
    localparam int          CSR_CTRL_WE_MIX_SHIFT = 8;

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
    logic        r_busy;
    logic        r_err_flag;
    logic [BUS_WIDTH-1:0] r_rsp_crc;
    logic [BUS_WIDTH-1:0] r_wdata_crc;

    // Latency / occupancy instrumentation (read-only, cleared on run start)
    logic [31:0] r_lat_cnt;   // cycles the in-flight request has waited
    logic [31:0] r_lat_min;
    logic [31:0] r_lat_max;
    logic [63:0] r_lat_sum;
    logic [31:0] r_run_cycles;
    logic [31:0] r_lat_hist [LAT_HIST_BUCKETS];

    assign o_done     = r_done;
    assign o_busy     = r_busy;
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
    // House address generator
    //   base  = r_addr_base
    //   stride = +1, wrap = r_addr_mask
    //   index = current LFSR output
    //   => addr = base + (lfsr & mask)
    //   Software must align base to (mask + 1) to match the old OR semantics.
    // ------------------------------------------------------------------
    logic                       w_addr_req_valid;
    logic                       w_addr_req_ready;
    logic [INDEX_WIDTH-1:0]     w_addr_index;
    logic                       w_addr_result_valid;
    logic                       w_addr_result_ready;
    logic [ADDR_WIDTH-1:0]      w_addr_result;

    assign w_addr_index = INDEX_WIDTH'(w_lfsr_out);

    dma_address_gen #(
        .ADDR_WIDTH  (ADDR_WIDTH),
        .INDEX_WIDTH (INDEX_WIDTH),
        .STRIDE_WIDTH(STRIDE_WIDTH),
        .TAG_WIDTH   (1)
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
        .i_req_tag         ('0),

        .o_result_valid    (w_addr_result_valid),
        .i_result_ready    (w_addr_result_ready),
        .o_result_addr     (w_addr_result),
        .o_result_tag      ()
    );

    // ------------------------------------------------------------------
    // Combinational request fields
    // ------------------------------------------------------------------
    logic [7:0]            w_we_mix;
    logic                  w_do_write;
    logic [STRB_W-1:0]     w_write_be;
    logic [BUS_WIDTH-1:0]  w_wdata;
    logic [ADDR_WIDTH-1:0] w_addr;

    assign w_we_mix   = r_ctrl[15:8];
    assign w_do_write = (w_lfsr_out[7:0] < w_we_mix);

    always_comb begin
        if (w_do_write) begin
            w_write_be = STRB_W'(w_lfsr_out);
            if (w_write_be == '0) w_write_be = {{(STRB_W-1){1'b0}}, 1'b1};
        end else begin
            w_write_be = {STRB_W{1'b1}};
        end
    end

    assign w_wdata = BUS_WIDTH'(w_lfsr_out);
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
    // Stimulus FSM
    // ------------------------------------------------------------------
    typedef enum logic [2:0] {
        FSM_IDLE,
        FSM_ADDR_WAIT,
        FSM_ISSUE,
        FSM_WAIT_RSP
    } fsm_state_t;

    fsm_state_t r_fsm;

    // Timeout while waiting for response (large but finite)
    localparam int TIMEOUT_BITS = 24;
    logic [TIMEOUT_BITS-1:0] r_timeout_cnt;

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

            // Clear run bit when the engine starts (leaves IDLE) and when
            // it finishes. Software can read STATUS to observe completion.
            if ((r_fsm == FSM_IDLE) && (r_ctrl[0] == 1'b1)) begin
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
            CSR_STATUS:        r_rdata = {30'b0, r_busy, r_done};
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
    // FSM + counters + CRC / LFSR controls
    // ------------------------------------------------------------------
    assign w_addr_result_ready = (r_fsm == FSM_ADDR_WAIT) && w_addr_result_valid;
    assign cpu_req_wr_valid    = (r_fsm == FSM_ISSUE);
    assign cpu_rsp_rd_ready    = (r_fsm == FSM_WAIT_RSP);

    // Address request valid whenever we are waiting for a fresh address.
    assign w_addr_req_valid = (r_fsm == FSM_ADDR_WAIT);

    // LFSR loads once on run start and advances only when the cpu_req is
    // accepted.  This keeps the LFSR value used for index, data, and we_mix
    // aligned for each transaction.
    assign w_lfsr_load    = (r_fsm == FSM_IDLE) && r_ctrl[0];
    assign w_lfsr_advance = (r_fsm == FSM_ISSUE) && cpu_req_wr_ready;

    // CRCs reset on run start; they accumulate on accepted issue (wdata) and
    // on every response beat (rsp).
    assign w_crc_start       = w_lfsr_load;
    assign w_crc_wdata_strobe = w_lfsr_advance;
    assign w_crc_rsp_strobe  = (r_fsm == FSM_WAIT_RSP) && cpu_rsp_rd_valid;

    // ------------------------------------------------------------------
    // Latency sample: cycles from request accept to response handshake.
    // r_lat_cnt runs while parked in FSM_WAIT_RSP; the sample adds the
    // handshake cycle itself, so a next-cycle response measures 1.
    // Bucket = floor(log2(sample)) capped at 7 (sample is always >= 1).
    // ------------------------------------------------------------------
    logic [31:0] w_lat_sample;
    logic [4:0]  w_lat_msb;
    logic [2:0]  w_lat_bucket;

    assign w_lat_sample = r_lat_cnt + 32'd1;

    always_comb begin
        w_lat_msb = 5'd0;
        for (int i = 1; i < 32; i++) begin
            if (w_lat_sample[i]) w_lat_msb = 5'(i);
        end
    end
    assign w_lat_bucket = (w_lat_msb > 5'd7) ? 3'd7 : w_lat_msb[2:0];

    `ALWAYS_FF_RST(aclk, aresetn,
        if (`RST_ASSERTED(aresetn)) begin
            r_fsm         <= FSM_IDLE;
            r_acc_count   <= '0;
            r_rsp_count   <= '0;
            r_done        <= 1'b0;
            r_busy        <= 1'b0;
            r_err_flag    <= 1'b0;
            r_timeout_cnt <= '0;
            r_lat_cnt     <= '0;
            r_lat_min     <= '1;
            r_lat_max     <= '0;
            r_lat_sum     <= '0;
            r_run_cycles  <= '0;
            for (int b = 0; b < LAT_HIST_BUCKETS; b++) r_lat_hist[b] <= '0;
        end else begin
            if (r_busy) begin
                r_run_cycles <= (r_run_cycles == 32'hFFFF_FFFF)
                                ? r_run_cycles : r_run_cycles + 1'b1;
            end
            case (r_fsm)
                FSM_IDLE: begin
                    if (r_ctrl[0]) begin
                        r_fsm         <= FSM_ADDR_WAIT;
                        r_busy        <= 1'b1;
                        r_done        <= 1'b0;
                        r_acc_count   <= '0;
                        r_rsp_count   <= '0;
                        r_err_flag    <= 1'b0;
                        r_timeout_cnt <= '0;
                        r_lat_cnt     <= '0;
                        r_lat_min     <= '1;
                        r_lat_max     <= '0;
                        r_lat_sum     <= '0;
                        r_run_cycles  <= '0;
                        for (int b = 0; b < LAT_HIST_BUCKETS; b++) r_lat_hist[b] <= '0;
                    end
                end

                FSM_ADDR_WAIT: begin
                    if (w_addr_result_valid) begin
                        r_fsm <= FSM_ISSUE;
                    end
                end

                FSM_ISSUE: begin
                    if (cpu_req_wr_ready) begin
                        r_acc_count   <= (r_acc_count == 32'hFFFF_FFFF)
                                         ? r_acc_count : r_acc_count + 1'b1;
                        r_fsm         <= FSM_WAIT_RSP;
                        r_timeout_cnt <= '0;
                        r_lat_cnt     <= '0;
                    end
                end

                FSM_WAIT_RSP: begin
                    if (cpu_rsp_rd_valid) begin
                        r_rsp_count <= (r_rsp_count == 32'hFFFF_FFFF)
                                       ? r_rsp_count : r_rsp_count + 1'b1;
                        if (w_lat_sample < r_lat_min) r_lat_min <= w_lat_sample;
                        if (w_lat_sample > r_lat_max) r_lat_max <= w_lat_sample;
                        r_lat_sum <= r_lat_sum + 64'(w_lat_sample);
                        if (r_lat_hist[w_lat_bucket] != 32'hFFFF_FFFF) begin
                            r_lat_hist[w_lat_bucket] <= r_lat_hist[w_lat_bucket] + 1'b1;
                        end
                        if (r_rsp_count + 1'b1 >= r_trans_count) begin
                            r_fsm  <= FSM_IDLE;
                            r_done <= 1'b1;
                            r_busy <= 1'b0;
                        end else begin
                            r_fsm <= FSM_ADDR_WAIT;
                        end
                    end else begin
                        r_timeout_cnt <= r_timeout_cnt + 1'b1;
                        r_lat_cnt     <= r_lat_cnt + 1'b1;
                        if (&r_timeout_cnt) begin
                            r_err_flag <= 1'b1;
                            r_fsm      <= FSM_IDLE;
                            r_done     <= 1'b1;
                            r_busy     <= 1'b0;
                        end
                    end
                end

                default: r_fsm <= FSM_IDLE;
            endcase
        end
    )

endmodule : amber_cycle_injector
