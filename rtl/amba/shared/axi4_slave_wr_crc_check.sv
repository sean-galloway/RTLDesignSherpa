`timescale 1ns / 1ps

//==============================================================================
// Module: axi4_slave_wr_crc_check
//==============================================================================
//
// TODO -- ARCHITECTURAL RULE: every AXI/AXIL agent must use the standard
// protocol modules under rtl/amba/. The AW/W/B protocol logic in this
// module is hand-rolled and therefore NON-COMPLIANT. Refactor to wrap
// `axi4_slave_wr_mon` (which already bundles `axi4_slave_wr` + filtered
// monitor) and drive the CRC accumulator from its fub_axi_aw* / fub_axi_w*
// / fub_axi_b* user interface. Tracked as task #79.
//
// Description:
//   AXI4 write-only slave that computes CRC-32 on received data for DMA
//   validation. Combines axi4_slave_wr protocol handler with CRC checker.
//
//   Per-channel mode (NUM_CHANNELS > 1): the slave maintains independent
//   CRC state per channel, demuxed off the low bits of the W-side wuser
//   (which the STREAM master drives with the burst's channel index). The
//   AW FSM accepts one burst at a time and W beats are in-order with AW,
//   so r_wr_id[CIW-1:0] is the active channel during W; we use that as
//   the demux selector.
//
// Per-channel outputs:
//   write_crc_value [NUM_CHANNELS][31:0] - per-channel CRC values
//   write_crc_valid [NUM_CHANNELS]       - per-channel valid flags
//   write_beat_count[NUM_CHANNELS][31:0] - per-channel beat counts
//
// Aggregate output (for harness timer):
//   write_beat_count_total [31:0]        - sum of per-channel beat counts
//
//==============================================================================

`include "reset_defs.svh"

module axi4_slave_wr_crc_check #(
    // AXI parameters
    parameter int NUM_CHANNELS  = 1,
    parameter int SKID_DEPTH_AW = 2,
    parameter int SKID_DEPTH_W  = 4,
    parameter int SKID_DEPTH_B  = 2,
    parameter int AXI_ID_WIDTH  = 8,
    parameter int AXI_ADDR_WIDTH = 32,
    parameter int AXI_DATA_WIDTH = 64,
    parameter int AXI_USER_WIDTH = 1,

    // CRC parameters (MUST MATCH axi4_slave_rd_injector!)
    parameter int CRC_WIDTH      = 32,
    parameter int CRC_DATA_WIDTH = 32,
    parameter logic [31:0] CRC_POLY    = 32'h04C11DB7,
    parameter logic [31:0] CRC_INIT    = 32'hFFFFFFFF,
    parameter logic [31:0] CRC_XOROUT  = 32'hFFFFFFFF,
    parameter int CRC_REFIN  = 1,
    parameter int CRC_REFOUT = 1,

    // Which 32-bit slice to CRC from AXI_DATA_WIDTH
    parameter int CRC_SLICE_OFFSET = 0,
    // BYTE_CRC=1 (byte-granular RAPIDS, rapids TASK-019): the per-channel CRC
    // runs over the STROBED bytes of every W beat in lane order, four per
    // cycle through cascade_sel, with wready held low while a beat is fed.
    // 0: the CRC_SLICE_OFFSET 32-bit slice of every beat (STREAM's harness).
    parameter bit BYTE_CRC = 1'b0,

    // ERR_INJECT=1 (rapids TASK-020) builds the B-response error injector:
    // a chosen burst on a chosen channel answers cfg_err_resp instead of
    // OKAY, so a DUT's write-error path can be reached from a harness.
    // 0 (default) elaborates none of it and holds BRESP at OKAY -- the block
    // is then identical to its pre-TASK-020 behaviour, which is what
    // STREAM's and the RAPIDS-beats harnesses keep using.
    parameter bit ERR_INJECT = 1'b0,

    // Derived
    parameter int CIW = (NUM_CHANNELS > 1) ? $clog2(NUM_CHANNELS) : 1
) (
    // Global Clock and Reset
    input  logic                        aclk,
    input  logic                        aresetn,

    // Test Control
    input  logic                        crc_reset,

    // Per-channel CRC and Status Outputs
    output logic [NUM_CHANNELS-1:0][31:0] write_crc_value,
    output logic [NUM_CHANNELS-1:0]       write_crc_valid,
    output logic [NUM_CHANNELS-1:0][31:0] write_beat_count,
    // Aggregate beat count (sum across channels) for the harness stop trigger.
    output logic [31:0]                   write_beat_count_total,

    // AXI4 Slave Interface (Write-Only)
    // Write address channel (AW)
    input  logic [AXI_ID_WIDTH-1:0]     s_axi_awid,
    input  logic [AXI_ADDR_WIDTH-1:0]   s_axi_awaddr,
    input  logic [7:0]                  s_axi_awlen,
    input  logic [2:0]                  s_axi_awsize,
    input  logic [1:0]                  s_axi_awburst,
    input  logic                        s_axi_awlock,
    input  logic [3:0]                  s_axi_awcache,
    input  logic [2:0]                  s_axi_awprot,
    input  logic [3:0]                  s_axi_awqos,
    input  logic [3:0]                  s_axi_awregion,
    input  logic [AXI_USER_WIDTH-1:0]   s_axi_awuser,
    input  logic                        s_axi_awvalid,
    output logic                        s_axi_awready,

    // Write data channel (W)
    input  logic [AXI_DATA_WIDTH-1:0]   s_axi_wdata,
    input  logic [AXI_DATA_WIDTH/8-1:0] s_axi_wstrb,
    input  logic                        s_axi_wlast,
    input  logic [AXI_USER_WIDTH-1:0]   s_axi_wuser,
    input  logic                        s_axi_wvalid,
    output logic                        s_axi_wready,

    // Write response channel (B)
    output logic [AXI_ID_WIDTH-1:0]     s_axi_bid,
    output logic [1:0]                  s_axi_bresp,
    output logic [AXI_USER_WIDTH-1:0]   s_axi_buser,
    output logic                        s_axi_bvalid,
    input  logic                        s_axi_bready,

    // Error-response injection config (rapids TASK-020).
    // Inert unless ERR_INJECT=1; tie off at 0 otherwise.
    input  logic                        cfg_err_enable,
    input  logic [CIW-1:0]              cfg_err_channel,
    input  logic [15:0]                 cfg_err_skip,
    input  logic [1:0]                  cfg_err_resp,
    input  logic                        cfg_err_oneshot,
    output logic                        err_injected,

    // Status Output
    output logic                        busy
);

    //==========================================================================
    // Internal Signals - FUB (Functional Unit Backend) Interface
    //==========================================================================

    logic [AXI_ID_WIDTH-1:0]     fub_axi_awid;
    logic [AXI_ADDR_WIDTH-1:0]   fub_axi_awaddr;
    logic [7:0]                  fub_axi_awlen;
    logic [2:0]                  fub_axi_awsize;
    logic [1:0]                  fub_axi_awburst;
    logic                        fub_axi_awlock;
    logic [3:0]                  fub_axi_awcache;
    logic [2:0]                  fub_axi_awprot;
    logic [3:0]                  fub_axi_awqos;
    logic [3:0]                  fub_axi_awregion;
    logic [AXI_USER_WIDTH-1:0]   fub_axi_awuser;
    logic                        fub_axi_awvalid;
    logic                        fub_axi_awready;

    logic [AXI_DATA_WIDTH-1:0]   fub_axi_wdata;
    logic [AXI_DATA_WIDTH/8-1:0] fub_axi_wstrb;
    logic                        fub_axi_wlast;
    logic [AXI_USER_WIDTH-1:0]   fub_axi_wuser;
    logic                        fub_axi_wvalid;
    logic                        fub_axi_wready;

    logic [AXI_ID_WIDTH-1:0]     fub_axi_bid;
    logic [1:0]                  fub_axi_bresp;
    logic [AXI_USER_WIDTH-1:0]   fub_axi_buser;
    logic                        fub_axi_bvalid;
    logic                        fub_axi_bready;

    //==========================================================================
    // Extract 32-bit Slice from AXI Data
    //==========================================================================

    logic [31:0] data_slice;

    generate
        if (AXI_DATA_WIDTH == 32) begin : gen_no_slice
            assign data_slice = fub_axi_wdata;
        end else begin : gen_slice
            localparam int SLICE_LSB = CRC_SLICE_OFFSET * 32;
            localparam int SLICE_MSB = SLICE_LSB + 31;

            initial begin
                if (SLICE_MSB >= AXI_DATA_WIDTH) begin
                    $error("CRC_SLICE_OFFSET=%0d out of range for AXI_DATA_WIDTH=%0d",
                           CRC_SLICE_OFFSET, AXI_DATA_WIDTH);
                end
            end

            assign data_slice = fub_axi_wdata[SLICE_MSB:SLICE_LSB];
        end
    endgenerate

    //==========================================================================
    // FUB burst state (declared early — used by per-channel CRC gating)
    //==========================================================================

    logic [AXI_ID_WIDTH-1:0]   r_wr_id;
    logic [AXI_USER_WIDTH-1:0] r_wr_user;
    logic                      r_wr_active;
    // B responses are queued in a small FIFO (see below): with 8 channels issuing
    // gapless back-to-back bursts (and a trailing 1-beat burst), two WLASTs can
    // land within the B-drain window. The old single r_b_pending bit dropped the
    // new B whenever a WLAST coincided with a B consume -> ~1 dropped B per
    // channel -> the DUT's write-commit counter stalled and the channel never
    // returned to idle. The module comment already called for a B FIFO here.

    // Active channel index for the in-flight burst (low bits of captured AW ID).
    logic [CIW-1:0] w_active_ch;
    assign w_active_ch = (NUM_CHANNELS == 1) ? '0 : r_wr_id[CIW-1:0];

    // Single accepted-W-beat strobe; per-channel CRC instances gate on this.
    wire w_w_beat = fub_axi_wvalid && fub_axi_wready && r_wr_active;

    //==========================================================================
    // Byte-granular CRC feed (BYTE_CRC)
    //==========================================================================
    // The strobed bytes of an accepted W beat are shifted down to lane 0 and
    // fed to the burst's channel CRC four bytes per cycle (cascade_sel picks
    // 1..4), so the CRC is over the bytes written, in address order.
    logic                        r_bc_busy;
    logic [AXI_DATA_WIDTH-1:0]   r_bc_data;
    logic [7:0]                  r_bc_left;
    logic [CIW-1:0]              r_bc_ch;
    logic [7:0]                  w_strb_bytes;
    logic [7:0]                  w_first_lane;
    logic [7:0]                  w_bc_take;
    logic [3:0]                  w_bc_sel;
    always_comb begin
        w_strb_bytes = '0;
        w_first_lane = '0;
        for (int b = AXI_DATA_WIDTH/8 - 1; b >= 0; b--) begin
            w_strb_bytes = w_strb_bytes + 8'(fub_axi_wstrb[b]);
            if (fub_axi_wstrb[b]) w_first_lane = 8'(b);
        end
    end
    assign w_bc_take = (r_bc_left > 8'd4) ? 8'd4 : r_bc_left;
    assign w_bc_sel  = 4'(4'b0001 << (w_bc_take - 8'd1));
    `ALWAYS_FF_RST(aclk, aresetn,
        if (`RST_ASSERTED(aresetn)) begin
            r_bc_busy <= 1'b0;
            r_bc_data <= '0;
            r_bc_left <= '0;
            r_bc_ch   <= '0;
        end else if (BYTE_CRC) begin
            if (r_bc_busy) begin
                r_bc_data <= r_bc_data >> 32;
                r_bc_left <= r_bc_left - w_bc_take;
                if (r_bc_left <= 8'd4) r_bc_busy <= 1'b0;
            end else if (w_w_beat && (w_strb_bytes != 8'd0)) begin
                r_bc_busy <= 1'b1;
                r_bc_data <= fub_axi_wdata >> (w_first_lane * 8);
                r_bc_left <= w_strb_bytes;
                r_bc_ch   <= w_active_ch;
            end
        end
    )

    //==========================================================================
    // Per-channel CRC-32 Calculators + beat counters
    //==========================================================================

    logic [31:0] crc_out_per_ch [NUM_CHANNELS];

    genvar gch;
    generate
        for (gch = 0; gch < NUM_CHANNELS; gch++) begin : gen_crc
            logic ch_load_from_cascade;
            logic r_ch_crc_valid;
            logic [31:0] r_ch_beat_count;

            // CRC accumulates only when the active burst belongs to this channel
            assign ch_load_from_cascade = w_w_beat
                                       && (w_active_ch == gch[CIW-1:0]);

            dataint_crc #(
                .DATA_WIDTH(CRC_DATA_WIDTH),
                .CRC_WIDTH (CRC_WIDTH),
                .REFIN     (CRC_REFIN),
                .REFOUT    (CRC_REFOUT)
            ) u_crc (
                .POLY             (CRC_POLY),
                .POLY_INIT        (CRC_INIT),
                .XOROUT           (CRC_XOROUT),
                .clk              (aclk),
                .rst_n            (aresetn),
                .load_crc_start   (crc_reset),
                .load_from_cascade(BYTE_CRC ? (r_bc_busy && (r_bc_ch == gch[CIW-1:0])) : ch_load_from_cascade),
                .cascade_sel      (BYTE_CRC ? w_bc_sel : 4'b1000),
                .data             (BYTE_CRC ? r_bc_data[31:0] : data_slice),
                .crc              (crc_out_per_ch[gch])
            );

            `ALWAYS_FF_RST(aclk, aresetn,
                if (`RST_ASSERTED(aresetn)) begin
                    r_ch_crc_valid  <= 1'b0;
                    r_ch_beat_count <= '0;
                end else begin
                    if (crc_reset) begin
                        r_ch_crc_valid  <= 1'b0;
                        r_ch_beat_count <= '0;
                    end else if (ch_load_from_cascade) begin
                        r_ch_crc_valid  <= 1'b1;
                        r_ch_beat_count <= r_ch_beat_count + 1'b1;
                    end
                end
            )

            assign write_crc_value [gch] = crc_out_per_ch[gch];
            assign write_crc_valid [gch] = r_ch_crc_valid;
            assign write_beat_count[gch] = r_ch_beat_count;
        end
    endgenerate

    //==========================================================================
    // Aggregate beat count (sum across all channels) for the harness timer
    //==========================================================================

    always_comb begin
        write_beat_count_total = '0;
        for (int ch = 0; ch < NUM_CHANNELS; ch++) begin
            write_beat_count_total = write_beat_count_total + write_beat_count[ch];
        end
    end

    //==========================================================================
    // FUB Interface - Burst FSM for Write Acceptance
    //==========================================================================

    // Accept AW when idle, OR on the last W beat of the current burst so the
    // next burst's W beats follow with no dead cycle. The original (idle-only)
    // accept forced a 1-cycle !active gap between bursts (wready=0); once the
    // read slave feeds the SRAM gaplessly this would become the write-side
    // limiter (~1 starvation cycle per burst). Mirrors the read-slave fix.
    wire w_wr_last_beat = r_wr_active && fub_axi_wvalid && fub_axi_wready &&
                          fub_axi_wlast;
    assign fub_axi_awready = !r_wr_active || w_wr_last_beat;
    assign fub_axi_wready  = r_wr_active && !r_bc_busy;   // BYTE_CRC: hold W while a beat is fed
    // fub_axi_bresp is driven by the error injector below (OKAY when
    // ERR_INJECT=0, which is every build but the byte-RAPIDS harness).

    // B-response FIFO (inline, self-contained): push {user,id} of the completing
    // burst on every WLAST, pop on the B handshake. Holds multiple outstanding B's
    // so gapless multi-channel bursts never drop one (the single r_b_pending bit
    // did). Kept inline (no gaxi_fifo_sync dependency) so this shared test-infra
    // slave pulls no extra modules into any consumer's filelist.
    localparam int BFIFO_W     = AXI_USER_WIDTH + AXI_ID_WIDTH;
    localparam int BFIFO_DEPTH = 16;
    localparam int BFIFO_AW    = $clog2(BFIFO_DEPTH);

    logic [BFIFO_W-1:0] r_bfifo_mem [BFIFO_DEPTH];
    logic [BFIFO_AW-1:0] r_bfifo_wptr, r_bfifo_rptr;
    logic [BFIFO_AW:0]   r_bfifo_count;

    wire   w_bfifo_din_valid = w_wr_last_beat;             // push
    wire   w_bfifo_rd_valid  = (r_bfifo_count != '0);      // not empty
    wire   w_bfifo_pop       = w_bfifo_rd_valid && fub_axi_bready;
    wire [BFIFO_W-1:0] w_bfifo_din = {r_wr_user, r_wr_id};

    //==========================================================================
    // B-response error injection (rapids TASK-020)
    //==========================================================================
    // Counts completing bursts on cfg_err_channel while armed; the burst whose
    // index equals cfg_err_skip answers cfg_err_resp. One-shot disarms after
    // it, so a sequence can prove recovery on the next burst. The resp travels
    // WITH its burst through the B FIFO rather than being muxed onto whatever
    // B happens to be presented -- with several bursts outstanding those are
    // different things, and only the former is addressable from a test.
    generate
        if (ERR_INJECT) begin : gen_err_inject
            logic [15:0] r_err_count;
            logic        r_err_done;
            logic [1:0]  r_bfifo_resp [BFIFO_DEPTH];

            wire w_err_arm_ch = (NUM_CHANNELS == 1) ? 1'b1
                                                    : (w_active_ch == cfg_err_channel);
            wire w_err_hit    = cfg_err_enable && !r_err_done && w_err_arm_ch &&
                                (r_err_count == cfg_err_skip);

            assign fub_axi_bresp = r_bfifo_resp[r_bfifo_rptr];

            `ALWAYS_FF_RST(aclk, aresetn,
                if (`RST_ASSERTED(aresetn)) begin
                    r_err_count  <= '0;
                    r_err_done   <= 1'b0;
                    err_injected <= 1'b0;
                    for (int i = 0; i < BFIFO_DEPTH; i++) begin
                        r_bfifo_resp[i] <= 2'b00;
                    end
                end else begin
                    if (crc_reset || !cfg_err_enable) begin
                        r_err_count <= '0;
                        r_err_done  <= 1'b0;
                    end else if (w_wr_last_beat && w_err_arm_ch) begin
                        if (w_err_hit) begin
                            if (cfg_err_oneshot) r_err_done  <= 1'b1;
                            else                 r_err_count <= '0;
                        end else begin
                            r_err_count <= r_err_count + 16'd1;
                        end
                    end

                    if (crc_reset) begin
                        err_injected <= 1'b0;
                    end else if (w_wr_last_beat && w_err_hit) begin
                        err_injected <= 1'b1;
                    end

                    // Every completing burst pushes its own response code.
                    if (w_bfifo_din_valid) begin
                        r_bfifo_resp[r_bfifo_wptr] <= w_err_hit ? cfg_err_resp : 2'b00;
                    end
                end
            )
        end else begin : gen_no_err_inject
            assign fub_axi_bresp = 2'b00;  // OKAY
            assign err_injected  = 1'b0;
        end
    endgenerate

    assign fub_axi_bvalid = w_bfifo_rd_valid;
    assign {fub_axi_buser, fub_axi_bid} = r_bfifo_mem[r_bfifo_rptr];

    `ALWAYS_FF_RST(aclk, aresetn,
        if (`RST_ASSERTED(aresetn)) begin
            r_bfifo_wptr  <= '0;
            r_bfifo_rptr  <= '0;
            r_bfifo_count <= '0;
        end else begin
            if (w_bfifo_din_valid) begin
                r_bfifo_mem[r_bfifo_wptr] <= w_bfifo_din;
                r_bfifo_wptr <= r_bfifo_wptr + 1'b1;
            end
            if (w_bfifo_pop) begin
                r_bfifo_rptr <= r_bfifo_rptr + 1'b1;
            end
            case ({w_bfifo_din_valid, w_bfifo_pop})
                2'b10:   r_bfifo_count <= r_bfifo_count + 1'b1;
                2'b01:   r_bfifo_count <= r_bfifo_count - 1'b1;
                default: r_bfifo_count <= r_bfifo_count;
            endcase
        end
    )

    `ALWAYS_FF_RST(aclk, aresetn,
        if (`RST_ASSERTED(aresetn)) begin
            r_wr_active <= 1'b0;
            r_wr_id <= '0;
            r_wr_user <= '0;
        end else begin
            // AW acceptance — start a new burst from idle.
            if (fub_axi_awvalid && fub_axi_awready && !r_wr_active) begin
                r_wr_active <= 1'b1;
                r_wr_id <= fub_axi_awid;
                r_wr_user <= fub_axi_awuser;
            end

            // W last beat — complete the burst: its {user,id} is pushed to the B
            // FIFO (above) so no B is ever dropped; accept the next AW back-to-back
            // if one is waiting (stay active so wready never drops).
            if (w_wr_last_beat) begin
                if (fub_axi_awvalid) begin
                    r_wr_id   <= fub_axi_awid;
                    r_wr_user <= fub_axi_awuser;
                    // r_wr_active stays 1 -> gapless
                end else begin
                    r_wr_active <= 1'b0;
                end
            end
        end
    )

    //==========================================================================
    // AXI4 Slave Write Protocol Handler
    //==========================================================================

    axi4_slave_wr #(
        .SKID_DEPTH_AW      (SKID_DEPTH_AW),
        .SKID_DEPTH_W       (SKID_DEPTH_W),
        .SKID_DEPTH_B       (SKID_DEPTH_B),
        .AXI_ID_WIDTH       (AXI_ID_WIDTH),
        .AXI_ADDR_WIDTH     (AXI_ADDR_WIDTH),
        .AXI_DATA_WIDTH     (AXI_DATA_WIDTH),
        .AXI_USER_WIDTH     (AXI_USER_WIDTH)
    ) u_axi4_slave_wr (
        .aclk               (aclk),
        .aresetn            (aresetn),

        .s_axi_awid         (s_axi_awid),
        .s_axi_awaddr       (s_axi_awaddr),
        .s_axi_awlen        (s_axi_awlen),
        .s_axi_awsize       (s_axi_awsize),
        .s_axi_awburst      (s_axi_awburst),
        .s_axi_awlock       (s_axi_awlock),
        .s_axi_awcache      (s_axi_awcache),
        .s_axi_awprot       (s_axi_awprot),
        .s_axi_awqos        (s_axi_awqos),
        .s_axi_awregion     (s_axi_awregion),
        .s_axi_awuser       (s_axi_awuser),
        .s_axi_awvalid      (s_axi_awvalid),
        .s_axi_awready      (s_axi_awready),

        .s_axi_wdata        (s_axi_wdata),
        .s_axi_wstrb        (s_axi_wstrb),
        .s_axi_wlast        (s_axi_wlast),
        .s_axi_wuser        (s_axi_wuser),
        .s_axi_wvalid       (s_axi_wvalid),
        .s_axi_wready       (s_axi_wready),

        .s_axi_bid          (s_axi_bid),
        .s_axi_bresp        (s_axi_bresp),
        .s_axi_buser        (s_axi_buser),
        .s_axi_bvalid       (s_axi_bvalid),
        .s_axi_bready       (s_axi_bready),

        .fub_axi_awid       (fub_axi_awid),
        .fub_axi_awaddr     (fub_axi_awaddr),
        .fub_axi_awlen      (fub_axi_awlen),
        .fub_axi_awsize     (fub_axi_awsize),
        .fub_axi_awburst    (fub_axi_awburst),
        .fub_axi_awlock     (fub_axi_awlock),
        .fub_axi_awcache    (fub_axi_awcache),
        .fub_axi_awprot     (fub_axi_awprot),
        .fub_axi_awqos      (fub_axi_awqos),
        .fub_axi_awregion   (fub_axi_awregion),
        .fub_axi_awuser     (fub_axi_awuser),
        .fub_axi_awvalid    (fub_axi_awvalid),
        .fub_axi_awready    (fub_axi_awready),

        .fub_axi_wdata      (fub_axi_wdata),
        .fub_axi_wstrb      (fub_axi_wstrb),
        .fub_axi_wlast      (fub_axi_wlast),
        .fub_axi_wuser      (fub_axi_wuser),
        .fub_axi_wvalid     (fub_axi_wvalid),
        .fub_axi_wready     (fub_axi_wready),

        .fub_axi_bid        (fub_axi_bid),
        .fub_axi_bresp      (fub_axi_bresp),
        .fub_axi_buser      (fub_axi_buser),
        .fub_axi_bvalid     (fub_axi_bvalid),
        .fub_axi_bready     (fub_axi_bready),

        .busy               (busy)
    );

endmodule : axi4_slave_wr_crc_check
