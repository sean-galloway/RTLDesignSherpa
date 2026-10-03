// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: 2026 sean galloway
//
// Module: rs_axi4_write_engine
// Description: Drains the codec cores' symbol stream into an AXI4 region.
//
//   The other half of the AXI4 boundary PRD D9 calls for, and the mirror of
//   rs_axi4_read_engine: a job is a destination address plus a beat count,
//   walked as INCR bursts of at most cfg_burst_len beats, with W data taken
//   straight from the core.
//
//   AW and W are DECOUPLED and walk the same job independently, which is the
//   arrangement axi4_master_wr_pattern_gen uses. Neither needs a queue of
//   burst lengths between them: both derive their burst boundaries from the
//   same (cfg_beats, cfg_burst_len) pair, so two counters stay in step by
//   construction. AW then runs as fast as awready allows while W runs at the
//   core's rate.
//
//   WSTRB is all ones. Every write is a full word, which is what lets the
//   memory on the far side run sdpram_core with USE_WSTRB = 0 and infer block
//   RAM -- at the default that block mixes a full-word clear and a
//   byte-granular write on a muxed address, Vivado cannot map it to a BRAM
//   write port, and a 64 KB instance costs ~23k LUTs of distributed RAM. A
//   caller whose final beat is partial pads to the beat and tells the far end
//   how many symbols matter out of band.
//
// Parameters:
//   ADDR_WIDTH       AXI address width
//   DATA_WIDTH       AXI and stream data width; one beat in, one beat out
//   ID_WIDTH         AXI id width
//   MAX_OUTSTANDING  AWs in flight, bounded so the slave is not flooded
//
//   No skid-depth parameters: this engine drives AW/W/B directly and the
//   enclosing top adds axi4_master_wr if it wants registered channels.
//
// Notes:
//   - cfg_done waits for the B responses, not the last W beat. A job is not
//     finished until the slave has acknowledged it; declaring done on W would
//     let a host read a destination region the writes had not yet reached.
//   - in_last is accepted and ignored. The job's beat count defines the
//     region, and honouring a stream boundary as well would give two sources
//     of truth for where the writes stop. The core's block boundary is the
//     reader's problem, and rs_axi4_read_engine reconstructs it from a beat
//     count for exactly that reason.
//   - A non-OKAY BRESP sets resp_err sticky and the job still completes, so
//     cfg_done always arrives.
module rs_axi4_write_engine #(
    parameter int ADDR_WIDTH      = 32,
    parameter int DATA_WIDTH      = 32,
    parameter int ID_WIDTH        = 4,
    parameter int MAX_OUTSTANDING = 4,
    parameter int USER_WIDTH      = 1
) (
    input  logic                    aclk,
    input  logic                    aresetn,

    // -- job ---------------------------------------------------------------
    input  logic                    cfg_start,          // one-cycle pulse
    input  logic [ADDR_WIDTH-1:0]   cfg_dst_addr,
    input  logic [31:0]             cfg_beats,          // total beats to write
    input  logic [7:0]              cfg_burst_len,      // beats per burst, 1..255
    input  logic [ID_WIDTH-1:0]     cfg_axi_id,
    input  logic [2:0]              cfg_axi_size,
    output logic                    cfg_done,
    output logic                    resp_err,           // sticky, cleared by cfg_start

    // -- symbol stream from the core ---------------------------------------
    input  logic                    in_valid,
    output logic                    in_ready,
    input  logic [DATA_WIDTH-1:0]   in_data,
    input  logic                    in_last,            // accepted and ignored

    // -- AXI4 write master -------------------------------------------------
    output logic [ID_WIDTH-1:0]     m_axi_awid,
    output logic [ADDR_WIDTH-1:0]   m_axi_awaddr,
    output logic [7:0]              m_axi_awlen,
    output logic [2:0]              m_axi_awsize,
    output logic [1:0]              m_axi_awburst,
    // Full AW attribute set for the same reason as the read engine: the house
    // axi4_master_wr wrapper and the AXI4 slave BFMs expect it.
    output logic                    m_axi_awlock,
    output logic [3:0]              m_axi_awcache,
    output logic [2:0]              m_axi_awprot,
    output logic [3:0]              m_axi_awqos,
    output logic [3:0]              m_axi_awregion,
    output logic [USER_WIDTH-1:0]   m_axi_awuser,
    output logic                    m_axi_awvalid,
    input  logic                    m_axi_awready,
    output logic [DATA_WIDTH-1:0]   m_axi_wdata,
    output logic [DATA_WIDTH/8-1:0] m_axi_wstrb,
    output logic                    m_axi_wlast,
    output logic [USER_WIDTH-1:0]   m_axi_wuser,
    output logic                    m_axi_wvalid,
    input  logic                    m_axi_wready,
    input  logic [ID_WIDTH-1:0]     m_axi_bid,
    input  logic [1:0]              m_axi_bresp,
    input  logic [USER_WIDTH-1:0]   m_axi_buser,
    input  logic                    m_axi_bvalid,
    output logic                    m_axi_bready
);

    localparam int OSW = $clog2(MAX_OUTSTANDING + 1);

    // =========================================================================
    // AW side
    // =========================================================================
    logic [ADDR_WIDTH-1:0] r_aw_addr;
    logic [31:0]           r_aw_left;       // beats still to REQUEST
    logic [OSW-1:0]        r_outstanding;   // AWs issued minus Bs received
    logic                  r_running;

    logic [8:0] w_aw_len;
    always_comb begin
        w_aw_len = {1'b0, cfg_burst_len};
        if (w_aw_len == 9'd0)            w_aw_len = 9'd1;
        if (32'(w_aw_len) > r_aw_left)   w_aw_len = 9'(r_aw_left);
    end

    logic w_aw_fire;
    assign m_axi_awvalid = r_running && (r_aw_left != '0)
                        && (r_outstanding < OSW'(MAX_OUTSTANDING));
    assign w_aw_fire     = m_axi_awvalid && m_axi_awready;
    assign m_axi_awid    = cfg_axi_id;
    assign m_axi_awaddr  = r_aw_addr;
    assign m_axi_awlen   = 8'(w_aw_len - 9'd1);
    assign m_axi_awsize  = cfg_axi_size;
    assign m_axi_awburst  = 2'b01;                  // INCR
    assign m_axi_awlock   = 1'b0;
    assign m_axi_awcache  = 4'b0011;
    assign m_axi_awprot   = 3'b000;
    assign m_axi_awqos    = 4'b0000;
    assign m_axi_awregion = 4'b0000;
    assign m_axi_awuser   = '0;
    assign m_axi_wuser    = '0;

    always_ff @(posedge aclk or negedge aresetn) begin
        if (!aresetn) begin
            r_aw_addr <= '0; r_aw_left <= '0; r_running <= 1'b0;
        end else if (cfg_start) begin
            r_aw_addr <= cfg_dst_addr;
            r_aw_left <= cfg_beats;
            r_running <= (cfg_beats != '0);
        end else if (w_aw_fire) begin
            r_aw_addr <= r_aw_addr + (ADDR_WIDTH'(w_aw_len) << cfg_axi_size);
            r_aw_left <= r_aw_left - 32'(w_aw_len);
        end
    end

    // =========================================================================
    // W side: an independent walk of the same job, so no burst-length queue
    // =========================================================================
    logic [31:0] r_w_left;        // beats still to SEND
    logic [8:0]  r_w_in_burst;    // beats sent in the current burst

    logic [8:0] w_w_len;
    always_comb begin
        w_w_len = {1'b0, cfg_burst_len};
        if (w_w_len == 9'd0)           w_w_len = 9'd1;
        if (32'(w_w_len) > r_w_left)   w_w_len = 9'(r_w_left);
    end

    logic w_w_fire;
    assign m_axi_wvalid = in_valid && (r_w_left != '0);
    assign in_ready     = m_axi_wready && (r_w_left != '0);
    assign w_w_fire     = m_axi_wvalid && m_axi_wready;
    assign m_axi_wdata  = in_data;
    assign m_axi_wstrb  = {(DATA_WIDTH/8){1'b1}};
    assign m_axi_wlast  = (r_w_in_burst + 9'd1) >= w_w_len;

    always_ff @(posedge aclk or negedge aresetn) begin
        if (!aresetn) begin
            r_w_left <= '0; r_w_in_burst <= '0;
        end else if (cfg_start) begin
            r_w_left <= cfg_beats; r_w_in_burst <= '0;
        end else if (w_w_fire) begin
            r_w_left     <= r_w_left - 32'd1;
            r_w_in_burst <= m_axi_wlast ? 9'd0 : r_w_in_burst + 9'd1;
        end
    end

    // =========================================================================
    // B side and completion
    // =========================================================================
    logic w_b_fire;

    assign m_axi_bready = 1'b1;   // nothing here can stall a response
    assign w_b_fire     = m_axi_bvalid && m_axi_bready;

    always_ff @(posedge aclk or negedge aresetn) begin
        if (!aresetn) begin
            r_outstanding <= '0;
        end else if (cfg_start) begin
            r_outstanding <= '0;
        end else if (w_aw_fire && !w_b_fire) begin
            r_outstanding <= r_outstanding + OSW'(1);
        end else if (w_b_fire && !w_aw_fire) begin
            r_outstanding <= r_outstanding - OSW'(1);
        end
    end

    // Completion WITHOUT counting bursts.
    //
    // The obvious form -- precompute ceil(beats / burst_len) at cfg_start and
    // count B responses down -- costs a 32-bit combinational DIVIDER on the
    // path from the block-count register to this counter's load. Measured on
    // the Nexys A7 at 100 MHz that was 105 CARRY4 cells plus a DSP, 61.7 ns of
    // data path, and a worst slack of -51.8 ns with 128 failing endpoints. It
    // was the whole timing failure of the AXI4 flavour's first synthesis.
    //
    // There is nothing to divide for. The job is finished when every AW has
    // been issued (r_aw_left is zero) and every one has been answered
    // (r_outstanding is zero). r_active distinguishes "finished" from "not
    // started", since both leave those two counters at zero.
    logic r_active;

    always_ff @(posedge aclk or negedge aresetn) begin
        if (!aresetn) begin
            r_active <= 1'b0; cfg_done <= 1'b0; resp_err <= 1'b0;
        end else if (cfg_start) begin
            r_active <= (cfg_beats != '0);
            cfg_done <= (cfg_beats == '0);        // an empty job is already done
            resp_err <= 1'b0;
        end else begin
            if (w_b_fire && (m_axi_bresp != 2'b00)) resp_err <= 1'b1;
            if (r_active && (r_aw_left == '0) && (r_outstanding == '0)) begin
                r_active <= 1'b0;
                cfg_done <= 1'b1;
            end
        end
    end

    // fields the engine does not inspect
    logic unused_w;
    assign unused_w = in_last ^ (^m_axi_bid) ^ (^m_axi_buser);

endmodule
