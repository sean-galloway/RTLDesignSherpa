// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: 2026 sean galloway
//
// Module: rs_axi4_read_engine
// Description: Turns an AXI4 read job into the codec cores' symbol stream.
//
//   One half of the AXI4 boundary PRD D9 calls for: a job is a source address
//   plus a beat count, and the engine walks it as INCR bursts of at most
//   cfg_burst_len beats, handing each R beat straight to the core as a
//   valid/ready symbol beat with out_last marking a block boundary.
//
//   Why this is not axi4_master_rd_crc_check with a different data port, even
//   though that block has exactly the right control shape (cfg_start pulse,
//   cfg_done, outstanding bounded, addresses walked): its data sink is an
//   internal CRC and its only stream-shaped port is a DEBUG capture FIFO
//   whose write-ready is discarded, so it drops records when full. A lossy
//   tap is fine for a bench and fatal for a datapath. What is borrowed here
//   is the control skeleton and the cfg_* naming, so a consumer that has
//   programmed one has programmed the other.
//
//   Addressing is a linear burst-base increment rather than dma_address_gen.
//   A codec job reads one contiguous region, so the strided and wrapped
//   dimensions that block exists to provide would be dead logic on the
//   critical path. Strided sources become a parameter the day something
//   needs them.
//
// Parameters:
//   ADDR_WIDTH       AXI address width
//   DATA_WIDTH       AXI and stream data width; one beat in, one beat out
//   ID_WIDTH         AXI id width
//   MAX_OUTSTANDING  ARs in flight, bounded so R cannot outrun the core
//
//   There are deliberately no skid-depth parameters. This engine drives the
//   AR/R channels directly and the enclosing top adds axi4_master_rd if it
//   wants registered channels, rather than this module claiming to own skids
//   it does not instantiate.
//
// Notes:
//   - R beats are NOT buffered here beyond the skid in axi4_master_rd: rready
//     is the core's ready, so the core back-pressures the bus directly. That
//     is deliberate. Buffering would hide a stalled core behind a FIFO that
//     eventually overflows, which is the failure mode that cost a bring-up
//     in the Nexys A7 loop harness.
//   - cfg_beats_per_block places out_last. It is a beat count, not a symbol
//     count: a caller with a partial final beat pads to the beat and tells
//     the far end how many symbols matter out of band.
//   - A non-OKAY RRESP sets resp_err sticky and the job still runs to
//     completion, so cfg_done always arrives and a host never hangs waiting
//     on it. The error is the evidence; a stall would be a second failure.
module rs_axi4_read_engine #(
    parameter int ADDR_WIDTH      = 32,
    parameter int DATA_WIDTH      = 32,
    parameter int ID_WIDTH        = 4,
    parameter int MAX_OUTSTANDING = 4,
    parameter int USER_WIDTH      = 1
) (
    input  logic                    aclk,
    input  logic                    aresetn,

    // -- job ---------------------------------------------------------------
    input  logic                    cfg_start,             // one-cycle pulse
    input  logic [ADDR_WIDTH-1:0]   cfg_src_addr,
    input  logic [31:0]             cfg_beats,             // total beats to read
    input  logic [7:0]              cfg_burst_len,         // beats per burst, 1..255
    input  logic [15:0]             cfg_beats_per_block,   // where out_last falls
    input  logic [ID_WIDTH-1:0]     cfg_axi_id,
    input  logic [2:0]              cfg_axi_size,
    output logic                    cfg_done,
    output logic                    resp_err,              // sticky, cleared by cfg_start

    // -- symbol stream to the core ----------------------------------------
    output logic                    out_valid,
    input  logic                    out_ready,
    output logic [DATA_WIDTH-1:0]   out_data,
    output logic                    out_last,

    // -- AXI4 read master --------------------------------------------------
    output logic [ID_WIDTH-1:0]     m_axi_arid,
    output logic [ADDR_WIDTH-1:0]   m_axi_araddr,
    output logic [7:0]              m_axi_arlen,
    output logic [2:0]              m_axi_arsize,
    output logic [1:0]              m_axi_arburst,
    // The rest of the AR attribute set. Driven to constants rather than
    // omitted: axi4_master_rd and the AXI4 slave BFMs both expect the full
    // surface, and a module that leaves them out forces every consumer to
    // tie them off at the instantiation instead of once here.
    output logic                    m_axi_arlock,
    output logic [3:0]              m_axi_arcache,
    output logic [2:0]              m_axi_arprot,
    output logic [3:0]              m_axi_arqos,
    output logic [3:0]              m_axi_arregion,
    output logic [USER_WIDTH-1:0]   m_axi_aruser,
    output logic                    m_axi_arvalid,
    input  logic                    m_axi_arready,
    input  logic [ID_WIDTH-1:0]     m_axi_rid,
    input  logic [DATA_WIDTH-1:0]   m_axi_rdata,
    input  logic [1:0]              m_axi_rresp,
    input  logic                    m_axi_rlast,
    input  logic [USER_WIDTH-1:0]   m_axi_ruser,
    input  logic                    m_axi_rvalid,
    output logic                    m_axi_rready
);

    localparam int OSW = $clog2(MAX_OUTSTANDING + 1);

    // =========================================================================
    // AR side: walk burst bases until every beat of the job is requested
    // =========================================================================
    logic [ADDR_WIDTH-1:0] r_ar_addr;
    logic [31:0]           r_ar_left;      // beats still to REQUEST
    logic [OSW-1:0]        r_outstanding;  // ARs issued minus RLASTs seen
    logic                  r_running;

    // beats in this burst: the cap, or whatever is left if that is smaller
    logic [8:0] w_this_len;
    always_comb begin
        w_this_len = {1'b0, cfg_burst_len};
        if (w_this_len == 9'd0)                w_this_len = 9'd1;   // 0 is not a burst
        if (32'(w_this_len) > r_ar_left)       w_this_len = 9'(r_ar_left);
    end

    logic w_ar_fire;
    assign m_axi_arvalid = r_running && (r_ar_left != '0) && (r_outstanding < OSW'(MAX_OUTSTANDING));
    assign w_ar_fire     = m_axi_arvalid && m_axi_arready;
    assign m_axi_arid    = cfg_axi_id;
    assign m_axi_araddr  = r_ar_addr;
    assign m_axi_arlen   = 8'(w_this_len - 9'd1);   // AXI encodes beats-1
    assign m_axi_arsize  = cfg_axi_size;
    assign m_axi_arburst = 2'b01;                   // INCR
    assign m_axi_arlock   = 1'b0;                   // normal access
    assign m_axi_arcache  = 4'b0011;                // normal, non-cacheable, bufferable
    assign m_axi_arprot   = 3'b000;                 // unprivileged, secure, data
    assign m_axi_arqos    = 4'b0000;
    assign m_axi_arregion = 4'b0000;
    assign m_axi_aruser   = '0;

    always_ff @(posedge aclk or negedge aresetn) begin
        if (!aresetn) begin
            r_ar_addr <= '0; r_ar_left <= '0; r_running <= 1'b0;
        end else if (cfg_start) begin
            r_ar_addr <= cfg_src_addr;
            r_ar_left <= cfg_beats;
            // stays set until the next job; arvalid is gated on r_ar_left too,
            // so nothing is issued once the last burst has been requested
            r_running <= (cfg_beats != '0);
        end else if (w_ar_fire) begin
            // one burst covers w_this_len beats of 2**cfg_axi_size bytes each
            r_ar_addr <= r_ar_addr + (ADDR_WIDTH'(w_this_len) << cfg_axi_size);
            r_ar_left <= r_ar_left - 32'(w_this_len);
        end
    end

    // =========================================================================
    // R side: straight through to the core, so the core back-pressures the bus
    // =========================================================================
    assign m_axi_rready = out_ready;
    assign out_valid    = m_axi_rvalid;
    assign out_data     = m_axi_rdata;

    logic w_r_fire;
    assign w_r_fire = m_axi_rvalid && m_axi_rready;

    always_ff @(posedge aclk or negedge aresetn) begin
        if (!aresetn)                          r_outstanding <= '0;
        else if (cfg_start)                    r_outstanding <= '0;
        else if (w_ar_fire && !(w_r_fire && m_axi_rlast)) r_outstanding <= r_outstanding + OSW'(1);
        else if (w_r_fire && m_axi_rlast && !w_ar_fire)   r_outstanding <= r_outstanding - OSW'(1);
    end

    // =========================================================================
    // Block boundaries and completion
    //
    // out_last is placed by COUNTING delivered beats, not by m_axi_rlast: a
    // burst boundary is an artefact of cfg_burst_len and has nothing to do
    // with where a codeword ends. Tying the two together is the bug that
    // makes a decoder work at one burst length and frame-error at another.
    // =========================================================================
    logic [15:0] r_in_block;      // beats delivered in the current block
    logic [31:0] r_beats_left;    // beats still to DELIVER

    // NOT qualified by the handshake: out_valid already says the beat is
    // there, and a `last` that moves with `ready` violates the streaming
    // contract -- a consumer sampling last while stalled would see it drop.
    // A zero block length would make every beat last, so it is floored at 1.
    logic [15:0] w_block_len;
    assign w_block_len = (cfg_beats_per_block == 16'd0) ? 16'd1 : cfg_beats_per_block;
    assign out_last    = (r_in_block + 16'd1) >= w_block_len;

    always_ff @(posedge aclk or negedge aresetn) begin
        if (!aresetn) begin
            r_in_block <= '0; r_beats_left <= '0; cfg_done <= 1'b0; resp_err <= 1'b0;
        end else if (cfg_start) begin
            r_in_block <= '0; r_beats_left <= cfg_beats; cfg_done <= 1'b0; resp_err <= 1'b0;
        end else begin
            if (w_r_fire) begin
                r_in_block   <= out_last ? 16'd0 : r_in_block + 16'd1;
                r_beats_left <= r_beats_left - 32'd1;
                if (m_axi_rresp != 2'b00) resp_err <= 1'b1;
                // done on the LAST delivered beat, not the last AR: the job is
                // finished when the data has reached the core
                if (r_beats_left == 32'd1) begin
                    cfg_done  <= 1'b1;
                end
            end
        end
    end

    // unused AXI fields the engine does not inspect
    logic unused_r;
    assign unused_r = (^m_axi_rid) ^ (^m_axi_ruser);

endmodule
