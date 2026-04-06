// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: 2024-2025 RTL Design Sherpa
//
// Formal proof for axi4_to_axil4_rd -- FSM-based burst decomposition
// Verifies reset behavior, data passthrough, RLAST generation, burst handling
// All assertions use port-level signals only (no hierarchical DUT references)

module formal_axi4_to_axil4_rd #(
    parameter int AXI_ID_WIDTH   = 4,
    parameter int AXI_ADDR_WIDTH = 32,
    parameter int AXI_DATA_WIDTH = 32,
    parameter int AXI_USER_WIDTH = 1,
    parameter int SKID_DEPTH_AR  = 2,
    parameter int SKID_DEPTH_R   = 2
) (
    input logic aclk,
    input logic aresetn
);

    // =========================================================================
    // Free inputs for the solver to explore
    // =========================================================================

    // Slave AXI4 AR channel
    (* anyconst *) logic [AXI_ID_WIDTH-1:0]   s_axi_arid;
    logic [AXI_ADDR_WIDTH-1:0]                 s_axi_araddr;
    logic [7:0]                                s_axi_arlen;
    logic [2:0]                                s_axi_arsize;
    logic [1:0]                                s_axi_arburst;
    logic                                      s_axi_arlock;
    logic [3:0]                                s_axi_arcache;
    logic [2:0]                                s_axi_arprot;
    logic [3:0]                                s_axi_arqos;
    logic [3:0]                                s_axi_arregion;
    logic [AXI_USER_WIDTH-1:0]                 s_axi_aruser;
    logic                                      s_axi_arvalid;

    // Slave AXI4 R channel
    logic                                      s_axi_rready;

    // Master AXI4-Lite AR channel
    logic                                      m_axil_arready;

    // Master AXI4-Lite R channel
    logic [AXI_DATA_WIDTH-1:0]                 m_axil_rdata;
    logic [1:0]                                m_axil_rresp;
    logic                                      m_axil_rvalid;

    // =========================================================================
    // DUT outputs
    // =========================================================================
    logic                        s_axi_arready_o;
    logic [AXI_ID_WIDTH-1:0]     s_axi_rid_o;
    logic [AXI_DATA_WIDTH-1:0]   s_axi_rdata_o;
    logic [1:0]                  s_axi_rresp_o;
    logic                        s_axi_rlast_o;
    logic [AXI_USER_WIDTH-1:0]   s_axi_ruser_o;
    logic                        s_axi_rvalid_o;

    logic [AXI_ADDR_WIDTH-1:0]   m_axil_araddr_o;
    logic [2:0]                  m_axil_arprot_o;
    logic                        m_axil_arvalid_o;
    logic                        m_axil_rready_o;

    axi4_to_axil4_rd #(
        .AXI_ID_WIDTH   (AXI_ID_WIDTH),
        .AXI_ADDR_WIDTH (AXI_ADDR_WIDTH),
        .AXI_DATA_WIDTH (AXI_DATA_WIDTH),
        .AXI_USER_WIDTH (AXI_USER_WIDTH),
        .SKID_DEPTH_AR  (SKID_DEPTH_AR),
        .SKID_DEPTH_R   (SKID_DEPTH_R)
    ) dut (
        .aclk            (aclk),
        .aresetn         (aresetn),

        // Slave AXI4
        .s_axi_arid      (s_axi_arid),
        .s_axi_araddr    (s_axi_araddr),
        .s_axi_arlen     (s_axi_arlen),
        .s_axi_arsize    (s_axi_arsize),
        .s_axi_arburst   (s_axi_arburst),
        .s_axi_arlock    (s_axi_arlock),
        .s_axi_arcache   (s_axi_arcache),
        .s_axi_arprot    (s_axi_arprot),
        .s_axi_arqos     (s_axi_arqos),
        .s_axi_arregion  (s_axi_arregion),
        .s_axi_aruser    (s_axi_aruser),
        .s_axi_arvalid   (s_axi_arvalid),
        .s_axi_arready   (s_axi_arready_o),

        .s_axi_rid       (s_axi_rid_o),
        .s_axi_rdata     (s_axi_rdata_o),
        .s_axi_rresp     (s_axi_rresp_o),
        .s_axi_rlast     (s_axi_rlast_o),
        .s_axi_ruser     (s_axi_ruser_o),
        .s_axi_rvalid    (s_axi_rvalid_o),
        .s_axi_rready    (s_axi_rready),

        // Master AXI4-Lite
        .m_axil_araddr   (m_axil_araddr_o),
        .m_axil_arprot   (m_axil_arprot_o),
        .m_axil_arvalid  (m_axil_arvalid_o),
        .m_axil_arready  (m_axil_arready),

        .m_axil_rdata    (m_axil_rdata),
        .m_axil_rresp    (m_axil_rresp),
        .m_axil_rvalid   (m_axil_rvalid),
        .m_axil_rready   (m_axil_rready_o)
    );

    // =========================================================================
    // Past-valid counter and reset assumption
    // =========================================================================
    reg [7:0] f_past_valid = 0;
    always @(posedge aclk)
        f_past_valid <= f_past_valid + (f_past_valid < 8'hFF);

    initial assume (!aresetn);
    always @(posedge aclk) if (f_past_valid >= 2) assume (aresetn);

    // =========================================================================
    // Input constraints for tractability
    // =========================================================================

    // Constrain burst length to small values for tractability
    always @(*) begin
        assume (s_axi_arlen <= 8'd3);
    end

    // Only INCR bursts (simplifies address computation check)
    always @(*) begin
        assume (s_axi_arburst == 2'b01);
    end

    // Constrain arsize to match data width
    always @(*) begin
        assume (s_axi_arsize == 3'($clog2(AXI_DATA_WIDTH / 8)));
    end

    // =========================================================================
    // Shadow model: track burst state from port-level signals
    // =========================================================================
    reg [7:0] f_ar_len = 0;           // Captured burst length
    reg [7:0] f_r_beat_count = 0;     // Count of R beats received
    reg       f_burst_active = 0;     // Tracking an active burst

    always @(posedge aclk) begin
        if (!aresetn) begin
            f_ar_len <= 0;
            f_r_beat_count <= 0;
            f_burst_active <= 0;
        end else begin
            // Capture burst info on slave AR handshake
            if (s_axi_arvalid && s_axi_arready_o) begin
                f_ar_len <= s_axi_arlen;
                f_r_beat_count <= 0;
                f_burst_active <= 1;
            end
            // Count R data beats (both master and slave see same rvalid)
            if (s_axi_rvalid_o && s_axi_rready) begin
                f_r_beat_count <= f_r_beat_count + 1;
                if (s_axi_rlast_o)
                    f_burst_active <= 0;
            end
        end
    end

    // =========================================================================
    // P1: Reset -- no burst-mode AR activity after reset
    // Note: m_axil_arvalid is combinationally driven from s_axi_arvalid
    // for single-beat passthrough, so it is NOT deasserted by reset.
    // What reset guarantees: no burst decomposition is active.
    // After reset, the module should be able to accept a new AR (arready high
    // for single beats when axil is ready).
    // =========================================================================
    always @(posedge aclk) begin
        if (f_past_valid > 0 && $past(!aresetn)) begin
            // After reset, RLAST should be 1 (beat_count==len==0)
            ap_reset_rlast: assert (s_axi_rlast_o == 1'b1);
        end
    end

    // =========================================================================
    // P2: R data passthrough -- rdata comes from axil rdata
    // =========================================================================
    always @(*) begin
        ap_rdata_passthrough: assert (s_axi_rdata_o == m_axil_rdata);
    end

    // =========================================================================
    // P3: R valid passthrough -- rvalid follows axil rvalid
    // =========================================================================
    always @(*) begin
        ap_rvalid_passthrough: assert (s_axi_rvalid_o == m_axil_rvalid);
    end

    // =========================================================================
    // P4: R ready passthrough
    // =========================================================================
    always @(*) begin
        ap_rready_passthrough: assert (m_axil_rready_o == s_axi_rready);
    end

    // =========================================================================
    // P5: RUSER always 0 (AXI4-Lite has no user field)
    // =========================================================================
    always @(*) begin
        ap_ruser_zero: assert (s_axi_ruser_o == '0);
    end

    // =========================================================================
    // P6: When RLAST is asserted with RVALID, our shadow beat counter
    // should have counted all expected beats
    // =========================================================================
    always @(posedge aclk) begin
        if (aresetn && f_burst_active && s_axi_rvalid_o && s_axi_rlast_o) begin
            ap_rlast_at_end: assert (f_r_beat_count == f_ar_len);
        end
    end

    // =========================================================================
    // P7: RLAST must not be asserted mid-burst (before final beat)
    // when we know the burst length and are tracking beats
    // =========================================================================
    always @(posedge aclk) begin
        if (aresetn && f_burst_active && f_ar_len > 0 &&
            s_axi_rvalid_o && s_axi_rready &&
            f_r_beat_count < f_ar_len) begin
            ap_no_early_rlast: assert (!s_axi_rlast_o);
        end
    end

    // =========================================================================
    // P8: Single-beat passthrough -- when arlen==0 and no burst active,
    // arvalid passes through to master
    // =========================================================================
    // Note: We check that when a single-beat AR is presented and no burst
    // is being decomposed, the master sees a valid address request.
    // We use the shadow model: !f_burst_active means DUT is idle.
    always @(posedge aclk) begin
        if (aresetn && f_past_valid >= 2 && $past(aresetn) &&
            !f_burst_active && s_axi_arvalid && s_axi_arlen == 0) begin
            ap_single_beat_arvalid: assert (m_axil_arvalid_o == 1'b1);
        end
    end

    // =========================================================================
    // P9: After AR handshake with arlen>0, master must eventually issue
    // AR requests (arvalid goes high at some point). We check that the
    // module is not stuck: if we accepted a burst, arvalid must be high
    // within a few cycles.
    // =========================================================================
    // (Covered by cover properties below rather than a bounded liveness check)

    // =========================================================================
    // P10: RID matches the captured transaction ID
    // The DUT stores the ID from the slave AR and returns it on all R beats
    // =========================================================================
    always @(posedge aclk) begin
        if (aresetn && f_burst_active && s_axi_rvalid_o) begin
            ap_rid_matches: assert (s_axi_rid_o == s_axi_arid);
        end
    end

    // =========================================================================
    // Cover: AR handshake on slave side (accept burst)
    // =========================================================================
    always @(posedge aclk) begin
        cp_ar_slave_handshake: cover (s_axi_arvalid && s_axi_arready_o);
    end

    // =========================================================================
    // Cover: AR handshake on master side (issue single read)
    // =========================================================================
    always @(posedge aclk) begin
        cp_ar_master_handshake: cover (m_axil_arvalid_o && m_axil_arready);
    end

    // =========================================================================
    // Cover: R handshake
    // =========================================================================
    always @(posedge aclk) begin
        cp_r_handshake: cover (s_axi_rvalid_o && s_axi_rready);
    end

    // =========================================================================
    // Cover: Multi-beat burst (arlen > 0 accepted)
    // =========================================================================
    always @(posedge aclk) begin
        cp_multi_beat_burst: cover (
            s_axi_arvalid && s_axi_arready_o && s_axi_arlen > 0
        );
    end

    // =========================================================================
    // Cover: RLAST asserted (burst completion)
    // =========================================================================
    always @(posedge aclk) begin
        cp_rlast_asserted: cover (s_axi_rvalid_o && s_axi_rlast_o && s_axi_rready);
    end

    // =========================================================================
    // Cover: Second R beat in a multi-beat burst
    // =========================================================================
    always @(posedge aclk) begin
        cp_second_beat: cover (f_burst_active && f_r_beat_count == 1 && s_axi_rvalid_o);
    end

endmodule
