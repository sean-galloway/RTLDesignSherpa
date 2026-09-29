// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: 2024-2025 sean galloway
//
// Formal AXI4 protocol model for bridge_1x2_rd
//
// This is a PROTOCOL MODEL — it defines how a correct 1x2 read bridge
// must behave, using assumptions for all ports. The assertions check
// cross-port consistency (e.g., address decode mutual exclusion).
//
// Purpose: validate that the AXI4 protocol rules and address decode
// constraints are self-consistent, and generate cover traces showing
// valid transaction flows through a bridge.
//
// When the bridge DUT becomes parseable by yosys, this model can be
// converted to: assume on inputs, assert on outputs.

module formal_bridge_1x2_rd (
    input logic aclk,
    input logic aresetn
);

    // =========================================================================
    // Master port: cpu_rd (read-only: AR + R channels)
    // =========================================================================
    logic [3:0]  m_arid, m_rid;
    logic [31:0] m_araddr, m_rdata;
    logic [7:0]  m_arlen;
    logic [2:0]  m_arsize;
    logic [1:0]  m_arburst, m_rresp;
    logic        m_arvalid, m_arready;
    logic        m_rvalid, m_rready, m_rlast;

    // Slave 0: ddr_rd  (0x00000000 - 0x7FFFFFFF)
    logic [3:0]  s0_arid, s0_rid;
    logic [31:0] s0_araddr, s0_rdata;
    logic [7:0]  s0_arlen;
    logic [2:0]  s0_arsize;
    logic [1:0]  s0_arburst, s0_rresp;
    logic        s0_arvalid, s0_arready;
    logic        s0_rvalid, s0_rready, s0_rlast;

    // Slave 1: sram_rd (0x80000000 - 0xFFFFFFFF)
    logic [3:0]  s1_arid, s1_rid;
    logic [31:0] s1_araddr, s1_rdata;
    logic [7:0]  s1_arlen;
    logic [2:0]  s1_arsize;
    logic [1:0]  s1_arburst, s1_rresp;
    logic        s1_arvalid, s1_arready;
    logic        s1_rvalid, s1_rready, s1_rlast;

    // =========================================================================
    // Formal infrastructure
    // =========================================================================
    reg [7:0] f_past_valid = 0;
    always @(posedge aclk)
        f_past_valid <= f_past_valid + (f_past_valid < 8'hFF);

    initial assume (!aresetn);
    always @(posedge aclk) begin
        if (f_past_valid >= 2) assume (aresetn);
    end

    // =========================================================================
    // Master AR assumptions (well-formed master)
    // =========================================================================
    always @(posedge aclk) begin
        if (f_past_valid > 0 && aresetn && $past(aresetn))
            if ($past(m_arvalid) && !$past(m_arready)) begin
                assume (m_arvalid);
                assume (m_araddr == $past(m_araddr));
                assume (m_arlen == $past(m_arlen));
                assume (m_arsize == $past(m_arsize));
                assume (m_arburst == $past(m_arburst));
                assume (m_arid == $past(m_arid));
            end
    end
    always @(posedge aclk) begin
        if (f_past_valid > 0 && $past(!aresetn))
            assume (!m_arvalid);
    end
    always @(posedge aclk) begin
        if (aresetn && m_arvalid) begin
            assume (m_arburst != 2'b11);
            assume ((8'h1 << m_arsize) <= 8'd4);
        end
    end

    // =========================================================================
    // Slave R assumptions (well-formed slaves)
    // =========================================================================
    // DDR slave R channel
    always @(posedge aclk) begin
        if (f_past_valid > 0 && aresetn && $past(aresetn))
            if ($past(s0_rvalid) && !$past(s0_rready)) begin
                assume (s0_rvalid);
                assume (s0_rdata == $past(s0_rdata));
                assume (s0_rresp == $past(s0_rresp));
                assume (s0_rlast == $past(s0_rlast));
                assume (s0_rid == $past(s0_rid));
            end
    end
    always @(posedge aclk) begin
        if (f_past_valid > 0 && $past(!aresetn))
            assume (!s0_rvalid);
    end

    // SRAM slave R channel
    always @(posedge aclk) begin
        if (f_past_valid > 0 && aresetn && $past(aresetn))
            if ($past(s1_rvalid) && !$past(s1_rready)) begin
                assume (s1_rvalid);
                assume (s1_rdata == $past(s1_rdata));
                assume (s1_rresp == $past(s1_rresp));
                assume (s1_rlast == $past(s1_rlast));
                assume (s1_rid == $past(s1_rid));
            end
    end
    always @(posedge aclk) begin
        if (f_past_valid > 0 && $past(!aresetn))
            assume (!s1_rvalid);
    end

    // =========================================================================
    // Bridge behavior model: address decode + forwarding
    // =========================================================================
    // A correct bridge forwards AR requests based on address:
    //   addr < 0x80000000 -> slave 0 (DDR)
    //   addr >= 0x80000000 -> slave 1 (SRAM)

    // Bridge output model: slave AR driven by address decode
    // Only one slave can be addressed at a time
    always @(posedge aclk) begin
        if (aresetn) begin
            // Address decode: DDR if addr < 0x80000000
            assume (s0_arvalid == (m_arvalid && (m_araddr < 32'h80000000)));
            assume (s1_arvalid == (m_arvalid && (m_araddr >= 32'h80000000)));
            // Forward address fields
            if (s0_arvalid) begin
                assume (s0_araddr == m_araddr);
                assume (s0_arlen == m_arlen);
                assume (s0_arsize == m_arsize);
            end
            if (s1_arvalid) begin
                assume (s1_araddr == m_araddr);
                assume (s1_arlen == m_arlen);
                assume (s1_arsize == m_arsize);
            end
        end
    end
    always @(posedge aclk) begin
        if (f_past_valid > 0 && $past(!aresetn)) begin
            assume (!s0_arvalid);
            assume (!s1_arvalid);
        end
    end

    // Master R valid stable
    always @(posedge aclk) begin
        if (f_past_valid > 0 && aresetn && $past(aresetn))
            if ($past(m_rvalid) && !$past(m_rready))
                assume (m_rvalid);
    end
    always @(posedge aclk) begin
        if (f_past_valid > 0 && $past(!aresetn))
            assume (!m_rvalid);
    end

    // =========================================================================
    // Cross-port assertions (bridge invariants)
    // =========================================================================

    // Address decode mutual exclusion: at most one slave gets AR
    always @(posedge aclk) begin
        if (aresetn)
            addr_mutex: assert (!(s0_arvalid && s1_arvalid));
    end

    // Address range: if DDR slave gets request, address must be < 0x80000000
    always @(posedge aclk) begin
        if (aresetn && s0_arvalid)
            addr_ddr_range: assert (s0_araddr < 32'h80000000);
    end

    // Address range: if SRAM slave gets request, address must be >= 0x80000000
    always @(posedge aclk) begin
        if (aresetn && s1_arvalid)
            addr_sram_range: assert (s1_araddr >= 32'h80000000);
    end

    // Note: both slaves can have pending R data simultaneously in buffered designs.
    // The bridge muxes responses — no assertion on simultaneous R valid.

    // =========================================================================
    // Cover: complete transaction flows
    // =========================================================================
    always @(posedge aclk) begin
        if (aresetn) begin
            // Master issues read request
            cp_m_ar: cover (m_arvalid && m_arready);
            // Master receives read data
            cp_m_r: cover (m_rvalid && m_rready);
            // DDR slave receives forwarded request
            cp_s0_ar: cover (s0_arvalid && s0_arready);
            // SRAM slave receives forwarded request
            cp_s1_ar: cover (s1_arvalid && s1_arready);
        end
    end

    // Complete DDR transaction: AR accepted then R returned
    always @(posedge aclk) begin
        if (f_past_valid > 0 && aresetn && $past(aresetn))
            cp_ddr_txn: cover (m_rvalid && m_rlast && $past(s0_arvalid && s0_arready));
    end

endmodule
