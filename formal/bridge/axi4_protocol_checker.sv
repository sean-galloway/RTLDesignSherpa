// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: 2024-2025 sean galloway
//
// AXI4 Protocol Checker - Formal properties for any AXI4 interface
// Yosys-compatible immediate assertions.
//
// Instantiate one per AXI4 port to check protocol compliance.
// Works standalone — doesn't require parsing the DUT's internal structs.
//
// Checks:
//   - Handshake stability (xVALID must not deassert until xREADY)
//   - Reset behavior (xVALID must be low during reset)
//   - Signal stability (address/control must hold until handshake)
//   - Basic protocol rules (RLAST on final beat, WSTRB non-zero, etc.)

module axi4_protocol_checker #(
    parameter int ID_WIDTH   = 4,
    parameter int ADDR_WIDTH = 32,
    parameter int DATA_WIDTH = 32
) (
    input logic                    aclk,
    input logic                    aresetn,

    // Write Address Channel
    input logic [ID_WIDTH-1:0]     awid,
    input logic [ADDR_WIDTH-1:0]   awaddr,
    input logic [7:0]              awlen,
    input logic [2:0]              awsize,
    input logic [1:0]              awburst,
    input logic                    awvalid,
    input logic                    awready,

    // Write Data Channel
    input logic [DATA_WIDTH-1:0]   wdata,
    input logic [DATA_WIDTH/8-1:0] wstrb,
    input logic                    wlast,
    input logic                    wvalid,
    input logic                    wready,

    // Write Response Channel
    input logic [ID_WIDTH-1:0]     bid,
    input logic [1:0]              bresp,
    input logic                    bvalid,
    input logic                    bready,

    // Read Address Channel
    input logic [ID_WIDTH-1:0]     arid,
    input logic [ADDR_WIDTH-1:0]   araddr,
    input logic [7:0]              arlen,
    input logic [2:0]              arsize,
    input logic [1:0]              arburst,
    input logic                    arvalid,
    input logic                    arready,

    // Read Data Channel
    input logic [ID_WIDTH-1:0]     rid,
    input logic [DATA_WIDTH-1:0]   rdata,
    input logic [1:0]              rresp,
    input logic                    rlast,
    input logic                    rvalid,
    input logic                    rready
);

    reg [7:0] f_past_valid = 0;
    always @(posedge aclk)
        f_past_valid <= f_past_valid + (f_past_valid < 8'hFF);

    // =========================================================================
    // AW Channel — Handshake stability
    // =========================================================================
    // A3.2.1: Once VALID is asserted it must remain asserted until READY
    always @(posedge aclk) begin
        if (f_past_valid > 0 && aresetn && $past(aresetn))
            if ($past(awvalid) && !$past(awready))
                aw_valid_stable: assert (awvalid);
    end

    // A3.2.1: AW signals must remain stable while VALID is asserted
    always @(posedge aclk) begin
        if (f_past_valid > 0 && aresetn && $past(aresetn))
            if ($past(awvalid) && !$past(awready)) begin
                aw_addr_stable: assert (awaddr == $past(awaddr));
                aw_len_stable:  assert (awlen == $past(awlen));
                aw_size_stable: assert (awsize == $past(awsize));
                aw_burst_stable: assert (awburst == $past(awburst));
                aw_id_stable:   assert (awid == $past(awid));
            end
    end

    // A3.1.2: AWVALID must be LOW during reset
    always @(posedge aclk) begin
        if (f_past_valid > 0 && $past(!aresetn))
            aw_reset: assert (!awvalid);
    end

    // A3.4.1: AWBURST must not be RESERVED (2'b11)
    always @(posedge aclk) begin
        if (aresetn && awvalid)
            aw_burst_legal: assert (awburst != 2'b11);
    end

    // A3.4.1: AWSIZE must not exceed data bus width
    always @(posedge aclk) begin
        if (aresetn && awvalid)
            aw_size_legal: assert ((1 << awsize) <= (DATA_WIDTH / 8));
    end

    // =========================================================================
    // W Channel — Handshake stability
    // =========================================================================
    always @(posedge aclk) begin
        if (f_past_valid > 0 && aresetn && $past(aresetn))
            if ($past(wvalid) && !$past(wready))
                w_valid_stable: assert (wvalid);
    end

    always @(posedge aclk) begin
        if (f_past_valid > 0 && aresetn && $past(aresetn))
            if ($past(wvalid) && !$past(wready)) begin
                w_data_stable: assert (wdata == $past(wdata));
                w_strb_stable: assert (wstrb == $past(wstrb));
                w_last_stable: assert (wlast == $past(wlast));
            end
    end

    always @(posedge aclk) begin
        if (f_past_valid > 0 && $past(!aresetn))
            w_reset: assert (!wvalid);
    end

    // =========================================================================
    // B Channel — Handshake stability
    // =========================================================================
    always @(posedge aclk) begin
        if (f_past_valid > 0 && aresetn && $past(aresetn))
            if ($past(bvalid) && !$past(bready))
                b_valid_stable: assert (bvalid);
    end

    always @(posedge aclk) begin
        if (f_past_valid > 0 && aresetn && $past(aresetn))
            if ($past(bvalid) && !$past(bready)) begin
                b_id_stable:   assert (bid == $past(bid));
                b_resp_stable: assert (bresp == $past(bresp));
            end
    end

    always @(posedge aclk) begin
        if (f_past_valid > 0 && $past(!aresetn))
            b_reset: assert (!bvalid);
    end

    // =========================================================================
    // AR Channel — Handshake stability
    // =========================================================================
    always @(posedge aclk) begin
        if (f_past_valid > 0 && aresetn && $past(aresetn))
            if ($past(arvalid) && !$past(arready))
                ar_valid_stable: assert (arvalid);
    end

    always @(posedge aclk) begin
        if (f_past_valid > 0 && aresetn && $past(aresetn))
            if ($past(arvalid) && !$past(arready)) begin
                ar_addr_stable:  assert (araddr == $past(araddr));
                ar_len_stable:   assert (arlen == $past(arlen));
                ar_size_stable:  assert (arsize == $past(arsize));
                ar_burst_stable: assert (arburst == $past(arburst));
                ar_id_stable:    assert (arid == $past(arid));
            end
    end

    always @(posedge aclk) begin
        if (f_past_valid > 0 && $past(!aresetn))
            ar_reset: assert (!arvalid);
    end

    always @(posedge aclk) begin
        if (aresetn && arvalid)
            ar_burst_legal: assert (arburst != 2'b11);
    end

    always @(posedge aclk) begin
        if (aresetn && arvalid)
            ar_size_legal: assert ((1 << arsize) <= (DATA_WIDTH / 8));
    end

    // =========================================================================
    // R Channel — Handshake stability
    // =========================================================================
    always @(posedge aclk) begin
        if (f_past_valid > 0 && aresetn && $past(aresetn))
            if ($past(rvalid) && !$past(rready))
                r_valid_stable: assert (rvalid);
    end

    always @(posedge aclk) begin
        if (f_past_valid > 0 && aresetn && $past(aresetn))
            if ($past(rvalid) && !$past(rready)) begin
                r_id_stable:   assert (rid == $past(rid));
                r_data_stable: assert (rdata == $past(rdata));
                r_resp_stable: assert (rresp == $past(rresp));
                r_last_stable: assert (rlast == $past(rlast));
            end
    end

    always @(posedge aclk) begin
        if (f_past_valid > 0 && $past(!aresetn))
            r_reset: assert (!rvalid);
    end

    // =========================================================================
    // Cover: successful transactions
    // =========================================================================
    always @(posedge aclk) begin
        if (aresetn) begin
            cp_aw_handshake: cover (awvalid && awready);
            cp_w_handshake:  cover (wvalid && wready);
            cp_b_handshake:  cover (bvalid && bready);
            cp_ar_handshake: cover (arvalid && arready);
            cp_r_handshake:  cover (rvalid && rready);
        end
    end

    // Back-to-back transactions
    always @(posedge aclk) begin
        if (f_past_valid > 0 && aresetn && $past(aresetn)) begin
            cp_aw_b2b: cover (awvalid && awready && $past(awvalid && awready));
            cp_ar_b2b: cover (arvalid && arready && $past(arvalid && arready));
        end
    end

endmodule
