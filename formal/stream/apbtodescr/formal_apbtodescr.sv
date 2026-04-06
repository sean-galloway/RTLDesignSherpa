// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: 2024-2025 sean galloway
//
// Formal wrapper for apbtodescr (yosys-compatible)
// Run with: sby apbtodescr.sby
//
// NOTE: Yosys does not support cross-module hierarchical references
//       (e.g., dut.r_state). All properties are expressed using
//       observable I/O signals only. The FSM state is fully observable
//       through apb_cmd_ready, apb_rsp_valid, desc_apb_valid, and
//       apb_descriptor_kickoff_hit which are direct combinational
//       functions of r_state.
//
// Properties verified:
//   P1: Reset - cmd_ready asserted, rsp_valid/desc_valid deasserted
//   P2: No simultaneous cmd_ready and rsp_valid (mutual exclusion)
//   P3: desc_apb_valid one-hot or zero
//   P4: desc_apb_valid implies NOT cmd_ready and NOT rsp_valid (ROUTE state)
//   P5: apb_rsp_rdata always zero (write-only module)
//   P6: kickoff_hit only when desc_valid or rsp_valid-without-error in late states
//   P7: desc_apb_valid implies kickoff_hit (routing implies kickoff active)
//   P8: Handshake stability - rsp_valid held until rsp_ready

module formal_apbtodescr (
    input  logic        clk,
    input  logic        rst_n
);

    // =========================================================================
    // Parameters (small for tractability)
    // =========================================================================
    localparam int ADDR_WIDTH    = 12;
    localparam int DATA_WIDTH    = 32;
    localparam int NUM_CHANNELS  = 4;

    // =========================================================================
    // Free inputs (driven by formal engine)
    // =========================================================================
    (* anyseq *) reg                            apb_cmd_valid;
    (* anyseq *) reg  [ADDR_WIDTH-1:0]          apb_cmd_addr;
    (* anyseq *) reg  [DATA_WIDTH-1:0]          apb_cmd_wdata;
    (* anyseq *) reg                            apb_cmd_write;
    (* anyseq *) reg                            apb_rsp_ready;
    (* anyseq *) reg  [NUM_CHANNELS-1:0]        desc_apb_ready;

    // =========================================================================
    // DUT outputs
    // =========================================================================
    wire                            apb_cmd_ready;
    wire                            apb_rsp_valid;
    wire [DATA_WIDTH-1:0]           apb_rsp_rdata;
    wire                            apb_rsp_error;
    wire [NUM_CHANNELS-1:0]         desc_apb_valid;
    wire [(NUM_CHANNELS*64)-1:0]    desc_apb_addr;
    wire                            apb_descriptor_kickoff_hit;

    // =========================================================================
    // DUT instantiation -- flat vectors connect directly
    // =========================================================================
    apbtodescr #(
        .ADDR_WIDTH    (ADDR_WIDTH),
        .DATA_WIDTH    (DATA_WIDTH),
        .NUM_CHANNELS  (NUM_CHANNELS)
    ) dut (
        .clk                        (clk),
        .rst_n                      (rst_n),

        // APB CMD interface
        .apb_cmd_valid              (apb_cmd_valid),
        .apb_cmd_ready              (apb_cmd_ready),
        .apb_cmd_addr               (apb_cmd_addr),
        .apb_cmd_wdata              (apb_cmd_wdata),
        .apb_cmd_write              (apb_cmd_write),

        // APB RSP interface
        .apb_rsp_valid              (apb_rsp_valid),
        .apb_rsp_ready              (apb_rsp_ready),
        .apb_rsp_rdata              (apb_rsp_rdata),
        .apb_rsp_error              (apb_rsp_error),

        // Descriptor engine ports
        .desc_apb_valid             (desc_apb_valid),
        .desc_apb_ready             (desc_apb_ready),
        .desc_apb_addr              (desc_apb_addr),

        // Integration control
        .apb_descriptor_kickoff_hit (apb_descriptor_kickoff_hit)
    );

    // =========================================================================
    // Formal infrastructure
    // =========================================================================
    reg [7:0] f_past_valid = 0;
    always @(posedge clk)
        f_past_valid <= f_past_valid + (f_past_valid < 8'hFF);

    // Reset sequence: assert reset for first 2 cycles
    initial assume (!rst_n);
    always @(posedge clk)
        if (f_past_valid >= 2) assume (rst_n);

    // =========================================================================
    // Input constraints
    // =========================================================================

    // Constrain apb_cmd_addr upper bits to zero (keep in valid range for
    // NUM_CHANNELS=4: addresses 0x00-0x1F within lower 12-bit field)
    always @(posedge clk) begin
        if (rst_n) begin
            assume (apb_cmd_addr[11:6] == 6'b0);
        end
    end

    // =========================================================================
    // Observable state decode
    // =========================================================================
    // The FSM has 5 states observable through output signals:
    //   IDLE:         cmd_ready=1, rsp_valid=0, desc_valid=0, kickoff=0
    //   RESPOND_LOW:  cmd_ready=0, rsp_valid=1, desc_valid=0, kickoff=0
    //   WAIT_HIGH:    cmd_ready=1, rsp_valid=0, desc_valid=0, kickoff=0
    //   ROUTE:        cmd_ready=0, rsp_valid=0, desc_valid=0/1, kickoff=0/1
    //   RESPOND_HIGH: cmd_ready=0, rsp_valid=1, desc_valid=0, kickoff=0/1
    //
    // Note: IDLE and WAIT_HIGH both have cmd_ready=1, rsp_valid=0, so they
    // are not distinguishable purely from outputs. Properties are written
    // to account for this.

    // =========================================================================
    // Safety properties
    // =========================================================================

    // P1: Reset - after reset deasserts, outputs reflect IDLE state
    //     In IDLE: cmd_ready=1, rsp_valid=0, desc_apb_valid=0
    always @(posedge clk) begin
        if (f_past_valid > 0 && $past(!rst_n)) begin
            ap_reset_cmd_ready: assert (apb_cmd_ready == 1'b1);
            ap_reset_desc_valid: assert (desc_apb_valid == '0);
            ap_reset_rsp_valid: assert (!apb_rsp_valid);
            ap_reset_kickoff: assert (!apb_descriptor_kickoff_hit);
        end
    end

    // P2: No simultaneous cmd_ready and rsp_valid
    //     cmd_ready is asserted in IDLE/WAIT_HIGH; rsp_valid in RESPOND_LOW/RESPOND_HIGH
    //     These state groups are disjoint, so this must always hold.
    always @(posedge clk) begin
        if (rst_n) begin
            ap_no_overlap: assert (!(apb_cmd_ready && apb_rsp_valid));
        end
    end

    // P3: desc_apb_valid one-hot or zero - at most one channel active
    always @(posedge clk) begin
        if (rst_n) begin
            ap_onehot0_valid: assert ($onehot0(desc_apb_valid));
        end
    end

    // P4: desc_apb_valid active implies NOT cmd_ready and NOT rsp_valid
    //     desc_apb_valid is only asserted in ROUTE state, where
    //     cmd_ready=0 and rsp_valid=0
    always @(posedge clk) begin
        if (rst_n && |desc_apb_valid) begin
            ap_desc_not_cmd: assert (!apb_cmd_ready);
            ap_desc_not_rsp: assert (!apb_rsp_valid);
        end
    end

    // P5: apb_rsp_rdata always zero (this is a write-only module)
    always @(posedge clk) begin
        if (rst_n) begin
            ap_rdata_zero: assert (apb_rsp_rdata == '0);
        end
    end

    // P6: kickoff_hit implies NOT cmd_ready
    //     kickoff_hit is asserted in ROUTE or RESPOND_HIGH (both have cmd_ready=0)
    always @(posedge clk) begin
        if (rst_n && apb_descriptor_kickoff_hit) begin
            ap_kickoff_not_cmd: assert (!apb_cmd_ready);
        end
    end

    // P7: desc_apb_valid active implies kickoff_hit
    //     desc_apb_valid is asserted in ROUTE with !r_error;
    //     kickoff_hit is asserted in ROUTE/RESPOND_HIGH with !r_error.
    //     So if desc_apb_valid is active, kickoff_hit must be active.
    always @(posedge clk) begin
        if (rst_n && |desc_apb_valid) begin
            ap_desc_implies_kickoff: assert (apb_descriptor_kickoff_hit);
        end
    end

    // P8: Response handshake stability
    //     Once apb_rsp_valid is asserted, it must remain asserted until
    //     apb_rsp_ready is seen (the FSM only leaves RESPOND_* on rsp_ready)
    always @(posedge clk) begin
        if (f_past_valid > 0 && rst_n && $past(rst_n)) begin
            if ($past(apb_rsp_valid) && !$past(apb_rsp_ready))
                ap_rsp_stable: assert (apb_rsp_valid);
        end
    end

    // P9: Command acceptance stability
    //     Once cmd_ready drops (transaction accepted), rsp_valid or desc_valid
    //     must eventually appear. This is a liveness property approximated by
    //     checking that cmd_ready and rsp_valid cannot both be low while
    //     desc_valid is also zero indefinitely. We check that at least one
    //     of cmd_ready, rsp_valid, or desc_valid is active.
    //     Actually: from RTL, in ROUTE state all three can be 0 (if r_error=1,
    //     desc_valid is 0). So this is not universally true. Skip this property.

    // =========================================================================
    // Cover properties
    // =========================================================================

    // Cover: Full LOW+HIGH write sequence completing (rsp_valid without error)
    always @(posedge clk) begin
        if (f_past_valid > 0 && rst_n)
            cp_full_sequence: cover (
                apb_rsp_valid && !apb_rsp_error && apb_descriptor_kickoff_hit
            );
    end

    // Cover: desc_apb_valid && desc_apb_ready handshake
    always @(posedge clk) begin
        if (rst_n)
            cp_desc_handshake: cover (
                |(desc_apb_valid & desc_apb_ready)
            );
    end

    // Cover: apb_rsp_error asserted
    always @(posedge clk) begin
        if (rst_n)
            cp_error_response: cover (apb_rsp_valid && apb_rsp_error);
    end

    // Cover: Descriptor routing active (desc_valid asserted)
    always @(posedge clk) begin
        if (rst_n)
            cp_desc_routing: cover (|desc_apb_valid);
    end

    // Cover: kickoff_hit asserted
    always @(posedge clk) begin
        if (rst_n)
            cp_kickoff: cover (apb_descriptor_kickoff_hit);
    end

    // Cover: cmd_ready deasserted (not in IDLE or WAIT_HIGH)
    always @(posedge clk) begin
        if (rst_n)
            cp_cmd_not_ready: cover (!apb_cmd_ready);
    end

endmodule
