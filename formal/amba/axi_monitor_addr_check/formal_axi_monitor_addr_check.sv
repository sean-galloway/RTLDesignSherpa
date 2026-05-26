// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: 2024-2026 RTL Design Sherpa
//
// Formal proof for axi_monitor_addr_check
//
// Properties verified:
//   P1: Reset deasserts addr_pkt_valid.
//   P2: When cfg_addr_check_enable=0, addr_pkt_valid stays low.
//   P3: An emitted packet's event_code is exactly AXI_ERR_ADDR_RANGE (4'hD)
//       and packet_type is PktTypeError (4'h0).
//   P4: The range_index extracted from event_data points to a range that
//       was enabled at the time of the hit (latched configuration).
//   P5: The latched address embedded in event_data[28:0] is consistent
//       with one of the enabled ranges' [low, high] bounds — i.e. the
//       emitted address really did hit the range it claims.
//   P6: addr_pkt_valid is stable (no glitches) — once asserted it stays
//       asserted until accepted.

module formal_axi_monitor_addr_check (
    input wire clk,
    input wire rst_n
);

    localparam integer N    = 2;
    localparam integer M    = 8;
    localparam integer IW   = 2;

    // Free inputs.  Per-range bounds are kept as flat packed vectors so
    // yosys can free-drive them via (* anyseq *) — element-wise unpacked
    // arrays fail to expand to memory in current yosys/smtbmc.
    (* anyseq *) reg [M-1:0]       cmd_addr;
    (* anyseq *) reg [IW-1:0]      cmd_id;
    (* anyseq *) reg               cmd_valid;
    (* anyseq *) reg               cmd_ready;
    // cfg_* are treated as anyconst (solver picks once, then stable for
    // the whole trace). This matches the real-world usage pattern: ranges
    // are programmed at boot and held fixed during monitoring.
    (* anyconst *) reg             cfg_addr_check_enable;
    (* anyconst *) reg [N-1:0]     cfg_addr_range_enable;
    (* anyconst *) reg [N*M-1:0]   cfg_addr_range_low_flat;
    (* anyconst *) reg [N*M-1:0]   cfg_addr_range_high_flat;
    (* anyseq *) reg               addr_pkt_ready;

    // Slice the flat vectors back into packed [N][M] for the DUT port shape.
    wire [N-1:0][M-1:0] cfg_low_packed;
    wire [N-1:0][M-1:0] cfg_high_packed;
    genvar gi;
    generate
        for (gi = 0; gi < N; gi = gi + 1) begin : g_pack
            assign cfg_low_packed [gi] = cfg_addr_range_low_flat [gi*M +: M];
            assign cfg_high_packed[gi] = cfg_addr_range_high_flat[gi*M +: M];
        end
    endgenerate

    // DUT outputs
    wire        addr_pkt_valid;
    wire [63:0] addr_pkt_data;

    axi_monitor_addr_check #(
        .N_ADDR_RANGES (N),
        .ADDR_WIDTH    (M),
        .ID_WIDTH      (IW),
        .UNIT_ID       (4'h0),
        .AGENT_ID      (8'h00),
        .IS_READ       (1'b1)
    ) dut (
        .clk                   (clk),
        .aresetn               (rst_n),
        .cmd_addr              (cmd_addr),
        .cmd_id                (cmd_id),
        .cmd_valid             (cmd_valid),
        .cmd_ready             (cmd_ready),
        .cfg_addr_check_enable (cfg_addr_check_enable),
        .cfg_addr_range_enable (cfg_addr_range_enable),
        .cfg_addr_range_low    (cfg_low_packed),
        .cfg_addr_range_high   (cfg_high_packed),
        .addr_pkt_valid        (addr_pkt_valid),
        .addr_pkt_ready        (addr_pkt_ready),
        .addr_pkt_data         (addr_pkt_data)
    );

    // Reset bring-up
    initial assume (!rst_n);
    reg [3:0] f_past_valid;
    always @(posedge clk) begin
        if (f_past_valid < 4'd15) f_past_valid <= f_past_valid + 1;
        if (f_past_valid < 4'd2)  assume (!rst_n);
        else                      assume (rst_n);
    end

    // Decode the emitted packet
    wire [3:0]  pkt_type     = addr_pkt_data[63:60];
    wire [3:0]  pkt_evcode   = addr_pkt_data[56:53];
    wire [4:0]  pkt_range_ix = addr_pkt_data[34:30];
    wire        pkt_is_read  = addr_pkt_data[29];
    wire [M-1:0] pkt_addr_lo = addr_pkt_data[M-1:0];

    // =========================================================================
    // P1: Reset deasserts addr_pkt_valid (after at least one posedge has
    //     run with rst_n=0 — the design uses sync reset, so the first
    //     clock edge is what clears the pending mask).
    // =========================================================================
    always @(posedge clk) begin
        if (f_past_valid >= 4'd1 && !rst_n)
            ap_reset_valid_low: assert (addr_pkt_valid == 1'b0);
    end

    // =========================================================================
    // P2: cfg_addr_check_enable=0 forces addr_pkt_valid low
    // =========================================================================
    always @(*) begin
        if (rst_n && !cfg_addr_check_enable)
            ap_disable_holds_quiet: assert (addr_pkt_valid == 1'b0);
    end

    // =========================================================================
    // P3: Emitted packet carries the right packet_type / event_code
    // =========================================================================
    always @(*) begin
        if (rst_n && addr_pkt_valid) begin
            ap_pkt_type_is_error: assert (pkt_type   == 4'h0);   // PktTypeError
            ap_evcode_is_addr_range: assert (pkt_evcode == 4'hD); // AXI_ERR_ADDR_RANGE
        end
    end

    // =========================================================================
    // P4: range_index points to an enabled range
    // =========================================================================
    always @(*) begin
        if (rst_n && addr_pkt_valid)
            ap_range_idx_enabled: assert (cfg_addr_range_enable[pkt_range_ix[$clog2(N)-1:0]]);
    end

    // =========================================================================
    // P5: The latched address falls within the claimed range's bounds.
    //     event_data[28:0] holds the lower 29 bits of cmd_addr; with M<=29
    //     it's the full address.
    // =========================================================================
    always @(*) begin
        if (rst_n && addr_pkt_valid) begin
            ap_addr_in_range_low:  assert (pkt_addr_lo >= cfg_low_packed [pkt_range_ix[$clog2(N)-1:0]]);
            ap_addr_in_range_high: assert (pkt_addr_lo <= cfg_high_packed[pkt_range_ix[$clog2(N)-1:0]]);
        end
    end

    // =========================================================================
    // P6: addr_pkt_valid is sticky — once asserted it stays asserted until
    //     consumer accepts.
    // =========================================================================
    reg r_prev_valid;
    reg r_prev_ready;
    always @(posedge clk) begin
        r_prev_valid <= addr_pkt_valid;
        r_prev_ready <= addr_pkt_ready;
    end
    always @(posedge clk) begin
        if (rst_n && r_prev_valid && !r_prev_ready)
            ap_valid_sticky: assert (addr_pkt_valid);
    end

    // =========================================================================
    // Cover properties
    // =========================================================================
    always @(posedge clk) begin
        if (rst_n) begin
            cp_emit:           cover (addr_pkt_valid);
            cp_emit_handshake: cover (addr_pkt_valid && addr_pkt_ready);
        end
    end

endmodule
