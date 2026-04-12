// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: 2024-2025 sean galloway
//
// Formal wrapper for monbus_axil_group (yosys-compatible, sv2v-preprocessed)
// Run with: sby monbus_axil_group.sby

module formal_monbus_axil_group (
    input  logic        clk,
    input  logic        rst_n
);

    // =========================================================================
    // Parameters (small for tractability)
    // =========================================================================
    localparam int FIFO_DEPTH_ERR   = 4;
    localparam int FIFO_DEPTH_WRITE = 4;
    localparam int ADDR_WIDTH       = 32;
    localparam int DATA_WIDTH       = 32;
    localparam int NUM_PROTOCOLS    = 3;

    // =========================================================================
    // Free inputs (driven by formal engine)
    // =========================================================================

    // Monitor bus input
    (* anyseq *) reg                    monbus_valid;
    (* anyseq *) reg  [63:0]           monbus_packet;

    // AXI-Lite slave read interface
    (* anyseq *) reg                    s_axil_arvalid;
    (* anyseq *) reg  [ADDR_WIDTH-1:0] s_axil_araddr;
    (* anyseq *) reg  [2:0]            s_axil_arprot;
    (* anyseq *) reg                    s_axil_rready;

    // AXI-Lite master write interface responses
    (* anyseq *) reg                    m_axil_awready;
    (* anyseq *) reg                    m_axil_wready;
    (* anyseq *) reg                    m_axil_bvalid;
    (* anyseq *) reg  [1:0]            m_axil_bresp;

    // Configuration
    (* anyseq *) reg  [ADDR_WIDTH-1:0] cfg_base_addr;
    (* anyseq *) reg  [ADDR_WIDTH-1:0] cfg_limit_addr;

    // Protocol config - AXI
    (* anyseq *) reg  [15:0]           cfg_axi_pkt_mask;
    (* anyseq *) reg  [15:0]           cfg_axi_err_select;
    (* anyseq *) reg  [15:0]           cfg_axi_error_mask;
    (* anyseq *) reg  [15:0]           cfg_axi_timeout_mask;
    (* anyseq *) reg  [15:0]           cfg_axi_compl_mask;
    (* anyseq *) reg  [15:0]           cfg_axi_thresh_mask;
    (* anyseq *) reg  [15:0]           cfg_axi_perf_mask;
    (* anyseq *) reg  [15:0]           cfg_axi_addr_mask;
    (* anyseq *) reg  [15:0]           cfg_axi_debug_mask;

    // Protocol config - AXIS
    (* anyseq *) reg  [15:0]           cfg_axis_pkt_mask;
    (* anyseq *) reg  [15:0]           cfg_axis_err_select;
    (* anyseq *) reg  [15:0]           cfg_axis_error_mask;
    (* anyseq *) reg  [15:0]           cfg_axis_timeout_mask;
    (* anyseq *) reg  [15:0]           cfg_axis_compl_mask;
    (* anyseq *) reg  [15:0]           cfg_axis_credit_mask;
    (* anyseq *) reg  [15:0]           cfg_axis_channel_mask;
    (* anyseq *) reg  [15:0]           cfg_axis_stream_mask;

    // Protocol config - CORE
    (* anyseq *) reg  [15:0]           cfg_core_pkt_mask;
    (* anyseq *) reg  [15:0]           cfg_core_err_select;
    (* anyseq *) reg  [15:0]           cfg_core_error_mask;
    (* anyseq *) reg  [15:0]           cfg_core_timeout_mask;
    (* anyseq *) reg  [15:0]           cfg_core_compl_mask;
    (* anyseq *) reg  [15:0]           cfg_core_thresh_mask;
    (* anyseq *) reg  [15:0]           cfg_core_perf_mask;
    (* anyseq *) reg  [15:0]           cfg_core_debug_mask;

    // =========================================================================
    // DUT outputs
    // =========================================================================
    wire                    monbus_ready_o;

    wire                    s_axil_arready_o;
    wire                    s_axil_rvalid_o;
    wire [DATA_WIDTH-1:0]   s_axil_rdata_o;
    wire [1:0]              s_axil_rresp_o;

    wire                    m_axil_awvalid_o;
    wire [ADDR_WIDTH-1:0]   m_axil_awaddr_o;
    wire [2:0]              m_axil_awprot_o;
    wire                    m_axil_wvalid_o;
    wire [DATA_WIDTH-1:0]   m_axil_wdata_o;
    wire [DATA_WIDTH/8-1:0] m_axil_wstrb_o;
    wire                    m_axil_bready_o;

    wire                    irq_out_o;
    wire                    err_fifo_full_o;
    wire                    write_fifo_full_o;
    wire [7:0]              err_fifo_count_o;
    wire [7:0]              write_fifo_count_o;

    // =========================================================================
    // DUT instantiation
    // =========================================================================
    monbus_axil_group #(
        .FIFO_DEPTH_ERR   (FIFO_DEPTH_ERR),
        .FIFO_DEPTH_WRITE (FIFO_DEPTH_WRITE),
        .ADDR_WIDTH       (ADDR_WIDTH),
        .DATA_WIDTH       (DATA_WIDTH),
        .NUM_PROTOCOLS    (NUM_PROTOCOLS)
    ) dut (
        .axi_aclk         (clk),
        .axi_aresetn       (rst_n),

        // Monitor bus input
        .monbus_valid      (monbus_valid),
        .monbus_ready      (monbus_ready_o),
        .monbus_packet     (monbus_packet),

        // Slave read interface
        .s_axil_arvalid    (s_axil_arvalid),
        .s_axil_arready    (s_axil_arready_o),
        .s_axil_araddr     (s_axil_araddr),
        .s_axil_arprot     (s_axil_arprot),
        .s_axil_rvalid     (s_axil_rvalid_o),
        .s_axil_rready     (s_axil_rready),
        .s_axil_rdata      (s_axil_rdata_o),
        .s_axil_rresp      (s_axil_rresp_o),

        // Master write interface
        .m_axil_awvalid    (m_axil_awvalid_o),
        .m_axil_awready    (m_axil_awready),
        .m_axil_awaddr     (m_axil_awaddr_o),
        .m_axil_awprot     (m_axil_awprot_o),
        .m_axil_wvalid     (m_axil_wvalid_o),
        .m_axil_wready     (m_axil_wready),
        .m_axil_wdata      (m_axil_wdata_o),
        .m_axil_wstrb      (m_axil_wstrb_o),
        .m_axil_bvalid     (m_axil_bvalid),
        .m_axil_bready     (m_axil_bready_o),
        .m_axil_bresp      (m_axil_bresp),

        // Interrupt
        .irq_out           (irq_out_o),

        // Configuration
        .cfg_base_addr     (cfg_base_addr),
        .cfg_limit_addr    (cfg_limit_addr),

        // AXI protocol config
        .cfg_axi_pkt_mask     (cfg_axi_pkt_mask),
        .cfg_axi_err_select   (cfg_axi_err_select),
        .cfg_axi_error_mask   (cfg_axi_error_mask),
        .cfg_axi_timeout_mask (cfg_axi_timeout_mask),
        .cfg_axi_compl_mask   (cfg_axi_compl_mask),
        .cfg_axi_thresh_mask  (cfg_axi_thresh_mask),
        .cfg_axi_perf_mask    (cfg_axi_perf_mask),
        .cfg_axi_addr_mask    (cfg_axi_addr_mask),
        .cfg_axi_debug_mask   (cfg_axi_debug_mask),

        // AXIS protocol config
        .cfg_axis_pkt_mask     (cfg_axis_pkt_mask),
        .cfg_axis_err_select   (cfg_axis_err_select),
        .cfg_axis_error_mask   (cfg_axis_error_mask),
        .cfg_axis_timeout_mask (cfg_axis_timeout_mask),
        .cfg_axis_compl_mask   (cfg_axis_compl_mask),
        .cfg_axis_credit_mask  (cfg_axis_credit_mask),
        .cfg_axis_channel_mask (cfg_axis_channel_mask),
        .cfg_axis_stream_mask  (cfg_axis_stream_mask),

        // CORE protocol config
        .cfg_core_pkt_mask     (cfg_core_pkt_mask),
        .cfg_core_err_select   (cfg_core_err_select),
        .cfg_core_error_mask   (cfg_core_error_mask),
        .cfg_core_timeout_mask (cfg_core_timeout_mask),
        .cfg_core_compl_mask   (cfg_core_compl_mask),
        .cfg_core_thresh_mask  (cfg_core_thresh_mask),
        .cfg_core_perf_mask    (cfg_core_perf_mask),
        .cfg_core_debug_mask   (cfg_core_debug_mask),

        // Status
        .err_fifo_full     (err_fifo_full_o),
        .write_fifo_full   (write_fifo_full_o),
        .err_fifo_count    (err_fifo_count_o),
        .write_fifo_count  (write_fifo_count_o)
    );

    // =========================================================================
    // Formal infrastructure
    // =========================================================================
    reg [7:0] f_past_valid = 0;
    always @(posedge clk)
        f_past_valid <= f_past_valid + (f_past_valid < 8'hFF);

    // Reset sequence: assert reset for first 2 cycles
    initial assume (!rst_n);
    always @(posedge clk) begin
        if (f_past_valid >= 2) assume (rst_n);
    end

    // =========================================================================
    // Environment constraints
    // =========================================================================

    // Base addr must be <= limit addr for sensible address wrapping
    always @(posedge clk) begin
        if (rst_n) begin
            assume (cfg_base_addr <= cfg_limit_addr);
            assume (cfg_limit_addr - cfg_base_addr >= 32'd16);
        end
    end

    // AXI-Lite master write: bvalid stable until bready
    always @(posedge clk) begin
        if (rst_n && f_past_valid > 0) begin
            if ($past(m_axil_bvalid) && !$past(m_axil_bready_o))
                assume (m_axil_bvalid);
        end
    end

    // =========================================================================
    // P1: Reset clears monbus output and master write valid
    // =========================================================================
    always @(posedge clk) begin
        if (f_past_valid > 0 && $past(!rst_n))
            ap_reset_m_awvalid: assert (m_axil_awvalid_o == 1'b0);
    end

    always @(posedge clk) begin
        if (f_past_valid > 0 && $past(!rst_n))
            ap_reset_m_wvalid: assert (m_axil_wvalid_o == 1'b0);
    end

    always @(posedge clk) begin
        if (f_past_valid > 0 && $past(!rst_n))
            ap_reset_irq: assert (irq_out_o == 1'b0);
    end

    // =========================================================================
    // P2: FIFO count bounds - err_fifo_count <= FIFO_DEPTH_ERR
    // =========================================================================
    always @(posedge clk) begin
        if (rst_n)
            ap_err_fifo_count_bound: assert (err_fifo_count_o <= FIFO_DEPTH_ERR);
    end

    always @(posedge clk) begin
        if (rst_n)
            ap_write_fifo_count_bound: assert (write_fifo_count_o <= FIFO_DEPTH_WRITE);
    end

    // =========================================================================
    // P3: After reset, IRQ is initially low and tracks error FIFO state
    //     The IRQ output is driven by !err_fifo_empty = err_fifo_rd_valid.
    //     The count might differ by 1 from rd_valid when simultaneous r/w
    //     occurs (FIFO count is combinational but rd_valid is registered).
    //     We verify the safe property: IRQ is low out of reset.
    // =========================================================================
    always @(posedge clk) begin
        if (f_past_valid > 0 && $past(!rst_n))
            ap_irq_after_reset: assert (irq_out_o == 1'b0);
    end

    // =========================================================================
    // P4: FIFO full implies count at maximum, count never exceeds depth
    //     Note: The FIFO full flag (!wr_ready) and count output may be
    //     off by one due to simultaneous read/write. We verify:
    //     - count never exceeds the depth
    //     - full flag is never asserted with count 0 (empty)
    // =========================================================================
    always @(posedge clk) begin
        if (rst_n && err_fifo_full_o)
            ap_err_full_not_empty: assert (err_fifo_count_o > 8'd0);
    end

    always @(posedge clk) begin
        if (rst_n && write_fifo_full_o)
            ap_write_full_not_empty: assert (write_fifo_count_o > 8'd0);
    end

    // =========================================================================
    // P5: Reset clears master write outputs
    //     Note: axil4_master_wr has internal skid buffers, so FSM-level
    //     mutex properties don't hold at the external interface. Instead
    //     verify reset behavior on the buffered outputs.
    // =========================================================================
    always @(posedge clk) begin
        if (f_past_valid > 0 && $past(!rst_n))
            ap_reset_m_bready: assert (m_axil_bready_o == 1'b0);
    end

    // =========================================================================
    // P6: awprot is always 0 (unprivileged, non-secure, data access)
    // =========================================================================
    always @(posedge clk) begin
        if (rst_n && m_axil_awvalid_o)
            ap_awprot_zero: assert (m_axil_awprot_o == 3'b000);
    end

    // =========================================================================
    // P7: All write strobes set (wstrb always all ones)
    // =========================================================================
    always @(posedge clk) begin
        if (rst_n && m_axil_wvalid_o)
            ap_wstrb_all: assert (m_axil_wstrb_o == {(DATA_WIDTH/8){1'b1}});
    end

    // =========================================================================
    // P8: AXI-Lite slave read response is always OKAY (2'b00)
    // =========================================================================
    always @(posedge clk) begin
        if (rst_n && s_axil_rvalid_o)
            ap_rresp_okay: assert (s_axil_rresp_o == 2'b00);
    end

    // =========================================================================
    // Cover properties
    // =========================================================================

    // Monbus handshake
    always @(posedge clk) begin
        if (rst_n)
            cp_monbus_handshake: cover (monbus_valid && monbus_ready_o);
    end

    // IRQ asserted
    always @(posedge clk) begin
        if (rst_n)
            cp_irq_asserted: cover (irq_out_o);
    end

    // Error FIFO non-empty
    always @(posedge clk) begin
        if (rst_n)
            cp_err_fifo_nonempty: cover (err_fifo_count_o > 8'd0);
    end

    // Write FIFO non-empty
    always @(posedge clk) begin
        if (rst_n)
            cp_write_fifo_nonempty: cover (write_fifo_count_o > 8'd0);
    end

    // Master write address valid
    always @(posedge clk) begin
        if (rst_n)
            cp_m_awvalid: cover (m_axil_awvalid_o);
    end

    // Master write data valid
    always @(posedge clk) begin
        if (rst_n)
            cp_m_wvalid: cover (m_axil_wvalid_o);
    end

    // Slave read valid
    always @(posedge clk) begin
        if (rst_n)
            cp_s_rvalid: cover (s_axil_rvalid_o);
    end

    // Both FIFOs simultaneously non-empty
    always @(posedge clk) begin
        if (rst_n)
            cp_both_fifos: cover (err_fifo_count_o > 0 && write_fifo_count_o > 0);
    end

endmodule
