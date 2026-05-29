// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: 2024-2025 sean galloway
//
// Module: bridge_1x2_rd_mon_smoke
// Purpose: Smoke-test wrapper for bridge_1x2_rd_mon (the monitored
//          variant of bridge_1x2_rd).
//
// Stage-3 of bridge USE_MONITOR support adds a large monitor-side port
// surface (per-port cfg, AXIL slave, AXIL master, group cfg, IRQ) at
// the bridge top. The existing cocotb smoke harness for bridge_1x2_rd
// only knows the original (non-monitor) AXI4 port surface, so we wrap
// the monitored bridge here, tie every monitor port to a safe default,
// and re-expose only the bridge's original AXI4 ports.
//
// Lives in dv/tests/ (not in rtl/generated/) so it survives bridge
// regeneration -- the generator rm -rf's its own output directory.
//
// Tie-offs:
//   - Every per-port cfg_*_* input  driven to '0  (monitors stay quiet)
//   - cfg_mon_group_*                driven to '0
//   - s_mon_axil_*                   held idle (arvalid=0, rready=0)
//   - m_mon_axil_*                   always-ready slave (awready=1,
//                                    wready=1, bvalid one cycle after W
//                                    handshake, bresp=2'b00)
//   - mon_irq_out                    unconnected

`timescale 1ns / 1ps

module bridge_1x2_rd_mon_smoke (
    input  logic aclk,
    input  logic aresetn,

    // Master: cpu_rd (rd channel)
    input  logic [3:0]  cpu_rd_axi_arid,
    input  logic [31:0] cpu_rd_axi_araddr,
    input  logic [7:0]  cpu_rd_axi_arlen,
    input  logic [2:0]  cpu_rd_axi_arsize,
    input  logic [1:0]  cpu_rd_axi_arburst,
    input  logic        cpu_rd_axi_arlock,
    input  logic [3:0]  cpu_rd_axi_arcache,
    input  logic [2:0]  cpu_rd_axi_arprot,
    input  logic [3:0]  cpu_rd_axi_arqos,
    input  logic [3:0]  cpu_rd_axi_arregion,
    input  logic        cpu_rd_axi_aruser,
    input  logic        cpu_rd_axi_arvalid,
    output logic        cpu_rd_axi_arready,

    output logic [3:0]  cpu_rd_axi_rid,
    output logic [31:0] cpu_rd_axi_rdata,
    output logic [1:0]  cpu_rd_axi_rresp,
    output logic        cpu_rd_axi_rlast,
    output logic        cpu_rd_axi_ruser,
    output logic        cpu_rd_axi_rvalid,
    input  logic        cpu_rd_axi_rready,

    // Slave: ddr_rd
    output logic [3:0]  ddr_rd_axi_arid,
    output logic [31:0] ddr_rd_axi_araddr,
    output logic [7:0]  ddr_rd_axi_arlen,
    output logic [2:0]  ddr_rd_axi_arsize,
    output logic [1:0]  ddr_rd_axi_arburst,
    output logic        ddr_rd_axi_arlock,
    output logic [3:0]  ddr_rd_axi_arcache,
    output logic [2:0]  ddr_rd_axi_arprot,
    output logic [3:0]  ddr_rd_axi_arqos,
    output logic [3:0]  ddr_rd_axi_arregion,
    output logic        ddr_rd_axi_aruser,
    output logic        ddr_rd_axi_arvalid,
    input  logic        ddr_rd_axi_arready,

    input  logic [3:0]  ddr_rd_axi_rid,
    input  logic [31:0] ddr_rd_axi_rdata,
    input  logic [1:0]  ddr_rd_axi_rresp,
    input  logic        ddr_rd_axi_rlast,
    input  logic        ddr_rd_axi_ruser,
    input  logic        ddr_rd_axi_rvalid,
    output logic        ddr_rd_axi_rready,

    // Slave: sram_rd
    output logic [3:0]  sram_rd_axi_arid,
    output logic [31:0] sram_rd_axi_araddr,
    output logic [7:0]  sram_rd_axi_arlen,
    output logic [2:0]  sram_rd_axi_arsize,
    output logic [1:0]  sram_rd_axi_arburst,
    output logic        sram_rd_axi_arlock,
    output logic [3:0]  sram_rd_axi_arcache,
    output logic [2:0]  sram_rd_axi_arprot,
    output logic [3:0]  sram_rd_axi_arqos,
    output logic [3:0]  sram_rd_axi_arregion,
    output logic        sram_rd_axi_aruser,
    output logic        sram_rd_axi_arvalid,
    input  logic        sram_rd_axi_arready,

    input  logic [3:0]  sram_rd_axi_rid,
    input  logic [31:0] sram_rd_axi_rdata,
    input  logic [1:0]  sram_rd_axi_rresp,
    input  logic        sram_rd_axi_rlast,
    input  logic        sram_rd_axi_ruser,
    input  logic        sram_rd_axi_rvalid,
    output logic        sram_rd_axi_rready
);

    // AXIL master tie-off: always-ready, OKAY-responding slave.
    // Drives bvalid one cycle after the W handshake completes so the
    // axil4_master_wr FSM inside monbus_axil_group can drain any
    // packets if monitoring is ever enabled mid-test.
    //
    // Post-MON-PKT-64-to-128: monbus_axil_group's master AXIL is now
    // 64-bit data / 8-bit wstrb (M_AXIL_DATA_WIDTH=64) -- the bridge top
    // surfaces matching widths. The tie-off below leaves wdata/wstrb
    // unconnected (`()`) so it is width-agnostic and remains correct;
    // no internal/loopback memory is wired to the master here, so no
    // explicit widening is required in this wrapper.
    logic m_mon_axil_awvalid;
    logic m_mon_axil_wvalid;
    logic m_mon_axil_bready;
    logic m_mon_axil_bvalid_q;

    always_ff @(posedge aclk or negedge aresetn) begin
        if (!aresetn) begin
            m_mon_axil_bvalid_q <= 1'b0;
        end else begin
            if (m_mon_axil_wvalid)      m_mon_axil_bvalid_q <= 1'b1;
            else if (m_mon_axil_bready) m_mon_axil_bvalid_q <= 1'b0;
        end
    end

    bridge_1x2_rd_mon u_dut (
        .aclk    (aclk),
        .aresetn (aresetn),

        // Original AXI4 surface
        .cpu_rd_axi_arid     (cpu_rd_axi_arid),
        .cpu_rd_axi_araddr   (cpu_rd_axi_araddr),
        .cpu_rd_axi_arlen    (cpu_rd_axi_arlen),
        .cpu_rd_axi_arsize   (cpu_rd_axi_arsize),
        .cpu_rd_axi_arburst  (cpu_rd_axi_arburst),
        .cpu_rd_axi_arlock   (cpu_rd_axi_arlock),
        .cpu_rd_axi_arcache  (cpu_rd_axi_arcache),
        .cpu_rd_axi_arprot   (cpu_rd_axi_arprot),
        .cpu_rd_axi_arqos    (cpu_rd_axi_arqos),
        .cpu_rd_axi_arregion (cpu_rd_axi_arregion),
        .cpu_rd_axi_aruser   (cpu_rd_axi_aruser),
        .cpu_rd_axi_arvalid  (cpu_rd_axi_arvalid),
        .cpu_rd_axi_arready  (cpu_rd_axi_arready),

        .cpu_rd_axi_rid    (cpu_rd_axi_rid),
        .cpu_rd_axi_rdata  (cpu_rd_axi_rdata),
        .cpu_rd_axi_rresp  (cpu_rd_axi_rresp),
        .cpu_rd_axi_rlast  (cpu_rd_axi_rlast),
        .cpu_rd_axi_ruser  (cpu_rd_axi_ruser),
        .cpu_rd_axi_rvalid (cpu_rd_axi_rvalid),
        .cpu_rd_axi_rready (cpu_rd_axi_rready),

        .ddr_rd_axi_arid     (ddr_rd_axi_arid),
        .ddr_rd_axi_araddr   (ddr_rd_axi_araddr),
        .ddr_rd_axi_arlen    (ddr_rd_axi_arlen),
        .ddr_rd_axi_arsize   (ddr_rd_axi_arsize),
        .ddr_rd_axi_arburst  (ddr_rd_axi_arburst),
        .ddr_rd_axi_arlock   (ddr_rd_axi_arlock),
        .ddr_rd_axi_arcache  (ddr_rd_axi_arcache),
        .ddr_rd_axi_arprot   (ddr_rd_axi_arprot),
        .ddr_rd_axi_arqos    (ddr_rd_axi_arqos),
        .ddr_rd_axi_arregion (ddr_rd_axi_arregion),
        .ddr_rd_axi_aruser   (ddr_rd_axi_aruser),
        .ddr_rd_axi_arvalid  (ddr_rd_axi_arvalid),
        .ddr_rd_axi_arready  (ddr_rd_axi_arready),

        .ddr_rd_axi_rid    (ddr_rd_axi_rid),
        .ddr_rd_axi_rdata  (ddr_rd_axi_rdata),
        .ddr_rd_axi_rresp  (ddr_rd_axi_rresp),
        .ddr_rd_axi_rlast  (ddr_rd_axi_rlast),
        .ddr_rd_axi_ruser  (ddr_rd_axi_ruser),
        .ddr_rd_axi_rvalid (ddr_rd_axi_rvalid),
        .ddr_rd_axi_rready (ddr_rd_axi_rready),

        .sram_rd_axi_arid     (sram_rd_axi_arid),
        .sram_rd_axi_araddr   (sram_rd_axi_araddr),
        .sram_rd_axi_arlen    (sram_rd_axi_arlen),
        .sram_rd_axi_arsize   (sram_rd_axi_arsize),
        .sram_rd_axi_arburst  (sram_rd_axi_arburst),
        .sram_rd_axi_arlock   (sram_rd_axi_arlock),
        .sram_rd_axi_arcache  (sram_rd_axi_arcache),
        .sram_rd_axi_arprot   (sram_rd_axi_arprot),
        .sram_rd_axi_arqos    (sram_rd_axi_arqos),
        .sram_rd_axi_arregion (sram_rd_axi_arregion),
        .sram_rd_axi_aruser   (sram_rd_axi_aruser),
        .sram_rd_axi_arvalid  (sram_rd_axi_arvalid),
        .sram_rd_axi_arready  (sram_rd_axi_arready),

        .sram_rd_axi_rid    (sram_rd_axi_rid),
        .sram_rd_axi_rdata  (sram_rd_axi_rdata),
        .sram_rd_axi_rresp  (sram_rd_axi_rresp),
        .sram_rd_axi_rlast  (sram_rd_axi_rlast),
        .sram_rd_axi_ruser  (sram_rd_axi_ruser),
        .sram_rd_axi_rvalid (sram_rd_axi_rvalid),
        .sram_rd_axi_rready (sram_rd_axi_rready),

        // Per-port cfg (all zeroed -- monitors stay quiet)
        // cpu_rd (master idx 0, rd channel)
        .cfg_cpu_rd_0_rd_monitor_enable    (1'b0),
        .cfg_cpu_rd_0_rd_error_enable      (1'b0),
        .cfg_cpu_rd_0_rd_timeout_enable    (1'b0),
        .cfg_cpu_rd_0_rd_perf_enable       (1'b0),
        .cfg_cpu_rd_0_rd_timeout_cycles    (16'h0),
        .cfg_cpu_rd_0_rd_latency_threshold (32'h0),
        .cfg_cpu_rd_0_rd_axi_pkt_mask      (16'h0),
        .cfg_cpu_rd_0_rd_axi_err_select    (16'h0),
        .cfg_cpu_rd_0_rd_axi_error_mask    (16'h0),
        .cfg_cpu_rd_0_rd_axi_timeout_mask  (16'h0),
        .cfg_cpu_rd_0_rd_axi_compl_mask    (16'h0),
        .cfg_cpu_rd_0_rd_axi_thresh_mask   (16'h0),
        .cfg_cpu_rd_0_rd_axi_perf_mask     (16'h0),
        .cfg_cpu_rd_0_rd_axi_addr_mask     (16'h0),
        .cfg_cpu_rd_0_rd_axi_debug_mask    (16'h0),
        // ddr_rd (slave idx 0, rd channel)
        .cfg_ddr_rd_0_rd_monitor_enable    (1'b0),
        .cfg_ddr_rd_0_rd_error_enable      (1'b0),
        .cfg_ddr_rd_0_rd_timeout_enable    (1'b0),
        .cfg_ddr_rd_0_rd_perf_enable       (1'b0),
        .cfg_ddr_rd_0_rd_timeout_cycles    (16'h0),
        .cfg_ddr_rd_0_rd_latency_threshold (32'h0),
        .cfg_ddr_rd_0_rd_axi_pkt_mask      (16'h0),
        .cfg_ddr_rd_0_rd_axi_err_select    (16'h0),
        .cfg_ddr_rd_0_rd_axi_error_mask    (16'h0),
        .cfg_ddr_rd_0_rd_axi_timeout_mask  (16'h0),
        .cfg_ddr_rd_0_rd_axi_compl_mask    (16'h0),
        .cfg_ddr_rd_0_rd_axi_thresh_mask   (16'h0),
        .cfg_ddr_rd_0_rd_axi_perf_mask     (16'h0),
        .cfg_ddr_rd_0_rd_axi_addr_mask     (16'h0),
        .cfg_ddr_rd_0_rd_axi_debug_mask    (16'h0),
        // sram_rd (slave idx 1, rd channel)
        .cfg_sram_rd_1_rd_monitor_enable    (1'b0),
        .cfg_sram_rd_1_rd_error_enable      (1'b0),
        .cfg_sram_rd_1_rd_timeout_enable    (1'b0),
        .cfg_sram_rd_1_rd_perf_enable       (1'b0),
        .cfg_sram_rd_1_rd_timeout_cycles    (16'h0),
        .cfg_sram_rd_1_rd_latency_threshold (32'h0),
        .cfg_sram_rd_1_rd_axi_pkt_mask      (16'h0),
        .cfg_sram_rd_1_rd_axi_err_select    (16'h0),
        .cfg_sram_rd_1_rd_axi_error_mask    (16'h0),
        .cfg_sram_rd_1_rd_axi_timeout_mask  (16'h0),
        .cfg_sram_rd_1_rd_axi_compl_mask    (16'h0),
        .cfg_sram_rd_1_rd_axi_thresh_mask   (16'h0),
        .cfg_sram_rd_1_rd_axi_perf_mask     (16'h0),
        .cfg_sram_rd_1_rd_axi_addr_mask     (16'h0),
        .cfg_sram_rd_1_rd_axi_debug_mask    (16'h0),

        // monbus_axil_group AXIL slave (idle)
        .s_mon_axil_arvalid (1'b0),
        .s_mon_axil_arready (),
        .s_mon_axil_araddr  (32'h0),
        .s_mon_axil_arprot  (3'h0),
        .s_mon_axil_rvalid  (),
        .s_mon_axil_rready  (1'b0),
        .s_mon_axil_rdata   (),
        .s_mon_axil_rresp   (),

        // monbus_axil_group AXIL master (always-ready slave)
        .m_mon_axil_awvalid (m_mon_axil_awvalid),
        .m_mon_axil_awready (1'b1),
        .m_mon_axil_awaddr  (),
        .m_mon_axil_awprot  (),
        .m_mon_axil_wvalid  (m_mon_axil_wvalid),
        .m_mon_axil_wready  (1'b1),
        .m_mon_axil_wdata   (),
        .m_mon_axil_wstrb   (),
        .m_mon_axil_bvalid  (m_mon_axil_bvalid_q),
        .m_mon_axil_bready  (m_mon_axil_bready),
        .m_mon_axil_bresp   (2'b00),

        // monbus_axil_group cfg (zeros = pass-through)
        .cfg_mon_group_base_addr         (32'h0),
        .cfg_mon_group_limit_addr        (32'hFFFF_FFFF),
        .cfg_mon_group_axi_pkt_mask      (16'h0),
        .cfg_mon_group_axi_err_select    (16'h0),
        .cfg_mon_group_axi_error_mask    (16'h0),
        .cfg_mon_group_axi_timeout_mask  (16'h0),
        .cfg_mon_group_axi_compl_mask    (16'h0),
        .cfg_mon_group_axi_thresh_mask   (16'h0),
        .cfg_mon_group_axi_perf_mask     (16'h0),
        .cfg_mon_group_axi_addr_mask     (16'h0),
        .cfg_mon_group_axi_debug_mask    (16'h0),
        .cfg_mon_group_axis_pkt_mask     (16'h0),
        .cfg_mon_group_axis_err_select   (16'h0),
        .cfg_mon_group_axis_error_mask   (16'h0),
        .cfg_mon_group_axis_timeout_mask (16'h0),
        .cfg_mon_group_axis_compl_mask   (16'h0),
        .cfg_mon_group_axis_credit_mask  (16'h0),
        .cfg_mon_group_axis_channel_mask (16'h0),
        .cfg_mon_group_axis_stream_mask  (16'h0),
        .cfg_mon_group_core_pkt_mask     (16'h0),
        .cfg_mon_group_core_err_select   (16'h0),
        .cfg_mon_group_core_error_mask   (16'h0),
        .cfg_mon_group_core_timeout_mask (16'h0),
        .cfg_mon_group_core_compl_mask   (16'h0),
        .cfg_mon_group_core_thresh_mask  (16'h0),
        .cfg_mon_group_core_perf_mask    (16'h0),
        .cfg_mon_group_core_debug_mask   (16'h0),

        // IRQ (unconnected)
        .mon_irq_out ()
    );

endmodule : bridge_1x2_rd_mon_smoke
