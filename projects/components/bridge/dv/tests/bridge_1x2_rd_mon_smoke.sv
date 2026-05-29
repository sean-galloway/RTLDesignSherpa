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

module bridge_1x2_rd_mon_smoke #(
    // When 0 (default), every cfg_*_*_monitor_enable input on the
    // monitored bridge is tied low -- the monitors stay quiescent and
    // emit no packets. The basic smoke test runs this way: it proves
    // the monitored generator output elaborates and that the monitor
    // tie-offs don't break ordinary AXI4 traffic.
    //
    // When 1, every cfg_*_*_monitor_enable is tied high so packets
    // actually fire. A companion test (test_bridge_1x2_rd_monitor_
    // capture.py) overrides this parameter, snoops m_mon_axil_* as
    // packets drain out of the write FIFO, and asserts decoded
    // packet content via the TBClasses.monbus parser library.
    // Declared as int (not bit) so cocotb-test's parameters={'MONITOR_
    // ENABLE': 1} flow through verilator without a WIDTHTRUNC warning
    // (cocotb-test passes a 32-bit constant). Treat 0 as off, non-zero
    // as on.
    parameter int MONITOR_ENABLE = 0,

    // When non-zero, ties cfg_mon_group_axi_err_select bit 1 (=
    // PktTypeCompletion) high so completion packets route to the err
    // FIFO instead of the bulk-trace write FIFO. The first completion
    // landing in the err FIFO drives mon_irq_out high. The companion
    // test (test_bridge_1x2_rd_monitor_irq.py) uses this to exercise
    // the IRQ + s_mon_axil drain path end-to-end without needing a
    // deliberate-bus-error injection mechanism. Default 0 (errors
    // path off, all packets stream out the bulk-trace path) keeps
    // the existing smoke + capture tests behaving as before.
    parameter int ROUTE_COMPL_TO_ERR_FIFO = 0
) (
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
    // monbus_axil_group's m_mon_axil_master is 64-bit data (8-bit
    // wstrb). The tie-off does not loop the writes back into any
    // memory model -- the wires below are PROBEABLE FROM COCOTB so a
    // test that turns on monitoring can snoop packets as they drain
    // through the master-write path. Leaving them as `()` would make
    // the signals open / unhandled from the simulator's perspective
    // and the cocotb test couldn't see them.
    logic        mon_irq_out;

    // s_mon_axil_* (slave AXIL read into the err FIFO drain path).
    // Internal nets so cocotb tests can drive the AR/R signals --
    // tying to literal constants in the instantiation makes the pins
    // unhandled from cocotb's perspective. Default values are set
    // in the initial block below: arvalid=0, rready=0 keeps the
    // interface idle for the basic smoke / capture tests; the IRQ
    // test deposits non-zero values at runtime to issue real reads.
    logic        s_mon_axil_arvalid;
    logic [31:0] s_mon_axil_araddr;
    logic [2:0]  s_mon_axil_arprot;
    logic        s_mon_axil_rready;
    logic        s_mon_axil_arready;
    logic        s_mon_axil_rvalid;
    logic [63:0] s_mon_axil_rdata;
    logic [1:0]  s_mon_axil_rresp;

    initial begin
        s_mon_axil_arvalid = 1'b0;
        s_mon_axil_araddr  = '0;
        s_mon_axil_arprot  = '0;
        s_mon_axil_rready  = 1'b0;
    end

    logic        m_mon_axil_awvalid;
    logic [31:0] m_mon_axil_awaddr;
    logic [2:0]  m_mon_axil_awprot;
    logic        m_mon_axil_wvalid;
    logic [63:0] m_mon_axil_wdata;
    logic [7:0]  m_mon_axil_wstrb;
    logic        m_mon_axil_bready;
    logic        m_mon_axil_bvalid_q;

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
        .cfg_cpu_rd_0_rd_monitor_enable    (MONITOR_ENABLE != 0),
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
        .cfg_ddr_rd_0_rd_monitor_enable    (MONITOR_ENABLE != 0),
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
        .cfg_sram_rd_1_rd_monitor_enable    (MONITOR_ENABLE != 0),
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
        .s_mon_axil_arvalid (s_mon_axil_arvalid),
        .s_mon_axil_arready (s_mon_axil_arready),
        .s_mon_axil_araddr  (s_mon_axil_araddr),
        .s_mon_axil_arprot  (s_mon_axil_arprot),
        .s_mon_axil_rvalid  (s_mon_axil_rvalid),
        .s_mon_axil_rready  (s_mon_axil_rready),
        .s_mon_axil_rdata   (s_mon_axil_rdata),
        .s_mon_axil_rresp   (s_mon_axil_rresp),

        // monbus_axil_group AXIL master (always-ready slave)
        .m_mon_axil_awvalid (m_mon_axil_awvalid),
        .m_mon_axil_awready (1'b1),
        .m_mon_axil_awaddr  (m_mon_axil_awaddr),
        .m_mon_axil_awprot  (m_mon_axil_awprot),
        .m_mon_axil_wvalid  (m_mon_axil_wvalid),
        .m_mon_axil_wready  (1'b1),
        .m_mon_axil_wdata   (m_mon_axil_wdata),
        .m_mon_axil_wstrb   (m_mon_axil_wstrb),
        .m_mon_axil_bvalid  (m_mon_axil_bvalid_q),
        .m_mon_axil_bready  (m_mon_axil_bready),
        .m_mon_axil_bresp   (2'b00),

        // monbus_axil_group cfg (zeros = pass-through)
        .cfg_mon_group_base_addr         (32'h0),
        .cfg_mon_group_limit_addr        (32'hFFFF_FFFF),
        .cfg_mon_group_axi_pkt_mask      (16'h0),
        // Bit 1 (PktTypeCompletion) routed to err FIFO when ROUTE_
        // COMPL_TO_ERR_FIFO != 0. Every other bit stays 0 so all
        // other packet types continue to drain via the bulk-trace
        // write path. "Mix, not flood": one packet per transaction
        // lands in the err FIFO and asserts mon_irq_out, but the
        // perf / debug / timeout types (which fire at much higher
        // rates) keep streaming out the master-write path.
        .cfg_mon_group_axi_err_select    (
            (ROUTE_COMPL_TO_ERR_FIFO != 0) ? 16'h0002 : 16'h0000
        ),
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
        // IRQ output: wired to an internal logic net so cocotb tests
        // can probe `dut.mon_irq_out` directly. The wrapper does
        // nothing else with it -- a real SoC integrator would tie
        // this to an interrupt-controller input.
        .mon_irq_out (mon_irq_out)
    );

endmodule : bridge_1x2_rd_mon_smoke
