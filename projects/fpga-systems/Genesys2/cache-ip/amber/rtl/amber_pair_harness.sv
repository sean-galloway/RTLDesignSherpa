// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: 2026 sean galloway
//
// Module: amber_pair_harness
// Purpose: Internal integration for the amber pair-rig Genesys2 board bring-up.
//   Host (UART) -> uart_axil_bridge -> bridge_amber_axil -> {
//      harness_csr, cycle_injector0, cycle_injector1, tally_cnt/cfgw/cfgr }
//   Two cycle injectors drive two amber_top caches; caches connect through
//   amber_pair_fabric to a shared sdpram_slave_axi4_axi4 memory. Cache
//   MonBus streams merge and feed a monbus_tally_axil for host read-out.

`timescale 1ns / 1ps

`include "reset_defs.svh"

// ILA observation taps: with AMBER_ILA_DBG defined (ILA debug build only) the
// macro expands to mark_debug so synthesis preserves these nets under their
// names; otherwise it is empty and the design is untouched. The tap names and
// layers mirror dv/amber_pair_harness_uart_tb.sv probe_* outputs 1:1 so a
// board ILA capture lines up with the sim golden reference (golden_probes.vcd).
`ifdef AMBER_ILA_DBG
  `define AMBER_DBG_NET (* mark_debug = "true" *)
`else
  `define AMBER_DBG_NET
`endif

module amber_pair_harness
    import l1_pkg::*;
#(
    parameter int FPGA_CLK_HZ = 90_000_000,
    parameter int UART_BAUD   = 115_200,

    // amber geometry: s128w4l64b64 (pair-rig FULL geometry)
    parameter int ADDR_WIDTH  = AMBER_ADDR_WIDTH,
    parameter int SETS        = AMBER_SETS,
    parameter int WAYS        = AMBER_WAYS,
    parameter int LINE_BYTES  = AMBER_LINE_BYTES,
    parameter int BUS_WIDTH   = AMBER_BUS_WIDTH,
    parameter int REPL_POLICY = int'(AMBER_REPL_LRU),
    parameter bit USE_MONITOR = 1'b1,

    parameter int AXI_ID_WIDTH   = 8,
    parameter int AXI_USER_WIDTH = 1,
    parameter int MEM_DEPTH      = 131072,   // 512 KB / (BUS_WIDTH/8)

    parameter int MON_N_PROFILE  = 32,

    // When 1, expose the bridge's AXIL host interface directly on the
    // port list and bypass the uart_axil_bridge. This lets cocotb/house
    // BFMs drive the generated bridge without bit-banging UART.
    parameter bit USE_DIRECT_HOST = 1'b0
) (
    input  logic aclk,
    input  logic aresetn,

    // UART host interface (used when USE_DIRECT_HOST=0)
    input  logic i_uart_rx,
    output logic o_uart_tx,

    // Direct AXIL4-Lite host interface (used when USE_DIRECT_HOST=1)
    // Connects to the generated bridge_amber_axil host_adapter instead
    // of the uart_axil_bridge. Signal names mirror the internal nets.
    input  logic [31:0] host_axi_awaddr,
    input  logic [2:0]  host_axi_awprot,
    input  logic        host_axi_awvalid,
    output logic        host_axi_awready,
    input  logic [31:0] host_axi_wdata,
    input  logic [3:0]  host_axi_wstrb,
    input  logic        host_axi_wvalid,
    output logic        host_axi_wready,
    output logic [1:0]  host_axi_bresp,
    output logic        host_axi_bvalid,
    input  logic        host_axi_bready,

    input  logic [31:0] host_axi_araddr,
    input  logic [2:0]  host_axi_arprot,
    input  logic        host_axi_arvalid,
    output logic        host_axi_arready,
    output logic [31:0] host_axi_rdata,
    output logic [1:0]  host_axi_rresp,
    output logic        host_axi_rvalid,
    input  logic        host_axi_rready,

    // Top-level status
    output logic o_done,
    output logic o_busy,
    output logic o_error
);

    localparam int STRB_W      = BUS_WIDTH / 8;
    localparam int IW          = AXI_ID_WIDTH;
    localparam int UW          = AXI_USER_WIDTH;
    localparam int CPU_REQ_W   = ADDR_WIDTH + 1 + STRB_W + BUS_WIDTH;
    localparam int CPU_RSP_W   = BUS_WIDTH;
    localparam int CLKS_PER_BIT = FPGA_CLK_HZ / UART_BAUD;

    // ------------------------------------------------------------------
    // UART -> AXIL bridge
    // ------------------------------------------------------------------
    logic [31:0] uart_awaddr, uart_araddr, uart_wdata;
    logic [2:0]  uart_awprot, uart_arprot;
    logic        uart_awvalid, uart_awready;
    logic [3:0]  uart_wstrb;
    logic        uart_wvalid, uart_wready;
    logic [1:0]  uart_bresp;
    logic        uart_bvalid, uart_bready;
    logic [31:0] uart_rdata;
    logic [1:0]  uart_rresp;
    logic        uart_rvalid, uart_rready;

    generate
        if (USE_DIRECT_HOST) begin : gen_direct_host
            // Bypass the UART bridge and expose the AXIL host interface
            // directly to the port list for cocotb/house BFM control.
            assign uart_awaddr  = host_axi_awaddr;
            assign uart_awprot  = host_axi_awprot;
            assign uart_awvalid = host_axi_awvalid;
            assign host_axi_awready = uart_awready;

            assign uart_wdata   = host_axi_wdata;
            assign uart_wstrb   = host_axi_wstrb;
            assign uart_wvalid  = host_axi_wvalid;
            assign host_axi_wready = uart_wready;

            assign host_axi_bresp  = uart_bresp;
            assign host_axi_bvalid = uart_bvalid;
            assign uart_bready     = host_axi_bready;

            assign uart_araddr  = host_axi_araddr;
            assign uart_arprot  = host_axi_arprot;
            assign uart_arvalid = host_axi_arvalid;
            assign host_axi_arready = uart_arready;

            assign host_axi_rdata  = uart_rdata;
            assign host_axi_rresp  = uart_rresp;
            assign host_axi_rvalid = uart_rvalid;
            assign uart_rready     = host_axi_rready;
        end else begin : gen_uart_bridge
            uart_axil_bridge #(
                .AXIL_ADDR_WIDTH (32),
                .AXIL_DATA_WIDTH (32),
                .CLKS_PER_BIT    (CLKS_PER_BIT)
            ) u_uart (
                .aclk     (aclk),
                .aresetn  (aresetn),
                .i_uart_rx(i_uart_rx),
                .o_uart_tx(o_uart_tx),
                .m_axil_awaddr (uart_awaddr),
                .m_axil_awprot (uart_awprot),
                .m_axil_awvalid(uart_awvalid),
                .m_axil_awready(uart_awready),
                .m_axil_wdata  (uart_wdata),
                .m_axil_wstrb  (uart_wstrb),
                .m_axil_wvalid (uart_wvalid),
                .m_axil_wready (uart_wready),
                .m_axil_bresp  (uart_bresp),
                .m_axil_bvalid (uart_bvalid),
                .m_axil_bready (uart_bready),
                .m_axil_araddr (uart_araddr),
                .m_axil_arprot (uart_arprot),
                .m_axil_arvalid(uart_arvalid),
                .m_axil_arready(uart_arready),
                .m_axil_rdata  (uart_rdata),
                .m_axil_rresp  (uart_rresp),
                .m_axil_rvalid (uart_rvalid),
                .m_axil_rready (uart_rready)
            );

            // ILA taps on uart_axil_bridge internals: the read hang never
            // reaches the fabric, so the wedge must be visible here --
            // dispatcher state, fub AR handshake, master AR, fub R stream.
`ifdef AMBER_ILA_DBG
            `AMBER_DBG_NET logic [3:0] ub_state;
            `AMBER_DBG_NET logic       ub_rx_valid;
            `AMBER_DBG_NET logic       ub_fub_arv;
            `AMBER_DBG_NET logic       ub_fub_arr;
            `AMBER_DBG_NET logic       ub_m_arv;
            `AMBER_DBG_NET logic       ub_m_arr;
            `AMBER_DBG_NET logic       ub_fub_rv;
            `AMBER_DBG_NET logic       ub_fub_rr;

            assign ub_state    = 4'(u_uart.r_cmd_state);
            assign ub_rx_valid = u_uart.w_rx_valid;
            assign ub_fub_arv  = u_uart.w_fub_arvalid;
            assign ub_fub_arr  = u_uart.w_fub_arready;
            assign ub_m_arv    = u_uart.m_axil_arvalid;
            assign ub_m_arr    = u_uart.m_axil_arready;
            assign ub_fub_rv   = u_uart.w_fub_rvalid;
            assign ub_fub_rr   = u_uart.w_fub_rready;
`endif
        end
    endgenerate

    // ------------------------------------------------------------------
    // Generated bridge (1 host master -> 6 slaves)
    // ------------------------------------------------------------------
    // Slave AXIL nets (suffix _sN_*)
    logic [31:0] s0_awaddr, s0_wdata, s0_araddr, s0_rdata;
    logic [3:0]  s0_wstrb;
    logic [2:0]  s0_awprot, s0_arprot;
    logic [1:0]  s0_bresp, s0_rresp;
    logic        s0_awvalid, s0_awready, s0_wvalid, s0_wready;
    logic        s0_bvalid, s0_bready, s0_arvalid, s0_arready;
    `AMBER_DBG_NET logic        s0_rvalid, s0_rready;

    logic [31:0] s1_awaddr, s1_wdata, s1_araddr, s1_rdata;
    logic [3:0]  s1_wstrb;
    logic [2:0]  s1_awprot, s1_arprot;
    logic [1:0]  s1_bresp, s1_rresp;
    logic        s1_awvalid, s1_awready, s1_wvalid, s1_wready;
    logic        s1_bvalid, s1_bready, s1_arvalid, s1_arready, s1_rvalid, s1_rready;

    logic [31:0] s2_awaddr, s2_wdata, s2_araddr, s2_rdata;
    logic [3:0]  s2_wstrb;
    logic [2:0]  s2_awprot, s2_arprot;
    logic [1:0]  s2_bresp, s2_rresp;
    logic        s2_awvalid, s2_awready, s2_wvalid, s2_wready;
    logic        s2_bvalid, s2_bready, s2_arvalid, s2_arready, s2_rvalid, s2_rready;

    // Tally slaves: 64-bit data
    logic [31:0] s3_awaddr, s3_araddr;
    logic [63:0] s3_wdata, s3_rdata;
    logic [7:0]  s3_wstrb;
    logic [2:0]  s3_awprot, s3_arprot;
    logic [1:0]  s3_bresp, s3_rresp;
    logic        s3_awvalid, s3_awready, s3_wvalid, s3_wready;
    logic        s3_bvalid, s3_bready, s3_arvalid, s3_arready, s3_rvalid, s3_rready;

    logic [31:0] s4_awaddr, s4_araddr;
    logic [63:0] s4_wdata, s4_rdata;
    logic [7:0]  s4_wstrb;
    logic [2:0]  s4_awprot, s4_arprot;
    logic [1:0]  s4_bresp, s4_rresp;
    logic        s4_awvalid, s4_awready, s4_wvalid, s4_wready;
    logic        s4_bvalid, s4_bready, s4_arvalid, s4_arready, s4_rvalid, s4_rready;

    logic [31:0] s5_awaddr, s5_araddr;
    logic [63:0] s5_wdata, s5_rdata;
    logic [7:0]  s5_wstrb;
    logic [2:0]  s5_awprot, s5_arprot;
    logic [1:0]  s5_bresp, s5_rresp;
    logic        s5_awvalid, s5_awready, s5_wvalid, s5_wready;
    logic        s5_bvalid, s5_bready, s5_arvalid, s5_arready, s5_rvalid, s5_rready;

    // Bridge unmapped-address status (tied off / observed)
    logic        bridge_unmapped_irq;
    logic [31:0] bridge_unmapped_addr;
    logic [7:0]  bridge_unmapped_count;

    bridge_amber_axil u_bridge (
        .aclk    (aclk),
        .aresetn (aresetn),

        .host_axi_awaddr (uart_awaddr),
        .host_axi_awprot (uart_awprot),
        .host_axi_awvalid(uart_awvalid),
        .host_axi_awready(uart_awready),
        .host_axi_wdata  (uart_wdata),
        .host_axi_wstrb  (uart_wstrb),
        .host_axi_wvalid (uart_wvalid),
        .host_axi_wready (uart_wready),
        .host_axi_bresp  (uart_bresp),
        .host_axi_bvalid (uart_bvalid),
        .host_axi_bready (uart_bready),
        .host_axi_araddr (uart_araddr),
        .host_axi_arprot (uart_arprot),
        .host_axi_arvalid(uart_arvalid),
        .host_axi_arready(uart_arready),
        .host_axi_rdata  (uart_rdata),
        .host_axi_rresp  (uart_rresp),
        .host_axi_rvalid (uart_rvalid),
        .host_axi_rready (uart_rready),

        // Slave 0: harness_csr
        .harness_csr_axi_awaddr (s0_awaddr),
        .harness_csr_axi_awprot (s0_awprot),
        .harness_csr_axi_awvalid(s0_awvalid),
        .harness_csr_axi_awready(s0_awready),
        .harness_csr_axi_wdata  (s0_wdata),
        .harness_csr_axi_wstrb  (s0_wstrb),
        .harness_csr_axi_wvalid (s0_wvalid),
        .harness_csr_axi_wready (s0_wready),
        .harness_csr_axi_bresp  (s0_bresp),
        .harness_csr_axi_bvalid (s0_bvalid),
        .harness_csr_axi_bready (s0_bready),
        .harness_csr_axi_araddr (s0_araddr),
        .harness_csr_axi_arprot (s0_arprot),
        .harness_csr_axi_arvalid(s0_arvalid),
        .harness_csr_axi_arready(s0_arready),
        .harness_csr_axi_rdata  (s0_rdata),
        .harness_csr_axi_rresp  (s0_rresp),
        .harness_csr_axi_rvalid (s0_rvalid),
        .harness_csr_axi_rready (s0_rready),

        // Slave 1: cycle_injector0
        .cycle_injector0_axi_awaddr (s1_awaddr),
        .cycle_injector0_axi_awprot (s1_awprot),
        .cycle_injector0_axi_awvalid(s1_awvalid),
        .cycle_injector0_axi_awready(s1_awready),
        .cycle_injector0_axi_wdata  (s1_wdata),
        .cycle_injector0_axi_wstrb  (s1_wstrb),
        .cycle_injector0_axi_wvalid (s1_wvalid),
        .cycle_injector0_axi_wready (s1_wready),
        .cycle_injector0_axi_bresp  (s1_bresp),
        .cycle_injector0_axi_bvalid (s1_bvalid),
        .cycle_injector0_axi_bready (s1_bready),
        .cycle_injector0_axi_araddr (s1_araddr),
        .cycle_injector0_axi_arprot (s1_arprot),
        .cycle_injector0_axi_arvalid(s1_arvalid),
        .cycle_injector0_axi_arready(s1_arready),
        .cycle_injector0_axi_rdata  (s1_rdata),
        .cycle_injector0_axi_rresp  (s1_rresp),
        .cycle_injector0_axi_rvalid (s1_rvalid),
        .cycle_injector0_axi_rready (s1_rready),

        // Slave 2: cycle_injector1
        .cycle_injector1_axi_awaddr (s2_awaddr),
        .cycle_injector1_axi_awprot (s2_awprot),
        .cycle_injector1_axi_awvalid(s2_awvalid),
        .cycle_injector1_axi_awready(s2_awready),
        .cycle_injector1_axi_wdata  (s2_wdata),
        .cycle_injector1_axi_wstrb  (s2_wstrb),
        .cycle_injector1_axi_wvalid (s2_wvalid),
        .cycle_injector1_axi_wready (s2_wready),
        .cycle_injector1_axi_bresp  (s2_bresp),
        .cycle_injector1_axi_bvalid (s2_bvalid),
        .cycle_injector1_axi_bready (s2_bready),
        .cycle_injector1_axi_araddr (s2_araddr),
        .cycle_injector1_axi_arprot (s2_arprot),
        .cycle_injector1_axi_arvalid(s2_arvalid),
        .cycle_injector1_axi_arready(s2_arready),
        .cycle_injector1_axi_rdata  (s2_rdata),
        .cycle_injector1_axi_rresp  (s2_rresp),
        .cycle_injector1_axi_rvalid (s2_rvalid),
        .cycle_injector1_axi_rready (s2_rready),

        // Slave 3: tally_cnt (read-only count readback)
        .tally_cnt_axi_awaddr (s3_awaddr),
        .tally_cnt_axi_awprot (s3_awprot),
        .tally_cnt_axi_awvalid(s3_awvalid),
        .tally_cnt_axi_awready(s3_awready),
        .tally_cnt_axi_wdata  (s3_wdata),
        .tally_cnt_axi_wstrb  (s3_wstrb),
        .tally_cnt_axi_wvalid (s3_wvalid),
        .tally_cnt_axi_wready (s3_wready),
        .tally_cnt_axi_bresp  (s3_bresp),
        .tally_cnt_axi_bvalid (s3_bvalid),
        .tally_cnt_axi_bready (s3_bready),
        .tally_cnt_axi_araddr (s3_araddr),
        .tally_cnt_axi_arprot (s3_arprot),
        .tally_cnt_axi_arvalid(s3_arvalid),
        .tally_cnt_axi_arready(s3_arready),
        .tally_cnt_axi_rdata  (s3_rdata),
        .tally_cnt_axi_rresp  (s3_rresp),
        .tally_cnt_axi_rvalid (s3_rvalid),
        .tally_cnt_axi_rready (s3_rready),

        // Slave 4: tally_cfgw (config write)
        .tally_cfgw_axi_awaddr (s4_awaddr),
        .tally_cfgw_axi_awprot (s4_awprot),
        .tally_cfgw_axi_awvalid(s4_awvalid),
        .tally_cfgw_axi_awready(s4_awready),
        .tally_cfgw_axi_wdata  (s4_wdata),
        .tally_cfgw_axi_wstrb  (s4_wstrb),
        .tally_cfgw_axi_wvalid (s4_wvalid),
        .tally_cfgw_axi_wready (s4_wready),
        .tally_cfgw_axi_bresp  (s4_bresp),
        .tally_cfgw_axi_bvalid (s4_bvalid),
        .tally_cfgw_axi_bready (s4_bready),
        .tally_cfgw_axi_araddr (s4_araddr),
        .tally_cfgw_axi_arprot (s4_arprot),
        .tally_cfgw_axi_arvalid(s4_arvalid),
        .tally_cfgw_axi_arready(s4_arready),
        .tally_cfgw_axi_rdata  (s4_rdata),
        .tally_cfgw_axi_rresp  (s4_rresp),
        .tally_cfgw_axi_rvalid (s4_rvalid),
        .tally_cfgw_axi_rready (s4_rready),

        // Slave 5: tally_cfgr (config readback)
        .tally_cfgr_axi_awaddr (s5_awaddr),
        .tally_cfgr_axi_awprot (s5_awprot),
        .tally_cfgr_axi_awvalid(s5_awvalid),
        .tally_cfgr_axi_awready(s5_awready),
        .tally_cfgr_axi_wdata  (s5_wdata),
        .tally_cfgr_axi_wstrb  (s5_wstrb),
        .tally_cfgr_axi_wvalid (s5_wvalid),
        .tally_cfgr_axi_wready (s5_wready),
        .tally_cfgr_axi_bresp  (s5_bresp),
        .tally_cfgr_axi_bvalid (s5_bvalid),
        .tally_cfgr_axi_bready (s5_bready),
        .tally_cfgr_axi_araddr (s5_araddr),
        .tally_cfgr_axi_arprot (s5_arprot),
        .tally_cfgr_axi_arvalid(s5_arvalid),
        .tally_cfgr_axi_arready(s5_arready),
        .tally_cfgr_axi_rdata  (s5_rdata),
        .tally_cfgr_axi_rresp  (s5_rresp),
        .tally_cfgr_axi_rvalid (s5_rvalid),
        .tally_cfgr_axi_rready (s5_rready),

        .unmapped_irq  (bridge_unmapped_irq),
        .unmapped_addr (bridge_unmapped_addr),
        .unmapped_count(bridge_unmapped_count),
        .unmapped_clear(1'b0)
    );

    logic [3:0] fabric_dbg_state;

    // ------------------------------------------------------------------
    // harness_csr: global control / status / cycle counter / fabric debug
    // ------------------------------------------------------------------
    localparam int HCSR_CTRL        = 4'h0;
    localparam int HCSR_STATUS      = 4'h1;
    localparam int HCSR_CYCLE_LO    = 4'h2;
    localparam int HCSR_CYCLE_HI    = 4'h3;
    localparam int HCSR_FABRIC_DBG  = 4'h4;

    logic [31:0] hcsr_ctrl, hcsr_status;
    logic [63:0] r_cycle_ctr;

    // Aggregate cycle-injector status
    `AMBER_DBG_NET logic ci0_done, ci0_busy, ci0_err;
    `AMBER_DBG_NET logic ci1_done, ci1_busy, ci1_err;

    assign hcsr_status = {26'b0,
                          ci1_err, ci0_err,
                          ci1_busy, ci0_busy,
                          ci1_done, ci0_done};

    // Free-running cycle counter
    `ALWAYS_FF_RST(aclk, aresetn,
        if (`RST_ASSERTED(aresetn)) begin
            r_cycle_ctr <= '0;
        end else begin
            r_cycle_ctr <= r_cycle_ctr + 1'b1;
        end
    )

    // Simple AXIL slave for harness_csr
    amber_harness_csr u_harness_csr (
        .aclk        (aclk),
        .aresetn     (aresetn),
        .s_axil_awaddr (s0_awaddr),
        .s_axil_awprot (s0_awprot),
        .s_axil_awvalid(s0_awvalid),
        .s_axil_awready(s0_awready),
        .s_axil_wdata  (s0_wdata),
        .s_axil_wstrb  (s0_wstrb),
        .s_axil_wvalid (s0_wvalid),
        .s_axil_wready (s0_wready),
        .s_axil_bresp  (s0_bresp),
        .s_axil_bvalid (s0_bvalid),
        .s_axil_bready (s0_bready),
        .s_axil_araddr (s0_araddr),
        .s_axil_arprot (s0_arprot),
        .s_axil_arvalid(s0_arvalid),
        .s_axil_arready(s0_arready),
        .s_axil_rdata  (s0_rdata),
        .s_axil_rresp  (s0_rresp),
        .s_axil_rvalid (s0_rvalid),
        .s_axil_rready (s0_rready),
        .o_ctrl        (hcsr_ctrl),
        .i_status      (hcsr_status),
        .i_cycle_lo    (r_cycle_ctr[31:0]),
        .i_cycle_hi    (r_cycle_ctr[63:32]),
        .i_fabric_dbg  (fabric_dbg_state)
    );

    // ------------------------------------------------------------------
    // Cycle injectors
    // ------------------------------------------------------------------
    `AMBER_DBG_NET logic ci0_req_valid, ci0_req_ready, ci0_rsp_valid, ci0_rsp_ready;
    logic [CPU_REQ_W-1:0] ci0_req_data;
    logic [CPU_RSP_W-1:0] ci0_rsp_data;

    `AMBER_DBG_NET logic ci1_req_valid, ci1_req_ready, ci1_rsp_valid, ci1_rsp_ready;
    logic [CPU_REQ_W-1:0] ci1_req_data;
    logic [CPU_RSP_W-1:0] ci1_rsp_data;

    amber_cycle_injector #(
        .ADDR_WIDTH  (ADDR_WIDTH),
        .BUS_WIDTH   (BUS_WIDTH),
        .USE_MONITOR (USE_MONITOR)
    ) u_ci0 (
        .aclk            (aclk),
        .aresetn         (aresetn),
        .s_axil_awaddr   (s1_awaddr),
        .s_axil_awprot   (s1_awprot),
        .s_axil_awvalid  (s1_awvalid),
        .s_axil_awready  (s1_awready),
        .s_axil_wdata    (s1_wdata),
        .s_axil_wstrb    (s1_wstrb),
        .s_axil_wvalid   (s1_wvalid),
        .s_axil_wready   (s1_wready),
        .s_axil_bresp    (s1_bresp),
        .s_axil_bvalid   (s1_bvalid),
        .s_axil_bready   (s1_bready),
        .s_axil_araddr   (s1_araddr),
        .s_axil_arprot   (s1_arprot),
        .s_axil_arvalid  (s1_arvalid),
        .s_axil_arready  (s1_arready),
        .s_axil_rdata    (s1_rdata),
        .s_axil_rresp    (s1_rresp),
        .s_axil_rvalid   (s1_rvalid),
        .s_axil_rready   (s1_rready),
        .cpu_req_wr_valid(ci0_req_valid),
        .cpu_req_wr_ready(ci0_req_ready),
        .cpu_req_wr_data (ci0_req_data),
        .cpu_rsp_rd_valid(ci0_rsp_valid),
        .cpu_rsp_rd_ready(ci0_rsp_ready),
        .cpu_rsp_rd_data (ci0_rsp_data),
        .o_done          (ci0_done),
        .o_busy          (ci0_busy),
        .o_err_flag      (ci0_err)
    );

    amber_cycle_injector #(
        .ADDR_WIDTH  (ADDR_WIDTH),
        .BUS_WIDTH   (BUS_WIDTH),
        .USE_MONITOR (USE_MONITOR)
    ) u_ci1 (
        .aclk            (aclk),
        .aresetn         (aresetn),
        .s_axil_awaddr   (s2_awaddr),
        .s_axil_awprot   (s2_awprot),
        .s_axil_awvalid  (s2_awvalid),
        .s_axil_awready  (s2_awready),
        .s_axil_wdata    (s2_wdata),
        .s_axil_wstrb    (s2_wstrb),
        .s_axil_wvalid   (s2_wvalid),
        .s_axil_wready   (s2_wready),
        .s_axil_bresp    (s2_bresp),
        .s_axil_bvalid   (s2_bvalid),
        .s_axil_bready   (s2_bready),
        .s_axil_araddr   (s2_araddr),
        .s_axil_arprot   (s2_arprot),
        .s_axil_arvalid  (s2_arvalid),
        .s_axil_arready  (s2_arready),
        .s_axil_rdata    (s2_rdata),
        .s_axil_rresp    (s2_rresp),
        .s_axil_rvalid   (s2_rvalid),
        .s_axil_rready   (s2_rready),
        .cpu_req_wr_valid(ci1_req_valid),
        .cpu_req_wr_ready(ci1_req_ready),
        .cpu_req_wr_data (ci1_req_data),
        .cpu_rsp_rd_valid(ci1_rsp_valid),
        .cpu_rsp_rd_ready(ci1_rsp_ready),
        .cpu_rsp_rd_data (ci1_rsp_data),
        .o_done          (ci1_done),
        .o_busy          (ci1_busy),
        .o_err_flag      (ci1_err)
    );

    // ILA taps on bridge-internal read-path nets. Downward hierarchy
    // references, exactly as the uart tb's probe_* outputs read them.
`ifdef AMBER_ILA_DBG
    `AMBER_DBG_NET logic        host_arvalid;
    `AMBER_DBG_NET logic        host_arready;
    `AMBER_DBG_NET logic        host_rvalid;
    `AMBER_DBG_NET logic        host_rready;
    `AMBER_DBG_NET logic [31:0] host_rdata;
    `AMBER_DBG_NET logic [1:0]  host_rresp;
    `AMBER_DBG_NET logic        host_rlast;
    `AMBER_DBG_NET logic        fub_rvalid;
    `AMBER_DBG_NET logic        fub_rready;
    `AMBER_DBG_NET logic        cvr_rvalid;
    `AMBER_DBG_NET logic        cvr_rlast;

    assign host_arvalid = u_bridge.host_32b_arvalid;
    assign host_arready = u_bridge.host_32b_arready;
    assign host_rvalid  = u_bridge.host_32b_rvalid;
    assign host_rready  = u_bridge.host_32b_rready;
    assign host_rdata   = u_bridge.host_32b_r.data;
    assign host_rresp   = u_bridge.host_32b_r.resp;
    assign host_rlast   = u_bridge.host_32b_r.last;
    assign fub_rvalid   = u_bridge.u_host_adapter.fub_axi_rvalid;
    assign fub_rready   = u_bridge.u_host_adapter.fub_axi_rready;
    assign cvr_rvalid   = u_bridge.u_harness_csr_adapter.converter_rvalid;
    assign cvr_rlast    = u_bridge.u_harness_csr_adapter.converter_rlast;
`endif

    // ------------------------------------------------------------------
    // Two amber_top caches + pair fabric + memory (mirror amber_pair_rig_tb)
    // ------------------------------------------------------------------
    logic [IW-1:0]        m0_arid, m1_arid;
    logic [ADDR_WIDTH-1:0] m0_araddr, m1_araddr;
    logic [7:0]           m0_arlen, m1_arlen;
    logic [2:0]           m0_arsize, m1_arsize;
    logic [1:0]           m0_arburst, m1_arburst;
    logic                 m0_arlock, m1_arlock;
    logic [3:0]           m0_arcache, m1_arcache;
    logic [2:0]           m0_arprot, m1_arprot;
    logic [3:0]           m0_arqos, m1_arqos;
    logic [3:0]           m0_arregion, m1_arregion;
    logic [UW-1:0]        m0_aruser, m1_aruser;
    logic                 m0_arvalid, m1_arvalid;
    logic                 m0_arready, m1_arready;
    logic [IW-1:0]        m0_rid, m1_rid;
    logic [BUS_WIDTH-1:0] m0_rdata, m1_rdata;
    logic [1:0]           m0_rresp, m1_rresp;
    logic                 m0_rlast, m1_rlast;
    logic [UW-1:0]        m0_ruser, m1_ruser;
    logic                 m0_rvalid, m1_rvalid;
    logic                 m0_rready, m1_rready;

    logic [IW-1:0]        m0_awid, m1_awid;
    logic [ADDR_WIDTH-1:0] m0_awaddr, m1_awaddr;
    logic [7:0]           m0_awlen, m1_awlen;
    logic [2:0]           m0_awsize, m1_awsize;
    logic [1:0]           m0_awburst, m1_awburst;
    logic                 m0_awlock, m1_awlock;
    logic [3:0]           m0_awcache, m1_awcache;
    logic [2:0]           m0_awprot, m1_awprot;
    logic [3:0]           m0_awqos, m1_awqos;
    logic [3:0]           m0_awregion, m1_awregion;
    logic [UW-1:0]        m0_awuser, m1_awuser;
    logic                 m0_awvalid, m1_awvalid;
    logic                 m0_awready, m1_awready;
    logic [BUS_WIDTH-1:0] m0_wdata, m1_wdata;
    logic [STRB_W-1:0]    m0_wstrb, m1_wstrb;
    logic                 m0_wlast, m1_wlast;
    logic [UW-1:0]        m0_wuser, m1_wuser;
    logic                 m0_wvalid, m1_wvalid;
    logic                 m0_wready, m1_wready;
    logic [IW-1:0]        m0_bid, m1_bid;
    logic [1:0]           m0_bresp, m1_bresp;
    logic [UW-1:0]        m0_buser, m1_buser;
    logic                 m0_bvalid, m1_bvalid;
    logic                 m0_bready, m1_bready;

    logic [ADDR_WIDTH-1:0] s0_acaddr, s1_acaddr;
    logic [3:0]            s0_acsnoop, s1_acsnoop;
    logic [2:0]            s0_acprot, s1_acprot;
    logic                  s0_acvalid, s1_acvalid;
    logic                  s0_acready, s1_acready;
    logic [AMBER_CRRESP_WIDTH-1:0] s0_crresp, s1_crresp;
    logic                  s0_crvalid, s1_crvalid;
    logic                  s0_crready, s1_crready;
    logic [BUS_WIDTH-1:0]  s0_cddata, s1_cddata;
    logic                  s0_cdlast, s1_cdlast;
    logic                  s0_cdvalid, s1_cdvalid;
    logic                  s0_cdready, s1_cdready;

    logic                  coh0_valid, coh1_valid;
    logic [ADDR_WIDTH-1:0] coh0_addr, coh1_addr;
    logic [2:0]            coh0_type, coh1_type;

    logic                  init_busy0, init_busy1;
    logic [3:0]            ctrl_state0, ctrl_state1;

    logic [127:0]          mon0_packet, mon1_packet;
    logic [63:0]           mon0_timestamp, mon1_timestamp;
    logic                  mon0_valid, mon1_valid;
    logic                  mon0_ready, mon1_ready;

    amber_top #(
        .ADDR_WIDTH     (ADDR_WIDTH),
        .SETS           (SETS),
        .WAYS           (WAYS),
        .LINE_BYTES     (LINE_BYTES),
        .BUS_WIDTH      (BUS_WIDTH),
        .REPL_POLICY    (REPL_POLICY),
        .AXI_ID_WIDTH   (AXI_ID_WIDTH),
        .AXI_USER_WIDTH (AXI_USER_WIDTH),
        .USE_MONITOR    (USE_MONITOR)
    ) u_amber0 (
        .aclk            (aclk),
        .aresetn         (aresetn),
        .cpu_req_wr_valid(ci0_req_valid),
        .cpu_req_wr_ready(ci0_req_ready),
        .cpu_req_wr_data (ci0_req_data),
        .cpu_rsp_rd_valid(ci0_rsp_valid),
        .cpu_rsp_rd_ready(ci0_rsp_ready),
        .cpu_rsp_rd_data (ci0_rsp_data),
        .m_axi_arid      (m0_arid),
        .m_axi_araddr    (m0_araddr),
        .m_axi_arlen     (m0_arlen),
        .m_axi_arsize    (m0_arsize),
        .m_axi_arburst   (m0_arburst),
        .m_axi_arlock    (m0_arlock),
        .m_axi_arcache   (m0_arcache),
        .m_axi_arprot    (m0_arprot),
        .m_axi_arqos     (m0_arqos),
        .m_axi_arregion  (m0_arregion),
        .m_axi_aruser    (m0_aruser),
        .m_axi_arvalid   (m0_arvalid),
        .m_axi_arready   (m0_arready),
        .m_axi_rid       (m0_rid),
        .m_axi_rdata     (m0_rdata),
        .m_axi_rresp     (m0_rresp),
        .m_axi_rlast     (m0_rlast),
        .m_axi_ruser     (m0_ruser),
        .m_axi_rvalid    (m0_rvalid),
        .m_axi_rready    (m0_rready),
        .m_axi_awid      (m0_awid),
        .m_axi_awaddr    (m0_awaddr),
        .m_axi_awlen     (m0_awlen),
        .m_axi_awsize    (m0_awsize),
        .m_axi_awburst   (m0_awburst),
        .m_axi_awlock    (m0_awlock),
        .m_axi_awcache   (m0_awcache),
        .m_axi_awprot    (m0_awprot),
        .m_axi_awqos     (m0_awqos),
        .m_axi_awregion  (m0_awregion),
        .m_axi_awuser    (m0_awuser),
        .m_axi_awvalid   (m0_awvalid),
        .m_axi_awready   (m0_awready),
        .m_axi_wdata     (m0_wdata),
        .m_axi_wstrb     (m0_wstrb),
        .m_axi_wlast     (m0_wlast),
        .m_axi_wuser     (m0_wuser),
        .m_axi_wvalid    (m0_wvalid),
        .m_axi_wready    (m0_wready),
        .m_axi_bid       (m0_bid),
        .m_axi_bresp     (m0_bresp),
        .m_axi_buser     (m0_buser),
        .m_axi_bvalid    (m0_bvalid),
        .m_axi_bready    (m0_bready),
        .m_axi_acaddr    (s0_acaddr),
        .m_axi_acsnoop   (s0_acsnoop),
        .m_axi_acprot    (s0_acprot),
        .m_axi_acvalid   (s0_acvalid),
        .m_axi_acready   (s0_acready),
        .m_axi_crresp    (s0_crresp),
        .m_axi_crvalid   (s0_crvalid),
        .m_axi_crready   (s0_crready),
        .m_axi_cddata    (s0_cddata),
        .m_axi_cdlast    (s0_cdlast),
        .m_axi_cdvalid   (s0_cdvalid),
        .m_axi_cdready   (s0_cdready),
        .coh_req_valid   (coh0_valid),
        .coh_req_addr    (coh0_addr),
        .coh_req_type    (coh0_type),
        .i_mon_time      (r_cycle_ctr),
        .mon_valid       (mon0_valid),
        .mon_ready       (mon0_ready),
        .mon_packet      (mon0_packet),
        .mon_timestamp   (mon0_timestamp),
        .init_busy       (init_busy0),
        .ctrl_state      (ctrl_state0)
    );

    amber_top #(
        .ADDR_WIDTH     (ADDR_WIDTH),
        .SETS           (SETS),
        .WAYS           (WAYS),
        .LINE_BYTES     (LINE_BYTES),
        .BUS_WIDTH      (BUS_WIDTH),
        .REPL_POLICY    (REPL_POLICY),
        .AXI_ID_WIDTH   (AXI_ID_WIDTH),
        .AXI_USER_WIDTH (AXI_USER_WIDTH),
        .USE_MONITOR    (USE_MONITOR)
    ) u_amber1 (
        .aclk            (aclk),
        .aresetn         (aresetn),
        .cpu_req_wr_valid(ci1_req_valid),
        .cpu_req_wr_ready(ci1_req_ready),
        .cpu_req_wr_data (ci1_req_data),
        .cpu_rsp_rd_valid(ci1_rsp_valid),
        .cpu_rsp_rd_ready(ci1_rsp_ready),
        .cpu_rsp_rd_data (ci1_rsp_data),
        .m_axi_arid      (m1_arid),
        .m_axi_araddr    (m1_araddr),
        .m_axi_arlen     (m1_arlen),
        .m_axi_arsize    (m1_arsize),
        .m_axi_arburst   (m1_arburst),
        .m_axi_arlock    (m1_arlock),
        .m_axi_arcache   (m1_arcache),
        .m_axi_arprot    (m1_arprot),
        .m_axi_arqos     (m1_arqos),
        .m_axi_arregion  (m1_arregion),
        .m_axi_aruser    (m1_aruser),
        .m_axi_arvalid   (m1_arvalid),
        .m_axi_arready   (m1_arready),
        .m_axi_rid       (m1_rid),
        .m_axi_rdata     (m1_rdata),
        .m_axi_rresp     (m1_rresp),
        .m_axi_rlast     (m1_rlast),
        .m_axi_ruser     (m1_ruser),
        .m_axi_rvalid    (m1_rvalid),
        .m_axi_rready    (m1_rready),
        .m_axi_awid      (m1_awid),
        .m_axi_awaddr    (m1_awaddr),
        .m_axi_awlen     (m1_awlen),
        .m_axi_awsize    (m1_awsize),
        .m_axi_awburst   (m1_awburst),
        .m_axi_awlock    (m1_awlock),
        .m_axi_awcache   (m1_awcache),
        .m_axi_awprot    (m1_awprot),
        .m_axi_awqos     (m1_awqos),
        .m_axi_awregion  (m1_awregion),
        .m_axi_awuser    (m1_awuser),
        .m_axi_awvalid   (m1_awvalid),
        .m_axi_awready   (m1_awready),
        .m_axi_wdata     (m1_wdata),
        .m_axi_wstrb     (m1_wstrb),
        .m_axi_wlast     (m1_wlast),
        .m_axi_wuser     (m1_wuser),
        .m_axi_wvalid    (m1_wvalid),
        .m_axi_wready    (m1_wready),
        .m_axi_bid       (m1_bid),
        .m_axi_bresp     (m1_bresp),
        .m_axi_buser     (m1_buser),
        .m_axi_bvalid    (m1_bvalid),
        .m_axi_bready    (m1_bready),
        .m_axi_acaddr    (s1_acaddr),
        .m_axi_acsnoop   (s1_acsnoop),
        .m_axi_acprot    (s1_acprot),
        .m_axi_acvalid   (s1_acvalid),
        .m_axi_acready   (s1_acready),
        .m_axi_crresp    (s1_crresp),
        .m_axi_crvalid   (s1_crvalid),
        .m_axi_crready   (s1_crready),
        .m_axi_cddata    (s1_cddata),
        .m_axi_cdlast    (s1_cdlast),
        .m_axi_cdvalid   (s1_cdvalid),
        .m_axi_cdready   (s1_cdready),
        .coh_req_valid   (coh1_valid),
        .coh_req_addr    (coh1_addr),
        .coh_req_type    (coh1_type),
        .i_mon_time      (r_cycle_ctr),
        .mon_valid       (mon1_valid),
        .mon_ready       (mon1_ready),
        .mon_packet      (mon1_packet),
        .mon_timestamp   (mon1_timestamp),
        .init_busy       (init_busy1),
        .ctrl_state      (ctrl_state1)
    );

    // Fabric -> memory AXI4
    logic [IW-1:0]        mem_arid, mem_awid, mem_rid, mem_bid;
    logic [ADDR_WIDTH-1:0] mem_araddr, mem_awaddr;
    logic [7:0]           mem_arlen, mem_awlen;
    logic [2:0]           mem_arsize, mem_awsize;
    logic [1:0]           mem_arburst, mem_awburst;
    logic                 mem_arlock, mem_awlock;
    logic [3:0]           mem_arcache, mem_awcache;
    logic [2:0]           mem_arprot, mem_awprot;
    logic [3:0]           mem_arqos, mem_awqos;
    logic [3:0]           mem_arregion, mem_awregion;
    logic [UW-1:0]        mem_aruser, mem_awuser, mem_ruser, mem_buser;
    logic                 mem_arvalid, mem_arready;
    logic [BUS_WIDTH-1:0] mem_rdata, mem_wdata;
    logic [1:0]           mem_rresp, mem_bresp;
    logic                 mem_rlast, mem_rvalid, mem_rready;
    logic                 mem_awvalid, mem_awready;
    logic [STRB_W-1:0]    mem_wstrb;
    logic                 mem_wlast, mem_wvalid, mem_wready;
    logic                 mem_bvalid, mem_bready;
    amber_pair_fabric #(
        .ADDR_WIDTH     (ADDR_WIDTH),
        .SETS           (SETS),
        .WAYS           (WAYS),
        .LINE_BYTES     (LINE_BYTES),
        .BUS_WIDTH      (BUS_WIDTH),
        .AXI_ID_WIDTH   (AXI_ID_WIDTH),
        .AXI_USER_WIDTH (AXI_USER_WIDTH)
    ) u_fabric (
        .clk               (aclk),
        .rst_n             (aresetn),
        .c0_arid           (m0_arid),
        .c0_araddr         (m0_araddr),
        .c0_arlen          (m0_arlen),
        .c0_arsize         (m0_arsize),
        .c0_arburst        (m0_arburst),
        .c0_arlock         (m0_arlock),
        .c0_arcache        (m0_arcache),
        .c0_arprot         (m0_arprot),
        .c0_arqos          (m0_arqos),
        .c0_arregion       (m0_arregion),
        .c0_aruser         (m0_aruser),
        .c0_arvalid        (m0_arvalid),
        .c0_arready        (m0_arready),
        .c0_rid            (m0_rid),
        .c0_rdata          (m0_rdata),
        .c0_rresp          (m0_rresp),
        .c0_rlast          (m0_rlast),
        .c0_ruser          (m0_ruser),
        .c0_rvalid         (m0_rvalid),
        .c0_rready         (m0_rready),
        .c0_awid           (m0_awid),
        .c0_awaddr         (m0_awaddr),
        .c0_awlen          (m0_awlen),
        .c0_awsize         (m0_awsize),
        .c0_awburst        (m0_awburst),
        .c0_awlock         (m0_awlock),
        .c0_awcache        (m0_awcache),
        .c0_awprot         (m0_awprot),
        .c0_awqos          (m0_awqos),
        .c0_awregion       (m0_awregion),
        .c0_awuser         (m0_awuser),
        .c0_awvalid        (m0_awvalid),
        .c0_awready        (m0_awready),
        .c0_wdata          (m0_wdata),
        .c0_wstrb          (m0_wstrb),
        .c0_wlast          (m0_wlast),
        .c0_wuser          (m0_wuser),
        .c0_wvalid         (m0_wvalid),
        .c0_wready         (m0_wready),
        .c0_bid            (m0_bid),
        .c0_bresp          (m0_bresp),
        .c0_buser          (m0_buser),
        .c0_bvalid         (m0_bvalid),
        .c0_bready         (m0_bready),
        .c1_arid           (m1_arid),
        .c1_araddr         (m1_araddr),
        .c1_arlen          (m1_arlen),
        .c1_arsize         (m1_arsize),
        .c1_arburst        (m1_arburst),
        .c1_arlock         (m1_arlock),
        .c1_arcache        (m1_arcache),
        .c1_arprot         (m1_arprot),
        .c1_arqos          (m1_arqos),
        .c1_arregion       (m1_arregion),
        .c1_aruser         (m1_aruser),
        .c1_arvalid        (m1_arvalid),
        .c1_arready        (m1_arready),
        .c1_rid            (m1_rid),
        .c1_rdata          (m1_rdata),
        .c1_rresp          (m1_rresp),
        .c1_rlast          (m1_rlast),
        .c1_ruser          (m1_ruser),
        .c1_rvalid         (m1_rvalid),
        .c1_rready         (m1_rready),
        .c1_awid           (m1_awid),
        .c1_awaddr         (m1_awaddr),
        .c1_awlen          (m1_awlen),
        .c1_awsize         (m1_awsize),
        .c1_awburst        (m1_awburst),
        .c1_awlock         (m1_awlock),
        .c1_awcache        (m1_awcache),
        .c1_awprot         (m1_awprot),
        .c1_awqos          (m1_awqos),
        .c1_awregion       (m1_awregion),
        .c1_awuser         (m1_awuser),
        .c1_awvalid        (m1_awvalid),
        .c1_awready        (m1_awready),
        .c1_wdata          (m1_wdata),
        .c1_wstrb          (m1_wstrb),
        .c1_wlast          (m1_wlast),
        .c1_wuser          (m1_wuser),
        .c1_wvalid         (m1_wvalid),
        .c1_wready         (m1_wready),
        .c1_bid            (m1_bid),
        .c1_bresp          (m1_bresp),
        .c1_buser          (m1_buser),
        .c1_bvalid         (m1_bvalid),
        .c1_bready         (m1_bready),
        .s0_acaddr         (s0_acaddr),
        .s0_acsnoop        (s0_acsnoop),
        .s0_acprot         (s0_acprot),
        .s0_acvalid        (s0_acvalid),
        .s0_acready        (s0_acready),
        .s0_crresp         (s0_crresp),
        .s0_crvalid        (s0_crvalid),
        .s0_crready        (s0_crready),
        .s0_cddata         (s0_cddata),
        .s0_cdlast         (s0_cdlast),
        .s0_cdvalid        (s0_cdvalid),
        .s0_cdready        (s0_cdready),
        .s1_acaddr         (s1_acaddr),
        .s1_acsnoop        (s1_acsnoop),
        .s1_acprot         (s1_acprot),
        .s1_acvalid        (s1_acvalid),
        .s1_acready        (s1_acready),
        .s1_crresp         (s1_crresp),
        .s1_crvalid        (s1_crvalid),
        .s1_crready        (s1_crready),
        .s1_cddata         (s1_cddata),
        .s1_cdlast         (s1_cdlast),
        .s1_cdvalid        (s1_cdvalid),
        .s1_cdready        (s1_cdready),
        .c0_coh_req_valid  (coh0_valid),
        .c0_coh_req_addr   (coh0_addr),
        .c0_coh_req_type   (coh0_type),
        .c1_coh_req_valid  (coh1_valid),
        .c1_coh_req_addr   (coh1_addr),
        .c1_coh_req_type   (coh1_type),
        .peer0_state       (ctrl_state0),
        .peer1_state       (ctrl_state1),
        .mem_arid          (mem_arid),
        .mem_araddr        (mem_araddr),
        .mem_arlen         (mem_arlen),
        .mem_arsize        (mem_arsize),
        .mem_arburst       (mem_arburst),
        .mem_arlock        (mem_arlock),
        .mem_arcache       (mem_arcache),
        .mem_arprot        (mem_arprot),
        .mem_arqos         (mem_arqos),
        .mem_arregion      (mem_arregion),
        .mem_aruser        (mem_aruser),
        .mem_arvalid       (mem_arvalid),
        .mem_arready       (mem_arready),
        .mem_rid           (mem_rid),
        .mem_rdata         (mem_rdata),
        .mem_rresp         (mem_rresp),
        .mem_rlast         (mem_rlast),
        .mem_ruser         (mem_ruser),
        .mem_rvalid        (mem_rvalid),
        .mem_rready        (mem_rready),
        .mem_awid          (mem_awid),
        .mem_awaddr        (mem_awaddr),
        .mem_awlen         (mem_awlen),
        .mem_awsize        (mem_awsize),
        .mem_awburst       (mem_awburst),
        .mem_awlock        (mem_awlock),
        .mem_awcache       (mem_awcache),
        .mem_awprot        (mem_awprot),
        .mem_awqos         (mem_awqos),
        .mem_awregion      (mem_awregion),
        .mem_awuser        (mem_awuser),
        .mem_awvalid       (mem_awvalid),
        .mem_awready       (mem_awready),
        .mem_wdata         (mem_wdata),
        .mem_wstrb         (mem_wstrb),
        .mem_wlast         (mem_wlast),
        .mem_wuser         (mem_wuser),
        .mem_wvalid        (mem_wvalid),
        .mem_wready        (mem_wready),
        .mem_bid           (mem_bid),
        .mem_bresp         (mem_bresp),
        .mem_buser         (mem_buser),
        .mem_bvalid        (mem_bvalid),
        .mem_bready        (mem_bready),
        .dbg_state         (fabric_dbg_state),
        .dbg_grant_dir     (),
        .dbg_pend_vld      (),
        .dbg_buf_vld       (),
        .dbg_abs_pend      (),
        .dbg_kill          (),
        .dbg_acsnoop       (),
        .dbg_grant_addr    ()
    );

    sdpram_slave_axi4_axi4 #(
        .AXI_ID_WIDTH  (AXI_ID_WIDTH),
        .ADDR_WIDTH    (ADDR_WIDTH),
        .DATA_WIDTH    (BUS_WIDTH),
        .USER_WIDTH    (AXI_USER_WIDTH),
        .MEM_DEPTH     (MEM_DEPTH),
        // The fabric only issues full-beat writes (cache-line evictions);
        // byte-enable mode prevents block-RAM inference in Vivado.
        .USE_WSTRB     (1'b0)
    ) u_mem (
        .aclk             (aclk),
        .aresetn          (aresetn),
        .s_axi_awid       (mem_awid),
        .s_axi_awaddr     (mem_awaddr),
        .s_axi_awlen      (mem_awlen),
        .s_axi_awsize     (mem_awsize),
        .s_axi_awburst    (mem_awburst),
        .s_axi_awlock     (mem_awlock),
        .s_axi_awcache    (mem_awcache),
        .s_axi_awprot     (mem_awprot),
        .s_axi_awqos      (mem_awqos),
        .s_axi_awregion   (mem_awregion),
        .s_axi_awuser     (mem_awuser),
        .s_axi_awvalid    (mem_awvalid),
        .s_axi_awready    (mem_awready),
        .s_axi_wdata      (mem_wdata),
        .s_axi_wstrb      (mem_wstrb),
        .s_axi_wlast      (mem_wlast),
        .s_axi_wuser      (mem_wuser),
        .s_axi_wvalid     (mem_wvalid),
        .s_axi_wready     (mem_wready),
        .s_axi_bid        (mem_bid),
        .s_axi_bresp      (mem_bresp),
        .s_axi_buser      (mem_buser),
        .s_axi_bvalid     (mem_bvalid),
        .s_axi_bready     (mem_bready),
        .s_axi_arid       (mem_arid),
        .s_axi_araddr     (mem_araddr),
        .s_axi_arlen      (mem_arlen),
        .s_axi_arsize     (mem_arsize),
        .s_axi_arburst    (mem_arburst),
        .s_axi_arlock     (mem_arlock),
        .s_axi_arcache    (mem_arcache),
        .s_axi_arprot     (mem_arprot),
        .s_axi_arqos      (mem_arqos),
        .s_axi_arregion   (mem_arregion),
        .s_axi_aruser     (mem_aruser),
        .s_axi_arvalid    (mem_arvalid),
        .s_axi_arready    (mem_arready),
        .s_axi_rid        (mem_rid),
        .s_axi_rdata      (mem_rdata),
        .s_axi_rresp      (mem_rresp),
        .s_axi_rlast      (mem_rlast),
        .s_axi_ruser      (mem_ruser),
        .s_axi_rvalid     (mem_rvalid),
        .s_axi_rready     (mem_rready),
        .i_cfg_start_clear(1'b0),
        .o_cfg_done_clear (),
        .o_dbg_vr         (),
        .o_dbg_fub_vr     (),
        .o_dbg_bram_wr    (),
        .o_dbg_bram_rd    (),
        .o_dbg_busy_wr    (),
        .o_dbg_busy_rd    ()
    );

    // ------------------------------------------------------------------
    // MonBus merge: {amber0, amber1} -> monbus_axil4_axil4_group -> tally
    // ------------------------------------------------------------------
    logic                    arb_vld [2];
    logic                    arb_rdy [2];
    monitor_common_pkg::monitor_packet_t   arb_pkt [2];
    monitor_common_pkg::monbus_timestamp_t arb_ts  [2];

    assign arb_vld[0] = mon0_valid;
    assign arb_vld[1] = mon1_valid;
    assign mon0_ready = arb_rdy[0];
    assign mon1_ready = arb_rdy[1];
    assign arb_pkt[0] = mon0_packet;
    assign arb_pkt[1] = mon1_packet;
    assign arb_ts[0]  = mon0_timestamp;
    assign arb_ts[1]  = mon1_timestamp;

    logic merged_valid, merged_ready;
    logic [127:0] merged_packet;
    logic [63:0]  merged_timestamp;

    monbus_arbiter #(
        .CLIENTS            (2),
        .INPUT_SKID_ENABLE  (1),
        .OUTPUT_SKID_ENABLE (1),
        .INPUT_SKID_DEPTH   (2),
        .OUTPUT_SKID_DEPTH  (2)
    ) u_monbus_arbiter (
        .axi_aclk            (aclk),
        .axi_aresetn         (aresetn),
        .block_arb           (1'b0),
        .monbus_valid_in     (arb_vld),
        .monbus_ready_in     (arb_rdy),
        .monbus_packet_in    (arb_pkt),
        .monbus_timestamp_in (arb_ts),
        .monbus_valid        (merged_valid),
        .monbus_ready        (merged_ready),
        .monbus_packet       (merged_packet),
        .monbus_timestamp    (merged_timestamp),
        .grant_valid         (),
        .grant               (),
        .grant_id            (),
        .last_grant          ()
    );

    // monbus_axil4_axil4_group: record ingest path only.
    logic [31:0] group_awaddr, group_araddr;
    logic [2:0]  group_awprot, group_arprot;
    logic        group_awvalid, group_awready;
    logic [63:0] group_wdata;
    logic [7:0]  group_wstrb;
    logic        group_wvalid, group_wready;
    logic [1:0]  group_bresp;
    logic        group_bvalid, group_bready;
    logic [63:0] group_rdata;
    logic [1:0]  group_rresp;
    logic        group_rvalid, group_rready;
    logic [63:0] mon_time_out_unused;

    monbus_axil4_axil4_group #(
        .ADDR_WIDTH        (32),
        .S_AXIL_DATA_WIDTH (64),
        .USE_COMPRESSION   (0),
        .HALF_BEAT_EN      (0)
    ) u_group (
        .axi_aclk     (aclk),
        .axi_aresetn  (aresetn),
        .cam_clear    (1'b0),
        .monbus_valid (merged_valid),
        .monbus_ready (merged_ready),
        .monbus_packet(merged_packet),
        .monbus_timestamp(merged_timestamp),
        .mon_time_out (mon_time_out_unused),
        // err FIFO drain (unused)
        .s_axil_arvalid(group_arvalid),
        .s_axil_arready(group_arready),
        .s_axil_araddr (group_araddr),
        .s_axil_arprot (group_arprot),
        .s_axil_rvalid (group_rvalid),
        .s_axil_rready (group_rready),
        .s_axil_rdata  (group_rdata),
        .s_axil_rresp  (group_rresp),
        // bulk capture write -> tally record ingest
        .m_axil_awvalid(group_awvalid),
        .m_axil_awready(group_awready),
        .m_axil_awaddr (group_awaddr),
        .m_axil_awprot (group_awprot),
        .m_axil_wvalid (group_wvalid),
        .m_axil_wready (group_wready),
        .m_axil_wdata  (group_wdata),
        .m_axil_wstrb  (group_wstrb),
        .m_axil_bvalid (group_bvalid),
        .m_axil_bready (group_bready),
        .m_axil_bresp  (group_bresp),
        .irq_out       (),
        .cfg_base_addr (32'h0000_0000),
        .cfg_limit_addr(32'hFFFF_FFFF),
        .cfg_flush_watermark(16'hFF00),
        .cfg_compress_en(1'b0),
        .cfg_axi_pkt_mask   (16'hFFFF),
        .cfg_axi_err_select (16'h0000),
        .cfg_axi_error_mask (16'hFFFF),
        .cfg_axi_timeout_mask(16'hFFFF),
        .cfg_axi_compl_mask (16'hFFFF),
        .cfg_axi_thresh_mask(16'hFFFF),
        .cfg_axi_perf_mask  (16'hFFFF),
        .cfg_axi_addr_mask  (16'hFFFF),
        .cfg_axi_debug_mask (16'hFFFF),
        .cfg_axis_pkt_mask   (16'h0000),
        .cfg_axis_err_select (16'h0000),
        .cfg_axis_error_mask (16'h0000),
        .cfg_axis_timeout_mask(16'h0000),
        .cfg_axis_compl_mask (16'h0000),
        .cfg_axis_credit_mask(16'h0000),
        .cfg_axis_channel_mask(16'h0000),
        .cfg_axis_stream_mask(16'h0000),
        .cfg_core_pkt_mask   (16'hFFFF),
        .cfg_core_err_select (16'h0000),
        .cfg_core_error_mask (16'hFFFF),
        .cfg_core_timeout_mask(16'hFFFF),
        .cfg_core_compl_mask (16'hFFFF),
        .cfg_core_thresh_mask(16'hFFFF),
        .cfg_core_perf_mask  (16'hFFFF),
        .cfg_core_debug_mask (16'hFFFF),
        .err_fifo_full  (),
        .write_fifo_full(),
        .err_fifo_count (),
        .write_fifo_count(),
        .mon_compressor_stat_tier1_a(),
        .mon_compressor_stat_tier1_b(),
        .mon_compressor_stat_tier1_c(),
        .mon_compressor_stat_tier0(),
        .mon_compressor_stat_cam_miss(),
        .mon_compressor_stat_delta_ts_ovf(),
        .mon_compressor_stat_event_data_ovf(),
        .mon_compressor_stat_ed_delta_ovf()
    );

    // Tie off the err FIFO drain side of the group.
    assign group_arvalid = 1'b0;
    assign group_rready  = 1'b1;

    // ------------------------------------------------------------------
    // MonBus tally
    // ------------------------------------------------------------------
    localparam int MON_TALLY_ADDR_BITS = $clog2(MON_N_PROFILE + 1);

    monbus_tally_axil #(
        .ADDR_WIDTH      (32),
        .DATA_WIDTH      (64),
        .TALLY_ADDR_BITS (MON_TALLY_ADDR_BITS),
        .N_PROFILE       (MON_N_PROFILE)
    ) u_tally (
        .aclk(aclk),
        .aresetn(aresetn),
        // record ingest from monbus group
        .rec_awaddr (group_awaddr),
        .rec_awprot (group_awprot),
        .rec_awvalid(group_awvalid),
        .rec_awready(group_awready),
        .rec_wdata  (group_wdata),
        .rec_wstrb  (group_wstrb),
        .rec_wvalid (group_wvalid),
        .rec_wready (group_wready),
        .rec_bresp  (group_bresp),
        .rec_bvalid (group_bvalid),
        .rec_bready (group_bready),
        // count readback
        .cnt_araddr (s3_araddr),
        .cnt_arprot (s3_arprot),
        .cnt_arvalid(s3_arvalid),
        .cnt_arready(s3_arready),
        .cnt_rdata  (s3_rdata),
        .cnt_rresp  (s3_rresp),
        .cnt_rvalid (s3_rvalid),
        .cnt_rready (s3_rready),
        // config write
        .cfgw_awaddr (s4_awaddr),
        .cfgw_awprot (s4_awprot),
        .cfgw_awvalid(s4_awvalid),
        .cfgw_awready(s4_awready),
        .cfgw_wdata  (s4_wdata),
        .cfgw_wstrb  (s4_wstrb),
        .cfgw_wvalid (s4_wvalid),
        .cfgw_wready (s4_wready),
        .cfgw_bresp  (s4_bresp),
        .cfgw_bvalid (s4_bvalid),
        .cfgw_bready (s4_bready),
        // config readback
        .cfgr_araddr (s5_araddr),
        .cfgr_arprot (s5_arprot),
        .cfgr_arvalid(s5_arvalid),
        .cfgr_arready(s5_arready),
        .cfgr_rdata  (s5_rdata),
        .cfgr_rresp  (s5_rresp),
        .cfgr_rvalid (s5_rvalid),
        .cfgr_rready (s5_rready),
        .tally_freeze(1'b0),
        .tally_flush (1'b0),
        .tally_flush_busy(),
        .tally_clear (1'b0)
    );

    // Tie off unused write channels on the count/read-only ports.
    assign s3_awvalid = 1'b0;
    assign s3_wvalid  = 1'b0;
    assign s3_bready  = 1'b1;
    assign s4_arvalid = 1'b0;
    assign s4_rready  = 1'b1;
    assign s5_awvalid = 1'b0;
    assign s5_wvalid  = 1'b0;
    assign s5_bready  = 1'b1;

    // ------------------------------------------------------------------
    // Top-level status aggregation
    // ------------------------------------------------------------------
    assign o_done  = ci0_done && ci1_done;
    assign o_busy  = ci0_busy || ci1_busy;
    assign o_error = ci0_err  || ci1_err;

    // ------------------------------------------------------------------
    // harness_csr sub-module
    // ------------------------------------------------------------------
endmodule : amber_pair_harness

// ----------------------------------------------------------------------------
// Small AXIL slave for the harness-level control/status registers.
// ----------------------------------------------------------------------------
module amber_harness_csr (
    input  logic        aclk,
    input  logic        aresetn,

    input  logic [31:0] s_axil_awaddr,
    input  logic [2:0]  s_axil_awprot,
    input  logic        s_axil_awvalid,
    output logic        s_axil_awready,
    input  logic [31:0] s_axil_wdata,
    input  logic [3:0]  s_axil_wstrb,
    input  logic        s_axil_wvalid,
    output logic        s_axil_wready,
    output logic [1:0]  s_axil_bresp,
    output logic        s_axil_bvalid,
    input  logic        s_axil_bready,

    input  logic [31:0] s_axil_araddr,
    input  logic [2:0]  s_axil_arprot,
    input  logic        s_axil_arvalid,
    output logic        s_axil_arready,
    output logic [31:0] s_axil_rdata,
    output logic [1:0]  s_axil_rresp,
    output logic        s_axil_rvalid,
    input  logic        s_axil_rready,

    output logic [31:0] o_ctrl,
    input  logic [31:0] i_status,
    input  logic [31:0] i_cycle_lo,
    input  logic [31:0] i_cycle_hi,
    input  logic [3:0]  i_fabric_dbg
);

    localparam int HCSR_CTRL       = 4'h0;
    localparam int HCSR_STATUS     = 4'h1;
    localparam int HCSR_CYCLE_LO   = 4'h2;
    localparam int HCSR_CYCLE_HI   = 4'h3;
    localparam int HCSR_FABRIC_DBG = 4'h4;

    logic [31:0] r_ctrl;
    assign o_ctrl = r_ctrl;

    // Write path: accept AW and W independently per AXI4-Lite spec.
    logic        r_bvalid;
    logic        r_aw_done;
    logic        r_w_done;
    logic [31:0] r_awaddr;
    logic [31:0] r_wdata;
    logic [3:0]  r_wstrb;

    assign s_axil_awready = ~r_bvalid & ~r_aw_done;
    assign s_axil_wready  = ~r_bvalid & ~r_w_done;
    assign s_axil_bvalid  = r_bvalid;
    assign s_axil_bresp   = 2'b00;

    `ALWAYS_FF_RST(aclk, aresetn,
        if (`RST_ASSERTED(aresetn)) begin
            r_bvalid  <= 1'b0;
            r_aw_done <= 1'b0;
            r_w_done  <= 1'b0;
            r_ctrl    <= '0;
        end else begin
            if (s_axil_awvalid && s_axil_awready) begin
                r_aw_done <= 1'b1;
                r_awaddr  <= s_axil_awaddr;
            end
            if (s_axil_wvalid && s_axil_wready) begin
                r_w_done <= 1'b1;
                r_wdata  <= s_axil_wdata;
                r_wstrb  <= s_axil_wstrb;
            end
            if (r_aw_done && r_w_done && ~r_bvalid) begin
                r_bvalid  <= 1'b1;
                r_aw_done <= 1'b0;
                r_w_done  <= 1'b0;
                for (int b = 0; b < 4; b++) begin
                    if (r_wstrb[b] && (r_awaddr[5:2] == HCSR_CTRL)) begin
                        r_ctrl[8*b +: 8] <= r_wdata[8*b +: 8];
                    end
                end
            end else if (s_axil_bvalid && s_axil_bready) begin
                r_bvalid <= 1'b0;
            end
        end
    )

    // Read path: capture AR address so the mux stays stable after handshake.
    logic        r_ar_done;
    logic [31:0] r_araddr;
    logic [31:0] r_rdata;
    assign s_axil_arready = ~r_ar_done;
    assign s_axil_rvalid  = r_ar_done;
    assign s_axil_rresp   = 2'b00;
    assign s_axil_rdata   = r_rdata;

    always_comb begin
        case (r_araddr[5:2])
            HCSR_CTRL:       r_rdata = r_ctrl;
            HCSR_STATUS:     r_rdata = i_status;
            HCSR_CYCLE_LO:   r_rdata = i_cycle_lo;
            HCSR_CYCLE_HI:   r_rdata = i_cycle_hi;
            HCSR_FABRIC_DBG: r_rdata = {28'b0, i_fabric_dbg};
            default:         r_rdata = 32'hDEAD_BEEF;
        endcase
    end

    `ALWAYS_FF_RST(aclk, aresetn,
        if (`RST_ASSERTED(aresetn)) begin
            r_ar_done <= 1'b0;
            r_araddr  <= '0;
        end else begin
            if (s_axil_arvalid && s_axil_arready) begin
                r_ar_done <= 1'b1;
                r_araddr  <= s_axil_araddr;
            end else if (s_axil_rvalid && s_axil_rready) begin
                r_ar_done <= 1'b0;
            end
        end
    )

endmodule : amber_harness_csr

`undef AMBER_DBG_NET
