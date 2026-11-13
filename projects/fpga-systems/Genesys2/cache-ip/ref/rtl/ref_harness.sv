// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: 2026 sean galloway
//
// Module: ref_harness
// Purpose: The cache-ip pair rig with a REFERENCE L1 in the cache slot
//   (cache-ip common-ip TASK-003): the jet pair harness minus coherence.
//   Host (UART) -> uart_axil_bridge -> bridge_jet_axil -> {
//      harness_csr, cycle_injector0, cycle_injector1, tally_cnt/cfgw/cfgr }
//   Injector 0 drives the cache in the slot -- REF_CACHE_SEL 0: ref_hpdcache_top
//   (the vendored OpenHW HPDcache), 1: ref_cva6_dcache_top (the vendored CVA6
//   write-back std_nbdcache), 2: jet_prime_top (the house jet fork, jet-prime
//   TASK-001 step 1: jet's RTL with NO pair fabric, its ACE snoop port tied
//   off, the same geometry and MSHR count as the jet rig) -- straight onto
//   the sdpram_slave_axi4_axi4 memory. There is ONE cache: injector 1 keeps
//   its CSR slot (the jet host stack runs unchanged) and talks to
//   ref_null_cache; the three MonBus tally apertures land on ref_axil_stub
//   (no tally, reads return 0). The same bridge, injector, memory, UART and
//   clocking as the jet rig, so a number measured here is like-for-like
//   with jet's and amber's ci0; the SEL 2 row against the jet rig's row
//   isolates what the pair fabric costs a single core.
`timescale 1ns / 1ps

`include "reset_defs.svh"

// ILA observation taps: with JET_ILA_DBG defined (ILA debug build only) the
// macro expands to mark_debug so synthesis preserves these nets under their
// names; otherwise it is empty and the design is untouched. The tap names and
// layers mirror dv/jet_pair_harness_uart_tb.sv probe_* outputs (jet rig) so a
// board ILA capture lines up with the sim golden reference (golden_probes.vcd).
`ifdef JET_ILA_DBG
  `define JET_DBG_NET (* mark_debug = "true" *)
`else
  `define JET_DBG_NET
`endif

module ref_harness
    import l1_pkg::*;
#(
    parameter int FPGA_CLK_HZ = 90_000_000,
    parameter int UART_BAUD   = 115_200,

    // geometry: the pair rig's s128w4l64b64, so the reference matches
    // amber and jet set for set
    parameter int ADDR_WIDTH  = AMBER_ADDR_WIDTH,
    parameter int SETS        = AMBER_SETS,
    parameter int WAYS        = AMBER_WAYS,
    parameter int LINE_BYTES  = AMBER_LINE_BYTES,
    parameter int BUS_WIDTH   = AMBER_BUS_WIDTH,

    parameter int AXI_ID_WIDTH   = 8,
    parameter int AXI_USER_WIDTH = 1,
    parameter int MEM_DEPTH      = 131072,   // 512 KB / (BUS_WIDTH/8)

    // reference cache knobs (HPDcache): outstanding misses, write-buffer
    // entries, and the response-ring depth of the GAXI adapter
    parameter int REF_MSHR_WAYS     = 8,
    parameter int REF_WBUF_ENTRIES  = 8,
    parameter int REF_REORDER_DEPTH = 16,
    // which reference sits in the cache slot: 0 = HPDcache (non-blocking,
    // jet's peer), 1 = CVA6 write-back std_nbdcache (blocking, amber's peer)
    parameter int REF_CACHE_SEL     = 0,     // 0 HPDcache, 1 CVA6 WB, 2 jet-prime direct
    parameter int REF_JETP_MSHR_COUNT = 8,   // SEL 2: J1 MSHR count (the jet rig's bin 17 value)

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
    // Connects to the generated bridge_jet_axil host_adapter instead
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
    logic        uart_arvalid, uart_arready;
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
`ifdef JET_ILA_DBG
            `JET_DBG_NET logic [3:0] ub_state;
            `JET_DBG_NET logic       ub_rx_valid;
            `JET_DBG_NET logic       ub_fub_arv;
            `JET_DBG_NET logic       ub_fub_arr;
            `JET_DBG_NET logic       ub_m_arv;
            `JET_DBG_NET logic       ub_m_arr;
            `JET_DBG_NET logic       ub_fub_rv;
            `JET_DBG_NET logic       ub_fub_rr;

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
    `JET_DBG_NET logic        s0_rvalid, s0_rready;

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

    bridge_jet_axil u_bridge (
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
    assign fabric_dbg_state = 4'b0;   // no coherence fabric in the reference rig

    // ------------------------------------------------------------------
    // harness_csr: global control / status / cycle counter / fabric debug
    // ------------------------------------------------------------------
    localparam logic [3:0] HCSR_CTRL        = 4'h0;
    localparam logic [3:0] HCSR_STATUS      = 4'h1;
    localparam logic [3:0] HCSR_CYCLE_LO    = 4'h2;
    localparam logic [3:0] HCSR_CYCLE_HI    = 4'h3;
    localparam logic [3:0] HCSR_FABRIC_DBG  = 4'h4;

    logic [31:0] hcsr_ctrl, hcsr_status;
    logic [63:0] r_cycle_ctr;

    // Aggregate cycle-injector status
    `JET_DBG_NET logic ci0_done, ci0_busy, ci0_err;
    `JET_DBG_NET logic ci1_done, ci1_busy, ci1_err;

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
    ref_harness_csr u_harness_csr (
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
    `JET_DBG_NET logic ci0_req_valid, ci0_req_ready, ci0_rsp_valid, ci0_rsp_ready;
    logic [CPU_REQ_W-1:0] ci0_req_data;
    logic [CPU_RSP_W-1:0] ci0_rsp_data;

    `JET_DBG_NET logic ci1_req_valid, ci1_req_ready, ci1_rsp_valid, ci1_rsp_ready;
    logic [CPU_REQ_W-1:0] ci1_req_data;
    logic [CPU_RSP_W-1:0] ci1_rsp_data;

    amber_cycle_injector #(
        .ADDR_WIDTH  (ADDR_WIDTH),
        .BUS_WIDTH   (BUS_WIDTH),
        .USE_MONITOR (1'b0)
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
        .USE_MONITOR (1'b0)
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
`ifdef JET_ILA_DBG
    `JET_DBG_NET logic        host_arvalid;
    `JET_DBG_NET logic        host_arready;
    `JET_DBG_NET logic        host_rvalid;
    `JET_DBG_NET logic        host_rready;
    `JET_DBG_NET logic [31:0] host_rdata;
    `JET_DBG_NET logic [1:0]  host_rresp;
    `JET_DBG_NET logic        host_rlast;
    `JET_DBG_NET logic        fub_rvalid;
    `JET_DBG_NET logic        fub_rready;
    `JET_DBG_NET logic        cvr_rvalid;
    `JET_DBG_NET logic        cvr_rlast;

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
    // Reference cache (injector 0) and the null second cache (injector 1)
    // ------------------------------------------------------------------
    ref_null_cache #(
        .REQ_W (CPU_REQ_W),
        .RSP_W (CPU_RSP_W)
    ) u_null1 (
        .aclk            (aclk),
        .aresetn         (aresetn),
        .cpu_req_wr_valid(ci1_req_valid),
        .cpu_req_wr_ready(ci1_req_ready),
        .cpu_req_wr_data (ci1_req_data),
        .cpu_rsp_rd_valid(ci1_rsp_valid),
        .cpu_rsp_rd_ready(ci1_rsp_ready),
        .cpu_rsp_rd_data (ci1_rsp_data)
    );

    /* verilator lint_off UNUSEDSIGNAL */
    logic ref_evt_read_miss, ref_evt_write_miss, ref_rsp_error;
    /* verilator lint_on UNUSEDSIGNAL */

    // Reference cache -> memory AXI4
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
    logic [UW-1:0]        mem_aruser, mem_awuser, mem_wuser, mem_ruser, mem_buser;
    logic                 mem_arvalid, mem_arready;
    logic [BUS_WIDTH-1:0] mem_rdata, mem_wdata;
    logic [1:0]           mem_rresp, mem_bresp;
    logic                 mem_rlast, mem_rvalid, mem_rready;
    logic                 mem_awvalid, mem_awready;
    logic [STRB_W-1:0]    mem_wstrb;
    logic                 mem_wlast, mem_wvalid, mem_wready;
    logic                 mem_bvalid, mem_bready;
    generate
        if (REF_CACHE_SEL == 1) begin : gen_ref_cva6
            assign ref_evt_write_miss = 1'b0;
        ref_cva6_dcache_top #(
            .ADDR_WIDTH     (ADDR_WIDTH),
            .BUS_WIDTH      (BUS_WIDTH),
            .AXI_ID_WIDTH   (AXI_ID_WIDTH),
            .AXI_USER_WIDTH (AXI_USER_WIDTH)
        ) u_ref0 (
            .aclk            (aclk),
            .aresetn         (aresetn),
            .cpu_req_wr_valid(ci0_req_valid),
            .cpu_req_wr_ready(ci0_req_ready),
            .cpu_req_wr_data (ci0_req_data),
            .cpu_rsp_rd_valid(ci0_rsp_valid),
            .cpu_rsp_rd_ready(ci0_rsp_ready),
            .cpu_rsp_rd_data (ci0_rsp_data),
            .m_axi_arid     (mem_arid),
            .m_axi_araddr   (mem_araddr),
            .m_axi_arlen    (mem_arlen),
            .m_axi_arsize   (mem_arsize),
            .m_axi_arburst  (mem_arburst),
            .m_axi_arlock   (mem_arlock),
            .m_axi_arcache  (mem_arcache),
            .m_axi_arprot   (mem_arprot),
            .m_axi_arqos    (mem_arqos),
            .m_axi_arregion (mem_arregion),
            .m_axi_aruser   (mem_aruser),
            .m_axi_arvalid  (mem_arvalid),
            .m_axi_arready  (mem_arready),
            .m_axi_rid      (mem_rid),
            .m_axi_rdata    (mem_rdata),
            .m_axi_rresp    (mem_rresp),
            .m_axi_rlast    (mem_rlast),
            .m_axi_ruser    (mem_ruser),
            .m_axi_rvalid   (mem_rvalid),
            .m_axi_rready   (mem_rready),
            .m_axi_awid     (mem_awid),
            .m_axi_awaddr   (mem_awaddr),
            .m_axi_awlen    (mem_awlen),
            .m_axi_awsize   (mem_awsize),
            .m_axi_awburst  (mem_awburst),
            .m_axi_awlock   (mem_awlock),
            .m_axi_awcache  (mem_awcache),
            .m_axi_awprot   (mem_awprot),
            .m_axi_awqos    (mem_awqos),
            .m_axi_awregion (mem_awregion),
            .m_axi_awuser   (mem_awuser),
            .m_axi_awvalid  (mem_awvalid),
            .m_axi_awready  (mem_awready),
            .m_axi_wdata    (mem_wdata),
            .m_axi_wstrb    (mem_wstrb),
            .m_axi_wlast    (mem_wlast),
            .m_axi_wuser    (mem_wuser),
            .m_axi_wvalid   (mem_wvalid),
            .m_axi_wready   (mem_wready),
            .m_axi_bid      (mem_bid),
            .m_axi_bresp    (mem_bresp),
            .m_axi_buser    (mem_buser),
            .m_axi_bvalid   (mem_bvalid),
            .m_axi_bready   (mem_bready),
            .o_miss          (ref_evt_read_miss),
            .o_rsp_error     (ref_rsp_error)
        );
        end else if (REF_CACHE_SEL == 2) begin : gen_ref_jetp
            // jet-prime straight onto memory: no pair fabric, the ACE snoop
            // port idle (acvalid low, CR/CD drained), the D-8 coherence
            // sideband and MonBus unobserved (mon_ready high so the monlite
            // transports never back-pressure the cache). Same parameters as
            // the jet rig's u_jet0 (LRU, monitors on, MSHR_COUNT from the
            // rig knob) so the only difference from the jet row is the fabric.
            assign ref_evt_read_miss  = 1'b0;   // jet reports misses on MonBus, not as pins
            assign ref_evt_write_miss = 1'b0;
            assign ref_rsp_error      = 1'b0;
            /* verilator lint_off UNUSEDSIGNAL */
            logic                        jetp_acready, jetp_crvalid, jetp_cdvalid, jetp_cdlast;
            logic [AMBER_CRRESP_WIDTH-1:0] jetp_crresp;
            logic [BUS_WIDTH-1:0]        jetp_cddata;
            logic                        jetp_coh_req_valid;
            logic [ADDR_WIDTH-1:0]       jetp_coh_req_addr;
            logic [2:0]                  jetp_coh_req_type;
            logic                        jetp_mon_valid, jetp_init_busy, jetp_lkup_live, jetp_busy;
            logic [127:0]                jetp_mon_packet;
            logic [63:0]                 jetp_mon_timestamp;
            logic [3:0]                  jetp_ctrl_state;
            /* verilator lint_on UNUSEDSIGNAL */
        jet_prime_top #(
            .ADDR_WIDTH     (ADDR_WIDTH),
            .SETS           (SETS),
            .WAYS           (WAYS),
            .LINE_BYTES     (LINE_BYTES),
            .BUS_WIDTH      (BUS_WIDTH),
            .REPL_POLICY    (int'(AMBER_REPL_LRU)),
            .AXI_ID_WIDTH   (AXI_ID_WIDTH),
            .AXI_USER_WIDTH (AXI_USER_WIDTH),
            .USE_MONITOR    (1'b1),
            .MSHR_COUNT     (REF_JETP_MSHR_COUNT)
        ) u_ref0 (
            .aclk            (aclk),
            .aresetn         (aresetn),
            .cpu_req_wr_valid(ci0_req_valid),
            .cpu_req_wr_ready(ci0_req_ready),
            .cpu_req_wr_data (ci0_req_data),
            .cpu_rsp_rd_valid(ci0_rsp_valid),
            .cpu_rsp_rd_ready(ci0_rsp_ready),
            .cpu_rsp_rd_data (ci0_rsp_data),
            .m_axi_arid     (mem_arid),
            .m_axi_araddr   (mem_araddr),
            .m_axi_arlen    (mem_arlen),
            .m_axi_arsize   (mem_arsize),
            .m_axi_arburst  (mem_arburst),
            .m_axi_arlock   (mem_arlock),
            .m_axi_arcache  (mem_arcache),
            .m_axi_arprot   (mem_arprot),
            .m_axi_arqos    (mem_arqos),
            .m_axi_arregion (mem_arregion),
            .m_axi_aruser   (mem_aruser),
            .m_axi_arvalid  (mem_arvalid),
            .m_axi_arready  (mem_arready),
            .m_axi_rid      (mem_rid),
            .m_axi_rdata    (mem_rdata),
            .m_axi_rresp    (mem_rresp),
            .m_axi_rlast    (mem_rlast),
            .m_axi_ruser    (mem_ruser),
            .m_axi_rvalid   (mem_rvalid),
            .m_axi_rready   (mem_rready),
            .m_axi_awid     (mem_awid),
            .m_axi_awaddr   (mem_awaddr),
            .m_axi_awlen    (mem_awlen),
            .m_axi_awsize   (mem_awsize),
            .m_axi_awburst  (mem_awburst),
            .m_axi_awlock   (mem_awlock),
            .m_axi_awcache  (mem_awcache),
            .m_axi_awprot   (mem_awprot),
            .m_axi_awqos    (mem_awqos),
            .m_axi_awregion (mem_awregion),
            .m_axi_awuser   (mem_awuser),
            .m_axi_awvalid  (mem_awvalid),
            .m_axi_awready  (mem_awready),
            .m_axi_wdata    (mem_wdata),
            .m_axi_wstrb    (mem_wstrb),
            .m_axi_wlast    (mem_wlast),
            .m_axi_wuser    (mem_wuser),
            .m_axi_wvalid   (mem_wvalid),
            .m_axi_wready   (mem_wready),
            .m_axi_bid      (mem_bid),
            .m_axi_bresp    (mem_bresp),
            .m_axi_buser    (mem_buser),
            .m_axi_bvalid   (mem_bvalid),
            .m_axi_bready   (mem_bready),
            // ACE snoop responder: no snooper on this rig
            .m_axi_acaddr   ('0),
            .m_axi_acsnoop  (4'h0),
            .m_axi_acprot   (3'h0),
            .m_axi_acvalid  (1'b0),
            .m_axi_acready  (jetp_acready),
            .m_axi_crresp   (jetp_crresp),
            .m_axi_crvalid  (jetp_crvalid),
            .m_axi_crready  (1'b1),
            .m_axi_cddata   (jetp_cddata),
            .m_axi_cdlast   (jetp_cdlast),
            .m_axi_cdvalid  (jetp_cdvalid),
            .m_axi_cdready  (1'b1),
            // D-8 coherence sideband: nobody listens
            .coh_req_valid  (jetp_coh_req_valid),
            .coh_req_addr   (jetp_coh_req_addr),
            .coh_req_type   (jetp_coh_req_type),
            // MonBus: produced, never consumed
            .i_mon_time     (r_cycle_ctr),
            .mon_valid      (jetp_mon_valid),
            .mon_ready      (1'b1),
            .mon_packet     (jetp_mon_packet),
            .mon_timestamp  (jetp_mon_timestamp),
            .init_busy      (jetp_init_busy),
            .ctrl_state     (jetp_ctrl_state),
            .lkup_live      (jetp_lkup_live),
            .busy           (jetp_busy)
        );
        end else begin : gen_ref_hpd
        ref_hpdcache_top #(
            .ADDR_WIDTH     (ADDR_WIDTH),
            .SETS           (SETS),
            .WAYS           (WAYS),
            .LINE_BYTES     (LINE_BYTES),
            .BUS_WIDTH      (BUS_WIDTH),
            .AXI_ID_WIDTH   (AXI_ID_WIDTH),
            .AXI_USER_WIDTH (AXI_USER_WIDTH),
            .MSHR_WAYS      (REF_MSHR_WAYS),
            .WBUF_ENTRIES   (REF_WBUF_ENTRIES),
            .REORDER_DEPTH  (REF_REORDER_DEPTH)
        ) u_ref0 (
            .aclk            (aclk),
            .aresetn         (aresetn),
            .cpu_req_wr_valid(ci0_req_valid),
            .cpu_req_wr_ready(ci0_req_ready),
            .cpu_req_wr_data (ci0_req_data),
            .cpu_rsp_rd_valid(ci0_rsp_valid),
            .cpu_rsp_rd_ready(ci0_rsp_ready),
            .cpu_rsp_rd_data (ci0_rsp_data),
            .m_axi_arid     (mem_arid),
            .m_axi_araddr   (mem_araddr),
            .m_axi_arlen    (mem_arlen),
            .m_axi_arsize   (mem_arsize),
            .m_axi_arburst  (mem_arburst),
            .m_axi_arlock   (mem_arlock),
            .m_axi_arcache  (mem_arcache),
            .m_axi_arprot   (mem_arprot),
            .m_axi_arqos    (mem_arqos),
            .m_axi_arregion (mem_arregion),
            .m_axi_aruser   (mem_aruser),
            .m_axi_arvalid  (mem_arvalid),
            .m_axi_arready  (mem_arready),
            .m_axi_rid      (mem_rid),
            .m_axi_rdata    (mem_rdata),
            .m_axi_rresp    (mem_rresp),
            .m_axi_rlast    (mem_rlast),
            .m_axi_ruser    (mem_ruser),
            .m_axi_rvalid   (mem_rvalid),
            .m_axi_rready   (mem_rready),
            .m_axi_awid     (mem_awid),
            .m_axi_awaddr   (mem_awaddr),
            .m_axi_awlen    (mem_awlen),
            .m_axi_awsize   (mem_awsize),
            .m_axi_awburst  (mem_awburst),
            .m_axi_awlock   (mem_awlock),
            .m_axi_awcache  (mem_awcache),
            .m_axi_awprot   (mem_awprot),
            .m_axi_awqos    (mem_awqos),
            .m_axi_awregion (mem_awregion),
            .m_axi_awuser   (mem_awuser),
            .m_axi_awvalid  (mem_awvalid),
            .m_axi_awready  (mem_awready),
            .m_axi_wdata    (mem_wdata),
            .m_axi_wstrb    (mem_wstrb),
            .m_axi_wlast    (mem_wlast),
            .m_axi_wuser    (mem_wuser),
            .m_axi_wvalid   (mem_wvalid),
            .m_axi_wready   (mem_wready),
            .m_axi_bid      (mem_bid),
            .m_axi_bresp    (mem_bresp),
            .m_axi_buser    (mem_buser),
            .m_axi_bvalid   (mem_bvalid),
            .m_axi_bready   (mem_bready),
            .o_evt_read_miss (ref_evt_read_miss),
            .o_evt_write_miss(ref_evt_write_miss),
            .o_rsp_error     (ref_rsp_error)
        );
        end
    endgenerate

    // Shared memory (the pair rig's: 512 KB block RAM behind AXI4)
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
    // No MonBus tally: the three tally apertures of the shared bridge map
    // ack writes and read zero, so the jet host stack runs unchanged
    // ------------------------------------------------------------------
    ref_axil_stub #(.ADDR_WIDTH(32), .DATA_WIDTH(64)) u_tally_stub_cnt (
        .aclk          (aclk),
        .aresetn       (aresetn),
        .s_axil_awaddr  (s3_awaddr),
        .s_axil_awprot  (s3_awprot),
        .s_axil_awvalid (s3_awvalid),
        .s_axil_awready (s3_awready),
        .s_axil_wdata   (s3_wdata),
        .s_axil_wstrb   (s3_wstrb),
        .s_axil_wvalid  (s3_wvalid),
        .s_axil_wready  (s3_wready),
        .s_axil_bresp   (s3_bresp),
        .s_axil_bvalid  (s3_bvalid),
        .s_axil_bready  (s3_bready),
        .s_axil_araddr  (s3_araddr),
        .s_axil_arprot  (s3_arprot),
        .s_axil_arvalid (s3_arvalid),
        .s_axil_arready (s3_arready),
        .s_axil_rdata   (s3_rdata),
        .s_axil_rresp   (s3_rresp),
        .s_axil_rvalid  (s3_rvalid),
        .s_axil_rready  (s3_rready)
    );

    ref_axil_stub #(.ADDR_WIDTH(32), .DATA_WIDTH(64)) u_tally_stub_cfgw (
        .aclk          (aclk),
        .aresetn       (aresetn),
        .s_axil_awaddr  (s4_awaddr),
        .s_axil_awprot  (s4_awprot),
        .s_axil_awvalid (s4_awvalid),
        .s_axil_awready (s4_awready),
        .s_axil_wdata   (s4_wdata),
        .s_axil_wstrb   (s4_wstrb),
        .s_axil_wvalid  (s4_wvalid),
        .s_axil_wready  (s4_wready),
        .s_axil_bresp   (s4_bresp),
        .s_axil_bvalid  (s4_bvalid),
        .s_axil_bready  (s4_bready),
        .s_axil_araddr  (s4_araddr),
        .s_axil_arprot  (s4_arprot),
        .s_axil_arvalid (s4_arvalid),
        .s_axil_arready (s4_arready),
        .s_axil_rdata   (s4_rdata),
        .s_axil_rresp   (s4_rresp),
        .s_axil_rvalid  (s4_rvalid),
        .s_axil_rready  (s4_rready)
    );

    ref_axil_stub #(.ADDR_WIDTH(32), .DATA_WIDTH(64)) u_tally_stub_cfgr (
        .aclk          (aclk),
        .aresetn       (aresetn),
        .s_axil_awaddr  (s5_awaddr),
        .s_axil_awprot  (s5_awprot),
        .s_axil_awvalid (s5_awvalid),
        .s_axil_awready (s5_awready),
        .s_axil_wdata   (s5_wdata),
        .s_axil_wstrb   (s5_wstrb),
        .s_axil_wvalid  (s5_wvalid),
        .s_axil_wready  (s5_wready),
        .s_axil_bresp   (s5_bresp),
        .s_axil_bvalid  (s5_bvalid),
        .s_axil_bready  (s5_bready),
        .s_axil_araddr  (s5_araddr),
        .s_axil_arprot  (s5_arprot),
        .s_axil_arvalid (s5_arvalid),
        .s_axil_arready (s5_arready),
        .s_axil_rdata   (s5_rdata),
        .s_axil_rresp   (s5_rresp),
        .s_axil_rvalid  (s5_rvalid),
        .s_axil_rready  (s5_rready)
    );

    // ------------------------------------------------------------------
    // Top-level status aggregation
    // ------------------------------------------------------------------
    assign o_done  = ci0_done && ci1_done;
    assign o_busy  = ci0_busy || ci1_busy;
    assign o_error = ci0_err  || ci1_err;

    // ------------------------------------------------------------------
    // harness_csr sub-module
    // ------------------------------------------------------------------
endmodule : ref_harness

// ----------------------------------------------------------------------------
// Small AXIL slave for the harness-level control/status registers.
// ----------------------------------------------------------------------------
module ref_harness_csr (
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

    localparam logic [3:0] HCSR_CTRL       = 4'h0;
    localparam logic [3:0] HCSR_STATUS     = 4'h1;
    localparam logic [3:0] HCSR_CYCLE_LO   = 4'h2;
    localparam logic [3:0] HCSR_CYCLE_HI   = 4'h3;
    localparam logic [3:0] HCSR_FABRIC_DBG = 4'h4;

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
            // CTRL[0] (tally_clear) is write-1-pulse: a write with bit 0 set
            // raises o_ctrl[0] for exactly one cycle, then it self-clears.
            r_ctrl[0] <= 1'b0;
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
    `JET_DBG_NET logic        r_ar_done;
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

endmodule : ref_harness_csr

`undef JET_DBG_NET
