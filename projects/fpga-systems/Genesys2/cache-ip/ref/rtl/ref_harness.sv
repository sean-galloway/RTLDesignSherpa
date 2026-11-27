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
//   the sdpram_slave_axi4_axi4 memory; 3: the jet-prime PAIR (two
//   jet_prime_top through the pipelined jet_prime_pair_fabric, TASK-001
//   step 3), the only selection with a cache behind injector 1. Otherwise
//   there is ONE cache: injector 1 keeps its CSR slot (the jet host stack
//   runs unchanged) and talks to ref_null_cache; the three MonBus tally
//   apertures land on ref_axil_stub (no tally, reads return 0). The same bridge, injector, memory, UART and
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
    parameter int REF_CACHE_SEL     = 0,     // 0 HPDcache, 1 CVA6 WB, 2 jet-prime direct, 3 jet-prime pair (pair fabric),
                                             // 4 jet-prime pair behind onyx_ccu (AR alongside the snoop), 5 the same with DEFER_AR
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
    logic [31:0] onyx_cnt [8];   // the onyx counters (zero outside SEL 4 / 5)
    logic [31:0] onyx_mon_ctrl;  // the onyx observer's masks (CSR 0x038 / 0x03C; onyx_monlite's ocelus layers)
    logic [31:0] onyx_mon_mask;
    logic [31:0] onyx_mon_win_low;   // the observer's address window (CSR 0x014 / 0x018; CTRL[3] enables)
    logic [31:0] onyx_mon_win_high;
    // the IO doorbell (CSR 0x040 .. 0x058; onyx TASK-001 step 7): one
    // single-beat access on onyx's ACE-Lite IO port per go
    logic        io_go, io_write, io_sh;
    logic [31:0] io_addr;
    logic [63:0] io_wdata;
    logic [7:0]  io_strb;
    logic        io_busy, io_done, io_absent;
    logic [1:0]  io_resp;
    logic [63:0] io_rdata;
    /* verilator lint_off UNUSEDSIGNAL */
    logic unused_onyx_mon_cfg;   // the selections without onyx, and the bits the two-port build leaves
    assign unused_onyx_mon_cfg = &{1'b0, onyx_mon_ctrl, onyx_mon_mask, onyx_mon_win_low, onyx_mon_win_high,
                                   io_go, io_write, io_sh, io_addr, io_wdata, io_strb};
    /* verilator lint_on UNUSEDSIGNAL */

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
        .i_fabric_dbg  (fabric_dbg_state),
        .i_onyx_cnt    (onyx_cnt),
        .o_onyx_mon_ctrl (onyx_mon_ctrl),
        .o_onyx_mon_mask (onyx_mon_mask),
        .o_onyx_mon_win_low  (onyx_mon_win_low),
        .o_onyx_mon_win_high (onyx_mon_win_high),
        .o_io_go       (io_go),
        .o_io_write    (io_write),
        .o_io_sh       (io_sh),
        .o_io_addr     (io_addr),
        .o_io_wdata    (io_wdata),
        .o_io_strb     (io_strb),
        .i_io_busy     (io_busy),
        .i_io_done     (io_done),
        .i_io_resp     (io_resp),
        .i_io_rdata    (io_rdata),
        .i_io_absent   (io_absent)
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
    // Reference cache (injector 0) and the null second cache (injector 1;
    // SEL 3 gives injector 1 a jet-prime of its own)
    // ------------------------------------------------------------------
    generate
        if (REF_CACHE_SEL < 3) begin : gen_null1
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
        end
    endgenerate

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
            for (genvar k = 0; k < 8; k++) begin : g_z
                assign onyx_cnt[k] = '0;
            end
            // no IO port in this selection: the doorbell reads absent
            assign io_busy = 1'b0; assign io_done = 1'b0; assign io_resp = 2'b00;
            assign io_rdata = '0;  assign io_absent = 1'b1;
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
            for (genvar k = 0; k < 8; k++) begin : g_z
                assign onyx_cnt[k] = '0;
            end
            // no IO port in this selection: the doorbell reads absent
            assign io_busy = 1'b0; assign io_done = 1'b0; assign io_resp = 2'b00;
            assign io_rdata = '0;  assign io_absent = 1'b1;
            /* verilator lint_off UNUSEDSIGNAL */
            logic                        jetp_acready, jetp_crvalid, jetp_cdvalid, jetp_cdlast;
            logic [AMBER_CRRESP_WIDTH-1:0] jetp_crresp;
            logic [BUS_WIDTH-1:0]        jetp_cddata;
            logic                        jetp_coh_req_valid;
            logic [ADDR_WIDTH-1:0]       jetp_coh_req_addr;
            logic [2:0]                  jetp_coh_req_type;
            logic                        jetp_mon_valid, jetp_init_busy, jetp_busy;
            logic                        jetp_coh_done_valid;
            logic [IW-1:0]               jetp_coh_done_id;
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
            .coh_done_valid (jetp_coh_done_valid),
            .coh_done_id    (jetp_coh_done_id),
            // MonBus: produced, never consumed
            .i_mon_time     (r_cycle_ctr),
            .mon_valid      (jetp_mon_valid),
            .mon_ready      (1'b1),
            .mon_packet     (jetp_mon_packet),
            .mon_timestamp  (jetp_mon_timestamp),
            .init_busy      (jetp_init_busy),
            .ctrl_state     (jetp_ctrl_state),
            .busy           (jetp_busy)
        );
        end else if (REF_CACHE_SEL >= 3) begin : gen_ref_jetpp
            // jet-prime PAIR (TASK-001 step 3): two jet_prime_top caches, one
            // per injector, through the pipelined jet_prime_pair_fabric onto
            // the memory -- the jet rig's structure with jet-prime's RTL, so
            // the ci1-idle row against SEL 2 is exactly the fabric's cost to
            // a single core, and against the jet rig's row the fabric
            // rebuild.  Same parameters as SEL 2 (LRU, monitors on,
            // MSHR_COUNT from the rig knob); MonBus produced, never consumed.
            assign ref_evt_read_miss  = 1'b0;
            assign ref_evt_write_miss = 1'b0;
            assign ref_rsp_error      = 1'b0;
            logic [IW-1:0]               c0_arid, c1_arid;
            logic [ADDR_WIDTH-1:0]       c0_araddr, c1_araddr;
            logic [8-1:0]                c0_arlen, c1_arlen;
            logic [3-1:0]                c0_arsize, c1_arsize;
            logic [2-1:0]                c0_arburst, c1_arburst;
            logic                        c0_arlock, c1_arlock;
            logic [4-1:0]                c0_arcache, c1_arcache;
            logic [3-1:0]                c0_arprot, c1_arprot;
            logic [4-1:0]                c0_arqos, c1_arqos;
            logic [4-1:0]                c0_arregion, c1_arregion;
            logic [UW-1:0]               c0_aruser, c1_aruser;
            logic                        c0_arvalid, c1_arvalid;
            logic                        c0_arready, c1_arready;
            logic [IW-1:0]               c0_rid, c1_rid;
            logic [BUS_WIDTH-1:0]        c0_rdata, c1_rdata;
            logic [2-1:0]                c0_rresp, c1_rresp;
            logic                        c0_rlast, c1_rlast;
            logic [UW-1:0]               c0_ruser, c1_ruser;
            logic                        c0_rvalid, c1_rvalid;
            logic                        c0_rready, c1_rready;
            logic [IW-1:0]               c0_awid, c1_awid;
            logic [ADDR_WIDTH-1:0]       c0_awaddr, c1_awaddr;
            logic [8-1:0]                c0_awlen, c1_awlen;
            logic [3-1:0]                c0_awsize, c1_awsize;
            logic [2-1:0]                c0_awburst, c1_awburst;
            logic                        c0_awlock, c1_awlock;
            logic [4-1:0]                c0_awcache, c1_awcache;
            logic [3-1:0]                c0_awprot, c1_awprot;
            logic [4-1:0]                c0_awqos, c1_awqos;
            logic [4-1:0]                c0_awregion, c1_awregion;
            logic [UW-1:0]               c0_awuser, c1_awuser;
            logic                        c0_awvalid, c1_awvalid;
            logic                        c0_awready, c1_awready;
            logic [BUS_WIDTH-1:0]        c0_wdata, c1_wdata;
            logic [STRB_W-1:0]           c0_wstrb, c1_wstrb;
            logic                        c0_wlast, c1_wlast;
            logic [UW-1:0]               c0_wuser, c1_wuser;
            logic                        c0_wvalid, c1_wvalid;
            logic                        c0_wready, c1_wready;
            logic [IW-1:0]               c0_bid, c1_bid;
            logic [2-1:0]                c0_bresp, c1_bresp;
            logic [UW-1:0]               c0_buser, c1_buser;
            logic                        c0_bvalid, c1_bvalid;
            logic                        c0_bready, c1_bready;
            logic [ADDR_WIDTH-1:0]       s0_acaddr, s1_acaddr;
            logic [3:0]                  s0_acsnoop, s1_acsnoop;
            logic [2:0]                  s0_acprot, s1_acprot;
            logic                        s0_acvalid, s1_acvalid, s0_acready, s1_acready;
            logic [AMBER_CRRESP_WIDTH-1:0] s0_crresp, s1_crresp;
            logic                        s0_crvalid, s1_crvalid, s0_crready, s1_crready;
            logic [BUS_WIDTH-1:0]        s0_cddata, s1_cddata;
            logic                        s0_cdlast, s1_cdlast, s0_cdvalid, s1_cdvalid, s0_cdready, s1_cdready;
            logic                        coh0_valid, coh1_valid;
            logic [ADDR_WIDTH-1:0]       coh0_addr, coh1_addr;
            logic [2:0]                  coh0_type, coh1_type;
            logic                        done0_valid, done1_valid;
            logic [IW-1:0]               done0_id, done1_id;
            /* verilator lint_off UNUSEDSIGNAL */
            logic [1:0]                  jpp_mon_valid, jpp_mon_ready, jpp_init_busy, jpp_busy;
            logic [127:0]                jpp_mon_packet [2];
            logic [63:0]                 jpp_mon_timestamp [2];
            logic                        onyx_mon_valid, onyx_mon_ready;
            logic [127:0]                onyx_mon_packet;
            logic [63:0]                 onyx_mon_timestamp;
            logic [3:0]                  jpp_ctrl_state [2];
            logic                        jpp_fab_busy;
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
            .m_axi_arid     (c0_arid),
            .m_axi_araddr   (c0_araddr),
            .m_axi_arlen    (c0_arlen),
            .m_axi_arsize   (c0_arsize),
            .m_axi_arburst  (c0_arburst),
            .m_axi_arlock   (c0_arlock),
            .m_axi_arcache  (c0_arcache),
            .m_axi_arprot   (c0_arprot),
            .m_axi_arqos    (c0_arqos),
            .m_axi_arregion (c0_arregion),
            .m_axi_aruser   (c0_aruser),
            .m_axi_arvalid  (c0_arvalid),
            .m_axi_arready  (c0_arready),
            .m_axi_rid      (c0_rid),
            .m_axi_rdata    (c0_rdata),
            .m_axi_rresp    (c0_rresp),
            .m_axi_rlast    (c0_rlast),
            .m_axi_ruser    (c0_ruser),
            .m_axi_rvalid   (c0_rvalid),
            .m_axi_rready   (c0_rready),
            .m_axi_awid     (c0_awid),
            .m_axi_awaddr   (c0_awaddr),
            .m_axi_awlen    (c0_awlen),
            .m_axi_awsize   (c0_awsize),
            .m_axi_awburst  (c0_awburst),
            .m_axi_awlock   (c0_awlock),
            .m_axi_awcache  (c0_awcache),
            .m_axi_awprot   (c0_awprot),
            .m_axi_awqos    (c0_awqos),
            .m_axi_awregion (c0_awregion),
            .m_axi_awuser   (c0_awuser),
            .m_axi_awvalid  (c0_awvalid),
            .m_axi_awready  (c0_awready),
            .m_axi_wdata    (c0_wdata),
            .m_axi_wstrb    (c0_wstrb),
            .m_axi_wlast    (c0_wlast),
            .m_axi_wuser    (c0_wuser),
            .m_axi_wvalid   (c0_wvalid),
            .m_axi_wready   (c0_wready),
            .m_axi_bid      (c0_bid),
            .m_axi_bresp    (c0_bresp),
            .m_axi_buser    (c0_buser),
            .m_axi_bvalid   (c0_bvalid),
            .m_axi_bready   (c0_bready),
            .m_axi_acaddr   (s0_acaddr),
            .m_axi_acsnoop  (s0_acsnoop),
            .m_axi_acprot   (s0_acprot),
            .m_axi_acvalid  (s0_acvalid),
            .m_axi_acready  (s0_acready),
            .m_axi_crresp   (s0_crresp),
            .m_axi_crvalid  (s0_crvalid),
            .m_axi_crready  (s0_crready),
            .m_axi_cddata   (s0_cddata),
            .m_axi_cdlast   (s0_cdlast),
            .m_axi_cdvalid  (s0_cdvalid),
            .m_axi_cdready  (s0_cdready),
            .coh_req_valid  (coh0_valid),
            .coh_req_addr   (coh0_addr),
            .coh_req_type   (coh0_type),
            .coh_done_valid (done0_valid),
            .coh_done_id    (done0_id),
            .i_mon_time     (r_cycle_ctr),
            .mon_valid      (jpp_mon_valid[0]),
            .mon_ready      (jpp_mon_ready[0]),
            .mon_packet     (jpp_mon_packet[0]),
            .mon_timestamp  (jpp_mon_timestamp[0]),
            .init_busy      (jpp_init_busy[0]),
            .ctrl_state     (jpp_ctrl_state[0]),
            .busy           (jpp_busy[0])
        );
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
        ) u_ref1 (
            .aclk            (aclk),
            .aresetn         (aresetn),
            .cpu_req_wr_valid(ci1_req_valid),
            .cpu_req_wr_ready(ci1_req_ready),
            .cpu_req_wr_data (ci1_req_data),
            .cpu_rsp_rd_valid(ci1_rsp_valid),
            .cpu_rsp_rd_ready(ci1_rsp_ready),
            .cpu_rsp_rd_data (ci1_rsp_data),
            .m_axi_arid     (c1_arid),
            .m_axi_araddr   (c1_araddr),
            .m_axi_arlen    (c1_arlen),
            .m_axi_arsize   (c1_arsize),
            .m_axi_arburst  (c1_arburst),
            .m_axi_arlock   (c1_arlock),
            .m_axi_arcache  (c1_arcache),
            .m_axi_arprot   (c1_arprot),
            .m_axi_arqos    (c1_arqos),
            .m_axi_arregion (c1_arregion),
            .m_axi_aruser   (c1_aruser),
            .m_axi_arvalid  (c1_arvalid),
            .m_axi_arready  (c1_arready),
            .m_axi_rid      (c1_rid),
            .m_axi_rdata    (c1_rdata),
            .m_axi_rresp    (c1_rresp),
            .m_axi_rlast    (c1_rlast),
            .m_axi_ruser    (c1_ruser),
            .m_axi_rvalid   (c1_rvalid),
            .m_axi_rready   (c1_rready),
            .m_axi_awid     (c1_awid),
            .m_axi_awaddr   (c1_awaddr),
            .m_axi_awlen    (c1_awlen),
            .m_axi_awsize   (c1_awsize),
            .m_axi_awburst  (c1_awburst),
            .m_axi_awlock   (c1_awlock),
            .m_axi_awcache  (c1_awcache),
            .m_axi_awprot   (c1_awprot),
            .m_axi_awqos    (c1_awqos),
            .m_axi_awregion (c1_awregion),
            .m_axi_awuser   (c1_awuser),
            .m_axi_awvalid  (c1_awvalid),
            .m_axi_awready  (c1_awready),
            .m_axi_wdata    (c1_wdata),
            .m_axi_wstrb    (c1_wstrb),
            .m_axi_wlast    (c1_wlast),
            .m_axi_wuser    (c1_wuser),
            .m_axi_wvalid   (c1_wvalid),
            .m_axi_wready   (c1_wready),
            .m_axi_bid      (c1_bid),
            .m_axi_bresp    (c1_bresp),
            .m_axi_buser    (c1_buser),
            .m_axi_bvalid   (c1_bvalid),
            .m_axi_bready   (c1_bready),
            .m_axi_acaddr   (s1_acaddr),
            .m_axi_acsnoop  (s1_acsnoop),
            .m_axi_acprot   (s1_acprot),
            .m_axi_acvalid  (s1_acvalid),
            .m_axi_acready  (s1_acready),
            .m_axi_crresp   (s1_crresp),
            .m_axi_crvalid  (s1_crvalid),
            .m_axi_crready  (s1_crready),
            .m_axi_cddata   (s1_cddata),
            .m_axi_cdlast   (s1_cdlast),
            .m_axi_cdvalid  (s1_cdvalid),
            .m_axi_cdready  (s1_cdready),
            .coh_req_valid  (coh1_valid),
            .coh_req_addr   (coh1_addr),
            .coh_req_type   (coh1_type),
            .coh_done_valid (done1_valid),
            .coh_done_id    (done1_id),
            .i_mon_time     (r_cycle_ctr),
            .mon_valid      (jpp_mon_valid[1]),
            .mon_ready      (jpp_mon_ready[1]),
            .mon_packet     (jpp_mon_packet[1]),
            .mon_timestamp  (jpp_mon_timestamp[1]),
            .init_busy      (jpp_init_busy[1]),
            .ctrl_state     (jpp_ctrl_state[1]),
            .busy           (jpp_busy[1])
        );
        if (REF_CACHE_SEL == 3) begin : gen_fab
        jet_prime_pair_fabric #(
            .ADDR_WIDTH     (ADDR_WIDTH),
            .SETS           (SETS),
            .WAYS           (WAYS),
            .LINE_BYTES     (LINE_BYTES),
            .BUS_WIDTH      (BUS_WIDTH),
            .AXI_ID_WIDTH   (AXI_ID_WIDTH),
            .AXI_USER_WIDTH (AXI_USER_WIDTH),
            .FAB_SLOTS      (2 * (REF_JETP_MSHR_COUNT + 1)),
            .SNOOP_INFLIGHT (2)
        ) u_fabric (
            .clk               (aclk),
            .rst_n             (aresetn),
            .c0_arid            (c0_arid),
            .c0_araddr          (c0_araddr),
            .c0_arlen           (c0_arlen),
            .c0_arsize          (c0_arsize),
            .c0_arburst         (c0_arburst),
            .c0_arlock          (c0_arlock),
            .c0_arcache         (c0_arcache),
            .c0_arprot          (c0_arprot),
            .c0_arqos           (c0_arqos),
            .c0_arregion        (c0_arregion),
            .c0_aruser          (c0_aruser),
            .c0_arvalid         (c0_arvalid),
            .c0_arready         (c0_arready),
            .c0_rid             (c0_rid),
            .c0_rdata           (c0_rdata),
            .c0_rresp           (c0_rresp),
            .c0_rlast           (c0_rlast),
            .c0_ruser           (c0_ruser),
            .c0_rvalid          (c0_rvalid),
            .c0_rready          (c0_rready),
            .c0_awid            (c0_awid),
            .c0_awaddr          (c0_awaddr),
            .c0_awlen           (c0_awlen),
            .c0_awsize          (c0_awsize),
            .c0_awburst         (c0_awburst),
            .c0_awlock          (c0_awlock),
            .c0_awcache         (c0_awcache),
            .c0_awprot          (c0_awprot),
            .c0_awqos           (c0_awqos),
            .c0_awregion        (c0_awregion),
            .c0_awuser          (c0_awuser),
            .c0_awvalid         (c0_awvalid),
            .c0_awready         (c0_awready),
            .c0_wdata           (c0_wdata),
            .c0_wstrb           (c0_wstrb),
            .c0_wlast           (c0_wlast),
            .c0_wuser           (c0_wuser),
            .c0_wvalid          (c0_wvalid),
            .c0_wready          (c0_wready),
            .c0_bid             (c0_bid),
            .c0_bresp           (c0_bresp),
            .c0_buser           (c0_buser),
            .c0_bvalid          (c0_bvalid),
            .c0_bready          (c0_bready),
            .c1_arid            (c1_arid),
            .c1_araddr          (c1_araddr),
            .c1_arlen           (c1_arlen),
            .c1_arsize          (c1_arsize),
            .c1_arburst         (c1_arburst),
            .c1_arlock          (c1_arlock),
            .c1_arcache         (c1_arcache),
            .c1_arprot          (c1_arprot),
            .c1_arqos           (c1_arqos),
            .c1_arregion        (c1_arregion),
            .c1_aruser          (c1_aruser),
            .c1_arvalid         (c1_arvalid),
            .c1_arready         (c1_arready),
            .c1_rid             (c1_rid),
            .c1_rdata           (c1_rdata),
            .c1_rresp           (c1_rresp),
            .c1_rlast           (c1_rlast),
            .c1_ruser           (c1_ruser),
            .c1_rvalid          (c1_rvalid),
            .c1_rready          (c1_rready),
            .c1_awid            (c1_awid),
            .c1_awaddr          (c1_awaddr),
            .c1_awlen           (c1_awlen),
            .c1_awsize          (c1_awsize),
            .c1_awburst         (c1_awburst),
            .c1_awlock          (c1_awlock),
            .c1_awcache         (c1_awcache),
            .c1_awprot          (c1_awprot),
            .c1_awqos           (c1_awqos),
            .c1_awregion        (c1_awregion),
            .c1_awuser          (c1_awuser),
            .c1_awvalid         (c1_awvalid),
            .c1_awready         (c1_awready),
            .c1_wdata           (c1_wdata),
            .c1_wstrb           (c1_wstrb),
            .c1_wlast           (c1_wlast),
            .c1_wuser           (c1_wuser),
            .c1_wvalid          (c1_wvalid),
            .c1_wready          (c1_wready),
            .c1_bid             (c1_bid),
            .c1_bresp           (c1_bresp),
            .c1_buser           (c1_buser),
            .c1_bvalid          (c1_bvalid),
            .c1_bready          (c1_bready),
            .s0_acaddr          (s0_acaddr),
            .s0_acsnoop         (s0_acsnoop),
            .s0_acprot          (s0_acprot),
            .s0_acvalid         (s0_acvalid),
            .s0_acready         (s0_acready),
            .s0_crresp          (s0_crresp),
            .s0_crvalid         (s0_crvalid),
            .s0_crready         (s0_crready),
            .s0_cddata          (s0_cddata),
            .s0_cdlast          (s0_cdlast),
            .s0_cdvalid         (s0_cdvalid),
            .s0_cdready         (s0_cdready),
            .s1_acaddr          (s1_acaddr),
            .s1_acsnoop         (s1_acsnoop),
            .s1_acprot          (s1_acprot),
            .s1_acvalid         (s1_acvalid),
            .s1_acready         (s1_acready),
            .s1_crresp          (s1_crresp),
            .s1_crvalid         (s1_crvalid),
            .s1_crready         (s1_crready),
            .s1_cddata          (s1_cddata),
            .s1_cdlast          (s1_cdlast),
            .s1_cdvalid         (s1_cdvalid),
            .s1_cdready         (s1_cdready),
            .c0_coh_req_valid  (coh0_valid),
            .c0_coh_req_addr   (coh0_addr),
            .c0_coh_req_type   (coh0_type),
            .c1_coh_req_valid  (coh1_valid),
            .c1_coh_req_addr   (coh1_addr),
            .c1_coh_req_type   (coh1_type),
            .c0_coh_done_valid (done0_valid),
            .c0_coh_done_id    (done0_id),
            .c1_coh_done_valid (done1_valid),
            .c1_coh_done_id    (done1_id),
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
            .dbg_busy          (jpp_fab_busy),
            .dbg_slot_vld      (),
            .dbg_pend_vld      (),
            .dbg_abs_pend      (),
            .dbg_grant         (),
            .dbg_grant_dir     (),
            .dbg_grant_addr    (),
            .dbg_grant_slot    ()
        );
        end else begin : gen_onyx
            // onyx TASK-001 step 6: onyx_ccu at N_PORTS 2 in the pair fabric's
            // place -- the same two caches, memory, injectors and knobs, so
            // the SEL 4 sweeps against SEL 3's are the manager swap alone
            // (PRD criterion 6); SEL 5 is the same build with the memory
            // read deferred until the gather (D6's other mode).  The caches'
            // flat ports pack into onyx's per-port arrays here.
            logic [IW-1:0]            oc_arid    [2];
            logic [ADDR_WIDTH-1:0]    oc_araddr  [2];
            logic [7:0]               oc_arlen   [2];
            logic [2:0]               oc_arsize  [2];
            logic [1:0]               oc_arburst [2];
            logic [3:0]               oc_arcache [2];
            logic [2:0]               oc_arprot  [2];
            logic [3:0]               oc_arqos   [2];
            logic [3:0]               oc_arregion[2];
            logic [UW-1:0]            oc_aruser  [2];
            logic [IW-1:0]            oc_rid     [2];
            logic [BUS_WIDTH-1:0]     oc_rdata   [2];
            logic [1:0]               oc_rresp   [2];
            logic [UW-1:0]            oc_ruser   [2];
            logic [IW-1:0]            oc_awid    [2];
            logic [ADDR_WIDTH-1:0]    oc_awaddr  [2];
            logic [7:0]               oc_awlen   [2];
            logic [2:0]               oc_awsize  [2];
            logic [1:0]               oc_awburst [2];
            logic [3:0]               oc_awcache [2];
            logic [2:0]               oc_awprot  [2];
            logic [3:0]               oc_awqos   [2];
            logic [3:0]               oc_awregion[2];
            logic [UW-1:0]            oc_awuser  [2];
            logic [BUS_WIDTH-1:0]     oc_wdata   [2];
            logic [STRB_W-1:0]        oc_wstrb   [2];
            logic [UW-1:0]            oc_wuser   [2];
            logic [IW-1:0]            oc_bid     [2];
            logic [1:0]               oc_bresp   [2];
            logic [UW-1:0]            oc_buser   [2];
            logic [ADDR_WIDTH-1:0]    os_acaddr  [2];
            logic [3:0]               os_acsnoop [2];
            logic [2:0]               os_acprot  [2];
            logic [AMBER_CRRESP_WIDTH-1:0] os_crresp [2];
            logic [BUS_WIDTH-1:0]     os_cddata  [2];
            logic [ADDR_WIDTH-1:0]    oc_coh_addr[2];
            logic [2:0]               oc_coh_type[2];
            logic [IW-1:0]            oc_done_id [2];
            logic [1:0]               oc_arready_v, oc_rlast_v, oc_rvalid_v, oc_awready_v, oc_wready_v, oc_bvalid_v;
            logic [1:0]               os_acvalid_v, os_crready_v, os_cdready_v;
            assign oc_arid[0] = c0_arid;         assign oc_arid[1] = c1_arid;
            assign oc_araddr[0] = c0_araddr;     assign oc_araddr[1] = c1_araddr;
            assign oc_arlen[0] = c0_arlen;       assign oc_arlen[1] = c1_arlen;
            assign oc_arsize[0] = c0_arsize;     assign oc_arsize[1] = c1_arsize;
            assign oc_arburst[0] = c0_arburst;   assign oc_arburst[1] = c1_arburst;
            assign oc_arcache[0] = c0_arcache;   assign oc_arcache[1] = c1_arcache;
            assign oc_arprot[0] = c0_arprot;     assign oc_arprot[1] = c1_arprot;
            assign oc_arqos[0] = c0_arqos;       assign oc_arqos[1] = c1_arqos;
            assign oc_arregion[0] = c0_arregion; assign oc_arregion[1] = c1_arregion;
            assign oc_aruser[0] = c0_aruser;     assign oc_aruser[1] = c1_aruser;
            assign {c1_arready, c0_arready} = oc_arready_v;
            assign c0_rid = oc_rid[0];           assign c1_rid = oc_rid[1];
            assign c0_rdata = oc_rdata[0];       assign c1_rdata = oc_rdata[1];
            assign c0_rresp = oc_rresp[0];       assign c1_rresp = oc_rresp[1];
            assign c0_ruser = oc_ruser[0];       assign c1_ruser = oc_ruser[1];
            assign {c1_rlast, c0_rlast} = oc_rlast_v;
            assign {c1_rvalid, c0_rvalid} = oc_rvalid_v;
            assign oc_awid[0] = c0_awid;         assign oc_awid[1] = c1_awid;
            assign oc_awaddr[0] = c0_awaddr;     assign oc_awaddr[1] = c1_awaddr;
            assign oc_awlen[0] = c0_awlen;       assign oc_awlen[1] = c1_awlen;
            assign oc_awsize[0] = c0_awsize;     assign oc_awsize[1] = c1_awsize;
            assign oc_awburst[0] = c0_awburst;   assign oc_awburst[1] = c1_awburst;
            assign oc_awcache[0] = c0_awcache;   assign oc_awcache[1] = c1_awcache;
            assign oc_awprot[0] = c0_awprot;     assign oc_awprot[1] = c1_awprot;
            assign oc_awqos[0] = c0_awqos;       assign oc_awqos[1] = c1_awqos;
            assign oc_awregion[0] = c0_awregion; assign oc_awregion[1] = c1_awregion;
            assign oc_awuser[0] = c0_awuser;     assign oc_awuser[1] = c1_awuser;
            assign {c1_awready, c0_awready} = oc_awready_v;
            assign oc_wdata[0] = c0_wdata;       assign oc_wdata[1] = c1_wdata;
            assign oc_wstrb[0] = c0_wstrb;       assign oc_wstrb[1] = c1_wstrb;
            assign oc_wuser[0] = c0_wuser;       assign oc_wuser[1] = c1_wuser;
            assign {c1_wready, c0_wready} = oc_wready_v;
            assign c0_bid = oc_bid[0];           assign c1_bid = oc_bid[1];
            assign c0_bresp = oc_bresp[0];       assign c1_bresp = oc_bresp[1];
            assign c0_buser = oc_buser[0];       assign c1_buser = oc_buser[1];
            assign {c1_bvalid, c0_bvalid} = oc_bvalid_v;
            assign s0_acaddr = os_acaddr[0];     assign s1_acaddr = os_acaddr[1];
            assign s0_acsnoop = os_acsnoop[0];   assign s1_acsnoop = os_acsnoop[1];
            assign s0_acprot = os_acprot[0];     assign s1_acprot = os_acprot[1];
            assign {s1_acvalid, s0_acvalid} = os_acvalid_v;
            assign os_crresp[0] = s0_crresp;     assign os_crresp[1] = s1_crresp;
            assign {s1_crready, s0_crready} = os_crready_v;
            assign os_cddata[0] = s0_cddata;     assign os_cddata[1] = s1_cddata;
            assign {s1_cdready, s0_cdready} = os_cdready_v;
            assign oc_coh_addr[0] = coh0_addr;   assign oc_coh_addr[1] = coh1_addr;
            assign oc_coh_type[0] = coh0_type;   assign oc_coh_type[1] = coh1_type;
            assign oc_done_id[0] = done0_id;     assign oc_done_id[1] = done1_id;

            // the ACE-Lite IO port (D1, step 7) and the host's doorbell
            // master on it: one single-beat read or write per IO_CTRL.go
            logic [IW-1:0]            io_arid, io_rid, io_awid, io_bid;
            logic [ADDR_WIDTH-1:0]    io_araddr, io_awaddr;
            logic [7:0]               io_arlen, io_awlen;
            logic [2:0]               io_arsize, io_awsize, io_arprot, io_awprot, io_awsnoop;
            logic [1:0]               io_arburst, io_awburst, io_ardomain, io_awdomain, io_arbar, io_awbar;
            logic [1:0]               io_rresp, io_bresp;
            logic                     io_arlock, io_awlock;
            logic [3:0]               io_arcache, io_awcache, io_arqos, io_awqos, io_arregion, io_awregion, io_arsnoop;
            logic [UW-1:0]            io_aruser, io_ruser, io_awuser, io_wuser, io_buser;
            logic                     io_arvalid, io_arready, io_rvalid, io_rready, io_rlast;
            logic                     io_awvalid, io_awready, io_wvalid, io_wready, io_wlast, io_bvalid, io_bready;
            logic [BUS_WIDTH-1:0]     io_rdata_b, io_wdata_b, io_rdata_lat;
            logic [STRB_W-1:0]        io_wstrb;
            assign io_absent = 1'b0;
            ref_io_master #(
                .ADDR_WIDTH (ADDR_WIDTH),
                .BUS_WIDTH  (BUS_WIDTH),
                .ID_WIDTH   (IW),
                .USER_WIDTH (UW)
            ) u_io_master (
                .aclk(aclk), .aresetn(aresetn),
                .go_i(io_go), .write_i(io_write), .shareable_i(io_sh),
                .addr_i(ADDR_WIDTH'(io_addr)), .wdata_i(BUS_WIDTH'(io_wdata)), .wstrb_i(STRB_W'(io_strb)),
                .busy_o(io_busy), .done_o(io_done), .resp_o(io_resp), .rdata_o(io_rdata_lat),
                .io_arid(io_arid), .io_araddr(io_araddr), .io_arlen(io_arlen), .io_arsize(io_arsize),
                .io_arburst(io_arburst), .io_arlock(io_arlock), .io_arcache(io_arcache), .io_arprot(io_arprot),
                .io_arqos(io_arqos), .io_arregion(io_arregion), .io_aruser(io_aruser), .io_arsnoop(io_arsnoop),
                .io_ardomain(io_ardomain), .io_arbar(io_arbar), .io_arvalid(io_arvalid), .io_arready(io_arready),
                .io_rid(io_rid), .io_rdata(io_rdata_b), .io_rresp(io_rresp), .io_rlast(io_rlast), .io_ruser(io_ruser),
                .io_rvalid(io_rvalid), .io_rready(io_rready),
                .io_awid(io_awid), .io_awaddr(io_awaddr), .io_awlen(io_awlen), .io_awsize(io_awsize),
                .io_awburst(io_awburst), .io_awlock(io_awlock), .io_awcache(io_awcache), .io_awprot(io_awprot),
                .io_awqos(io_awqos), .io_awregion(io_awregion), .io_awuser(io_awuser), .io_awsnoop(io_awsnoop),
                .io_awdomain(io_awdomain), .io_awbar(io_awbar), .io_awvalid(io_awvalid), .io_awready(io_awready),
                .io_wdata(io_wdata_b), .io_wstrb(io_wstrb), .io_wlast(io_wlast), .io_wuser(io_wuser),
                .io_wvalid(io_wvalid), .io_wready(io_wready), .io_bid(io_bid), .io_bresp(io_bresp),
                .io_buser(io_buser), .io_bvalid(io_bvalid), .io_bready(io_bready)
            );
            assign io_rdata = 64'(io_rdata_lat);
        onyx_top #(
            .N_PORTS        (2),
            .ADDR_WIDTH     (ADDR_WIDTH),
            .LINE_BYTES     (LINE_BYTES),
            .BUS_WIDTH      (BUS_WIDTH),
            .AXI_ID_WIDTH   (AXI_ID_WIDTH),
            .AXI_USER_WIDTH (AXI_USER_WIDTH),
            .SLOTS          (2 * (REF_JETP_MSHR_COUNT + 1)),
            .SNOOP_INFLIGHT (2),
            .DEFER_AR       (REF_CACHE_SEL == 5),
            .SERIAL_MODE    (1'b0),
            .USE_MONITOR    (1'b1)
        ) u_onyx (
            .clk              (aclk),
            .rst_n            (aresetn),
            .c_arid           (oc_arid),
            .c_araddr         (oc_araddr),
            .c_arlen          (oc_arlen),
            .c_arsize         (oc_arsize),
            .c_arburst        (oc_arburst),
            .c_arlock         ({c1_arlock, c0_arlock}),
            .c_arcache        (oc_arcache),
            .c_arprot         (oc_arprot),
            .c_arqos          (oc_arqos),
            .c_arregion       (oc_arregion),
            .c_aruser         (oc_aruser),
            .c_arvalid        ({c1_arvalid, c0_arvalid}),
            .c_arready        (oc_arready_v),
            .c_rid            (oc_rid),
            .c_rdata          (oc_rdata),
            .c_rresp          (oc_rresp),
            .c_rlast          (oc_rlast_v),
            .c_ruser          (oc_ruser),
            .c_rvalid         (oc_rvalid_v),
            .c_rready         ({c1_rready, c0_rready}),
            .c_awid           (oc_awid),
            .c_awaddr         (oc_awaddr),
            .c_awlen          (oc_awlen),
            .c_awsize         (oc_awsize),
            .c_awburst        (oc_awburst),
            .c_awlock         ({c1_awlock, c0_awlock}),
            .c_awcache        (oc_awcache),
            .c_awprot         (oc_awprot),
            .c_awqos          (oc_awqos),
            .c_awregion       (oc_awregion),
            .c_awuser         (oc_awuser),
            .c_awvalid        ({c1_awvalid, c0_awvalid}),
            .c_awready        (oc_awready_v),
            .c_wdata          (oc_wdata),
            .c_wstrb          (oc_wstrb),
            .c_wlast          ({c1_wlast, c0_wlast}),
            .c_wuser          (oc_wuser),
            .c_wvalid         ({c1_wvalid, c0_wvalid}),
            .c_wready         (oc_wready_v),
            .c_bid            (oc_bid),
            .c_bresp          (oc_bresp),
            .c_buser          (oc_buser),
            .c_bvalid         (oc_bvalid_v),
            .c_bready         ({c1_bready, c0_bready}),
            .s_acaddr         (os_acaddr),
            .s_acsnoop        (os_acsnoop),
            .s_acprot         (os_acprot),
            .s_acvalid        (os_acvalid_v),
            .s_acready        ({s1_acready, s0_acready}),
            .s_crresp         (os_crresp),
            .s_crvalid        ({s1_crvalid, s0_crvalid}),
            .s_crready        (os_crready_v),
            .s_cddata         (os_cddata),
            .s_cdlast         ({s1_cdlast, s0_cdlast}),
            .s_cdvalid        ({s1_cdvalid, s0_cdvalid}),
            .s_cdready        (os_cdready_v),
            .c_coh_req_valid  ({coh1_valid, coh0_valid}),
            .c_coh_req_addr   (oc_coh_addr),
            .c_coh_req_type   (oc_coh_type),
            .c_coh_done_valid ({done1_valid, done0_valid}),
            .c_coh_done_id    (oc_done_id),
            .io_arid(io_arid), .io_araddr(io_araddr), .io_arlen(io_arlen), .io_arsize(io_arsize),
            .io_arburst(io_arburst), .io_arlock(io_arlock), .io_arcache(io_arcache), .io_arprot(io_arprot),
            .io_arqos(io_arqos), .io_arregion(io_arregion), .io_aruser(io_aruser), .io_arsnoop(io_arsnoop),
            .io_ardomain(io_ardomain), .io_arbar(io_arbar), .io_arvalid(io_arvalid), .io_arready(io_arready),
            .io_rid(io_rid), .io_rdata(io_rdata_b), .io_rresp(io_rresp), .io_rlast(io_rlast), .io_ruser(io_ruser),
            .io_rvalid(io_rvalid), .io_rready(io_rready),
            .io_awid(io_awid), .io_awaddr(io_awaddr), .io_awlen(io_awlen), .io_awsize(io_awsize),
            .io_awburst(io_awburst), .io_awlock(io_awlock), .io_awcache(io_awcache), .io_awprot(io_awprot),
            .io_awqos(io_awqos), .io_awregion(io_awregion), .io_awuser(io_awuser), .io_awsnoop(io_awsnoop),
            .io_awdomain(io_awdomain), .io_awbar(io_awbar), .io_awvalid(io_awvalid), .io_awready(io_awready),
            .io_wdata(io_wdata_b), .io_wstrb(io_wstrb), .io_wlast(io_wlast), .io_wuser(io_wuser),
            .io_wvalid(io_wvalid), .io_wready(io_wready), .io_bid(io_bid), .io_bresp(io_bresp),
            .io_buser(io_buser), .io_bvalid(io_bvalid), .io_bready(io_bready),
            .mem_arid         (mem_arid),
            .mem_araddr       (mem_araddr),
            .mem_arlen        (mem_arlen),
            .mem_arsize       (mem_arsize),
            .mem_arburst      (mem_arburst),
            .mem_arlock       (mem_arlock),
            .mem_arcache      (mem_arcache),
            .mem_arprot       (mem_arprot),
            .mem_arqos        (mem_arqos),
            .mem_arregion     (mem_arregion),
            .mem_aruser       (mem_aruser),
            .mem_arvalid      (mem_arvalid),
            .mem_arready      (mem_arready),
            .mem_rid          (mem_rid),
            .mem_rdata        (mem_rdata),
            .mem_rresp        (mem_rresp),
            .mem_rlast        (mem_rlast),
            .mem_ruser        (mem_ruser),
            .mem_rvalid       (mem_rvalid),
            .mem_rready       (mem_rready),
            .mem_awid         (mem_awid),
            .mem_awaddr       (mem_awaddr),
            .mem_awlen        (mem_awlen),
            .mem_awsize       (mem_awsize),
            .mem_awburst      (mem_awburst),
            .mem_awlock       (mem_awlock),
            .mem_awcache      (mem_awcache),
            .mem_awprot       (mem_awprot),
            .mem_awqos        (mem_awqos),
            .mem_awregion     (mem_awregion),
            .mem_awuser       (mem_awuser),
            .mem_awvalid      (mem_awvalid),
            .mem_awready      (mem_awready),
            .mem_wdata        (mem_wdata),
            .mem_wstrb        (mem_wstrb),
            .mem_wlast        (mem_wlast),
            .mem_wuser        (mem_wuser),
            .mem_wvalid       (mem_wvalid),
            .mem_wready       (mem_wready),
            .mem_bid          (mem_bid),
            .mem_bresp        (mem_bresp),
            .mem_buser        (mem_buser),
            .mem_bvalid       (mem_bvalid),
            .mem_bready       (mem_bready),
            .i_mon_time       (r_cycle_ctr),
            .mon_valid        (onyx_mon_valid),
            .mon_ready        (onyx_mon_ready),
            .mon_packet       (onyx_mon_packet),
            .mon_timestamp    (onyx_mon_timestamp),
            .mon_dropped      (),
            // the observer's masks from the harness CSR: ONYX_MON_CTRL [0]
            // enable, [1] error enable, [2] perf enable, [6:4] port mask
            // (the two caches, bit 6 the IO port), [31:16] perf (event
            // class) mask; ONYX_MON_MASK [15:0] packet type mask, [31:16]
            // error (event code) mask
            .mon_cfg_enable       (onyx_mon_ctrl[0]),
            .mon_cfg_error_enable (onyx_mon_ctrl[1]),
            .mon_cfg_perf_enable  (onyx_mon_ctrl[2]),
            .mon_cfg_port_mask    (onyx_mon_ctrl[6:4]),
            .mon_cfg_perf_mask    (onyx_mon_ctrl[31:16]),
            .mon_cfg_pkt_mask     (onyx_mon_mask[15:0]),
            .mon_cfg_error_mask   (onyx_mon_mask[31:16]),
            // the content filter: ONYX_MON_CTRL [3] enables the inclusive
            // address window ONYX_MON_WIN_LOW .. ONYX_MON_WIN_HIGH
            .mon_cfg_addr_win_enable (onyx_mon_ctrl[3]),
            .mon_cfg_addr_win_low    (ADDR_WIDTH'(onyx_mon_win_low)),
            .mon_cfg_addr_win_high   (ADDR_WIDTH'(onyx_mon_win_high)),
            .cnt_clear        (hcsr_ctrl[0]),
            .cnt_freeze       (hcsr_ctrl[1]),
            .cnt_txn          (onyx_cnt[0]),
            .cnt_supplied     (onyx_cnt[1]),
            .cnt_mem_read     (onyx_cnt[2]),
            .cnt_read_wasted  (onyx_cnt[3]),
            .cnt_absorb       (onyx_cnt[4]),
            .cnt_wb           (onyx_cnt[5]),
            .cnt_cu_dt        (onyx_cnt[6]),
            .cnt_old_wb       (onyx_cnt[7]),
            .dbg_busy         (jpp_fab_busy),
            .dbg_slot_vld     (),
            .dbg_pend_vld     (),
            .dbg_abs_pend     (),
            .dbg_grant        (),
            .dbg_grant_dir    (),
            .dbg_grant_addr   (),
            .dbg_grant_slot   ()
        );
        end
        if (REF_CACHE_SEL == 3) begin : gen_no_onyx_mon
            assign onyx_mon_valid     = 1'b0;
            assign onyx_mon_packet    = '0;
            assign onyx_mon_timestamp = '0;
            for (genvar k = 0; k < 8; k++) begin : g_z
                assign onyx_cnt[k] = '0;
            end
            // no IO port in the pair fabric: the doorbell reads absent
            assign io_busy = 1'b0;
            assign io_done = 1'b0;
            assign io_resp = 2'b00;
            assign io_rdata = '0;
            assign io_absent = 1'b1;
        end

        // ------------------------------------------------------------------
        // MonBus: {cache 0, cache 1, onyx} -> arbiter -> group -> tally, the
        // jet pair rig's chain (onyx TASK-001 step 6b, D9): the host reads
        // the bins through the shared bridge's tally apertures (s3/s4/s5)
        // with the harness CSR's CTRL[0] clear and CTRL[1] freeze.  SEL 3
        // gets the two caches' streams (onyx's client idle).
        // ------------------------------------------------------------------
        logic                                 arb_vld [3];
        logic                                 arb_rdy [3];
        ocelus_common_pkg::monitor_packet_t   arb_pkt [3];
        ocelus_common_pkg::monbus_timestamp_t arb_ts  [3];
        assign arb_vld[0] = jpp_mon_valid[0];   assign arb_vld[1] = jpp_mon_valid[1];
        assign arb_pkt[0] = jpp_mon_packet[0];  assign arb_pkt[1] = jpp_mon_packet[1];
        assign arb_ts[0]  = jpp_mon_timestamp[0]; assign arb_ts[1] = jpp_mon_timestamp[1];
        assign arb_vld[2] = onyx_mon_valid;
        assign arb_pkt[2] = onyx_mon_packet;
        assign arb_ts[2]  = onyx_mon_timestamp;
        assign onyx_mon_ready = arb_rdy[2];
        assign jpp_mon_ready  = {arb_rdy[1], arb_rdy[0]};

        logic         merged_valid, merged_ready;
        logic [127:0] merged_packet;
        logic [63:0]  merged_timestamp;
        monbus_arbiter #(
            .CLIENTS            (3),
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

        logic [31:0] group_awaddr;
        logic [2:0]  group_awprot;
        logic        group_awvalid, group_awready;
        logic [63:0] group_wdata;
        logic [7:0]  group_wstrb;
        logic        group_wvalid, group_wready;
        logic [1:0]  group_bresp;
        logic        group_bvalid, group_bready;
        logic [63:0] mon_time_out_unused;
        monbus_axil4_group_1wr #(
            .ADDR_WIDTH        (32),
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
            .err_rec_count (),
            .cfg_base_addr (32'h0000_0000),
            .cfg_limit_addr(32'hFFFF_FFFF),
            // flush early and often (the jet rig's BUG-004 finding)
            .cfg_flush_watermark(16'd48),
            .cfg_err_base_addr (32'h0000_0000),
            .cfg_err_limit_addr(32'h0000_0000),
            .cfg_err_flush_watermark(16'd3),
            .cfg_compress_en(1'b0),
            .cfg_axi_pkt_mask   (16'h0000),
            .cfg_axi_err_select (16'h0000),
            .cfg_axi_error_mask (16'h0000),
            .cfg_axi_timeout_mask(16'h0000),
            .cfg_axi_compl_mask (16'h0000),
            .cfg_axi_thresh_mask(16'h0000),
            .cfg_axi_perf_mask  (16'h0000),
            .cfg_axi_addr_mask  (16'h0000),
            .cfg_axi_debug_mask (16'h0000),
            .cfg_axis_pkt_mask   (16'h0000),
            .cfg_axis_err_select (16'h0000),
            .cfg_axis_error_mask (16'h0000),
            .cfg_axis_timeout_mask(16'h0000),
            .cfg_axis_compl_mask (16'h0000),
            .cfg_axis_credit_mask(16'h0000),
            .cfg_axis_channel_mask(16'h0000),
            .cfg_axis_stream_mask(16'h0000),
            .cfg_core_pkt_mask   (16'h0000),
            .cfg_core_err_select (16'h0000),
            .cfg_core_error_mask (16'h0000),
            .cfg_core_timeout_mask(16'h0000),
            .cfg_core_compl_mask (16'h0000),
            .cfg_core_thresh_mask(16'h0000),
            .cfg_core_perf_mask  (16'h0000),
            .cfg_core_debug_mask (16'h0000),
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

        localparam int MON_N_PROFILE       = 32;
        localparam int MON_TALLY_ADDR_BITS = $clog2(MON_N_PROFILE + 1);
        monbus_tally_axil #(
            .ADDR_WIDTH      (32),
            .DATA_WIDTH      (64),
            .TALLY_ADDR_BITS (MON_TALLY_ADDR_BITS),
            .N_PROFILE       (MON_N_PROFILE),
            .TALLY_NUM_LATCH (16)
        ) u_tally (
            .aclk(aclk),
            .aresetn(aresetn),
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
            .cnt_araddr (s3_araddr),
            .cnt_arprot (s3_arprot),
            .cnt_arvalid(s3_arvalid),
            .cnt_arready(s3_arready),
            .cnt_rdata  (s3_rdata),
            .cnt_rresp  (s3_rresp),
            .cnt_rvalid (s3_rvalid),
            .cnt_rready (s3_rready),
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
            .cfgr_araddr (s5_araddr),
            .cfgr_arprot (s5_arprot),
            .cfgr_arvalid(s5_arvalid),
            .cfgr_arready(s5_arready),
            .cfgr_rdata  (s5_rdata),
            .cfgr_rresp  (s5_rresp),
            .cfgr_rvalid (s5_rvalid),
            .cfgr_rready (s5_rready),
            .tally_freeze(hcsr_ctrl[1]),
            .tally_flush (1'b0),
            .tally_flush_busy(),
            .tally_clear (hcsr_ctrl[0])
        );
        // the count / config apertures' unused channels
        assign s3_awready = 1'b1; assign s3_wready = 1'b1; assign s3_bvalid = 1'b0; assign s3_bresp = 2'b00;
        assign s4_arready = 1'b1; assign s4_rvalid = 1'b0; assign s4_rdata = '0; assign s4_rresp = 2'b00;
        assign s5_awready = 1'b1; assign s5_wready = 1'b1; assign s5_bvalid = 1'b0; assign s5_bresp = 2'b00;
        end else begin : gen_ref_hpd
            for (genvar k = 0; k < 8; k++) begin : g_z
                assign onyx_cnt[k] = '0;
            end
            // no IO port in this selection: the doorbell reads absent
            assign io_busy = 1'b0; assign io_done = 1'b0; assign io_resp = 2'b00;
            assign io_rdata = '0;  assign io_absent = 1'b1;
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
    // No MonBus tally for the single-cache selections (0-2): the three
    // tally apertures of the shared bridge ack writes and read zero, so
    // the jet host stack runs unchanged.  The pair block (3-5) carries the
    // real tally above.
    // ------------------------------------------------------------------
    generate if (REF_CACHE_SEL < 3) begin : gen_tally_stubs
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
    end endgenerate

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
    input  logic [3:0]  i_fabric_dbg,
    input  logic [31:0] i_onyx_cnt [8],  // onyx TASK-001: txn, supplied, mem_read, read_wasted, absorb, wb, cu_dt, old_wb
    output logic [31:0] o_onyx_mon_ctrl,  // 0x038: the onyx observer's enables, port mask and class mask
    output logic [31:0] o_onyx_mon_mask,  // 0x03C: its packet-type mask and error-code mask
    output logic [31:0] o_onyx_mon_win_low,   // 0x014 / 0x018: its address window (CTRL[3] enables)
    output logic [31:0] o_onyx_mon_win_high,
    // 0x040 .. 0x058: the IO doorbell (onyx TASK-001 step 7) -- one
    // single-beat access on onyx's ACE-Lite IO port per IO_CTRL.go
    output logic        o_io_go,          // one-cycle pulse (IO_CTRL[0], write-1)
    output logic        o_io_write,       // IO_CTRL[1]: 1 write, 0 read
    output logic        o_io_sh,          // IO_CTRL[2]: shareable (ReadOnce / WriteUnique)
    output logic [31:0] o_io_addr,        // IO_ADDR
    output logic [63:0] o_io_wdata,       // IO_WDATA_LO / HI
    output logic [7:0]  o_io_strb,        // IO_CTRL[15:8]
    input  logic        i_io_busy,        // IO_STATUS[0]
    input  logic        i_io_done,        // IO_STATUS[1]
    input  logic [1:0]  i_io_resp,        // IO_STATUS[3:2]
    input  logic [63:0] i_io_rdata,       // IO_RDATA_LO / HI
    input  logic        i_io_absent       // IO_STATUS[31]: no IO port in this selection
);

    // the word index is addr[6:2]: 0x00 .. 0x7C (the first sixteen words
    // were the whole map until the IO doorbell took 0x40 .. 0x58)
    localparam logic [4:0] HCSR_CTRL       = 5'h00;
    localparam logic [4:0] HCSR_STATUS     = 5'h01;
    localparam logic [4:0] HCSR_CYCLE_LO   = 5'h02;
    localparam logic [4:0] HCSR_CYCLE_HI   = 5'h03;
    localparam logic [4:0] HCSR_FABRIC_DBG = 5'h04;
    localparam logic [4:0] HCSR_ONYX_CNT0  = 5'h08;   // 0x020 .. 0x034: the six onyx counters
    // 0x038 / 0x03C: the onyx observer's masks, the ocelus layers (enables
    // 1 = on, masks bit set = drop).  Reset: observer, error and perf
    // enabled, no port masked, the per-transaction classes (TXN_START,
    // GATHER_DONE, MEM_READ, READ_WASTED, ABSORB, WRITEBACK) masked and
    // LOCK_WAIT open -- the MonBus is a low-bandwidth event channel and the
    // host opens the classes it wants to transmit.
    localparam logic [4:0] HCSR_ONYX_MON_CTRL = 5'h0E;
    localparam logic [4:0] HCSR_ONYX_MON_MASK = 5'h0F;
    // 0x014 / 0x018: the observer's inclusive address window, the content
    // filter the AXI monitors carry as address ranges; CTRL[3] enables it
    localparam logic [4:0] HCSR_ONYX_MON_WIN_LO = 5'h05;
    localparam logic [4:0] HCSR_ONYX_MON_WIN_HI = 5'h06;
    localparam logic [31:0] ONYX_MON_CTRL_RESET = 32'h007D_0007;
    // 0x040 .. 0x058: the IO doorbell
    localparam logic [4:0] HCSR_IO_ADDR     = 5'h10;
    localparam logic [4:0] HCSR_IO_WDATA_LO = 5'h11;
    localparam logic [4:0] HCSR_IO_WDATA_HI = 5'h12;
    localparam logic [4:0] HCSR_IO_CTRL     = 5'h13;   // [0] go (W1 pulse) [1] write [2] shareable [15:8] wstrb
    localparam logic [4:0] HCSR_IO_STATUS   = 5'h14;   // [0] busy [1] done [3:2] resp [31] absent
    localparam logic [4:0] HCSR_IO_RDATA_LO = 5'h15;
    localparam logic [4:0] HCSR_IO_RDATA_HI = 5'h16;
    // 0x05C / 0x060: onyx's two corner counters (the six above were the
    // whole block until onyx BUG-001..003): CleanUnique slots that ended
    // with data, and cache writes first presented on a line a slot still
    // gathers
    localparam logic [4:0] HCSR_ONYX_CNT_CU_DT  = 5'h17;
    localparam logic [4:0] HCSR_ONYX_CNT_OLD_WB = 5'h18;

    logic [31:0] r_ctrl;
    assign o_ctrl = r_ctrl;
    logic [31:0] r_onyx_mon_ctrl, r_onyx_mon_mask, r_onyx_mon_win_lo, r_onyx_mon_win_hi;
    assign o_onyx_mon_ctrl = r_onyx_mon_ctrl;
    assign o_onyx_mon_mask = r_onyx_mon_mask;
    assign o_onyx_mon_win_low  = r_onyx_mon_win_lo;
    assign o_onyx_mon_win_high = r_onyx_mon_win_hi;
    logic [31:0] r_io_addr, r_io_wdata_lo, r_io_wdata_hi, r_io_ctrl;
    assign o_io_go    = r_io_ctrl[0];
    assign o_io_write = r_io_ctrl[1];
    assign o_io_sh    = r_io_ctrl[2];
    assign o_io_strb  = r_io_ctrl[15:8];
    assign o_io_addr  = r_io_addr;
    assign o_io_wdata = {r_io_wdata_hi, r_io_wdata_lo};

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
            r_onyx_mon_ctrl <= ONYX_MON_CTRL_RESET;
            r_onyx_mon_mask <= '0;
            r_onyx_mon_win_lo <= '0;
            r_onyx_mon_win_hi <= '0;
            r_io_addr     <= '0;
            r_io_wdata_lo <= '0;
            r_io_wdata_hi <= '0;
            r_io_ctrl     <= '0;
        end else begin
            // CTRL[0] (tally_clear) is write-1-pulse: a write with bit 0 set
            // raises o_ctrl[0] for exactly one cycle, then it self-clears.
            // IO_CTRL[0] (go) is the same shape.
            r_ctrl[0] <= 1'b0;
            r_io_ctrl[0] <= 1'b0;
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
                    if (r_wstrb[b] && (r_awaddr[6:2] == HCSR_CTRL)) begin
                        r_ctrl[8*b +: 8] <= r_wdata[8*b +: 8];
                    end
                    if (r_wstrb[b] && (r_awaddr[6:2] == HCSR_ONYX_MON_CTRL)) begin
                        r_onyx_mon_ctrl[8*b +: 8] <= r_wdata[8*b +: 8];
                    end
                    if (r_wstrb[b] && (r_awaddr[6:2] == HCSR_ONYX_MON_MASK)) begin
                        r_onyx_mon_mask[8*b +: 8] <= r_wdata[8*b +: 8];
                    end
                    if (r_wstrb[b] && (r_awaddr[6:2] == HCSR_ONYX_MON_WIN_LO)) begin
                        r_onyx_mon_win_lo[8*b +: 8] <= r_wdata[8*b +: 8];
                    end
                    if (r_wstrb[b] && (r_awaddr[6:2] == HCSR_ONYX_MON_WIN_HI)) begin
                        r_onyx_mon_win_hi[8*b +: 8] <= r_wdata[8*b +: 8];
                    end
                    if (r_wstrb[b] && (r_awaddr[6:2] == HCSR_IO_ADDR)) begin
                        r_io_addr[8*b +: 8] <= r_wdata[8*b +: 8];
                    end
                    if (r_wstrb[b] && (r_awaddr[6:2] == HCSR_IO_WDATA_LO)) begin
                        r_io_wdata_lo[8*b +: 8] <= r_wdata[8*b +: 8];
                    end
                    if (r_wstrb[b] && (r_awaddr[6:2] == HCSR_IO_WDATA_HI)) begin
                        r_io_wdata_hi[8*b +: 8] <= r_wdata[8*b +: 8];
                    end
                    if (r_wstrb[b] && (r_awaddr[6:2] == HCSR_IO_CTRL)) begin
                        r_io_ctrl[8*b +: 8] <= r_wdata[8*b +: 8];
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
        case (r_araddr[6:2])
            HCSR_CTRL:       r_rdata = r_ctrl;
            HCSR_STATUS:     r_rdata = i_status;
            HCSR_CYCLE_LO:   r_rdata = i_cycle_lo;
            HCSR_CYCLE_HI:   r_rdata = i_cycle_hi;
            HCSR_FABRIC_DBG: r_rdata = {28'b0, i_fabric_dbg};
            5'h08, 5'h09, 5'h0A, 5'h0B, 5'h0C, 5'h0D:
                             r_rdata = i_onyx_cnt[3'(r_araddr[6:2] - HCSR_ONYX_CNT0)];
            HCSR_ONYX_CNT_CU_DT:  r_rdata = i_onyx_cnt[6];
            HCSR_ONYX_CNT_OLD_WB: r_rdata = i_onyx_cnt[7];
            HCSR_ONYX_MON_CTRL: r_rdata = r_onyx_mon_ctrl;
            HCSR_ONYX_MON_MASK: r_rdata = r_onyx_mon_mask;
            HCSR_ONYX_MON_WIN_LO: r_rdata = r_onyx_mon_win_lo;
            HCSR_ONYX_MON_WIN_HI: r_rdata = r_onyx_mon_win_hi;
            HCSR_IO_ADDR:     r_rdata = r_io_addr;
            HCSR_IO_WDATA_LO: r_rdata = r_io_wdata_lo;
            HCSR_IO_WDATA_HI: r_rdata = r_io_wdata_hi;
            HCSR_IO_CTRL:     r_rdata = r_io_ctrl;      // go reads 0
            HCSR_IO_STATUS:   r_rdata = {i_io_absent, 27'b0, i_io_resp, i_io_done, i_io_busy};
            HCSR_IO_RDATA_LO: r_rdata = i_io_rdata[31:0];
            HCSR_IO_RDATA_HI: r_rdata = i_io_rdata[63:32];
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
