// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: 2025 sean galloway
//
// Module: stream_char_harness
// Purpose: Internal integration for the STREAM characterization harness.
//
// Instantiates:
//   - uart_axil_bridge                (host interface)
//   - bridge_stream_char_axil         (1->6 generated bridge w/ APB+AXIL slaves;
//                                      handles every port natively — no
//                                      external converter glue needed)
//   - harness_csr                     (control/status)
//   - desc_ram                        (descriptor storage)
//   - debug_sram                      (MonBus trace capture)
//   - axi4_slave_rd_pattern_gen       (DMA source)
//   - axi4_slave_wr_crc_check         (DMA sink)
//   - stream_top_ch8                  (DUT: STREAM DMA)
//
// The top level (stream_char_top.sv) wraps this with FPGA pin-level I/O.

`timescale 1ns / 1ps

`include "reset_defs.svh"

module stream_char_harness #(
    parameter int FPGA_CLK_HZ  = 100_000_000,
    parameter int UART_BAUD    = 115_200,
    parameter int DATA_WIDTH   = 128,
    parameter int ADDR_WIDTH   = 32,
    parameter int SRAM_DEPTH   = 256,
    // NUM_CHANNELS is overridable so the FPGA target can build a 4-channel
    // configuration to fit the Artix-7 100T without changing the DUT's native
    // DATA_WIDTH. Valid values: any power of 2 that the DUT supports (1/2/4/8).
    parameter int NUM_CHANNELS = 8,

    // Harness-side memory sizing. Defaults match the big ASIC simulation
    // target. The FPGA top overrides these to fit in Artix-7 BRAM: see
    // rtl/stream_char_top.sv. Descriptor test traffic uses ~256 B; monitor
    // trace depth is user-adjustable based on what the characterization
    // campaign needs to capture.
    parameter int DESC_RAM_ENTRIES = 2048,   // 2048 × 256 b  = 64 KB
    parameter int DEBUG_SRAM_WORDS = 65536,  //  64K ×  32 b  = 256 KB

    // axi_response_delay pipeline depths (in beats). Each delay block
    // models a real memory controller: every beat dwells exactly L cycles
    // (set by csr_*_resp_delay_cyc) but multiple beats are in flight in
    // parallel up to CAPACITY. Sized to absorb the engines' worst-case
    // outstanding count without back-pressuring the slave:
    //   R channel — AR_MAX_OUTSTANDING × max burst length (16)
    //   B channel — AW_MAX_OUTSTANDING (one BRESP per AW)
    // Override these at the top level if you change the engines' AR/AW
    // outstanding parameters or push to longer bursts.
    parameter int RESP_DELAY_R_CAPACITY = 256,
    parameter int RESP_DELAY_B_CAPACITY = 16,

    // STREAM engine outstanding queue (side-Q) depths. These are the
    // values stream_core uses to size its AR/AW reorder/outstanding-
    // tracking queues — the levers for measuring how much memory latency
    // the engines can hide. Defaults match stream_core's historical
    // values so this parameter is invisible unless overridden.
    parameter int AR_MAX_OUTSTANDING     = 8,
    parameter int AW_MAX_OUTSTANDING     = 8
) (
    input  logic            aclk,
    input  logic            aresetn,

    // UART
    input  logic            i_uart_rx,
    output logic            o_uart_tx,

    // Top-level status (to LEDs)
    output logic            o_stream_irq,
    output logic            o_any_error,
    output logic            o_trace_overflow,
    output logic [3:0]      o_heartbeat,

    // Characterization timer status (to top for LED PASS/FAIL display)
    output logic            o_timer_done,
    output logic            o_timer_pass
);

    localparam int AXI_ID_WIDTH   = 8;
    localparam int AXI_USER_WIDTH = $clog2(NUM_CHANNELS) > 0 ? $clog2(NUM_CHANNELS) : 1;
    localparam int APB_ADDR_WIDTH = 12;
    localparam int APB_DATA_WIDTH = 32;

    localparam int CLKS_PER_BIT = FPGA_CLK_HZ / UART_BAUD;

    // =========================================================================
    // UART-AXIL bridge
    // =========================================================================
    logic [31:0] uart_awaddr;
    logic [2:0]  uart_awprot;
    logic        uart_awvalid, uart_awready;
    logic [31:0] uart_wdata;
    logic [3:0]  uart_wstrb;
    logic        uart_wvalid, uart_wready;
    logic [1:0]  uart_bresp;
    logic        uart_bvalid, uart_bready;
    logic [31:0] uart_araddr;
    logic [2:0]  uart_arprot;
    logic        uart_arvalid, uart_arready;
    logic [31:0] uart_rdata;
    logic [1:0]  uart_rresp;
    logic        uart_rvalid, uart_rready;

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

    // =========================================================================
    // Generated 1 -> 6 AXIL bridge (replaces hand-rolled axil_decode_5s +
    // axil2apb). Source of truth:
    //   stream_char_framework/rtl/bridges/configs/bridge_stream_char_axil.toml
    //   stream_char_framework/rtl/bridges/configs/bridge_stream_char_axil_connectivity.csv
    //
    // Address map (host's view):
    //   stream_apb     0x0000_0000  4 KB    APB    STREAM config (auto-conv)
    //   harness_csr    0x0001_0000  256 B   AXIL   timer/delay/kick/status
    //   desc_ram       0x0002_0000  64 KB   AXIL   descriptor preload
    //   stream_err     0x0003_0000  64 B    AXIL   small err FIFO
    //   debug_sram     0x0004_0000  256 KB  AXIL   monitor trace
    //   dma_axil       0x0008_0000  4 KB    AXIL   DMA bridge port (unused
    //                                              in flows-stream-bridge;
    //                                              tied off below)
    //
    // Bridge implementation note: the generator emits native AXIL on
    // every slave port marked protocol="axil" — the AXI4-to-AXIL shim
    // lives inside each generated slave adapter, so the harness wires
    // AXIL signals directly from the bridge's <slave>_axi_* ports to
    // the AXIL slaves. APB is also emitted natively and goes straight
    // to the STREAM APB ports.
    //
    // The host port is full AXI4 (the bridge crossbar is AXI4-internal
    // and that's where the master plugs in). We drive the AXI4-only
    // fields (awid/awlen/awsize/awburst/awcache/awqos/awregion/awuser
    // plus the r-side equivalents) from constants matching AXIL
    // semantics: id=0, single beat (len=0), 4-byte size (size=2), INCR
    // burst (burst=01).
    // =========================================================================

    // ---- Host-side AXI4 wires (bridge expects AXI4; we have AXIL) ----------
    logic        host_axi_awid;
    logic        host_axi_bid;
    logic        host_axi_arid;
    logic        host_axi_rid;
    logic        host_axi_buser;
    logic        host_axi_ruser;
    logic        host_axi_rlast;

    // ---- Slave-side AXIL wires consumed by the rest of the harness ---------
    // (s1_* harness_csr, s2_* desc_ram, s3_* stream_err, s4_* debug_sram)
    logic [31:0] s1_awaddr, s1_wdata, s1_araddr, s1_rdata;
    logic [3:0]  s1_wstrb;
    logic [2:0]  s1_awprot, s1_arprot;
    logic [1:0]  s1_bresp, s1_rresp;
    logic s1_awvalid, s1_awready, s1_wvalid, s1_wready, s1_bvalid, s1_bready;
    logic s1_arvalid, s1_arready, s1_rvalid, s1_rready;

    logic [31:0] s2_awaddr, s2_wdata, s2_araddr, s2_rdata;
    logic [3:0]  s2_wstrb;
    logic [2:0]  s2_awprot, s2_arprot;
    logic [1:0]  s2_bresp, s2_rresp;
    logic s2_awvalid, s2_awready, s2_wvalid, s2_wready, s2_bvalid, s2_bready;
    logic s2_arvalid, s2_arready, s2_rvalid, s2_rready;

    logic [31:0] s3_awaddr, s3_wdata, s3_araddr, s3_rdata;
    logic [3:0]  s3_wstrb;
    logic [2:0]  s3_awprot, s3_arprot;
    logic [1:0]  s3_bresp, s3_rresp;
    logic s3_awvalid, s3_awready, s3_wvalid, s3_wready, s3_bvalid, s3_bready;
    logic s3_arvalid, s3_arready, s3_rvalid, s3_rready;

    logic [31:0] s4_awaddr, s4_wdata, s4_araddr, s4_rdata;
    logic [3:0]  s4_wstrb;
    logic [2:0]  s4_awprot, s4_arprot;
    logic [1:0]  s4_bresp, s4_rresp;
    logic s4_awvalid, s4_awready, s4_wvalid, s4_wready, s4_bvalid, s4_bready;
    logic s4_arvalid, s4_arready, s4_rvalid, s4_rready;

    // ---- APB output to STREAM (driven directly by bridge.stream_apb_*) -----
    // Bridge emits 32-bit PADDR; STREAM APB takes APB_ADDR_WIDTH (12 bits).
    // Wire the full 32-bit at the bridge boundary, slice down to apb_paddr.
    logic [31:0]                   stream_apb_PADDR_full;
    logic [APB_ADDR_WIDTH-1:0]     apb_paddr;
    logic                          apb_psel, apb_penable, apb_pwrite;
    logic [APB_DATA_WIDTH-1:0]     apb_pwdata, apb_prdata;
    logic [(APB_DATA_WIDTH/8)-1:0] apb_pstrb;
    logic                          apb_pready, apb_pslverr;
    assign apb_paddr = stream_apb_PADDR_full[APB_ADDR_WIDTH-1:0];

    // The previous incarnation of this harness declared b2csr_/b2desc_/
    // b2err_/b2dbg_ AXI4 intermediate wires and instantiated four
    // axi4_to_axil4_{wr,rd} shim pairs between the bridge and each AXIL
    // slave. That was a workaround for an earlier bridge generator that
    // emitted full AXI4 on every slave port regardless of the toml's
    // protocol field. The generator now produces native AXIL ports for
    // AXIL slaves, so the external shims are gone and the bridge's
    // AXIL signals wire straight to s1_*/s2_*/s3_*/s4_*. One bridge
    // handles every port — no external converter glue.

    // ---- Bridge instance ---------------------------------------------------
    bridge_stream_char_axil u_bridge (
        .aclk    (aclk),
        .aresetn (aresetn),

        // Master 0: host (bridge expects AXI4; we drive AXIL semantics)
        .host_axi_awid     (1'b0),
        .host_axi_awaddr   (uart_awaddr),
        .host_axi_awlen    (8'd0),
        .host_axi_awsize   (3'd2),
        .host_axi_awburst  (2'b01),
        .host_axi_awlock   (1'b0),
        .host_axi_awcache  (4'd0),
        .host_axi_awprot   (uart_awprot),
        .host_axi_awqos    (4'd0),
        .host_axi_awregion (4'd0),
        .host_axi_awuser   (1'b0),
        .host_axi_awvalid  (uart_awvalid),
        .host_axi_awready  (uart_awready),

        .host_axi_wdata    (uart_wdata),
        .host_axi_wstrb    (uart_wstrb),
        .host_axi_wlast    (1'b1),  // single-beat (len=0)
        .host_axi_wuser    (1'b0),
        .host_axi_wvalid   (uart_wvalid),
        .host_axi_wready   (uart_wready),

        .host_axi_bid      (host_axi_bid),     // ignored (id_width=1, always 0)
        .host_axi_bresp    (uart_bresp),
        .host_axi_buser    (host_axi_buser),   // ignored
        .host_axi_bvalid   (uart_bvalid),
        .host_axi_bready   (uart_bready),

        .host_axi_arid     (1'b0),
        .host_axi_araddr   (uart_araddr),
        .host_axi_arlen    (8'd0),
        .host_axi_arsize   (3'd2),
        .host_axi_arburst  (2'b01),
        .host_axi_arlock   (1'b0),
        .host_axi_arcache  (4'd0),
        .host_axi_arprot   (uart_arprot),
        .host_axi_arqos    (4'd0),
        .host_axi_arregion (4'd0),
        .host_axi_aruser   (1'b0),
        .host_axi_arvalid  (uart_arvalid),
        .host_axi_arready  (uart_arready),

        .host_axi_rid      (host_axi_rid),     // ignored
        .host_axi_rdata    (uart_rdata),
        .host_axi_rresp    (uart_rresp),
        .host_axi_rlast    (host_axi_rlast),   // ignored (single-beat)
        .host_axi_ruser    (host_axi_ruser),   // ignored
        .host_axi_rvalid   (uart_rvalid),
        .host_axi_rready   (uart_rready),

        // Slave 0: stream_apb (APB native — direct connection)
        .stream_apb_PSEL    (apb_psel),
        .stream_apb_PADDR   (stream_apb_PADDR_full),
        .stream_apb_PENABLE (apb_penable),
        .stream_apb_PWRITE  (apb_pwrite),
        .stream_apb_PWDATA  (apb_pwdata),
        .stream_apb_PSTRB   (apb_pstrb),
        .stream_apb_PPROT   (),
        .stream_apb_PRDATA  (apb_prdata),
        .stream_apb_PREADY  (apb_pready),
        .stream_apb_PSLVERR (apb_pslverr),

        // Slave 1: harness_csr (native AXIL — wired directly to s1_*)
        .harness_csr_axi_awaddr   (s1_awaddr),
        .harness_csr_axi_awprot   (s1_awprot),
        .harness_csr_axi_awvalid  (s1_awvalid),
        .harness_csr_axi_awready  (s1_awready),
        .harness_csr_axi_wdata    (s1_wdata),
        .harness_csr_axi_wstrb    (s1_wstrb),
        .harness_csr_axi_wvalid   (s1_wvalid),
        .harness_csr_axi_wready   (s1_wready),
        .harness_csr_axi_bresp    (s1_bresp),
        .harness_csr_axi_bvalid   (s1_bvalid),
        .harness_csr_axi_bready   (s1_bready),
        .harness_csr_axi_araddr   (s1_araddr),
        .harness_csr_axi_arprot   (s1_arprot),
        .harness_csr_axi_arvalid  (s1_arvalid),
        .harness_csr_axi_arready  (s1_arready),
        .harness_csr_axi_rdata    (s1_rdata),
        .harness_csr_axi_rresp    (s1_rresp),
        .harness_csr_axi_rvalid   (s1_rvalid),
        .harness_csr_axi_rready   (s1_rready),

        // Slave 2: desc_ram (native AXIL — wired directly to s2_*)
        .desc_ram_axi_awaddr   (s2_awaddr),
        .desc_ram_axi_awprot   (s2_awprot),
        .desc_ram_axi_awvalid  (s2_awvalid),
        .desc_ram_axi_awready  (s2_awready),
        .desc_ram_axi_wdata    (s2_wdata),
        .desc_ram_axi_wstrb    (s2_wstrb),
        .desc_ram_axi_wvalid   (s2_wvalid),
        .desc_ram_axi_wready   (s2_wready),
        .desc_ram_axi_bresp    (s2_bresp),
        .desc_ram_axi_bvalid   (s2_bvalid),
        .desc_ram_axi_bready   (s2_bready),
        .desc_ram_axi_araddr   (s2_araddr),
        .desc_ram_axi_arprot   (s2_arprot),
        .desc_ram_axi_arvalid  (s2_arvalid),
        .desc_ram_axi_arready  (s2_arready),
        .desc_ram_axi_rdata    (s2_rdata),
        .desc_ram_axi_rresp    (s2_rresp),
        .desc_ram_axi_rvalid   (s2_rvalid),
        .desc_ram_axi_rready   (s2_rready),

        // Slave 3: stream_err (native AXIL — wired directly to s3_*)
        .stream_err_axi_awaddr   (s3_awaddr),
        .stream_err_axi_awprot   (s3_awprot),
        .stream_err_axi_awvalid  (s3_awvalid),
        .stream_err_axi_awready  (s3_awready),
        .stream_err_axi_wdata    (s3_wdata),
        .stream_err_axi_wstrb    (s3_wstrb),
        .stream_err_axi_wvalid   (s3_wvalid),
        .stream_err_axi_wready   (s3_wready),
        .stream_err_axi_bresp    (s3_bresp),
        .stream_err_axi_bvalid   (s3_bvalid),
        .stream_err_axi_bready   (s3_bready),
        .stream_err_axi_araddr   (s3_araddr),
        .stream_err_axi_arprot   (s3_arprot),
        .stream_err_axi_arvalid  (s3_arvalid),
        .stream_err_axi_arready  (s3_arready),
        .stream_err_axi_rdata    (s3_rdata),
        .stream_err_axi_rresp    (s3_rresp),
        .stream_err_axi_rvalid   (s3_rvalid),
        .stream_err_axi_rready   (s3_rready),

        // Slave 4: debug_sram (native AXIL — wired directly to s4_*)
        .debug_sram_axi_awaddr   (s4_awaddr),
        .debug_sram_axi_awprot   (s4_awprot),
        .debug_sram_axi_awvalid  (s4_awvalid),
        .debug_sram_axi_awready  (s4_awready),
        .debug_sram_axi_wdata    (s4_wdata),
        .debug_sram_axi_wstrb    (s4_wstrb),
        .debug_sram_axi_wvalid   (s4_wvalid),
        .debug_sram_axi_wready   (s4_wready),
        .debug_sram_axi_bresp    (s4_bresp),
        .debug_sram_axi_bvalid   (s4_bvalid),
        .debug_sram_axi_bready   (s4_bready),
        .debug_sram_axi_araddr   (s4_araddr),
        .debug_sram_axi_arprot   (s4_arprot),
        .debug_sram_axi_arvalid  (s4_arvalid),
        .debug_sram_axi_arready  (s4_arready),
        .debug_sram_axi_rdata    (s4_rdata),
        .debug_sram_axi_rresp    (s4_rresp),
        .debug_sram_axi_rvalid   (s4_rvalid),
        .debug_sram_axi_rready   (s4_rready),

        // Slave 5: dma_axil (unused in flows-stream-bridge — tied off so
        // accidental writes don't hang the bus; never addressed in normal
        // operation, so this is purely defensive). Native AXIL signal set
        // only — id/len/burst/etc. no longer exist on this port.
        .dma_axil_awaddr   (),
        .dma_axil_awprot   (),
        .dma_axil_awvalid  (),
        .dma_axil_awready  (1'b1),         // always accept
        .dma_axil_wdata    (),
        .dma_axil_wstrb    (),
        .dma_axil_wvalid   (),
        .dma_axil_wready   (1'b1),         // always accept
        .dma_axil_bresp    (2'b11),        // DECERR if anything lands here
        .dma_axil_bvalid   (1'b0),         // never assert (host should never address this)
        .dma_axil_bready   (),
        .dma_axil_araddr   (),
        .dma_axil_arprot   (),
        .dma_axil_arvalid  (),
        .dma_axil_arready  (1'b1),
        .dma_axil_rdata    (32'hDEAD_BEEF),
        .dma_axil_rresp    (2'b11),
        .dma_axil_rvalid   (1'b0),
        .dma_axil_rready   ()
    );


    // =========================================================================
    // S1: harness_csr
    // =========================================================================
    logic        csr_start_pulse, csr_clear_pulse, csr_freeze, csr_soft_reset;
    logic        csr_timer_clear_pulse;
    logic [31:0] csr_timer_expected_beats;
    logic [31:0] dbg_wr_ptr;
    logic        dbg_overflow;
    logic        dbg_clear_busy;
    // Per-channel CRC + beat-count outputs from the slaves. The slaves
    // demux off s_axi_arid / s_axi_wuser low-bits and keep independent
    // LFSR/CRC state per channel, so multi-channel runs verify integrity
    // per channel instead of being scrambled by interleave at the shared
    // AXI port. Aggregates feed the harness-timer beat-count stop trigger.
    logic [NUM_CHANNELS-1:0][31:0] read_crc_value;
    logic [NUM_CHANNELS-1:0]       read_crc_valid;
    logic [NUM_CHANNELS-1:0][31:0] read_beat_count_per_ch;
    logic [31:0]                   read_beat_count;   // aggregate
    logic [NUM_CHANNELS-1:0][31:0] write_crc_value;
    logic [NUM_CHANNELS-1:0]       write_crc_valid;
    logic [NUM_CHANNELS-1:0][31:0] write_beat_count_per_ch;
    logic [31:0]                   write_beat_count;  // aggregate
    logic        stream_irq;

    // Characterization timer outputs (driven below, consumed by harness_csr
    // and exposed to the top-level for the LED override).
    logic        timer_done;
    logic        timer_running;
    logic        timer_pass;
    logic [63:0] timer_cycles;

    // Per-engine cycle stamps captured during the timed window. Used to
    // compute R2R and W2W steady-state engine throughput, which strip the
    // descriptor-fetch fill and last-burst drain overhead from the total.
    //   r_first / r_last : cycle counts at first / last R beat
    //   w_first / w_last : cycle counts at first / last W beat
    // All four are sampled from timer_cycles, so they share its time base.
    logic [63:0] timer_r_first, timer_r_last;
    logic [63:0] timer_w_first, timer_w_last;

    // Per-channel match: equal CRC AND both halves valid for that channel.
    // Aggregate "test passed" = at least one channel was active (saw beats
    // and produced a valid CRC) AND no active channel mismatched. This
    // sidesteps needing visibility into cfg_channel_enable here — channels
    // that were never enabled have valid=0 so they neither pass nor fail.
    logic [NUM_CHANNELS-1:0] crc_match_per_ch;
    logic [NUM_CHANNELS-1:0] crc_valid_per_ch;
    always_comb begin
        for (int ch = 0; ch < NUM_CHANNELS; ch++) begin
            crc_valid_per_ch[ch] = read_crc_valid[ch] && write_crc_valid[ch];
            crc_match_per_ch[ch] = crc_valid_per_ch[ch]
                                && (read_crc_value[ch] == write_crc_value[ch]);
        end
    end
    wire any_active   = |crc_valid_per_ch;
    wire any_mismatch = |(crc_valid_per_ch & ~crc_match_per_ch);
    wire crc_match      = any_active && !any_mismatch;
    wire crc_both_valid = any_active;
    // any_error: sticky "something went wrong" signal routed to CSR_STATUS[1].
    // TODO: drive from a real error source. stream_top_ch8 does not yet expose
    // a scheduler/engine error wire at its boundary, so for now this stays tied
    // to 0 and callers must poll the in-band SCHED_ERROR register (stream_regs
    // @ 0x170) for error visibility. The primary completion signal for tests is
    // stream_irq from monbus_axil_group.irq_out.
    wire any_error = 1'b0;

    // Wires from harness_csr → axi_response_delay blocks below (RESP_DELAY @ 0x3C).
    logic [15:0] csr_rd_resp_delay_cyc;
    logic [15:0] csr_wr_resp_delay_cyc;

    // Wires from harness_csr → stream_top_ch8 (kick-burst fast path).
    logic [NUM_CHANNELS-1:0]       csr_kick_burst_mask;
    logic [NUM_CHANNELS-1:0][31:0] csr_kick_burst_addr;

    harness_csr #(.AW(32), .DW(32), .NUM_CHANNELS(NUM_CHANNELS)) u_csr (
        .aclk(aclk), .aresetn(aresetn),
        .s_awaddr(s1_awaddr), .s_awprot(s1_awprot),
        .s_awvalid(s1_awvalid), .s_awready(s1_awready),
        .s_wdata(s1_wdata), .s_wstrb(s1_wstrb),
        .s_wvalid(s1_wvalid), .s_wready(s1_wready),
        .s_bresp(s1_bresp), .s_bvalid(s1_bvalid), .s_bready(s1_bready),
        .s_araddr(s1_araddr), .s_arprot(s1_arprot),
        .s_arvalid(s1_arvalid), .s_arready(s1_arready),
        .s_rdata(s1_rdata), .s_rresp(s1_rresp),
        .s_rvalid(s1_rvalid), .s_rready(s1_rready),
        .o_start_pulse      (csr_start_pulse),
        .o_clear_stats_pulse(csr_clear_pulse),
        .o_freeze_trace     (csr_freeze),
        .o_soft_reset_pulse (csr_soft_reset),
        .i_stream_irq       (stream_irq),
        .i_any_error        (any_error),
        .i_dbg_wr_ptr       (dbg_wr_ptr),
        .i_dbg_overflow     (dbg_overflow),
        .i_dbg_clear_busy   (dbg_clear_busy),
        // Aggregate scalars (back-compat at 0x10/0x14/0x18/0x1C): channel-0
        // CRC plus any-active/all-active reductions across channels.
        .i_crc_rd_expected  (read_crc_value[0]),
        .i_crc_wr_expected  (read_crc_value[0]),  // expected = source CRC
        .i_crc_wr_computed  (write_crc_value[0]),
        .i_crc_valid        (crc_both_valid),
        .i_crc_match        (crc_match),
        // Per-channel CRC arrays + bitmasks for multi-channel verification.
        .i_crc_rd_per_ch    (read_crc_value),
        .i_crc_wr_per_ch    (write_crc_value),
        .i_crc_valid_mask   (crc_valid_per_ch),
        .i_crc_match_mask   (crc_match_per_ch),

        // Characterization timer
        .o_timer_clear_pulse   (csr_timer_clear_pulse),
        .o_timer_expected_beats(csr_timer_expected_beats),
        .i_timer_done          (timer_done),
        .i_timer_running       (timer_running),
        .i_timer_pass          (timer_pass),
        .i_timer_cycles        (timer_cycles),
        .i_timer_r_first       (timer_r_first),
        .i_timer_r_last        (timer_r_last),
        .i_timer_w_first       (timer_w_first),
        .i_timer_w_last        (timer_w_last),

        // Response-delay knobs (driven by RESP_DELAY register @ 0x3C)
        .o_rd_resp_delay_cyc   (csr_rd_resp_delay_cyc),
        .o_wr_resp_delay_cyc   (csr_wr_resp_delay_cyc),

        // Kick-burst outputs (CH_KICK_ADDR @ 0xB0+4*ch, KICK_GO @ 0xC0)
        .o_kick_burst_mask     (csr_kick_burst_mask),
        .o_kick_burst_addr     (csr_kick_burst_addr)
    );

    // =========================================================================
    // Characterization timer
    // =========================================================================
    // 64-bit cycle counter at aclk (10 ns / cycle). Captures the wall-clock
    // duration of a DMA "session" so the host can compute measured throughput
    // without depending on the broken stream_irq -> CSR_STATUS path.
    //
    //   START : rising edge of (desc_arvalid & desc_arready) — the first AR
    //           handshake the scheduler issues on the descriptor-RAM bus
    //           after a TIMER_CTRL clear. Latched: only one start per
    //           session (ignored once running OR done).
    //   STOP  : write_beat_count >= csr_timer_expected_beats. The sink
    //           slave's write_beat_count increments on each W beat, so this
    //           reaches the programmed expected count exactly when the last
    //           beat has been consumed by the CRC checker. The host
    //           programs CSR_TIMER_EXP_BEATS (0x38) before the kick.
    //           Disabled when expected_beats == 0 (host can keep timer
    //           running indefinitely if it wants to read cycles live).
    //   PASS  : crc_match sampled SETTLE_CYCLES after the stop trigger.
    //           dataint_crc has a 2-cycle pipeline (cascade compute +
    //           output register), so write_crc_value lags write_beat_count
    //           by one cycle. We let it settle for SETTLE_CYCLES before
    //           capturing pass to avoid a 1-cycle race that would mark a
    //           correct transfer as failed. The settle window is NOT
    //           counted in timer_cycles — that freezes at the true
    //           transfer-end so reported throughput stays accurate.
    //   CLEAR : csr_timer_clear_pulse from harness_csr (0x28[0] write).
    localparam logic [2:0] SETTLE_CYCLES = 3'd5;

    logic r_desc_handshake_d;
    logic [2:0] r_settle_cnt;
    wire  w_desc_handshake      = desc_arvalid & desc_arready;
    wire  w_desc_handshake_rise = w_desc_handshake & ~r_desc_handshake_d;
    wire  w_beat_count_reached  = (csr_timer_expected_beats != 32'd0) &&
                                  (write_beat_count >= csr_timer_expected_beats);

    `ALWAYS_FF_RST(aclk, aresetn,
        if (`RST_ASSERTED(aresetn)) begin
            r_desc_handshake_d <= 1'b0;
        end else begin
            r_desc_handshake_d <= w_desc_handshake;
        end
    )

    // First/last beat detection on the slave side. read_beat_count and
    // write_beat_count both start at 0 and increment monotonically; we
    // latch cycle stamps on the first cycle each crosses 0 and on the
    // first cycle each reaches the programmed expected_beats target.
    logic        r_rd_first_seen, r_wr_first_seen;
    logic        r_rd_last_seen,  r_wr_last_seen;
    wire         w_rd_first_now  = timer_running && !r_rd_first_seen
                                                  && (read_beat_count != 32'd0);
    wire         w_wr_first_now  = timer_running && !r_wr_first_seen
                                                  && (write_beat_count != 32'd0);
    wire         w_rd_last_now   = timer_running && !r_rd_last_seen
                                                  && (csr_timer_expected_beats != 32'd0)
                                                  && (read_beat_count >= csr_timer_expected_beats);
    wire         w_wr_last_now   = timer_running && !r_wr_last_seen
                                                  && w_beat_count_reached;

    `ALWAYS_FF_RST(aclk, aresetn,
        if (`RST_ASSERTED(aresetn)) begin
            timer_running <= 1'b0;
            timer_done    <= 1'b0;
            timer_pass    <= 1'b0;
            timer_cycles  <= '0;
            r_settle_cnt  <= 3'd0;
            timer_r_first <= '0;
            timer_r_last  <= '0;
            timer_w_first <= '0;
            timer_w_last  <= '0;
            r_rd_first_seen <= 1'b0;
            r_wr_first_seen <= 1'b0;
            r_rd_last_seen  <= 1'b0;
            r_wr_last_seen  <= 1'b0;
        end else if (csr_timer_clear_pulse) begin
            timer_running <= 1'b0;
            timer_done    <= 1'b0;
            timer_pass    <= 1'b0;
            timer_cycles  <= '0;
            r_settle_cnt  <= 3'd0;
            timer_r_first <= '0;
            timer_r_last  <= '0;
            timer_w_first <= '0;
            timer_w_last  <= '0;
            r_rd_first_seen <= 1'b0;
            r_wr_first_seen <= 1'b0;
            r_rd_last_seen  <= 1'b0;
            r_wr_last_seen  <= 1'b0;
        end else if (timer_running) begin
            // Latch first/last beat stamps. Sampled from timer_cycles so all
            // four share the same start-of-session time base (cycle 1 = first
            // post-start cycle). Each is latched exactly once per session.
            if (w_rd_first_now) begin
                timer_r_first   <= timer_cycles;
                r_rd_first_seen <= 1'b1;
            end
            if (w_wr_first_now) begin
                timer_w_first   <= timer_cycles;
                r_wr_first_seen <= 1'b1;
            end
            if (w_rd_last_now) begin
                timer_r_last   <= timer_cycles;
                r_rd_last_seen <= 1'b1;
            end
            if (w_wr_last_now) begin
                timer_w_last   <= timer_cycles;
                r_wr_last_seen <= 1'b1;
            end

            if (w_beat_count_reached) begin
                // Stop counting cycles; begin settle window.
                timer_running <= 1'b0;
                r_settle_cnt  <= 3'd1;
            end else begin
                timer_cycles  <= timer_cycles + 64'd1;
            end
        end else if (r_settle_cnt != 3'd0) begin
            if (r_settle_cnt == SETTLE_CYCLES) begin
                r_settle_cnt <= 3'd0;
                timer_done   <= 1'b1;
                timer_pass   <= crc_match;
            end else begin
                r_settle_cnt <= r_settle_cnt + 3'd1;
            end
        end else if (!timer_done && w_desc_handshake_rise) begin
            // First AR handshake on the descriptor RAM bus — start.
            timer_running <= 1'b1;
            timer_cycles  <= 64'd1;  // count the start cycle
        end
    )

    // =========================================================================
    // S2: desc_ram  (AXIL write + AXI4 read)
    // =========================================================================
    // AXI4 read side wired to STREAM m_axi_desc
    logic [AXI_ID_WIDTH-1:0]    desc_arid;
    logic [ADDR_WIDTH-1:0]      desc_araddr;
    logic [7:0]                 desc_arlen;
    logic [2:0]                 desc_arsize;
    logic [1:0]                 desc_arburst;
    logic                       desc_arlock;
    logic [3:0]                 desc_arcache;
    logic [2:0]                 desc_arprot;
    logic [3:0]                 desc_arqos;
    logic [3:0]                 desc_arregion;
    logic [AXI_USER_WIDTH-1:0]  desc_aruser;
    logic                       desc_arvalid, desc_arready;
    logic [AXI_ID_WIDTH-1:0]    desc_rid;
    logic [255:0]               desc_rdata;
    logic [1:0]                 desc_rresp;
    logic                       desc_rlast;
    logic [AXI_USER_WIDTH-1:0]  desc_ruser;
    logic                       desc_rvalid, desc_rready;

    desc_ram #(
        .AXI_ID_WIDTH  (AXI_ID_WIDTH),
        .AXI_USER_WIDTH(AXI_USER_WIDTH),
        .AXI_ADDR_WIDTH(ADDR_WIDTH),
        .DEPTH_256     (DESC_RAM_ENTRIES)
    ) u_desc_ram (
        .aclk(aclk), .aresetn(aresetn),
        // AXIL write (from host decode S2)
        .s_axil_awaddr (s2_awaddr), .s_axil_awprot(s2_awprot),
        .s_axil_awvalid(s2_awvalid), .s_axil_awready(s2_awready),
        .s_axil_wdata  (s2_wdata), .s_axil_wstrb(s2_wstrb),
        .s_axil_wvalid (s2_wvalid), .s_axil_wready(s2_wready),
        .s_axil_bresp  (s2_bresp), .s_axil_bvalid(s2_bvalid), .s_axil_bready(s2_bready),
        .s_axil_araddr (s2_araddr), .s_axil_arprot(s2_arprot),
        .s_axil_arvalid(s2_arvalid), .s_axil_arready(s2_arready),
        .s_axil_rdata  (s2_rdata), .s_axil_rresp(s2_rresp),
        .s_axil_rvalid (s2_rvalid), .s_axil_rready(s2_rready),
        // AXI4 read (from STREAM m_axi_desc)
        .s_axi_arid   (desc_arid),   .s_axi_araddr(desc_araddr),
        .s_axi_arlen  (desc_arlen),  .s_axi_arsize(desc_arsize),
        .s_axi_arburst(desc_arburst),.s_axi_arlock(desc_arlock),
        .s_axi_arcache(desc_arcache),.s_axi_arprot(desc_arprot),
        .s_axi_arqos  (desc_arqos),  .s_axi_arregion(desc_arregion),
        .s_axi_aruser (desc_aruser), .s_axi_arvalid(desc_arvalid),
        .s_axi_arready(desc_arready),
        .s_axi_rid    (desc_rid),    .s_axi_rdata(desc_rdata),
        .s_axi_rresp  (desc_rresp),  .s_axi_rlast(desc_rlast),
        .s_axi_ruser  (desc_ruser),  .s_axi_rvalid(desc_rvalid),
        .s_axi_rready (desc_rready)
    );

    // =========================================================================
    // S3: STREAM err FIFO AXIL slave (wired to stream.s_axil_err_*)
    //
    // S3 from decoder drives the AXIL read channel of STREAM err FIFO.
    // Write channel on this slot is unused; tie off with OKAY.
    // =========================================================================
    logic        s3_err_arvalid, s3_err_arready;
    logic [31:0] s3_err_araddr;
    logic [2:0]  s3_err_arprot;
    logic        s3_err_rvalid,  s3_err_rready;
    logic [31:0] s3_err_rdata;
    logic [1:0]  s3_err_rresp;

    assign s3_err_arvalid = s3_arvalid;
    assign s3_err_araddr  = s3_araddr;
    assign s3_err_arprot  = s3_arprot;
    assign s3_arready     = s3_err_arready;

    assign s3_rvalid      = s3_err_rvalid;
    assign s3_rdata       = s3_err_rdata;
    assign s3_rresp       = s3_err_rresp;
    assign s3_err_rready  = s3_rready;

    // Write side on S3: sink with OKAY (host shouldn't write here)
    logic r_s3_bvalid;
    `ALWAYS_FF_RST(aclk, aresetn,
        if (`RST_ASSERTED(aresetn)) begin
            r_s3_bvalid <= 1'b0;
        end else begin
            if (s3_awvalid && s3_wvalid && !r_s3_bvalid) r_s3_bvalid <= 1'b1;
            else if (s3_bready && r_s3_bvalid)            r_s3_bvalid <= 1'b0;
        end
    )
    assign s3_awready = !r_s3_bvalid;
    assign s3_wready  = !r_s3_bvalid;
    assign s3_bvalid  = r_s3_bvalid;
    assign s3_bresp   = 2'b10;  // SLVERR

    // =========================================================================
    // S4: debug_sram (host read port) + STREAM m_axil_mon writes
    // =========================================================================
    // STREAM m_axil_mon AXIL master signals
    logic        mon_awvalid, mon_awready;
    logic [31:0] mon_awaddr;
    logic [2:0]  mon_awprot;
    logic        mon_wvalid,  mon_wready;
    logic [31:0] mon_wdata;
    logic [3:0]  mon_wstrb;
    logic        mon_bvalid,  mon_bready;
    logic [1:0]  mon_bresp;

    debug_sram #(
        .DEPTH_WORDS(DEBUG_SRAM_WORDS)
    ) u_debug_sram (
        .aclk(aclk), .aresetn(aresetn),
        .i_freeze     (csr_freeze),
        .i_clear_pulse(csr_clear_pulse),
        .o_wr_ptr     (dbg_wr_ptr),
        .o_overflow   (dbg_overflow),
        .o_clear_busy (dbg_clear_busy),
        // Write-only port from STREAM monbus AXIL master
        .wr_awaddr (mon_awaddr), .wr_awprot(mon_awprot),
        .wr_awvalid(mon_awvalid), .wr_awready(mon_awready),
        .wr_wdata  (mon_wdata), .wr_wstrb(mon_wstrb),
        .wr_wvalid (mon_wvalid), .wr_wready(mon_wready),
        .wr_bresp  (mon_bresp), .wr_bvalid(mon_bvalid), .wr_bready(mon_bready),
        .wr_araddr (32'h0), .wr_arprot(3'h0),
        .wr_arvalid(1'b0), .wr_arready(),
        .wr_rdata  (), .wr_rresp(),
        .wr_rvalid (), .wr_rready(1'b1),
        // Read-only port from host decoder S4
        .rd_awaddr (s4_awaddr), .rd_awprot(s4_awprot),
        .rd_awvalid(s4_awvalid), .rd_awready(s4_awready),
        .rd_wdata  (s4_wdata), .rd_wstrb(s4_wstrb),
        .rd_wvalid (s4_wvalid), .rd_wready(s4_wready),
        .rd_bresp  (s4_bresp), .rd_bvalid(s4_bvalid), .rd_bready(s4_bready),
        .rd_araddr (s4_araddr), .rd_arprot(s4_arprot),
        .rd_arvalid(s4_arvalid), .rd_arready(s4_arready),
        .rd_rdata  (s4_rdata), .rd_rresp(s4_rresp),
        .rd_rvalid (s4_rvalid), .rd_rready(s4_rready)
    );

    // =========================================================================
    // DMA source: axi4_slave_rd_pattern_gen (wired to STREAM m_axi_rd)
    // =========================================================================
    logic [AXI_ID_WIDTH-1:0]    rd_arid;
    logic [ADDR_WIDTH-1:0]      rd_araddr;
    logic [7:0]                 rd_arlen;
    logic [2:0]                 rd_arsize;
    logic [1:0]                 rd_arburst;
    logic                       rd_arlock;
    logic [3:0]                 rd_arcache;
    logic [2:0]                 rd_arprot;
    logic [3:0]                 rd_arqos;
    logic [3:0]                 rd_arregion;
    logic [AXI_USER_WIDTH-1:0]  rd_aruser;
    logic                       rd_arvalid, rd_arready;
    logic [AXI_ID_WIDTH-1:0]    rd_rid;
    logic [DATA_WIDTH-1:0]      rd_rdata;
    logic [1:0]                 rd_rresp;
    logic                       rd_rlast;
    logic [AXI_USER_WIDTH-1:0]  rd_ruser;
    logic                       rd_rvalid;
    logic                       rd_rready;

    // Slave-side R wires (u_rd_pattern -> u_rd_resp_delay).
    // Master-side R wires (u_rd_resp_delay -> u_stream) keep the historical
    // rd_r* names so the u_stream port map below is untouched.
    logic [AXI_ID_WIDTH-1:0]   s_rd_rid;
    logic [DATA_WIDTH-1:0]     s_rd_rdata;
    logic [1:0]                s_rd_rresp;
    logic                      s_rd_rlast;
    logic [AXI_USER_WIDTH-1:0] s_rd_ruser;
    logic                      s_rd_rvalid;
    logic                      s_rd_rready;

    axi4_slave_rd_pattern_gen #(
        .NUM_CHANNELS  (NUM_CHANNELS),
        .AXI_ID_WIDTH  (AXI_ID_WIDTH),
        .AXI_ADDR_WIDTH(ADDR_WIDTH),
        .AXI_DATA_WIDTH(DATA_WIDTH),
        .AXI_USER_WIDTH(AXI_USER_WIDTH)
    ) u_rd_pattern (
        .aclk(aclk), .aresetn(aresetn),
        .crc_lfsr_reset       (csr_clear_pulse),
        .read_crc_value       (read_crc_value),
        .read_crc_valid       (read_crc_valid),
        .read_beat_count      (read_beat_count_per_ch),
        .read_beat_count_total(read_beat_count),
        .s_axi_arid    (rd_arid),    .s_axi_araddr(rd_araddr),
        .s_axi_arlen   (rd_arlen),   .s_axi_arsize(rd_arsize),
        .s_axi_arburst (rd_arburst), .s_axi_arlock(rd_arlock),
        .s_axi_arcache (rd_arcache), .s_axi_arprot(rd_arprot),
        .s_axi_arqos   (rd_arqos),   .s_axi_arregion(rd_arregion),
        .s_axi_aruser  (rd_aruser),  .s_axi_arvalid(rd_arvalid),
        .s_axi_arready (rd_arready),
        // R channel routed through u_rd_resp_delay (below)
        .s_axi_rid     (s_rd_rid),    .s_axi_rdata(s_rd_rdata),
        .s_axi_rresp   (s_rd_rresp),  .s_axi_rlast(s_rd_rlast),
        .s_axi_ruser   (s_rd_ruser),  .s_axi_rvalid(s_rd_rvalid),
        .s_axi_rready  (s_rd_rready),
        .busy          ()
    );

    // Optional per-beat response delay on the R channel. Bypass when
    // i_rd_resp_delay_en is 0 (zero added latency). When asserted, each beat
    // is held for RD_RESP_DELAY_CYCLES cycles before reaching u_stream.
    localparam int RD_R_PAYLOAD_W = AXI_ID_WIDTH + DATA_WIDTH + 2 + 1 + AXI_USER_WIDTH;
    logic [RD_R_PAYLOAD_W-1:0] s_rd_r_payload;
    logic [RD_R_PAYLOAD_W-1:0] m_rd_r_payload;

    assign s_rd_r_payload = {s_rd_rid, s_rd_rdata, s_rd_rresp, s_rd_rlast, s_rd_ruser};
    assign {rd_rid, rd_rdata, rd_rresp, rd_rlast, rd_ruser} = m_rd_r_payload;

    axi_response_delay #(
        .DATA_WIDTH (RD_R_PAYLOAD_W),
        .DELAY_W    (16),
        .CAPACITY   (RESP_DELAY_R_CAPACITY)
    ) u_rd_resp_delay (
        .aclk          (aclk),
        .aresetn       (aresetn),
        .i_delay_cycles(csr_rd_resp_delay_cyc),
        .s_data        (s_rd_r_payload),
        .s_valid       (s_rd_rvalid),
        .s_ready       (s_rd_rready),
        .m_data        (m_rd_r_payload),
        .m_valid       (rd_rvalid),
        .m_ready       (rd_rready)
    );

    // =========================================================================
    // DMA sink: axi4_slave_wr_crc_check (wired to STREAM m_axi_wr)
    // =========================================================================
    logic [AXI_ID_WIDTH-1:0]    wr_awid;
    logic [ADDR_WIDTH-1:0]      wr_awaddr;
    logic [7:0]                 wr_awlen;
    logic [2:0]                 wr_awsize;
    logic [1:0]                 wr_awburst;
    logic                       wr_awlock;
    logic [3:0]                 wr_awcache;
    logic [2:0]                 wr_awprot;
    logic [3:0]                 wr_awqos;
    logic [3:0]                 wr_awregion;
    logic [AXI_USER_WIDTH-1:0]  wr_awuser;
    logic                       wr_awvalid, wr_awready;
    logic [DATA_WIDTH-1:0]      wr_wdata;
    logic [DATA_WIDTH/8-1:0]    wr_wstrb;
    logic                       wr_wlast;
    logic [AXI_USER_WIDTH-1:0]  wr_wuser;
    logic                       wr_wvalid, wr_wready;
    logic [AXI_ID_WIDTH-1:0]    wr_bid;
    logic [1:0]                 wr_bresp;
    logic [AXI_USER_WIDTH-1:0]  wr_buser;
    logic                       wr_bvalid;
    logic                       wr_bready;

    // Slave-side B wires (u_wr_crc_check -> u_wr_resp_delay).
    // Master-side B wires (u_wr_resp_delay -> u_stream) keep the historical
    // wr_b* names so the u_stream port map below is untouched.
    logic [AXI_ID_WIDTH-1:0]   s_wr_bid;
    logic [1:0]                s_wr_bresp;
    logic [AXI_USER_WIDTH-1:0] s_wr_buser;
    logic                      s_wr_bvalid;
    logic                      s_wr_bready;

    axi4_slave_wr_crc_check #(
        .NUM_CHANNELS  (NUM_CHANNELS),
        .AXI_ID_WIDTH  (AXI_ID_WIDTH),
        .AXI_ADDR_WIDTH(ADDR_WIDTH),
        .AXI_DATA_WIDTH(DATA_WIDTH),
        .AXI_USER_WIDTH(AXI_USER_WIDTH)
    ) u_wr_crc_check (
        .aclk(aclk), .aresetn(aresetn),
        .crc_reset             (csr_clear_pulse),
        .write_crc_value       (write_crc_value),
        .write_crc_valid       (write_crc_valid),
        .write_beat_count      (write_beat_count_per_ch),
        .write_beat_count_total(write_beat_count),
        .s_axi_awid   (wr_awid),   .s_axi_awaddr(wr_awaddr),
        .s_axi_awlen  (wr_awlen),  .s_axi_awsize(wr_awsize),
        .s_axi_awburst(wr_awburst),.s_axi_awlock(wr_awlock),
        .s_axi_awcache(wr_awcache),.s_axi_awprot(wr_awprot),
        .s_axi_awqos  (wr_awqos),  .s_axi_awregion(wr_awregion),
        .s_axi_awuser (wr_awuser), .s_axi_awvalid(wr_awvalid),
        .s_axi_awready(wr_awready),
        .s_axi_wdata  (wr_wdata),  .s_axi_wstrb(wr_wstrb),
        .s_axi_wlast  (wr_wlast),  .s_axi_wuser(wr_wuser),
        .s_axi_wvalid (wr_wvalid), .s_axi_wready(wr_wready),
        // B channel routed through u_wr_resp_delay (below)
        .s_axi_bid    (s_wr_bid),    .s_axi_bresp(s_wr_bresp),
        .s_axi_buser  (s_wr_buser),  .s_axi_bvalid(s_wr_bvalid),
        .s_axi_bready (s_wr_bready),
        .busy         ()
    );

    // Optional per-beat response delay on the B channel. Bypass when
    // i_wr_resp_delay_en is 0 (zero added latency). When asserted, each B
    // response is held for WR_RESP_DELAY_CYCLES cycles before reaching
    // u_stream — which back-pressures the write pipeline and lets us study
    // sustained write bandwidth under realistic memory latency.
    localparam int WR_B_PAYLOAD_W = AXI_ID_WIDTH + 2 + AXI_USER_WIDTH;
    logic [WR_B_PAYLOAD_W-1:0] s_wr_b_payload;
    logic [WR_B_PAYLOAD_W-1:0] m_wr_b_payload;

    assign s_wr_b_payload = {s_wr_bid, s_wr_bresp, s_wr_buser};
    assign {wr_bid, wr_bresp, wr_buser} = m_wr_b_payload;

    axi_response_delay #(
        .DATA_WIDTH (WR_B_PAYLOAD_W),
        .DELAY_W    (16),
        .CAPACITY   (RESP_DELAY_B_CAPACITY)
    ) u_wr_resp_delay (
        .aclk          (aclk),
        .aresetn       (aresetn),
        .i_delay_cycles(csr_wr_resp_delay_cyc),
        .s_data        (s_wr_b_payload),
        .s_valid       (s_wr_bvalid),
        .s_ready       (s_wr_bready),
        .m_data        (m_wr_b_payload),
        .m_valid       (wr_bvalid),
        .m_ready       (wr_bready)
    );

    // =========================================================================
    // STREAM DUT
    // =========================================================================
    stream_top_ch8 #(
        .NUM_CHANNELS       (NUM_CHANNELS),
        .DATA_WIDTH         (DATA_WIDTH),
        .ADDR_WIDTH         (ADDR_WIDTH),
        .SRAM_DEPTH         (SRAM_DEPTH),
        .APB_ADDR_WIDTH     (APB_ADDR_WIDTH),
        .APB_DATA_WIDTH     (APB_DATA_WIDTH),
        .AXI_ID_WIDTH       (AXI_ID_WIDTH),
        .AXI_USER_WIDTH     (AXI_USER_WIDTH),
        .USE_AXI_MONITORS   (1),
        .CDC_ENABLE         (0),
        .AR_MAX_OUTSTANDING (AR_MAX_OUTSTANDING),
        .AW_MAX_OUTSTANDING (AW_MAX_OUTSTANDING)
    ) u_stream (
        .aclk    (aclk),   .aresetn(aresetn),
        .pclk    (aclk),   .presetn(aresetn),

        // Kick-burst fast path (1-cycle pulse from harness_csr KICK_GO,
        // shadow addresses from CH_KICK_ADDR[ch]).
        .i_kick_burst_mask (csr_kick_burst_mask),
        .i_kick_burst_addr (csr_kick_burst_addr),

        // APB config
        .s_apb_paddr  (apb_paddr),
        .s_apb_psel   (apb_psel),
        .s_apb_penable(apb_penable),
        .s_apb_pwrite (apb_pwrite),
        .s_apb_pwdata (apb_pwdata),
        .s_apb_pstrb  (apb_pstrb),
        .s_apb_prdata (apb_prdata),
        .s_apb_pready (apb_pready),
        .s_apb_pslverr(apb_pslverr),

        // Descriptor fetch master
        .m_axi_desc_arid   (desc_arid),   .m_axi_desc_araddr(desc_araddr),
        .m_axi_desc_arlen  (desc_arlen),  .m_axi_desc_arsize(desc_arsize),
        .m_axi_desc_arburst(desc_arburst),.m_axi_desc_arlock(desc_arlock),
        .m_axi_desc_arcache(desc_arcache),.m_axi_desc_arprot(desc_arprot),
        .m_axi_desc_arqos  (desc_arqos),  .m_axi_desc_arregion(desc_arregion),
        .m_axi_desc_aruser (desc_aruser), .m_axi_desc_arvalid(desc_arvalid),
        .m_axi_desc_arready(desc_arready),
        .m_axi_desc_rid    (desc_rid),    .m_axi_desc_rdata(desc_rdata),
        .m_axi_desc_rresp  (desc_rresp),  .m_axi_desc_rlast(desc_rlast),
        .m_axi_desc_ruser  (desc_ruser),  .m_axi_desc_rvalid(desc_rvalid),
        .m_axi_desc_rready (desc_rready),

        // Data read master
        .m_axi_rd_arid   (rd_arid),   .m_axi_rd_araddr(rd_araddr),
        .m_axi_rd_arlen  (rd_arlen),  .m_axi_rd_arsize(rd_arsize),
        .m_axi_rd_arburst(rd_arburst),.m_axi_rd_arlock(rd_arlock),
        .m_axi_rd_arcache(rd_arcache),.m_axi_rd_arprot(rd_arprot),
        .m_axi_rd_arqos  (rd_arqos),  .m_axi_rd_arregion(rd_arregion),
        .m_axi_rd_aruser (rd_aruser), .m_axi_rd_arvalid(rd_arvalid),
        .m_axi_rd_arready(rd_arready),
        .m_axi_rd_rid    (rd_rid),    .m_axi_rd_rdata(rd_rdata),
        .m_axi_rd_rresp  (rd_rresp),  .m_axi_rd_rlast(rd_rlast),
        .m_axi_rd_ruser  (rd_ruser),  .m_axi_rd_rvalid(rd_rvalid),
        .m_axi_rd_rready (rd_rready),

        // Data write master
        .m_axi_wr_awid   (wr_awid),   .m_axi_wr_awaddr(wr_awaddr),
        .m_axi_wr_awlen  (wr_awlen),  .m_axi_wr_awsize(wr_awsize),
        .m_axi_wr_awburst(wr_awburst),.m_axi_wr_awlock(wr_awlock),
        .m_axi_wr_awcache(wr_awcache),.m_axi_wr_awprot(wr_awprot),
        .m_axi_wr_awqos  (wr_awqos),  .m_axi_wr_awregion(wr_awregion),
        .m_axi_wr_awuser (wr_awuser), .m_axi_wr_awvalid(wr_awvalid),
        .m_axi_wr_awready(wr_awready),
        .m_axi_wr_wdata  (wr_wdata),  .m_axi_wr_wstrb(wr_wstrb),
        .m_axi_wr_wlast  (wr_wlast),  .m_axi_wr_wuser(wr_wuser),
        .m_axi_wr_wvalid (wr_wvalid), .m_axi_wr_wready(wr_wready),
        .m_axi_wr_bid    (wr_bid),    .m_axi_wr_bresp(wr_bresp),
        .m_axi_wr_buser  (wr_buser),  .m_axi_wr_bvalid(wr_bvalid),
        .m_axi_wr_bready (wr_bready),

        // Err FIFO AXIL slave (host reads via S3)
        .s_axil_err_arvalid(s3_err_arvalid),
        .s_axil_err_arready(s3_err_arready),
        .s_axil_err_araddr (s3_err_araddr),
        .s_axil_err_arprot (s3_err_arprot),
        .s_axil_err_rvalid (s3_err_rvalid),
        .s_axil_err_rready (s3_err_rready),
        .s_axil_err_rdata  (s3_err_rdata),
        .s_axil_err_rresp  (s3_err_rresp),

        // Monitor data AXIL master (writes to debug_sram)
        .m_axil_mon_awvalid(mon_awvalid),
        .m_axil_mon_awready(mon_awready),
        .m_axil_mon_awaddr (mon_awaddr),
        .m_axil_mon_awprot (mon_awprot),
        .m_axil_mon_wvalid (mon_wvalid),
        .m_axil_mon_wready (mon_wready),
        .m_axil_mon_wdata  (mon_wdata),
        .m_axil_mon_wstrb  (mon_wstrb),
        .m_axil_mon_bvalid (mon_bvalid),
        .m_axil_mon_bready (mon_bready),
        .m_axil_mon_bresp  (mon_bresp),

        // Interrupt out
        .stream_irq        (stream_irq),

        // Monitor capture region: point monbus_axil_group's master
        // writes at debug_sram (0x0004_0000, 256 KB). Each record is
        // 24 bytes (packet[63:0], packet[127:64], source_ts[63:0]);
        // the 256 KB window therefore holds 262144/24 ~= 10923
        // records before wrap.
        .cfg_mon_base_addr  (32'h0004_0000),
        .cfg_mon_limit_addr (32'h0004_0000 + 32'(DEBUG_SRAM_WORDS) * 32'h4 - 32'h1),

        // Debug outputs (unconnected at top level)
        .debug_hwif_scheduler_idle  (),
        .debug_hwif_desc_engine_idle(),
        .debug_hwif_channel_idle    (),
        .debug_regblk_req           (),
        .debug_regblk_req_is_wr     (),
        .debug_regblk_addr          (),
        .debug_regblk_rd_data       (),
        .debug_regblk_rd_ack        (),
        .debug_peakrdl_cmd_valid    (),
        .debug_peakrdl_cmd_paddr    (),
        .debug_peakrdl_rsp_valid    (),
        .debug_peakrdl_rsp_prdata   (),
        .debug_last_cpuif_addr      (),
        .debug_last_cpuif_rd_data   (),
        .debug_last_cpuif_rd_ack    (),
        .debug_apb_cmd_valid          (),
        .debug_apb_cmd_ready          (),
        .debug_apb_cmd_pwrite         (),
        .debug_apb_cmd_paddr          (),
        .debug_apb_rsp_valid          (),
        .debug_apb_rsp_ready          (),
        .debug_apb_rsp_prdata         (),
        .debug_apb_rd_cmd_seen        (),
        .debug_apb_rd_cmd_addr        (),
        .debug_apb_rsp_prdata_captured(),
        .debug_apb_rd_count           (),
        .debug_peakrdl_rd_count       (),
        .debug_regblk_rd_count        ()
    );

    // =========================================================================
    // Status outputs to top (→ LEDs)
    // =========================================================================
    assign o_stream_irq     = stream_irq;
    assign o_any_error      = any_error;
    assign o_trace_overflow = dbg_overflow;

    // Heartbeat (bit-26 of a free-running counter = ~1 Hz blink at 100 MHz)
    logic [26:0] r_hb;
    `ALWAYS_FF_RST(aclk, aresetn,
        if (`RST_ASSERTED(aresetn)) begin
            r_hb <= '0;
        end else begin
            r_hb <= r_hb + 27'd1;
        end
    )
    assign o_heartbeat = r_hb[26:23];

    // Characterization timer outputs to the board top for LED PASS/FAIL.
    assign o_timer_done = timer_done;
    assign o_timer_pass = timer_pass;

    // Prevent unused signal warnings
    /* verilator lint_off UNUSED */
    wire _unused_ok = &{1'b0,
        read_beat_count,
        csr_start_pulse, csr_soft_reset,
        1'b0};
    /* verilator lint_on UNUSED */

endmodule : stream_char_harness
