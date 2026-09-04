// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: 2025 sean galloway
//
// Module: stream_harness
// Purpose: Internal integration for the STREAM characterization harness.
//
// Instantiates:
//   - uart_axil_bridge                (host interface)
//   - bridge_stream_char_axil         (1->6 generated bridge w/ APB+AXIL slaves;
//                                      handles every port natively — no
//                                      external converter glue needed)
//   - harness_csr                     (control/status)
//   - desc_ram                        (descriptor storage)
//   - stream_tally / slave_tally      (observer monbus records, counted)
//   - comp_sram                       (STREAM monbus capture, host download)
//   - axi4_slave_rd_pattern_gen       (DMA source)
//   - axi4_slave_wr_crc_check         (DMA sink)
//   - stream_top_ch8                  (DUT: STREAM DMA)
//
// The top level (stream_char_top.sv) wraps this with FPGA pin-level I/O.

`timescale 1ns / 1ps

`include "reset_defs.svh"

// Every geometry default below comes from stream_char_cfg_pkg -- ONE source,
// shared with stream_genesys2_top. Do not write a literal here: a literal is
// how sim and board drifted apart (build-perf characterized AR/AW=16 against a
// board built at 2). Override at the instantiation if a test needs to deviate,
// and say why there.
module stream_harness #(
    parameter int FPGA_CLK_HZ  = 100_000_000,
    parameter int UART_BAUD    = 115_200,
    parameter int DATA_WIDTH   = stream_char_cfg_pkg::CFG_DATA_WIDTH,
    parameter int ADDR_WIDTH   = stream_char_cfg_pkg::CFG_ADDR_WIDTH,
    // TASK-101 STREAM Extended addressing
    parameter int USE_ROW_COL_MAJOR_ADDRESSING =
                      stream_char_cfg_pkg::CFG_USE_ROW_COL_MAJOR_ADDRESSING,
    // ---- Observer transaction-table sizing (Vivado generics) --------------
    // OBS_MAX_TRANSACTIONS is the TOTAL slots per tap; the CAM is generated
    // OBS_NUM_BANKS times at OBS_MAX_TRANSACTIONS/OBS_NUM_BANKS each, because
    // timing scales with the depth of ONE cam, not the total (16 deep measured
    // at WNS +1.018 ns, 40 deep at -25.183 ns -- so 64 as one flat CAM will
    // not close, while 64 as 4x16 is four CAMs at a depth that does).
    // Banking is by ID, so per-ID concurrency is capped by the BANK depth:
    //     OBS_MAX_TRANSACTIONS/OBS_NUM_BANKS >= IDs-per-bank * outstanding-per-ID
    // 8 channels x 8 outstanding over 4 banks => 64/4 = 16 per bank.
    parameter int OBS_MAX_TRANSACTIONS   = stream_char_cfg_pkg::CFG_OBS_MAX_TRANSACTIONS,
    parameter int OBS_NUM_BANKS          = stream_char_cfg_pkg::CFG_OBS_NUM_BANKS,
    // Mandatory once a WRITE monitor is banked: the WID-less select is not
    // ID-matched, and trans_mgr refuses to elaborate without this.
    parameter bit OBS_USE_WDATA_ORDER_Q  = stream_char_cfg_pkg::CFG_OBS_USE_WDATA_ORDER_Q,
    // Heavy in-core AXI monitors (CAM/reporter cones + latency histograms).
    // Default 0 = board build (area): the always-on bus meters still give
    // utilisation. Cosim monitor-validation tests (rw_perf hist tail, obs_equiv,
    // desc_perf) override to 1 to exercise the full monitor suite.
    parameter int USE_AXI_MONITORS = stream_char_cfg_pkg::CFG_USE_AXI_MONITORS,
    // In-core AR/AW monitor CAM banking. From the package: ONE build, monitors
    // on, CAMs banked. See CFG_MON_NUM_BANKS for the depth arithmetic.
    parameter int MON_NUM_BANKS    = stream_char_cfg_pkg::CFG_MON_NUM_BANKS,
    // Observer monitor TAPS -- deliberately NOT the same decision as
    // USE_AXI_MONITORS. That knob builds the in-core rd/wr datapath monitors
    // inside stream_core; this one arms the per-transaction CAM inside the
    // two interface OBSERVERS, and the two were welded together.
    //
    // A measurement build wants them apart. The bus meters and latency
    // histograms live OUTSIDE this gate and keep counting either way, so every
    // number this harness characterizes with is unaffected. What the tap adds
    // is error/timeout/completion attribution. The PERF build does not consume
    // it, so there the reporter cones stay compiled out. The MONITOR build
    // does: this parameter now drives TAP_ENABLE_ERROR/TIMEOUT/COMPL_LOGIC at
    // both observers as well, because arming the CAM alone is not enough --
    // with the cones out, an observer tracks transactions and emits nothing.
    // (cfg_perf_enable is tied low inside the observer either way, so the perf
    // cone it builds by default is inert; error/timeout/compl have their
    // runtime cfg_*_enable tied HIGH, so building the cone is what turns them
    // on.)
    //
    // It is not free to leave armed. An enabled tap gates the DMA's ready
    //     ready = core_ready & (block_ready | ~cfg_monitor_enable)
    // so it back-pressures at MAX_TRANSACTIONS: the instrument becomes the
    // bottleneck and reports its own limit as the engine's throughput.
    //
    // Default 0 = measurement-only. Set 1 when the error/completion monbus
    // stream is genuinely wanted, and size OBS_MAX_TRANSACTIONS for the real
    // concurrency if you do.
    // Observer monitor taps: ON for the monitor flavour, OFF for perf.
    //
    // The instantiation comment below has always SAID this was "tied to the
    // build flavor, NOT hardcoded" -- it was not. The parameter was a literal
    // 1'b0 that nothing overrode, so BOTH observers were built with their
    // monitor taps off in every flavour, and the observer-hosted master/slave
    // monitors could not emit an error, completion, timeout or threshold packet
    // at all. Only the bus meters and latency histograms (which sit outside the
    // tap gate) ever counted.
    //
    // Deriving it from USE_AXI_MONITORS makes the code do what the comment
    // claims: build-perf (USE_AXI_MONITORS=0) keeps taps off -- no command-
    // channel gate, no CAM on the critical path, which is exactly what a perf
    // build wants and leaves that flavour bit-identical. build-mon
    // (USE_AXI_MONITORS=1) turns them on so the monitors are testable.
    //
    // Sizing is already correct for taps-on: CFG_OBS_MAX_TRANSACTIONS=64 is
    // NUM_CHANNELS(8) x OBS_MAX_OUTSTANDING(8), banked CFG_OBS_NUM_BANKS=4 ways
    // = 16 deep, the depth measured at WNS +1.018 ns. The "72 will not close"
    // note below is about a FLAT cam, not this banked one.
    // NOT derived from USE_AXI_MONITORS: the observers are the measurement
    // vehicle and must stay armed when the in-core monitors are removed
    // for area. See CFG_OBS_ENABLE_MON_TAPS in stream_cfg_pkg.sv.
    parameter bit OBS_ENABLE_MON_TAPS = stream_char_cfg_pkg::CFG_OBS_ENABLE_MON_TAPS,
    parameter int SRAM_DEPTH   = stream_char_cfg_pkg::CFG_SRAM_DEPTH,
    // NUM_CHANNELS is overridable so the FPGA target can build a 4-channel
    // configuration to fit the Artix-7 100T without changing the DUT's native
    // DATA_WIDTH. Valid values: any power of 2 that the DUT supports (1/2/4/8).
    parameter int NUM_CHANNELS = stream_char_cfg_pkg::CFG_NUM_CHANNELS,

    // Harness-side memory sizing. These used to default to a "big ASIC
    // simulation target" (2048 / 65536) that no build ever used, so every
    // cosim which did not override them ran 8x the descriptor RAM and 16x the
    // trace depth of the board -- invisibly, because the divergence lived in a
    // default rather than at a call site. Now they come from the package, i.e.
    // from silicon. A test that genuinely needs a longer capture overrides at
    // its own instantiation and says so.
    parameter int DESC_RAM_ENTRIES = stream_char_cfg_pkg::CFG_DESC_RAM_ENTRIES,
    parameter int DEBUG_SRAM_WORDS = stream_char_cfg_pkg::CFG_DEBUG_SRAM_WORDS,

    // axi_response_delay pipeline depths (in beats). Each delay block
    // models a real memory controller: every beat dwells exactly L cycles
    // (set by csr_*_resp_delay_cyc) but multiple beats are in flight in
    // parallel up to CAPACITY. Sized to absorb the engines' worst-case
    // outstanding count without back-pressuring the slave:
    //   R channel — AR_MAX_OUTSTANDING × max burst length (16)
    //   B channel — AW_MAX_OUTSTANDING (one BRESP per AW)
    // Override these at the top level if you change the engines' AR/AW
    // outstanding parameters or push to longer bursts.
    parameter int RESP_DELAY_R_CAPACITY = stream_char_cfg_pkg::CFG_RESP_DELAY_R_CAPACITY,
    parameter int RESP_DELAY_B_CAPACITY = stream_char_cfg_pkg::CFG_RESP_DELAY_B_CAPACITY,

    // STREAM engine outstanding queue (side-Q) depths. These are the
    // values stream_core uses to size its AR/AW reorder/outstanding-
    // tracking queues — the levers for measuring how much memory latency
    // the engines can hide. Defaults match stream_core's historical
    // values so this parameter is invisible unless overridden.
    parameter int AR_MAX_OUTSTANDING     = stream_char_cfg_pkg::CFG_AR_MAX_OUTSTANDING,
    parameter int AW_MAX_OUTSTANDING     = stream_char_cfg_pkg::CFG_AW_MAX_OUTSTANDING,
    // MonBus bulk-trace compression. 1 for this project -- whenever the
    // monitors run, the compressor is in-path. The cocotb characterization
    // test overrides this to 0 to measure the uncompressed baseline.
    parameter int USE_MON_COMPRESSION    = stream_char_cfg_pkg::CFG_USE_MON_COMPRESSION,
    // Half-beat packing on the compressed bulk-trace path: two 30-bit slots
    // per 64-bit beat (~80% reduction vs the 66.7% one-slot ceiling). Only
    // meaningful with USE_MON_COMPRESSION=1 and runtime cfg_compress_en.
    parameter int USE_MON_HALFBEAT       = stream_char_cfg_pkg::CFG_USE_MON_HALFBEAT,
    // 0 = omit the per-channel completion/error MonBus emitters (descriptor_
    // engine/scheduler) for FPGA area. stream_char_top sets this 0 on the board
    // build; cosim leaves it 1 so the compression-trace tests keep working.
    parameter bit GEN_MON                = stream_char_cfg_pkg::CFG_GEN_MON,
    // Agent-resolved tally legal-set size, for BOTH tally memories. The host
    // loads the legal set over each tally's cfg AXIL slave and bins become
    // dense per-agent indices, plus an UNEXPECTED bin at index MON_N_PROFILE.
    // (The CAM is unconditional -- there is no direct-mapped mode to select.)
    parameter int MON_N_PROFILE          = stream_char_cfg_pkg::CFG_MON_N_PROFILE,
    // Monitor-validation DATAPATH-monitor cone selection:
    //   0 (default) = "all except error" -> completion/timeout/threshold/perf/debug
    //                 (+ AddrMatch). The error cone is compiled OUT for timing.
    //   1           = "error flavor" -> ONLY the error cone is compiled in; the
    //                 other reporter cones are compiled OUT so the low-priority
    //                 addr_check ADDR_RANGE (allowlist-miss) error stream is not
    //                 starved and meets timing. Two bitstreams cover all classes.
    //                 Mode 2 is the UNION of both cone sets: one bitstream that
    //                 can emit every packet class, so a validation campaign no
    //                 longer has to re-flash between phases or compare results
    //                 across two different builds. It costs both cone sets'
    //                 area and timing at once -- affordable at the 90 MHz
    //                 harness clock, not at 100 MHz.
    parameter int DATA_MON_CONE_MODE     = 2
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
    // 13 bits (8 KB) to match stream_top_ch8's default: STREAM's monitor CSR
    // block was relocated to 0x1000+ (RDMON/WRMON perf @ 0x1180/0x11B0). A
    // 12-bit (4 KB) window truncated those addresses -> perf CSRs unreachable
    // (rw_perf / ext_char read zero). The bridge stream_apb page was widened to
    // 8 KB to match (configs/bridge_stream_char_axil.toml, regenerated).
    localparam int APB_ADDR_WIDTH = 13;
    localparam int APB_DATA_WIDTH = 32;

    localparam int CLKS_PER_BIT = FPGA_CLK_HZ / UART_BAUD;

    // Observer monitor-timer LUT frequency. Derived from the clock rather than
    // set independently: counter_freq_invariant divides BY this for its 1 us
    // tick, so a value that drifts from aclk skews every monitor timeout by
    // the ratio, silently and uniformly.
    localparam int OBS_ACLK_MHZ = FPGA_CLK_HZ / 1_000_000;

    // Datapath-monitor cone predicates. Mode 2 (union) asserts BOTH, which is
    // what makes one bitstream able to emit every packet class.
    localparam bit w_data_mon_error_cone = (DATA_MON_CONE_MODE != 0);
    localparam bit w_data_mon_main_cones = (DATA_MON_CONE_MODE != 1);

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
    //   stream_tally   0x0004_0000  256 KB  AXIL   master-observer records
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
    // host master is AXIL — the AXI4 extras (id/buser/rid/ruser/rlast)
    // that used to be tied off here are now handled inside the bridge
    // generator (master.protocol="axil" emits AXIL-only top ports).

    // STREAM m_axil_mon master signals (declared early so the bridge
    // instance port-map at the next section can reach them; stream_top_ch8
    // drives them from its monbus_axil_group output further down).
    logic        mon_awvalid, mon_awready;
    logic [31:0] mon_awaddr;
    logic [2:0]  mon_awprot;
    logic        mon_wvalid,  mon_wready;
    logic [63:0] mon_wdata;
    logic [7:0]  mon_wstrb;
    logic        mon_bvalid,  mon_bready;
    logic [1:0]  mon_bresp;

    // STREAM m_axi_desc master signals (declared early so the bridge's
    // stream_desc_* master port-map can reach them; stream_top_ch8 drives
    // them as a 256-bit AXI4 master further down).
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
    // Bridge drives a single ruser bit; zero-extend to the harness net width.
    logic                       w_desc_ruser_b0;
    assign desc_ruser = AXI_USER_WIDTH'(w_desc_ruser_b0);
    logic                       desc_rvalid, desc_rready;

    // ---- Slave-side AXIL wires consumed by the rest of the harness ---------
    // (s1_* harness_csr, s2_* desc_ram, s3_* stream_err, s4_* stream_tally)
    logic [31:0] s1_awaddr, s1_wdata, s1_araddr, s1_rdata;
    logic [3:0]  s1_wstrb;
    logic [2:0]  s1_awprot, s1_arprot;
    logic [1:0]  s1_bresp, s1_rresp;
    logic s1_awvalid, s1_awready, s1_wvalid, s1_wready, s1_bvalid, s1_bready;
    logic s1_arvalid, s1_arready, s1_rvalid, s1_rready;

    // Slave 2 (desc_ram): 256-bit AXI4 end-to-end. Host's 32-bit AXIL
    // writes go through the bridge's axil_to_axi4_wide_align_wr (master
    // adapter) and land here as single-beat 256b AXI4 writes positioned
    // by awaddr's low bits. STREAM's 256b AXI4 reads pass through with
    // zero conversion. The previous axi4_to_axil4_rd/wr converters at
    // the bridge slave adapter are GONE — desc_ram is now AXI4 native.
    logic [7:0]   s2_awid,    s2_arid,    s2_bid,     s2_rid;
    logic [31:0]  s2_awaddr,  s2_araddr;
    logic [7:0]   s2_awlen,   s2_arlen;
    logic [2:0]   s2_awsize,  s2_arsize;
    logic [1:0]   s2_awburst, s2_arburst;
    logic         s2_awlock,  s2_arlock;
    logic [3:0]   s2_awcache, s2_arcache;
    logic [2:0]   s2_awprot,  s2_arprot;
    logic [3:0]   s2_awqos,   s2_arqos;
    logic [3:0]   s2_awregion,s2_arregion;
    logic         s2_awuser,  s2_aruser;
    logic [255:0] s2_wdata,   s2_rdata;
    logic [31:0]  s2_wstrb;
    logic         s2_wlast,   s2_rlast;
    logic         s2_wuser,   s2_ruser,   s2_buser;
    logic [1:0]   s2_bresp,   s2_rresp;
    logic s2_awvalid, s2_awready, s2_wvalid, s2_wready, s2_bvalid, s2_bready;
    logic s2_arvalid, s2_arready, s2_rvalid, s2_rready;

    logic [31:0] s3_awaddr, s3_wdata, s3_araddr, s3_rdata;
    logic [3:0]  s3_wstrb;
    logic [2:0]  s3_awprot, s3_arprot;
    logic [1:0]  s3_bresp, s3_rresp;
    logic s3_awvalid, s3_awready, s3_wvalid, s3_wready, s3_bvalid, s3_bready;
    logic s3_arvalid, s3_arready, s3_rvalid, s3_rready;

    // Slave 4 (stream_tally): 64-bit AXIL. Records no longer arrive here --
    // the master observer drives the tally's rec_* port directly -- so this
    // is the host's count-READ path; host reads go through the 32->64 upsize.
    logic [31:0] s4_awaddr, s4_araddr;
    logic [63:0] s4_wdata, s4_rdata;
    logic [7:0]  s4_wstrb;
    logic [2:0]  s4_awprot, s4_arprot;
    logic [1:0]  s4_bresp, s4_rresp;
    logic s4_awvalid, s4_awready, s4_wvalid, s4_wready, s4_bvalid, s4_bready;
    logic s4_arvalid, s4_arready, s4_rvalid, s4_rready;

    // Dedicated host cfg/readback ports for the two tally memories
    // (stream_tally_cfg @0xA0000 -> sc0, slave_tally_cfg @0xB0000 -> sc1).
    logic [31:0] sc0_awaddr, sc0_araddr; logic [63:0] sc0_wdata, sc0_rdata;
    logic [7:0]  sc0_wstrb; logic [2:0] sc0_awprot, sc0_arprot; logic [1:0] sc0_bresp, sc0_rresp;
    logic sc0_awvalid, sc0_awready, sc0_wvalid, sc0_wready, sc0_bvalid, sc0_bready;
    logic sc0_arvalid, sc0_arready, sc0_rvalid, sc0_rready;
    logic [31:0] sc1_awaddr, sc1_araddr; logic [63:0] sc1_wdata, sc1_rdata;
    logic [7:0]  sc1_wstrb; logic [2:0] sc1_awprot, sc1_arprot; logic [1:0] sc1_bresp, sc1_rresp;
    logic sc1_awvalid, sc1_awready, sc1_wvalid, sc1_wready, sc1_bvalid, sc1_bready;
    logic sc1_arvalid, sc1_arready, sc1_rvalid, sc1_rready;

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

    // ---- Interconnect wires for the new mon-bridge ports -------------------
    // Slave observer monbus group -> u_slave_tally.rec_* (DIRECT, no bridge).
    logic [31:0] slmon_awaddr; logic [2:0] slmon_awprot;
    logic        slmon_awvalid, slmon_awready;
    logic [63:0] slmon_wdata;  logic [7:0] slmon_wstrb;
    logic        slmon_wvalid, slmon_wready;
    logic [1:0]  slmon_bresp;  logic slmon_bvalid, slmon_bready;

    // Master observer monbus group -> u_stream_tally.rec_* (DIRECT, no bridge).
    logic [31:0] dmamon_awaddr; logic [2:0] dmamon_awprot;
    logic        dmamon_awvalid, dmamon_awready;
    logic [63:0] dmamon_wdata;  logic [7:0] dmamon_wstrb;
    logic        dmamon_wvalid, dmamon_wready;
    logic [1:0]  dmamon_bresp;  logic dmamon_bvalid, dmamon_bready;
    // slave_err slave (read side) -> u_slave_observer.s_axil_* (32-bit AXIL rd)
    logic [31:0] se_araddr; logic [2:0] se_arprot;
    logic        se_arvalid, se_arready;
    logic [31:0] se_rdata;  logic [1:0] se_rresp;
    logic        se_rvalid, se_rready;
    // slave_tally slave <-> u_slave_tally.s_axil_* (64-bit AXIL rd/wr)
    logic [31:0] s6_awaddr; logic [2:0] s6_awprot; logic s6_awvalid, s6_awready;
    logic [63:0] s6_wdata;  logic [7:0] s6_wstrb;  logic s6_wvalid, s6_wready;
    logic [1:0]  s6_bresp;  logic s6_bvalid, s6_bready;
    logic [31:0] s6_araddr; logic [2:0] s6_arprot; logic s6_arvalid, s6_arready;
    logic [63:0] s6_rdata;  logic [1:0] s6_rresp;  logic s6_rvalid, s6_rready;

    // comp_sram: a REAL memory (sdpram_slave_axil_axil), not a tally. The tally
    // reassembles RAW 3-beat records and cannot consume the compressed monbus
    // stream, so with compression enabled there was nowhere for the traffic to
    // land. Writes here are ordinary memory writes: the host reads the bytes
    // back and diffs them against the bit-exact Python golden
    // (bin/TBClasses/monbus/monbus_compressor.py), which verifies the format on
    // silicon with no RTL decoder in the loop.
    logic [31:0] cs_awaddr; logic [2:0] cs_awprot; logic cs_awvalid, cs_awready;
    logic [63:0] cs_wdata;  logic [7:0] cs_wstrb;  logic cs_wvalid, cs_wready;
    logic [1:0]  cs_bresp;  logic cs_bvalid, cs_bready;
    logic [31:0] cs_araddr; logic [2:0] cs_arprot; logic cs_arvalid, cs_arready;
    logic [63:0] cs_rdata;  logic [1:0] cs_rresp;  logic cs_rvalid, cs_rready;

    // ---- Bridge instance ---------------------------------------------------
    // ---- Observer / slave-monitor config APB nets ---------------------------
    // DECLARED HERE, BEFORE THE BRIDGE INSTANTIATION BELOW USES THEM.
    //
    // These sat ~790 lines further down, after their first use in the bridge
    // port map. An undeclared identifier in a port connection is IMPLICITLY a
    // 1-BIT WIRE, so Vivado created 1-bit obs_apb_PADDR / PWDATA (32-bit),
    // PSTRB (4-bit) and PPROT (3-bit), then warned that the real declaration
    // was "already implicitly declared" -- Synth 8-8895, twenty of them.
    //
    // Effect on silicon: the observer's and slave monitors' APB carried one bit
    // of address and one bit of data, so their register blocks could not be
    // configured at all -- while the cosim passed, because Verilator resolves
    // the later declaration instead of truncating.
    //
    // Keep declarations ahead of first use in this file. `default_nettype none`
    // would make the whole class fatal; see [[STREAM-NETTYPE]].
    // Observer config APB (bridge obs_apb -> axi4_intf_master_observer).
    logic        obs_apb_PSEL, obs_apb_PENABLE, obs_apb_PWRITE;
    logic        obs_apb_PREADY, obs_apb_PSLVERR;
    logic [31:0] obs_apb_PADDR, obs_apb_PWDATA, obs_apb_PRDATA;
    logic [3:0]  obs_apb_PSTRB;
    logic [2:0]  obs_apb_PPROT;

    // Slave-observer config APB (bridge slvmon_apb @ 0x180000 -> u_slave_observer).
    logic        slvmon_apb_PSEL, slvmon_apb_PENABLE, slvmon_apb_PWRITE;
    logic        slvmon_apb_PREADY, slvmon_apb_PSLVERR;
    logic [31:0] slvmon_apb_PADDR, slvmon_apb_PWDATA, slvmon_apb_PRDATA;
    logic [3:0]  slvmon_apb_PSTRB;
    logic [2:0]  slvmon_apb_PPROT;

    bridge_stream_mon_axil u_bridge (
        .aclk    (aclk),
        .aresetn (aresetn),

        // Master 0: host — AXI4-Lite. Bridge top exposes only AXIL
        // signals (generator branches on master.protocol="axil").
        .host_axi_awaddr   (uart_awaddr),
        .host_axi_awprot   (uart_awprot),
        .host_axi_awvalid  (uart_awvalid),
        .host_axi_awready  (uart_awready),
        .host_axi_wdata    (uart_wdata),
        .host_axi_wstrb    (uart_wstrb),
        .host_axi_wvalid   (uart_wvalid),
        .host_axi_wready   (uart_wready),
        .host_axi_bresp    (uart_bresp),
        .host_axi_bvalid   (uart_bvalid),
        .host_axi_bready   (uart_bready),
        .host_axi_araddr   (uart_araddr),
        .host_axi_arprot   (uart_arprot),
        .host_axi_arvalid  (uart_arvalid),
        .host_axi_arready  (uart_arready),
        .host_axi_rdata    (uart_rdata),
        .host_axi_rresp    (uart_rresp),
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

        // Slave 2: desc_ram (native AXI4 256-bit — wired directly to s2_*)
        .desc_ram_axi_awid     (s2_awid),
        .desc_ram_axi_awaddr   (s2_awaddr),
        .desc_ram_axi_awlen    (s2_awlen),
        .desc_ram_axi_awsize   (s2_awsize),
        .desc_ram_axi_awburst  (s2_awburst),
        .desc_ram_axi_awlock   (s2_awlock),
        .desc_ram_axi_awcache  (s2_awcache),
        .desc_ram_axi_awprot   (s2_awprot),
        .desc_ram_axi_awqos    (s2_awqos),
        .desc_ram_axi_awregion (s2_awregion),
        .desc_ram_axi_awuser   (s2_awuser),
        .desc_ram_axi_awvalid  (s2_awvalid),
        .desc_ram_axi_awready  (s2_awready),
        .desc_ram_axi_wdata    (s2_wdata),
        .desc_ram_axi_wstrb    (s2_wstrb),
        .desc_ram_axi_wlast    (s2_wlast),
        .desc_ram_axi_wuser    (s2_wuser),
        .desc_ram_axi_wvalid   (s2_wvalid),
        .desc_ram_axi_wready   (s2_wready),
        .desc_ram_axi_bid      (s2_bid),
        .desc_ram_axi_bresp    (s2_bresp),
        .desc_ram_axi_buser    (s2_buser),
        .desc_ram_axi_bvalid   (s2_bvalid),
        .desc_ram_axi_bready   (s2_bready),
        .desc_ram_axi_arid     (s2_arid),
        .desc_ram_axi_araddr   (s2_araddr),
        .desc_ram_axi_arlen    (s2_arlen),
        .desc_ram_axi_arsize   (s2_arsize),
        .desc_ram_axi_arburst  (s2_arburst),
        .desc_ram_axi_arlock   (s2_arlock),
        .desc_ram_axi_arcache  (s2_arcache),
        .desc_ram_axi_arprot   (s2_arprot),
        .desc_ram_axi_arqos    (s2_arqos),
        .desc_ram_axi_arregion (s2_arregion),
        .desc_ram_axi_aruser   (s2_aruser),
        .desc_ram_axi_arvalid  (s2_arvalid),
        .desc_ram_axi_arready  (s2_arready),
        .desc_ram_axi_rid      (s2_rid),
        .desc_ram_axi_rdata    (s2_rdata),
        .desc_ram_axi_rresp    (s2_rresp),
        .desc_ram_axi_rlast    (s2_rlast),
        .desc_ram_axi_ruser    (s2_ruser),
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

        // Slave 4: stream_tally (native AXIL — wired directly to s4_*)
        .stream_tally_axi_awaddr   (s4_awaddr),
        .stream_tally_axi_awprot   (s4_awprot),
        .stream_tally_axi_awvalid  (s4_awvalid),
        .stream_tally_axi_awready  (s4_awready),
        .stream_tally_axi_wdata    (s4_wdata),
        .stream_tally_axi_wstrb    (s4_wstrb),
        .stream_tally_axi_wvalid   (s4_wvalid),
        .stream_tally_axi_wready   (s4_wready),
        .stream_tally_axi_bresp    (s4_bresp),
        .stream_tally_axi_bvalid   (s4_bvalid),
        .stream_tally_axi_bready   (s4_bready),
        .stream_tally_axi_araddr   (s4_araddr),
        .stream_tally_axi_arprot   (s4_arprot),
        .stream_tally_axi_arvalid  (s4_arvalid),
        .stream_tally_axi_arready  (s4_arready),
        .stream_tally_axi_rdata    (s4_rdata),
        .stream_tally_axi_rresp    (s4_rresp),
        .stream_tally_axi_rvalid   (s4_rvalid),
        .stream_tally_axi_rready   (s4_rready),

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
        .dma_axil_rready   (),

        // Master 1: stream_desc — STREAM's m_axi_desc, 256-bit AXI4, read-only.
        //
        // No write-channel connections: the bridge no longer HAS them. The
        // config said channels="r", which the generator silently downgraded to
        // "rw" until the validator was tightened -- so every earlier bridge
        // carried a dead AW/W/B path that this harness tied off by name. With
        // channels="rd" the ports are gone and the tie-offs went with them
        // (24 pins here, 8 on monbus_wr for the mirror
        // case). Config and RTL now agree on what this master is.
        
        
        
        
        
        
        
        
        
        
        
        
        
        
        
        
        
        
        
        
        
        
        
        

        // Bridge stream_desc port is now 8-bit AXI_ID_WIDTH end-to-end
        // (matches STREAM's m_axi_desc natively — no truncation, no
        // zero-extend). This eliminates a class of id-aliasing wedges
        // on the shared 7-channel desc bus.
        .stream_desc_arid     (desc_arid),
        .stream_desc_araddr   (desc_araddr),
        .stream_desc_arlen    (desc_arlen),
        .stream_desc_arsize   (desc_arsize),
        .stream_desc_arburst  (desc_arburst),
        .stream_desc_arlock   (desc_arlock),
        .stream_desc_arcache  (desc_arcache),
        .stream_desc_arprot   (desc_arprot),
        .stream_desc_arqos    (desc_arqos),
        .stream_desc_arregion (desc_arregion),
        // The bridge carries ONE user bit on this port while the harness net is
        // AXI_USER_WIDTH ($clog2(NUM_CHANNELS)). STREAM never drives desc aruser
        // (m_axi_desc_aruser is an unassigned output of stream_core), so nothing
        // is lost -- but narrow explicitly rather than by implicit truncation.
        .stream_desc_aruser   (desc_aruser[0]),
        .stream_desc_arvalid  (desc_arvalid),
        .stream_desc_arready  (desc_arready),

        .stream_desc_rid      (desc_rid),
        .stream_desc_rdata    (desc_rdata),
        .stream_desc_rresp    (desc_rresp),
        .stream_desc_rlast    (desc_rlast),
        .stream_desc_ruser    (w_desc_ruser_b0),
        .stream_desc_rvalid   (desc_rvalid),
        .stream_desc_rready   (desc_rready),

        // Master 2: monbus_wr — STREAM's m_axil_mon, 64-bit AXIL.
        // Bridge top exposes only AXIL signals (generator branches on
        // master.protocol="axil" — see _generate_master_ports).
        .monbus_wr_awaddr     (mon_awaddr),
        .monbus_wr_awprot     (mon_awprot),
        .monbus_wr_awvalid    (mon_awvalid),
        .monbus_wr_awready    (mon_awready),
        .monbus_wr_wdata      (mon_wdata),
        .monbus_wr_wstrb      (mon_wstrb),
        .monbus_wr_wvalid     (mon_wvalid),
        .monbus_wr_wready     (mon_wready),
        .monbus_wr_bresp      (mon_bresp),
        .monbus_wr_bvalid     (mon_bvalid),
        .monbus_wr_bready     (mon_bready),
        // Master 3: slave_monbus_wr — UNUSED in this design.
        // The slave observer now drives u_slave_tally.rec_* DIRECTLY, so no
        // record traffic rides the bridge on this port any more. The master is
        // kept in the bridge on purpose: there is ONE bridge for all three
        // build flavours (perf/obs/mon) and respinning it to drop a master
        // rewrites the xbar arbitration under stream_desc, the descriptor
        // fetch path. Tie the request side off instead; an always-idle master
        // costs nothing and the arbiter never grants it.
        .slave_monbus_wr_awaddr  (32'h0),
        .slave_monbus_wr_awprot  (3'h0),
        .slave_monbus_wr_awvalid (1'b0),
        .slave_monbus_wr_awready (),
        .slave_monbus_wr_wdata   (64'h0),
        .slave_monbus_wr_wstrb   (8'h0),
        .slave_monbus_wr_wvalid  (1'b0),
        .slave_monbus_wr_wready  (),
        .slave_monbus_wr_bresp   (),
        .slave_monbus_wr_bvalid  (),
        .slave_monbus_wr_bready  (1'b1),

        // Slave 6: slave_err — dma_slave_monitors' s_axil_* err/IRQ read.
        // Read side -> the group's s_axil; write side tied (err FIFO not writable).
        .slave_err_axi_awaddr  (), .slave_err_axi_awprot  (),
        .slave_err_axi_awvalid (), .slave_err_axi_awready (1'b1),
        .slave_err_axi_wdata   (), .slave_err_axi_wstrb   (),
        .slave_err_axi_wvalid  (), .slave_err_axi_wready  (1'b1),
        .slave_err_axi_bresp   (2'b00), .slave_err_axi_bvalid (1'b0), .slave_err_axi_bready (),
        .slave_err_axi_araddr  (se_araddr),  .slave_err_axi_arprot  (se_arprot),
        .slave_err_axi_arvalid (se_arvalid), .slave_err_axi_arready (se_arready),
        .slave_err_axi_rdata   (se_rdata),   .slave_err_axi_rresp   (se_rresp),
        .slave_err_axi_rvalid  (se_rvalid),  .slave_err_axi_rready  (se_rready),


        // Slave 11: obs_apb — the observer's own config regblock.
        .obs_apb_PSEL   (obs_apb_PSEL),    .obs_apb_PADDR  (obs_apb_PADDR),
        .obs_apb_PENABLE(obs_apb_PENABLE), .obs_apb_PWRITE (obs_apb_PWRITE),
        .obs_apb_PWDATA (obs_apb_PWDATA),  .obs_apb_PSTRB  (obs_apb_PSTRB),
        .obs_apb_PPROT  (obs_apb_PPROT),   .obs_apb_PRDATA (obs_apb_PRDATA),
        .obs_apb_PREADY (obs_apb_PREADY),  .obs_apb_PSLVERR(obs_apb_PSLVERR),

        // Slave 10: slvmon_apb — dma_slave_monitors' own config regblock.
        .slvmon_apb_PSEL   (slvmon_apb_PSEL),    .slvmon_apb_PADDR  (slvmon_apb_PADDR),
        .slvmon_apb_PENABLE(slvmon_apb_PENABLE), .slvmon_apb_PWRITE (slvmon_apb_PWRITE),
        .slvmon_apb_PWDATA (slvmon_apb_PWDATA),  .slvmon_apb_PSTRB  (slvmon_apb_PSTRB),
        .slvmon_apb_PPROT  (slvmon_apb_PPROT),   .slvmon_apb_PRDATA (slvmon_apb_PRDATA),
        .slvmon_apb_PREADY (slvmon_apb_PREADY),  .slvmon_apb_PSLVERR(slvmon_apb_PSLVERR),

        // Slave 7: slave_tally — the slave-side tally SRAM (monbus_tally_axil, 64-bit).
        .slave_tally_axi_awaddr  (s6_awaddr),  .slave_tally_axi_awprot  (s6_awprot),
        .slave_tally_axi_awvalid (s6_awvalid), .slave_tally_axi_awready (s6_awready),
        .slave_tally_axi_wdata   (s6_wdata),   .slave_tally_axi_wstrb   (s6_wstrb),
        .slave_tally_axi_wvalid  (s6_wvalid),  .slave_tally_axi_wready  (s6_wready),
        .slave_tally_axi_bresp   (s6_bresp),   .slave_tally_axi_bvalid  (s6_bvalid),
        .slave_tally_axi_bready  (s6_bready),
        .slave_tally_axi_araddr  (s6_araddr),  .slave_tally_axi_arprot  (s6_arprot),
        .slave_tally_axi_arvalid (s6_arvalid), .slave_tally_axi_arready (s6_arready),
        .slave_tally_axi_rdata   (s6_rdata),   .slave_tally_axi_rresp   (s6_rresp),
        .slave_tally_axi_rvalid  (s6_rvalid),  .slave_tally_axi_rready  (s6_rready),

        // Slave 10: comp_sram — compression capture memory.
        .comp_sram_axi_awaddr  (cs_awaddr),  .comp_sram_axi_awprot  (cs_awprot),
        .comp_sram_axi_awvalid (cs_awvalid), .comp_sram_axi_awready (cs_awready),
        .comp_sram_axi_wdata   (cs_wdata),   .comp_sram_axi_wstrb   (cs_wstrb),
        .comp_sram_axi_wvalid  (cs_wvalid),  .comp_sram_axi_wready  (cs_wready),
        .comp_sram_axi_bresp   (cs_bresp),   .comp_sram_axi_bvalid  (cs_bvalid),
        .comp_sram_axi_bready  (cs_bready),
        .comp_sram_axi_araddr  (cs_araddr),  .comp_sram_axi_arprot  (cs_arprot),
        .comp_sram_axi_arvalid (cs_arvalid), .comp_sram_axi_arready (cs_arready),
        .comp_sram_axi_rdata   (cs_rdata),   .comp_sram_axi_rresp   (cs_rresp),
        .comp_sram_axi_rvalid  (cs_rvalid),  .comp_sram_axi_rready  (cs_rready),

        // Dedicated host cfg/readback ports (AXIL subset; AXI4 extras open).
        .stream_tally_cfg_axi_awaddr (sc0_awaddr), .stream_tally_cfg_axi_awprot (sc0_awprot),
        .stream_tally_cfg_axi_awvalid(sc0_awvalid),.stream_tally_cfg_axi_awready(sc0_awready),
        .stream_tally_cfg_axi_wdata  (sc0_wdata),  .stream_tally_cfg_axi_wstrb  (sc0_wstrb),
        .stream_tally_cfg_axi_wvalid (sc0_wvalid), .stream_tally_cfg_axi_wready (sc0_wready),
        .stream_tally_cfg_axi_bresp  (sc0_bresp),  .stream_tally_cfg_axi_bvalid (sc0_bvalid),
        .stream_tally_cfg_axi_bready (sc0_bready),
        .stream_tally_cfg_axi_araddr (sc0_araddr), .stream_tally_cfg_axi_arprot (sc0_arprot),
        .stream_tally_cfg_axi_arvalid(sc0_arvalid),.stream_tally_cfg_axi_arready(sc0_arready),
        .stream_tally_cfg_axi_rdata  (sc0_rdata),  .stream_tally_cfg_axi_rresp  (sc0_rresp),
        .stream_tally_cfg_axi_rvalid (sc0_rvalid), .stream_tally_cfg_axi_rready (sc0_rready),

        .slave_tally_cfg_axi_awaddr  (sc1_awaddr), .slave_tally_cfg_axi_awprot  (sc1_awprot),
        .slave_tally_cfg_axi_awvalid (sc1_awvalid),.slave_tally_cfg_axi_awready (sc1_awready),
        .slave_tally_cfg_axi_wdata   (sc1_wdata),  .slave_tally_cfg_axi_wstrb   (sc1_wstrb),
        .slave_tally_cfg_axi_wvalid  (sc1_wvalid), .slave_tally_cfg_axi_wready  (sc1_wready),
        .slave_tally_cfg_axi_bresp   (sc1_bresp),  .slave_tally_cfg_axi_bvalid  (sc1_bvalid),
        .slave_tally_cfg_axi_bready  (sc1_bready),
        .slave_tally_cfg_axi_araddr  (sc1_araddr), .slave_tally_cfg_axi_arprot  (sc1_arprot),
        .slave_tally_cfg_axi_arvalid (sc1_arvalid),.slave_tally_cfg_axi_arready (sc1_arready),
        .slave_tally_cfg_axi_rdata   (sc1_rdata),  .slave_tally_cfg_axi_rresp   (sc1_rresp),
        .slave_tally_cfg_axi_rvalid  (sc1_rvalid), .slave_tally_cfg_axi_rready  (sc1_rready)
    );


    // =========================================================================
    // S1: harness_csr
    // =========================================================================
    logic        csr_start_pulse, csr_clear_pulse, csr_freeze, csr_soft_reset;
    logic        csr_cam_clear;   // 1-cycle pulse: sync-clear all stream CAMs
    logic        csr_timer_clear_pulse;
    logic [31:0] csr_timer_expected_beats;
    logic [31:0] dbg_wr_ptr;
    // MonBus compressor statistics: stream_top_ch8 -> harness_csr.
    logic [31:0] mon_comp_tier1_a, mon_comp_tier1_b, mon_comp_tier1_c;
    logic [31:0] mon_comp_tier0, mon_comp_cam_miss;
    logic [31:0] mon_comp_delta_ts_ovf, mon_comp_event_data_ovf, mon_comp_ed_delta_ovf;
    logic        dbg_overflow;
    logic        dbg_clear_busy;

    // =========================================================================
    // Unit reset: pulse-extend csr_soft_reset and AND with aresetn so a
    // single CSR write resets the whole DMA+harness unit (sram, bridge,
    // monitors, scheduler, descriptor engine, meters, pattern_gen,
    // crc_check, response-delay queues). Without this, the soft reset
    // path the host has been using (STREAM.GLOBAL_RST) only resets
    // per-channel state -- the monitor blocks and the SRAM controller
    // accumulate state across matrix configs and eventually wedge the
    // engines. Excluded from unit_aresetn: u_csr itself (must keep its
    // own state through the pulse so the pulse can self-terminate),
    // u_uart (would break the host serial connection), and u_bridge
    // (must hold long enough to BRESP the write that triggered the
    // pulse).
    //
    // 16 cycles is far more than needed for any sequential logic inside
    // here to fully clear, and is short enough to be invisible at the
    // host level (160 ns @ 100 MHz vs ~85 us / UART byte).
    localparam int SOFT_RST_PULSE_CYCLES = 16;
    logic [4:0] r_soft_rst_cnt;
    `ALWAYS_FF_RST(aclk, aresetn,
        if (`RST_ASSERTED(aresetn)) begin
            r_soft_rst_cnt <= '0;
        end else if (csr_soft_reset) begin
            r_soft_rst_cnt <= 5'(SOFT_RST_PULSE_CYCLES);
        end else if (r_soft_rst_cnt != 0) begin
            r_soft_rst_cnt <= r_soft_rst_cnt - 5'd1;
        end
    )
    wire unit_aresetn = aresetn & (r_soft_rst_cnt == 0);

    // (axi_bus_meter output + sideband wires retired in RFC Stage E.4 --
    //  datapath utilization is now measured in-core; see the retirement note
    //  at the former meter-instance site below.)
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
    //
    // EVERY channel is checked. There is no ignore mask and none may be added:
    // a channel excluded from the aggregate is a channel whose data corruption
    // reports PASS, which is worse than having no check at all.
    //
    // Bit 0 used to be masked, for a "pre-existing harness-side CRC-aggregation
    // bug on channel 0". It does not reproduce. The 8-channel cosim
    // (test_stream_mon_perf[dma_8ch]) reports match_mask=0xFF and
    // valid_mask=0xFF -- all eight channels agree, ch0 included -- and
    // match_mask is the RAW per-channel comparison, which the mask never
    // touched, so it was not flattering the number. Whatever the original
    // symptom was, it was either fixed elsewhere or misattributed.
    //
    // If ch0 mismatches on silicon, that is a finding to debug, not to mask.
    logic [NUM_CHANNELS-1:0] crc_match_per_ch;
    logic [NUM_CHANNELS-1:0] crc_valid_per_ch;
    always_comb begin
        for (int ch = 0; ch < NUM_CHANNELS; ch++) begin
            crc_valid_per_ch[ch] = read_crc_valid[ch] && write_crc_valid[ch];
            crc_match_per_ch[ch] = crc_valid_per_ch[ch]
                                && (read_crc_value[ch] == write_crc_value[ch]);
        end
    end
    // any_active: at least one channel produced valid CRCs, i.e. a test ran.
    // Channels that were never enabled have valid=0, so they neither pass nor
    // fail and an idle channel cannot hold the aggregate down.
    // any_mismatch: ANY active channel that disagrees fails the aggregate.
    wire any_active   = |crc_valid_per_ch;
    wire any_mismatch = |(crc_valid_per_ch & ~crc_match_per_ch);
    wire crc_match      = any_active && !any_mismatch;
    wire crc_both_valid = any_active;  // raw activity
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

    // desc_ram observation bus + handshake/stall counters (consumed by the
    // harness_csr instance below; counters use w_desc_*_hs / *_stall wires
    // derived in the obs-counter block further down).
    // Bit layout:
    //   [ 0] s2_awvalid  [ 1] s2_awready  (bridge -> desc_ram host writes)
    //   [ 2] s2_wvalid   [ 3] s2_wready
    //   [ 4] s2_bvalid   [ 5] s2_bready
    //   [ 6] s2_arvalid  [ 7] s2_arready  (bridge -> desc_ram, host reads)
    //   [ 8] s2_rvalid   [ 9] s2_rready
    //   [10] desc_arvalid [11] desc_arready  (STREAM 256b AXI4 master)
    //   [12] desc_rvalid  [13] desc_rready
    //   [15:14] reserved
    logic [15:0] w_desc_ram_dbg_vr;
    assign w_desc_ram_dbg_vr = {
        2'b00,
        desc_rready,  desc_rvalid,
        desc_arready, desc_arvalid,
        s2_rready,    s2_rvalid,
        s2_arready,   s2_arvalid,
        s2_bready,    s2_bvalid,
        s2_wready,    s2_wvalid,
        s2_awready,   s2_awvalid
    };
    logic [31:0] r_desc_ar_hs_cnt;
    logic [31:0] r_desc_ar_stall_cnt;
    logic [31:0] r_desc_r_hs_cnt;
    logic [31:0] r_desc_r_stall_cnt;
    logic [31:0] r_desc_aw_hs_cnt;
    logic [31:0] r_desc_w_hs_cnt;
    logic [31:0] r_desc_b_hs_cnt;
    // SRAM-side AXIL AR/R handshake counters. The bridge-side STREAM 256b
    // counters (r_desc_ar_hs_cnt / r_desc_r_hs_cnt) say "did STREAM
    // hand the bridge an AR?". These say "did the bridge ever drive an
    // AXIL AR all the way to the SRAM port?". Combined, they bisect
    // the wedge into a bridge-internal vs SRAM-internal failure.
    logic [31:0] r_desc_sram_ar_hs_cnt;
    logic [31:0] r_desc_sram_r_hs_cnt;

    // RFC Stage E external DMA observer readback nets. Declared here (ahead of
    // the observer instance further down) so u_csr can read them; the observer
    // drives them and the selector/mux logic lives next to its instance.
    logic [31:0] obs_rd_agg_prod  [1];
    logic [31:0] obs_rd_agg_bp    [1];
    logic [31:0] obs_rd_agg_starv [1];
    logic [31:0] obs_rd_agg_idle  [1];
    logic [31:0] obs_wr_agg_prod  [1];
    logic [31:0] obs_wr_agg_bp    [1];
    logic [31:0] obs_wr_agg_starv [1];
    logic [31:0] obs_wr_agg_idle  [1];
    // (obs_hist_data_mux / obs_hist_total_mux removed -- see the histogram
    //  note further down; they fed harness_csr 0x124/0x128, both retired.)

    // Build identity is driven from THIS harness's own parameters, so what a
    // host reads is what the bitstream was compiled with. Two bitstreams ship
    // from this build (all-except-error / error-only) and nothing on the board
    // said which was loaded -- a host then reports an absent cone as a missed
    // fault. GEN_MON is reported too: with it 0 the per-channel CORE emitters
    // are compiled out, so agents 48/16 CANNOT emit and their empty tally bins
    // are structural rather than a coverage gap.
    harness_csr #(
        .AW(32), .DW(32), .NUM_CHANNELS(NUM_CHANNELS),
        // The host reads these to know which classes this bitstream can emit.
        .BUILD_ERROR_FLAVOR(int'(w_data_mon_error_cone)),
        .BUILD_MAIN_CONES  (int'(w_data_mon_main_cones)),
        // Derived from the harness clock, never a literal: a second copy
        // would be free to disagree with the MMCM, which is exactly the
        // failure this register exists to remove.
        .BUILD_CLK_HZ      (FPGA_CLK_HZ),
        .BUILD_NUM_CHANNELS(NUM_CHANNELS),
        // Derived, not a literal: the host reads this to size beats and
        // throughput, so it must track the datapath it is actually built with.
        .BUILD_DATA_WIDTH_B(DATA_WIDTH / 8),
        .BUILD_N_PROFILE   (MON_N_PROFILE),
        .BUILD_USE_MONITORS(USE_AXI_MONITORS),
        .BUILD_GEN_MON     (int'(GEN_MON))
    ) u_csr (
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
        .o_cam_clear_pulse  (csr_cam_clear),
        .i_stream_irq       (stream_irq),
        .i_any_error        (any_error),
        .i_dbg_wr_ptr       (dbg_wr_ptr),
        .i_dbg_overflow     (dbg_overflow),
        .i_dbg_clear_busy   (dbg_clear_busy),
        // MonBus compressor statistics (0x1E0..0x1FC).
        .i_mon_comp_tier1_a        (mon_comp_tier1_a),
        .i_mon_comp_tier1_b        (mon_comp_tier1_b),
        .i_mon_comp_tier1_c        (mon_comp_tier1_c),
        .i_mon_comp_tier0          (mon_comp_tier0),
        .i_mon_comp_cam_miss       (mon_comp_cam_miss),
        .i_mon_comp_delta_ts_ovf   (mon_comp_delta_ts_ovf),
        .i_mon_comp_event_data_ovf (mon_comp_event_data_ovf),
        .i_mon_comp_ed_delta_ovf   (mon_comp_ed_delta_ovf),
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

        // Kick-burst outputs (CH_KICK_ADDR slots split around KICK_GO @ 0xC0;
        // see harness_csr.sv address-map block for the per-channel offsets)

        // (AXI bus meter readback retired in RFC Stage E.4 -- datapath
        //  utilization is now measured in-core via the STREAM RDMON/WRMON_PERF
        //  CSRs, read directly from the regblock.)

        // desc_ram observation counters (CSR readback at 0xD4/0xD8 + 0xE0-0xFC)
        .i_desc_sram_ar_hs (r_desc_sram_ar_hs_cnt),
        .i_desc_sram_r_hs  (r_desc_sram_r_hs_cnt),
        .i_desc_ar_hs    (r_desc_ar_hs_cnt),
        .i_desc_ar_stall (r_desc_ar_stall_cnt),
        .i_desc_r_hs     (r_desc_r_hs_cnt),
        .i_desc_r_stall  (r_desc_r_stall_cnt),
        .i_desc_aw_hs    (r_desc_aw_hs_cnt),
        .i_desc_w_hs     (r_desc_w_hs_cnt),
        .i_desc_b_hs     (r_desc_b_hs_cnt),
        .i_desc_vr_live  (w_desc_ram_dbg_vr)

        // NO observer readback through harness_csr. 0x100-0x128 is retired in
        // full: the observer owns its telemetry and the host reads it from the
        // observer's own regblock (OBS_STAT_SEL / OBS_STAT_DATA, bin/obs_addrs.py).
        // The last survivor, OBS_HIST_SEL @ 0x120, was a register the host could
        // write and read back that drove nothing -- its decoded {bin,metric,bus}
        // fed only a mux the harness had already orphaned.
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

    // Pipeline the aggregate beat counts and the expected-beats threshold
    // by one stage before doing the wide-comparison + AND-reduce that
    // fires w_{rd,wr}_{first,last}_now. The aggregates come from
    // u_{rd,wr}_crc_check.{read,write}_beat_count_total, which is itself
    // an 8-channel adder tree. Without this register stage, at 8 channels
    // the combinational path
    //   per-ch beat count -> 8-way adder -> compare -> AND with running
    //   -> timer_w_last_reg/CE + timer_cycles_reg/CE
    // lands at 14 levels and blows -1.05 ns of slack at 100 MHz on the
    // xc7a100t-1. Breaking it into two ~7-level halves around the new
    // r_{rd,wr}_beat_count_q flop adds 1 cycle of measurement-side
    // latency on the FIRST and LAST beat-stamps -- harmless for cycle-
    // count measurements that span tens of thousands of cycles, and
    // invisible to software since the host polls TIMER_STATUS for done.
    logic [31:0] r_rd_beat_count_q;
    logic [31:0] r_wr_beat_count_q;
    logic [31:0] r_csr_exp_beats_q;
    `ALWAYS_FF_RST(aclk, aresetn,
        if (`RST_ASSERTED(aresetn)) begin
            r_desc_handshake_d <= 1'b0;
            r_rd_beat_count_q  <= '0;
            r_wr_beat_count_q  <= '0;
            r_csr_exp_beats_q  <= '0;
        end else begin
            r_desc_handshake_d <= w_desc_handshake;
            r_rd_beat_count_q  <= read_beat_count;
            r_wr_beat_count_q  <= write_beat_count;
            r_csr_exp_beats_q  <= csr_timer_expected_beats;
        end
    )

    wire w_beat_count_reached = (r_csr_exp_beats_q != 32'd0) &&
                                (r_wr_beat_count_q >= r_csr_exp_beats_q);

    // First/last beat detection on the slave side. read_beat_count and
    // write_beat_count both start at 0 and increment monotonically; we
    // latch cycle stamps on the first cycle each crosses 0 and on the
    // first cycle each reaches the programmed expected_beats target.
    // All sources here are the *_q registered flavors above so the
    // wide compare + AND lands on a flop boundary, not on the per-
    // channel CRC counter.
    logic        r_rd_first_seen, r_wr_first_seen;
    logic        r_rd_last_seen,  r_wr_last_seen;
    wire         w_rd_first_now  = timer_running && !r_rd_first_seen
                                                  && (r_rd_beat_count_q != 32'd0);
    wire         w_wr_first_now  = timer_running && !r_wr_first_seen
                                                  && (r_wr_beat_count_q != 32'd0);
    wire         w_rd_last_now   = timer_running && !r_rd_last_seen
                                                  && (r_csr_exp_beats_q != 32'd0)
                                                  && (r_rd_beat_count_q >= r_csr_exp_beats_q);
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
    // S2: desc_ram — sdpram_slave at 256-bit, AXI4 wr + AXI4 rd.
    //
    // Both host (writes) and STREAM (reads) go through the bridge to this
    // slave. The bridge's stream_desc → desc_ram path is direct AXI4 256b
    // (no converter). The host's AXIL 32b writes hit the bridge master
    // adapter's axil_to_axi4_wide_align_wr, exit the bridge as AXI4 256b
    // single-beat writes positioned by awaddr's low bits, and land here.
    // =========================================================================
    // desc_* master signals are declared early (near the mon_* block)
    // so the bridge's stream_desc_* master port-map can reach them.

    // Internal obs port from sdpram_slave (10b raw valid/ready).
    logic [9:0] w_desc_ram_dbg_vr_axi4;
    /* verilator lint_off UNUSED */
    logic [9:0] w_desc_ram_dbg_fub_vr;
    logic w_desc_ram_dbg_bram_wr_pulse, w_desc_ram_dbg_bram_rd_pulse;
    logic w_desc_ram_dbg_busy_wr, w_desc_ram_dbg_busy_rd;
    logic w_desc_ram_dbg_clear_done;
    /* verilator lint_on UNUSED */

    sdpram_slave_axi4_axi4 #(
        .AXI_ID_WIDTH (8),
        .ADDR_WIDTH   (32),
        // 256b per the descriptor-fetch-must-be-256b-end-to-end rule.
        // MEM_DEPTH = DESC_RAM_ENTRIES because each descriptor is one
        // 256b beat.
        .DATA_WIDTH   (256),
        .USER_WIDTH   (1),
        .MEM_DEPTH    (DESC_RAM_ENTRIES)
    ) u_desc_ram (
        .aclk(aclk), .aresetn(unit_aresetn),

        .s_axi_awid    (s2_awid),    .s_axi_awaddr  (s2_awaddr),
        .s_axi_awlen   (s2_awlen),   .s_axi_awsize  (s2_awsize),
        .s_axi_awburst (s2_awburst), .s_axi_awlock  (s2_awlock),
        .s_axi_awcache (s2_awcache), .s_axi_awprot  (s2_awprot),
        .s_axi_awqos   (s2_awqos),   .s_axi_awregion(s2_awregion),
        .s_axi_awuser  (s2_awuser),
        .s_axi_awvalid (s2_awvalid), .s_axi_awready (s2_awready),

        .s_axi_wdata   (s2_wdata),   .s_axi_wstrb   (s2_wstrb),
        .s_axi_wlast   (s2_wlast),   .s_axi_wuser   (s2_wuser),
        .s_axi_wvalid  (s2_wvalid),  .s_axi_wready  (s2_wready),

        .s_axi_bid     (s2_bid),     .s_axi_bresp   (s2_bresp),
        .s_axi_buser   (s2_buser),
        .s_axi_bvalid  (s2_bvalid),  .s_axi_bready  (s2_bready),

        .s_axi_arid    (s2_arid),    .s_axi_araddr  (s2_araddr),
        .s_axi_arlen   (s2_arlen),   .s_axi_arsize  (s2_arsize),
        .s_axi_arburst (s2_arburst), .s_axi_arlock  (s2_arlock),
        .s_axi_arcache (s2_arcache), .s_axi_arprot  (s2_arprot),
        .s_axi_arqos   (s2_arqos),   .s_axi_arregion(s2_arregion),
        .s_axi_aruser  (s2_aruser),
        .s_axi_arvalid (s2_arvalid), .s_axi_arready (s2_arready),

        .s_axi_rid     (s2_rid),     .s_axi_rdata   (s2_rdata),
        .s_axi_rresp   (s2_rresp),   .s_axi_rlast   (s2_rlast),
        .s_axi_ruser   (s2_ruser),
        .s_axi_rvalid  (s2_rvalid),  .s_axi_rready  (s2_rready),

        // Bulk-clear control. The SRAM's clear-FSM is sticky-done; CSR
        // plumbing for host-issued start pulses + done polling lives in
        // harness_csr (CSR_CTRL[4] / CSR_STATUS[3]). Tied off here
        // for now until that wiring lands.
        .i_cfg_start_clear (1'b0),
        .o_cfg_done_clear  (w_desc_ram_dbg_clear_done),
        // Obs
        .o_dbg_vr      (w_desc_ram_dbg_vr_axi4),
        .o_dbg_fub_vr  (w_desc_ram_dbg_fub_vr),
        .o_dbg_bram_wr (w_desc_ram_dbg_bram_wr_pulse),
        .o_dbg_bram_rd (w_desc_ram_dbg_bram_rd_pulse),
        .o_dbg_busy_wr (w_desc_ram_dbg_busy_wr),
        .o_dbg_busy_rd (w_desc_ram_dbg_busy_rd)
    );

    // -------------------------------------------------------------------------
    // desc_ram handshake / stall counters
    //
    // Bit map (matches desc_ram.sv o_dbg_vr):
    //   [ 0] axil awvalid   [ 1] axil awready
    //   [ 2] axil wvalid    [ 3] axil wready
    //   [ 4] axil bvalid    [ 5] axil bready
    //   [10] axi4 arvalid   [11] axi4 arready
    //   [12] axi4 rvalid    [13] axi4 rready
    //
    // Lets the host answer "is the SRAM responding or is STREAM not
    // accepting?" via plain UART reads — no trace SRAM needed.
    // -------------------------------------------------------------------------
    wire w_desc_ar_hs      = w_desc_ram_dbg_vr[10] &&  w_desc_ram_dbg_vr[11];
    wire w_desc_ar_stall   = w_desc_ram_dbg_vr[10] && !w_desc_ram_dbg_vr[11];
    wire w_desc_r_hs       = w_desc_ram_dbg_vr[12] &&  w_desc_ram_dbg_vr[13];
    wire w_desc_r_stall    = w_desc_ram_dbg_vr[12] && !w_desc_ram_dbg_vr[13];
    wire w_desc_aw_hs      = w_desc_ram_dbg_vr[0]  &&  w_desc_ram_dbg_vr[1];
    wire w_desc_w_hs       = w_desc_ram_dbg_vr[2]  &&  w_desc_ram_dbg_vr[3];
    wire w_desc_b_hs       = w_desc_ram_dbg_vr[4]  &&  w_desc_ram_dbg_vr[5];
    // SRAM-side AXIL AR/R from bits [6][7] and [8][9] of the bus
    // (s2_arvalid/ready and s2_rvalid/ready at the SRAM port).
    wire w_desc_sram_ar_hs = w_desc_ram_dbg_vr[6]  &&  w_desc_ram_dbg_vr[7];
    wire w_desc_sram_r_hs  = w_desc_ram_dbg_vr[8]  &&  w_desc_ram_dbg_vr[9];

    // Capture the first AR that STREAM hands to the bridge so we can
    // see exactly what address/burst-shape it emitted at timeout.
    // STREAM only drives desc_arvalid for the handshake cycle, so a
    // live peek at the wires returns 0; this latch holds the values
    // until reset/clear. cocotb reads via --public-flat-rw.
    /* verilator lint_off UNUSED */
    logic [ADDR_WIDTH-1:0]   r_first_desc_araddr;
    logic [7:0]              r_first_desc_arlen;
    logic [2:0]              r_first_desc_arsize;
    logic [1:0]              r_first_desc_arburst;
    logic [AXI_ID_WIDTH-1:0] r_first_desc_arid;
    logic                    r_first_desc_ar_seen;
    /* verilator lint_on UNUSED */
    `ALWAYS_FF_RST(aclk, aresetn,
        if (`RST_ASSERTED(aresetn)) begin
            r_first_desc_ar_seen <= 1'b0;
            r_first_desc_araddr  <= '0;
            r_first_desc_arlen   <= '0;
            r_first_desc_arsize  <= '0;
            r_first_desc_arburst <= '0;
            r_first_desc_arid    <= '0;
        end else if (csr_clear_pulse) begin
            r_first_desc_ar_seen <= 1'b0;
        end else if (w_desc_ar_hs && !r_first_desc_ar_seen) begin
            r_first_desc_ar_seen <= 1'b1;
            r_first_desc_araddr  <= desc_araddr;
            r_first_desc_arlen   <= desc_arlen;
            r_first_desc_arsize  <= desc_arsize;
            r_first_desc_arburst <= desc_arburst;
            r_first_desc_arid    <= desc_arid;
        end
    )

    `ALWAYS_FF_RST(aclk, aresetn,
        if (`RST_ASSERTED(aresetn)) begin
            r_desc_ar_hs_cnt      <= '0;
            r_desc_ar_stall_cnt   <= '0;
            r_desc_r_hs_cnt       <= '0;
            r_desc_r_stall_cnt    <= '0;
            r_desc_aw_hs_cnt      <= '0;
            r_desc_w_hs_cnt       <= '0;
            r_desc_b_hs_cnt       <= '0;
            r_desc_sram_ar_hs_cnt <= '0;
            r_desc_sram_r_hs_cnt  <= '0;
        end else if (csr_clear_pulse) begin
            r_desc_ar_hs_cnt      <= '0;
            r_desc_ar_stall_cnt   <= '0;
            r_desc_r_hs_cnt       <= '0;
            r_desc_r_stall_cnt    <= '0;
            r_desc_aw_hs_cnt      <= '0;
            r_desc_w_hs_cnt       <= '0;
            r_desc_b_hs_cnt       <= '0;
            r_desc_sram_ar_hs_cnt <= '0;
            r_desc_sram_r_hs_cnt  <= '0;
        end else begin
            // 32-bit saturating — clamps at 2^32-1 instead of wrapping.
            if (w_desc_ar_hs      && (r_desc_ar_hs_cnt      != 32'hFFFF_FFFF)) r_desc_ar_hs_cnt      <= r_desc_ar_hs_cnt      + 1'b1;
            if (w_desc_ar_stall   && (r_desc_ar_stall_cnt   != 32'hFFFF_FFFF)) r_desc_ar_stall_cnt   <= r_desc_ar_stall_cnt   + 1'b1;
            if (w_desc_r_hs       && (r_desc_r_hs_cnt       != 32'hFFFF_FFFF)) r_desc_r_hs_cnt       <= r_desc_r_hs_cnt       + 1'b1;
            if (w_desc_r_stall    && (r_desc_r_stall_cnt    != 32'hFFFF_FFFF)) r_desc_r_stall_cnt    <= r_desc_r_stall_cnt    + 1'b1;
            if (w_desc_aw_hs      && (r_desc_aw_hs_cnt      != 32'hFFFF_FFFF)) r_desc_aw_hs_cnt      <= r_desc_aw_hs_cnt      + 1'b1;
            if (w_desc_w_hs       && (r_desc_w_hs_cnt       != 32'hFFFF_FFFF)) r_desc_w_hs_cnt       <= r_desc_w_hs_cnt       + 1'b1;
            if (w_desc_b_hs       && (r_desc_b_hs_cnt       != 32'hFFFF_FFFF)) r_desc_b_hs_cnt       <= r_desc_b_hs_cnt       + 1'b1;
            if (w_desc_sram_ar_hs && (r_desc_sram_ar_hs_cnt != 32'hFFFF_FFFF)) r_desc_sram_ar_hs_cnt <= r_desc_sram_ar_hs_cnt + 1'b1;
            if (w_desc_sram_r_hs  && (r_desc_sram_r_hs_cnt  != 32'hFFFF_FFFF)) r_desc_sram_r_hs_cnt  <= r_desc_sram_r_hs_cnt  + 1'b1;
        end
    )

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
    // S4: stream_tally — monbus_tally_axil at 64-bit.
    //
    // Records come DIRECTLY from u_dma_observer's monbus group (dmamon_*), with
    // no bridge in the record path -- that is the whole point of the observer:
    // it is the monitor under test, and its packets are counted here.
    //
    // Through the bridge this slave is READ-ONLY in practice: the host reads the
    // histogram. Its write channel is SLVERR-terminated below, since no master
    // produces records into it any more. STREAM's own m_axil_mon is a separate
    // story -- it drives bridge master monbus_wr into comp_sram.
    // Tally record-ingest arbiter nets, declared ahead of the tally
    // instances that consume them. The arbiters themselves live with the
    // bridge slave channels further down, next to the s4/s6 ports they mux.
    logic        tally_s4_awvalid, tally_s4_awready;
    logic        tally_s4_wvalid,  tally_s4_wready;
    logic        tally_s4_bvalid,  tally_s4_bready;
    logic [1:0]  tally_s4_bresp;
    logic [31:0] tally_s4_awaddr;
    logic [2:0]  tally_s4_awprot;
    logic [63:0] tally_s4_wdata;
    logic [7:0]  tally_s4_wstrb;

    logic        tally_s6_awvalid, tally_s6_awready;
    logic        tally_s6_wvalid,  tally_s6_wready;
    logic        tally_s6_bvalid,  tally_s6_bready;
    logic [1:0]  tally_s6_bresp;
    logic [31:0] tally_s6_awaddr;
    logic [2:0]  tally_s6_awprot;
    logic [63:0] tally_s6_wdata;
    logic [7:0]  tally_s6_wstrb;

    // =========================================================================
    // mon_* signals are declared up near the bridge instance (search
    // "// STREAM m_axil_mon master signals (declared early"). They have
    // to live before the bridge port-map, which references them.

    // Internal obs port from sdpram_slave (10b raw valid/ready).
    /* verilator lint_off UNUSED */
    logic [9:0] w_debug_sram_dbg_vr_axil;
    logic [9:0] w_debug_sram_dbg_fub_vr;
    logic w_debug_sram_dbg_bram_wr_pulse, w_debug_sram_dbg_bram_rd_pulse;
    logic w_debug_sram_dbg_busy_wr, w_debug_sram_dbg_busy_rd;
    logic w_debug_sram_dbg_clear_done;
    /* verilator lint_on UNUSED */

    // MONITOR HARNESS: the trace-capture SRAM (debug_sram) is replaced by the
    // STREAM-side tally. It presents the SAME AXIL surface at Slave 4 (0x40000),
    // but instead of storing beats it reassembles the monbus group's raw 3-beat
    // records into packets and counts them; the host reads the histogram at the
    // same window. Control shares the CSR freeze/clear used by the slave tally.
    logic w_stream_tally_flush_busy;
    logic w_tally_flush;                 // auto-flush pulse shared by both tally SRAMs (assigned below)
    // Tally sizing: the legal-set CAM always maps to dense bins 0..N-1 plus the
    // UNEXPECTED bin (N), so clog2(N+1) address bits.
    localparam int MON_TALLY_ADDR_BITS = $clog2(MON_N_PROFILE + 1);
    monbus_tally_axil #(
        .ADDR_WIDTH       (32),
        .DATA_WIDTH       (64),
        .TALLY_ADDR_BITS  (MON_TALLY_ADDR_BITS),
        .N_PROFILE        (MON_N_PROFILE)
    ) u_stream_tally (
        .aclk(aclk), .aresetn(unit_aresetn),
        // WR1 record ingest <- stream_tally observer monbus group, DIRECT. Was: bridge @ 0x40000.
        .rec_awaddr  (tally_s4_awaddr),  .rec_awprot  (tally_s4_awprot),
        .rec_awvalid (tally_s4_awvalid), .rec_awready (tally_s4_awready),
        .rec_wdata   (tally_s4_wdata),   .rec_wstrb   (tally_s4_wstrb),
        .rec_wvalid  (tally_s4_wvalid),  .rec_wready  (tally_s4_wready),
        .rec_bresp   (tally_s4_bresp),   .rec_bvalid  (tally_s4_bvalid),
        .rec_bready  (tally_s4_bready),
        // RD1 count readback <- stream_tally slave READ channels @ 0x40000.
        .cnt_araddr  (s4_araddr),  .cnt_arprot  (s4_arprot),
        .cnt_arvalid (s4_arvalid), .cnt_arready (s4_arready),
        .cnt_rdata   (s4_rdata),   .cnt_rresp   (s4_rresp),
        .cnt_rvalid  (s4_rvalid),  .cnt_rready  (s4_rready),
        // WR2 config <- stream_tally_cfg observer monbus group, DIRECT. Was: bridge @ 0x100000.
        .cfgw_awaddr (sc0_awaddr),  .cfgw_awprot (sc0_awprot),
        .cfgw_awvalid(sc0_awvalid), .cfgw_awready(sc0_awready),
        .cfgw_wdata  (sc0_wdata),   .cfgw_wstrb  (sc0_wstrb),
        .cfgw_wvalid (sc0_wvalid),  .cfgw_wready (sc0_wready),
        .cfgw_bresp  (sc0_bresp),   .cfgw_bvalid (sc0_bvalid),
        .cfgw_bready (sc0_bready),
        // RD2 config readback <- stream_tally_cfg slave READ channels @ 0x100000.
        .cfgr_araddr (sc0_araddr),  .cfgr_arprot (sc0_arprot),
        .cfgr_arvalid(sc0_arvalid), .cfgr_arready(sc0_arready),
        .cfgr_rdata  (sc0_rdata),   .cfgr_rresp  (sc0_rresp),
        .cfgr_rvalid (sc0_rvalid),  .cfgr_rready (sc0_rready),
        .tally_freeze    (csr_freeze),    .tally_flush    (w_tally_flush),
        .tally_flush_busy(w_stream_tally_flush_busy), .tally_clear(csr_clear_pulse)
    );

    // Slave-side tally SRAM. Records arrive DIRECTLY from the slave observer's
    // monbus group (slmon_*); the bridge slave_tally window @ 0xC0000 is the
    // host's READ path for the counts only.
    logic w_slave_tally_flush_busy;

    monbus_tally_axil #(
        .ADDR_WIDTH(32), .DATA_WIDTH(64),
        .TALLY_ADDR_BITS(MON_TALLY_ADDR_BITS),
        .N_PROFILE(MON_N_PROFILE)
    ) u_slave_tally (
        .aclk(aclk), .aresetn(unit_aresetn),
        // WR1 record ingest <- slave_tally observer monbus group, DIRECT. Was: bridge @ 0xC0000.
        .rec_awaddr(tally_s6_awaddr),  .rec_awprot(tally_s6_awprot),
        .rec_awvalid(tally_s6_awvalid), .rec_awready(tally_s6_awready),
        .rec_wdata(tally_s6_wdata),    .rec_wstrb(tally_s6_wstrb),
        .rec_wvalid(tally_s6_wvalid),  .rec_wready(tally_s6_wready),
        .rec_bresp(tally_s6_bresp),    .rec_bvalid(tally_s6_bvalid), .rec_bready(tally_s6_bready),
        // RD1 count readback <- slave_tally slave READ channels @ 0xC0000.
        .cnt_araddr(s6_araddr),  .cnt_arprot(s6_arprot),
        .cnt_arvalid(s6_arvalid), .cnt_arready(s6_arready),
        .cnt_rdata(s6_rdata),    .cnt_rresp(s6_rresp),
        .cnt_rvalid(s6_rvalid),  .cnt_rready(s6_rready),
        // WR2 config <- slave_tally_cfg observer monbus group, DIRECT. Was: bridge @ 0x140000.
        .cfgw_awaddr(sc1_awaddr),  .cfgw_awprot(sc1_awprot),
        .cfgw_awvalid(sc1_awvalid), .cfgw_awready(sc1_awready),
        .cfgw_wdata(sc1_wdata),    .cfgw_wstrb(sc1_wstrb),
        .cfgw_wvalid(sc1_wvalid),  .cfgw_wready(sc1_wready),
        .cfgw_bresp(sc1_bresp),    .cfgw_bvalid(sc1_bvalid), .cfgw_bready(sc1_bready),
        // RD2 config readback <- slave_tally_cfg slave READ channels @ 0x140000.
        .cfgr_araddr(sc1_araddr),  .cfgr_arprot(sc1_arprot),
        .cfgr_arvalid(sc1_arvalid), .cfgr_arready(sc1_arready),
        .cfgr_rdata(sc1_rdata),    .cfgr_rresp(sc1_rresp),
        .cfgr_rvalid(sc1_rvalid),  .cfgr_rready(sc1_rready),
        .tally_freeze(csr_freeze),  .tally_flush(w_tally_flush),
        .tally_flush_busy(w_slave_tally_flush_busy), .tally_clear(csr_clear_pulse)
    );

    // s4 write channel: RECORD INGEST for u_stream_tally, arbitrated between the
    // observer's monbus group (direct) and the bridge window @ 0x40000.
    //
    // This used to be SLVERR-terminated, on the reasoning that the observer
    // rewire made the direct path the only producer. That was true of the obs
    // flavour and false as a rule: the monbus group's destination is a runtime
    // register (MON_GROUP_BASE_ADDR, RDL default 0x40000), so the in-core monitors
    // can address this tally too -- and in build-mon they are the ONLY producer,
    // because the observers' taps are off. Terminating the bridge write made
    // that configuration silently impossible: records were emitted, SLVERR'd,
    // and the tally read back empty with nothing reporting an error.
    //
    // Priority to the observer: in obs the bridge side is idle, in mon the
    // observer side is idle, so the arbiter never actually contends -- it
    // exists so neither path can be starved if both are ever armed at once.
    // Grant is LATCHED until B completes; an AXIL write is three handshakes and
    // interleaving two masters mid-burst would corrupt both.
    logic r_s4_gr_bridge, r_s4_gr_obs, r_s4_busy;
    `ALWAYS_FF_RST(aclk, aresetn,
        if (`RST_ASSERTED(aresetn)) begin
            r_s4_gr_bridge <= 1'b0; r_s4_gr_obs <= 1'b0; r_s4_busy <= 1'b0;
        end else if (!r_s4_busy) begin
            if (dmamon_awvalid) begin
                r_s4_gr_obs <= 1'b1; r_s4_busy <= 1'b1;
            end else if (s4_awvalid) begin
                r_s4_gr_bridge <= 1'b1; r_s4_busy <= 1'b1;
            end
        end else if (tally_s4_bvalid && tally_s4_bready) begin
            r_s4_gr_bridge <= 1'b0; r_s4_gr_obs <= 1'b0; r_s4_busy <= 1'b0;
        end
    )

    always_comb begin
        if (r_s4_gr_bridge) begin
            tally_s4_awaddr  = s4_awaddr;  tally_s4_awprot = s4_awprot;
            tally_s4_awvalid = s4_awvalid; tally_s4_wdata  = s4_wdata;
            tally_s4_wstrb   = s4_wstrb;   tally_s4_wvalid = s4_wvalid;
            tally_s4_bready  = s4_bready;
        end else begin
            tally_s4_awaddr  = dmamon_awaddr;  tally_s4_awprot = dmamon_awprot;
            tally_s4_awvalid = dmamon_awvalid; tally_s4_wdata  = dmamon_wdata;
            tally_s4_wstrb   = dmamon_wstrb;   tally_s4_wvalid = dmamon_wvalid;
            tally_s4_bready  = dmamon_bready;
        end
    end

    assign dmamon_awready = r_s4_gr_obs    ? tally_s4_awready : 1'b0;
    assign dmamon_wready  = r_s4_gr_obs    ? tally_s4_wready  : 1'b0;
    assign dmamon_bvalid  = r_s4_gr_obs    ? tally_s4_bvalid  : 1'b0;
    assign dmamon_bresp   = tally_s4_bresp;
    assign s4_awready  = r_s4_gr_bridge ? tally_s4_awready : 1'b0;
    assign s4_wready   = r_s4_gr_bridge ? tally_s4_wready  : 1'b0;
    assign s4_bvalid   = r_s4_gr_bridge ? tally_s4_bvalid  : 1'b0;
    assign s4_bresp    = tally_s4_bresp;

    // s6 write channel: RECORD INGEST for u_slave_tally, arbitrated between the
    // observer's monbus group (direct) and the bridge window @ 0xC0000.
    //
    // This used to be SLVERR-terminated, on the reasoning that the observer
    // rewire made the direct path the only producer. That was true of the obs
    // flavour and false as a rule: the monbus group's destination is a runtime
    // register (MON_GROUP_BASE_ADDR, RDL default 0xC0000), so the in-core monitors
    // can address this tally too -- and in build-mon they are the ONLY producer,
    // because the observers' taps are off. Terminating the bridge write made
    // that configuration silently impossible: records were emitted, SLVERR'd,
    // and the tally read back empty with nothing reporting an error.
    //
    // Priority to the observer: in obs the bridge side is idle, in mon the
    // observer side is idle, so the arbiter never actually contends -- it
    // exists so neither path can be starved if both are ever armed at once.
    // Grant is LATCHED until B completes; an AXIL write is three handshakes and
    // interleaving two masters mid-burst would corrupt both.
    logic r_s6_gr_bridge, r_s6_gr_obs, r_s6_busy;
    `ALWAYS_FF_RST(aclk, aresetn,
        if (`RST_ASSERTED(aresetn)) begin
            r_s6_gr_bridge <= 1'b0; r_s6_gr_obs <= 1'b0; r_s6_busy <= 1'b0;
        end else if (!r_s6_busy) begin
            if (slmon_awvalid) begin
                r_s6_gr_obs <= 1'b1; r_s6_busy <= 1'b1;
            end else if (s6_awvalid) begin
                r_s6_gr_bridge <= 1'b1; r_s6_busy <= 1'b1;
            end
        end else if (tally_s6_bvalid && tally_s6_bready) begin
            r_s6_gr_bridge <= 1'b0; r_s6_gr_obs <= 1'b0; r_s6_busy <= 1'b0;
        end
    )

    always_comb begin
        if (r_s6_gr_bridge) begin
            tally_s6_awaddr  = s6_awaddr;  tally_s6_awprot = s6_awprot;
            tally_s6_awvalid = s6_awvalid; tally_s6_wdata  = s6_wdata;
            tally_s6_wstrb   = s6_wstrb;   tally_s6_wvalid = s6_wvalid;
            tally_s6_bready  = s6_bready;
        end else begin
            tally_s6_awaddr  = slmon_awaddr;  tally_s6_awprot = slmon_awprot;
            tally_s6_awvalid = slmon_awvalid; tally_s6_wdata  = slmon_wdata;
            tally_s6_wstrb   = slmon_wstrb;   tally_s6_wvalid = slmon_wvalid;
            tally_s6_bready  = slmon_bready;
        end
    end

    assign slmon_awready = r_s6_gr_obs    ? tally_s6_awready : 1'b0;
    assign slmon_wready  = r_s6_gr_obs    ? tally_s6_wready  : 1'b0;
    assign slmon_bvalid  = r_s6_gr_obs    ? tally_s6_bvalid  : 1'b0;
    assign slmon_bresp   = tally_s6_bresp;
    assign s6_awready  = r_s6_gr_bridge ? tally_s6_awready : 1'b0;
    assign s6_wready   = r_s6_gr_bridge ? tally_s6_wready  : 1'b0;
    assign s6_bvalid   = r_s6_gr_bridge ? tally_s6_bvalid  : 1'b0;
    assign s6_bresp    = tally_s6_bresp;


    // =========================================================================
    // Compression capture SRAM (comp_sram @ 0x001A_0000, 64 KB)
    // =========================================================================
    // MEM_DEPTH is in 64-bit words: the bridge window is 64 KB and the data bus
    // is 64 bits, so 65536/8 = 8192 entries. Sizing it from the window rather
    // than a literal keeps the two from drifting -- a memory smaller than its
    // window aliases silently, which on a capture buffer looks like corrupted
    // records rather than a wrap.
    localparam int COMP_SRAM_BYTES = 32'h0001_0000;   // must match addr_range
    localparam int COMP_SRAM_WORDS = COMP_SRAM_BYTES / 8;

    sdpram_slave_axil_axil #(
        .ADDR_WIDTH (32),
        .DATA_WIDTH (64),
        .MEM_DEPTH  (COMP_SRAM_WORDS),
        // The monbus writer emits whole 64-bit beats -- this memory never sees
        // a partial strobe. Saying so lets the array infer BLOCK RAM: with byte
        // enables it fell into distributed RAM and cost ~23k LUTs (81% device
        // utilisation) for a buffer that belongs in ~14 BRAM tiles.
        .USE_WSTRB  (1'b0)
    ) u_comp_sram (
        .aclk(aclk), .aresetn(unit_aresetn),

        .s_axil_awaddr  (cs_awaddr),
        .s_axil_awprot  (cs_awprot),
        .s_axil_awvalid (cs_awvalid),
        .s_axil_awready (cs_awready),

        .s_axil_wdata   (cs_wdata),
        .s_axil_wstrb   (cs_wstrb),
        .s_axil_wvalid  (cs_wvalid),
        .s_axil_wready  (cs_wready),

        .s_axil_bresp   (cs_bresp),
        .s_axil_bvalid  (cs_bvalid),
        .s_axil_bready  (cs_bready),

        .s_axil_araddr  (cs_araddr),
        .s_axil_arprot  (cs_arprot),
        .s_axil_arvalid (cs_arvalid),
        .s_axil_arready (cs_arready),

        .s_axil_rdata   (cs_rdata),
        .s_axil_rresp   (cs_rresp),
        .s_axil_rvalid  (cs_rvalid),
        .s_axil_rready  (cs_rready),

        // Bulk clear unused: the host zeroes the window before a capture run
        // so a short capture cannot be read as stale bytes from the last one.
        // Zeroing is the ONLY host write that behaves intuitively here. With
        // USE_WSTRB=0 the strobes are ignored, so a 32-bit host write rewrites
        // the whole 64-bit word -- data into the addressed lane, ZEROES into
        // the other. Seeding a non-zero 64-bit pattern as two 32-bit writes
        // therefore leaves only the second one (measured on silicon). That is
        // correct for the traffic that matters: the monbus writer emits full
        // 64-bit beats. Read-back is unaffected.
        .i_cfg_start_clear (1'b0),
        .o_cfg_done_clear  (),

        .o_dbg_vr      (),
        .o_dbg_fub_vr  (),
        .o_dbg_bram_wr (),
        .o_dbg_bram_rd (),
        .o_dbg_busy_wr (),
        .o_dbg_busy_rd ()
    );
    // debug_sram's trace-log debug signals no longer exist; tie them off so the
    // legacy host-visible wr_ptr / CSR plumbing below still compiles (those
    // fields are meaningless for a count matrix and read back as 0).
    assign w_debug_sram_dbg_vr_axil       = '0;
    assign w_debug_sram_dbg_fub_vr        = '0;
    assign w_debug_sram_dbg_bram_wr_pulse = 1'b0;
    assign w_debug_sram_dbg_bram_rd_pulse = 1'b0;
    assign w_debug_sram_dbg_busy_wr       = 1'b0;
    assign w_debug_sram_dbg_busy_rd       = 1'b0;
    assign w_debug_sram_dbg_clear_done    = 1'b1;

    // Legacy csr-side wr_ptr / overflow / clear_busy: derive from the
    // BRAM write pulse counter. The old clear engine is gone; the host
    // can re-program with bridge writes if needed.
    logic [31:0] r_dbg_wr_ptr;
    logic        r_dbg_overflow;
    `ALWAYS_FF_RST(aclk, unit_aresetn,
        if (`RST_ASSERTED(unit_aresetn)) begin
            r_dbg_wr_ptr   <= '0;
            r_dbg_overflow <= 1'b0;
        end else if (csr_clear_pulse) begin
            r_dbg_wr_ptr   <= '0;
            r_dbg_overflow <= 1'b0;
        end else if (w_debug_sram_dbg_bram_wr_pulse) begin
            // Each 64-bit BRAM write equals 2 host-visible 32-bit words.
            // CIRCULAR: the monbus group's write address wraps to cfg_base
            // when it reaches the window limit (overwrite-oldest), so this
            // host-visible pointer MUST wrap to 0 too -- NOT saturate. A
            // saturating pointer froze at the limit (host could never read a
            // live position again until a soft-reset). overflow is a sticky
            // "wrapped at least once" flag, not a stop.
            if (r_dbg_wr_ptr >= DEBUG_SRAM_WORDS - 32'd2) begin
                r_dbg_wr_ptr   <= 32'd0;
                r_dbg_overflow <= 1'b1;
            end else begin
                r_dbg_wr_ptr <= r_dbg_wr_ptr + 32'd2;
            end
        end
    )
    assign dbg_wr_ptr     = r_dbg_wr_ptr;
    assign dbg_overflow   = r_dbg_overflow;
    assign dbg_clear_busy = 1'b0;

    // =========================================================================
    // DMA source + sink: axi4_dma_slaves (LFSR pattern gen on AR/R,
    // CRC accumulator on AW/W/B). Wraps the previous side-by-side
    // u_rd_pattern + u_wr_crc_check pair into a single instance.
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

    // -------------------------------------------------------------------------
    // Observer fabric-side wires (f_rd_* / f_wr_*).
    //
    // axi4_intf_master_observer SNOOPS the STREAM DUT's master ports (which stay
    // on rd_*/wr_*) and the axi4_dma_slaves + axi_response_delay blocks. The
    // observer's DMA side carries rd_*/wr_*; its fabric side carries these
    // f_*. The slaves and resp-delay master sides are re-pointed to f_* below.
    //   AR/AW/W : observer drives f_* toward the slaves.
    //   R/B     : resp-delay drives f_*_r/b toward the observer.
    // -------------------------------------------------------------------------
    // Read fabric AR (observer -> slaves)
    logic [AXI_ID_WIDTH-1:0]    f_rd_arid;
    logic [ADDR_WIDTH-1:0]      f_rd_araddr;
    logic [7:0]                 f_rd_arlen;
    logic [2:0]                 f_rd_arsize;
    logic [1:0]                 f_rd_arburst;
    logic                       f_rd_arlock;
    logic [3:0]                 f_rd_arcache;
    logic [2:0]                 f_rd_arprot;
    logic [3:0]                 f_rd_arqos;
    logic [3:0]                 f_rd_arregion;
    logic [AXI_USER_WIDTH-1:0]  f_rd_aruser;
    logic                       f_rd_arvalid, f_rd_arready;
    // Read fabric R (resp-delay -> observer)
    logic [AXI_ID_WIDTH-1:0]    f_rd_rid;
    logic [DATA_WIDTH-1:0]      f_rd_rdata;
    logic [1:0]                 f_rd_rresp;
    logic                       f_rd_rlast;
    logic [AXI_USER_WIDTH-1:0]  f_rd_ruser;
    logic                       f_rd_rvalid, f_rd_rready;
    // Write fabric AW (observer -> slaves)
    logic [AXI_ID_WIDTH-1:0]    f_wr_awid;
    logic [ADDR_WIDTH-1:0]      f_wr_awaddr;
    logic [7:0]                 f_wr_awlen;
    logic [2:0]                 f_wr_awsize;
    logic [1:0]                 f_wr_awburst;
    logic                       f_wr_awlock;
    logic [3:0]                 f_wr_awcache;
    logic [2:0]                 f_wr_awprot;
    logic [3:0]                 f_wr_awqos;
    logic [3:0]                 f_wr_awregion;
    logic [AXI_USER_WIDTH-1:0]  f_wr_awuser;
    logic                       f_wr_awvalid, f_wr_awready;
    // Write fabric W (observer -> slaves)
    logic [DATA_WIDTH-1:0]      f_wr_wdata;
    logic [DATA_WIDTH/8-1:0]    f_wr_wstrb;
    logic                       f_wr_wlast;
    logic [AXI_USER_WIDTH-1:0]  f_wr_wuser;
    logic                       f_wr_wvalid, f_wr_wready;
    // Write fabric B (resp-delay -> observer)
    logic [AXI_ID_WIDTH-1:0]    f_wr_bid;
    logic [1:0]                 f_wr_bresp;
    logic [AXI_USER_WIDTH-1:0]  f_wr_buser;
    logic                       f_wr_bvalid, f_wr_bready;

    // (axi4_dma_slaves instance moved below the AW/W/B wire decls so
    // both port halves are visible at instantiation time.)

    // Optional per-beat response delay on the R channel. Bypass when
    // i_rd_resp_delay_en is 0 (zero added latency). When asserted, each beat
    // is held for RD_RESP_DELAY_CYCLES cycles before reaching u_stream.
    localparam int RD_R_PAYLOAD_W = AXI_ID_WIDTH + DATA_WIDTH + 2 + 1 + AXI_USER_WIDTH;
    logic [RD_R_PAYLOAD_W-1:0] s_rd_r_payload;
    logic [RD_R_PAYLOAD_W-1:0] m_rd_r_payload;

    assign s_rd_r_payload = {s_rd_rid, s_rd_rdata, s_rd_rresp, s_rd_rlast, s_rd_ruser};
    // Master side of the R resp-delay now feeds the observer's fabric R port
    // (f_rd_*) instead of STREAM directly; the observer drives rd_r* to STREAM.
    assign {f_rd_rid, f_rd_rdata, f_rd_rresp, f_rd_rlast, f_rd_ruser} = m_rd_r_payload;

    axi_response_delay #(
        .DATA_WIDTH (RD_R_PAYLOAD_W),
        .DELAY_W    (16),
        .CAPACITY   (RESP_DELAY_R_CAPACITY)
    ) u_rd_resp_delay (
        .aclk          (aclk),
        .aresetn(unit_aresetn),
        .i_delay_cycles(csr_rd_resp_delay_cyc),
        .s_data        (s_rd_r_payload),
        .s_valid       (s_rd_rvalid),
        .s_ready       (s_rd_rready),
        .m_data        (m_rd_r_payload),
        .m_valid       (f_rd_rvalid),
        .m_ready       (f_rd_rready)
    );

    // =========================================================================
    // DMA sink-side wire decls + axi4_dma_slaves instance (combines
    // pat_gen + crc_check; AR/R wires declared above).
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

    // --- MONITOR HARNESS: the bare DMA slaves are replaced by dma_slave_monitors
    //     (slaves + rd/wr monitors + monbus group). Its m_axil_* drives
    //     u_slave_tally.rec_* DIRECTLY -- no bridge in the record path; its
    //     s_axil_* err read goes to bridge slave slave_err. NO tally inside.
    //     w_tally_flush auto-flush pulse is shared by both tally SRAMs.
    //     (declared up with the first tally instance so both instances can use it.)
    logic         r_tally_freeze_d;
    always_ff @(posedge aclk or negedge unit_aresetn)
        if (!unit_aresetn) r_tally_freeze_d <= 1'b0;
        else               r_tally_freeze_d <= csr_freeze;
    assign w_tally_flush   = csr_freeze & ~r_tally_freeze_d;  // auto-flush on freeze rising edge

    // The bare DMA slaves. The monitors that used to be spliced INLINE here
    // (dma_slave_monitors) are gone: an in-path monitor whose table
    // saturates gates the bus, and that is what replayed 49 ARs as 367 on
    // channel 3. Observation is done by u_slave_observer below, which only
    // watches these wires.
    axi4_dma_slaves #(
        .NUM_CHANNELS  (NUM_CHANNELS),
        .AXI_ID_WIDTH  (AXI_ID_WIDTH),
        .AXI_ADDR_WIDTH(ADDR_WIDTH),
        .AXI_DATA_WIDTH(DATA_WIDTH),
        .AXI_USER_WIDTH(AXI_USER_WIDTH)
    ) u_dma_slaves (
        .aclk(aclk), .aresetn(unit_aresetn),
        .read_lfsr_reset       (csr_clear_pulse),
        .write_crc_reset       (csr_clear_pulse),
        .read_crc_value        (read_crc_value),
        .read_crc_valid        (read_crc_valid),
        .read_beat_count       (read_beat_count_per_ch),
        .read_beat_count_total (read_beat_count),
        .write_crc_value        (write_crc_value),
        .write_crc_valid        (write_crc_valid),
        .write_beat_count       (write_beat_count_per_ch),
        .write_beat_count_total (write_beat_count),
        .s_axi_arid    (f_rd_arid),   .s_axi_araddr  (f_rd_araddr),
        .s_axi_arlen   (f_rd_arlen),  .s_axi_arsize  (f_rd_arsize),
        .s_axi_arburst (f_rd_arburst),.s_axi_arlock  (f_rd_arlock),
        .s_axi_arcache (f_rd_arcache),.s_axi_arprot  (f_rd_arprot),
        .s_axi_arqos   (f_rd_arqos),  .s_axi_arregion(f_rd_arregion),
        .s_axi_aruser  (f_rd_aruser), .s_axi_arvalid (f_rd_arvalid),
        .s_axi_arready (f_rd_arready),
        .s_axi_rid     (s_rd_rid),    .s_axi_rdata   (s_rd_rdata),
        .s_axi_rresp   (s_rd_rresp),  .s_axi_rlast   (s_rd_rlast),
        .s_axi_ruser   (s_rd_ruser),  .s_axi_rvalid  (s_rd_rvalid),
        .s_axi_rready  (s_rd_rready),
        .s_axi_awid    (f_wr_awid),   .s_axi_awaddr  (f_wr_awaddr),
        .s_axi_awlen   (f_wr_awlen),  .s_axi_awsize  (f_wr_awsize),
        .s_axi_awburst (f_wr_awburst),.s_axi_awlock  (f_wr_awlock),
        .s_axi_awcache (f_wr_awcache),.s_axi_awprot  (f_wr_awprot),
        .s_axi_awqos   (f_wr_awqos),  .s_axi_awregion(f_wr_awregion),
        .s_axi_awuser  (f_wr_awuser), .s_axi_awvalid (f_wr_awvalid),
        .s_axi_awready (f_wr_awready),
        .s_axi_wdata   (f_wr_wdata),  .s_axi_wstrb   (f_wr_wstrb),
        .s_axi_wlast   (f_wr_wlast),  .s_axi_wuser   (f_wr_wuser),
        .s_axi_wvalid  (f_wr_wvalid), .s_axi_wready  (f_wr_wready),
        .s_axi_bid     (s_wr_bid),    .s_axi_bresp   (s_wr_bresp),
        .s_axi_buser   (s_wr_buser),  .s_axi_bvalid  (s_wr_bvalid),
        .s_axi_bready  (s_wr_bready),
        .busy_rd       (),
        .busy_wr       ()
    );
    // MOVED: this was declared ~160 lines BELOW its first use at the
    // slave-observer instantiation. Vivado flagged it (Synth 8-6901,
    // 'used before its declaration') and build-perf's synthesis stalls
    // immediately after that warning. The repo's decl-order CI check
    // only covers SIGNALS (implicit 1-bit nets), so a localparam used
    // ahead of its declaration passes 144 files clean.
    // =========================================================================
    // axi4_intf_master_observer (RFC Stage E option 2): snoop-only meter.
    //
    // Sits transparently between STREAM's rd_*/wr_* data masters and the
    // axi4_dma_slaves + axi_response_delay fabric (f_rd_*/f_wr_*). Both the
    // in-core STREAM monitors (USE_AXI_MONITORS=1, unchanged) and this observer
    // run simultaneously so a cosim can prove they meter equivalently.
    //
    // The observer's monbus dump/IRQ path is NOT used here — its err/write
    // FIFOs are left undrained and all central-filter cfg masks are 0. The AXI
    // taps are pure pass-through, so AXI traffic flows regardless of monbus
    // back-pressure. Only the bus-meter + latency-histogram outputs are read.
    // =========================================================================
    // The observer's channel count is FIXED at 8, independent of how many
    // channels this build actually runs.
    //
    // Every per-channel readback array below is sized by it, and those arrays
    // are what the CSR block exposes -- so letting it track NUM_CHANNELS makes
    // the register LAYOUT change with the build. The host reads these by name
    // from a generated map, and a layout that moves under it is exactly how the
    // perf counters silently read zero once before (monitor 0x1000 relocation).
    // Fixing it at 8 costs a few unused per-channel counters in a 4-channel
    // build -- they simply read 0 -- and buys one register map for every build.
    //
    // 8 is also the design ceiling: stream_top_ch8, and PERF_CH_SEL.CH_SEL is a
    // 3-bit field, so no build can exceed it.
    localparam int OBS_NUM_CHANNELS = 8;



    // SLAVE-ROLE observer on the DMA SLAVES' port (f_rd_*/f_wr_*). Pure snoop: every AXI4
    // port below is an INPUT, so unlike the block it replaces it cannot gate
    // or corrupt the bus no matter how full its tables get. Together with
    // u_dma_observer (master role) on STREAM's own port, this is what
    // exercises all four axi4 monitor flavours -- master rd/wr and slave
    // rd/wr -- which is the point of the build-mon configuration.
    axi4_intf_slave_observer #(
        .NUM_RD_PORTS        (1),
        .NUM_WR_PORTS        (1),
        .ADDR_WIDTH          (ADDR_WIDTH),
        .DATA_WIDTH          (DATA_WIDTH),
        .AXI_ID_WIDTH        (AXI_ID_WIDTH),
        .AXI_USER_WIDTH      (AXI_USER_WIDTH),
        .MAX_TRANSACTIONS    (OBS_MAX_TRANSACTIONS),
        .NUM_BANKS           (OBS_NUM_BANKS),
        .USE_WDATA_ORDER_Q   (OBS_USE_WDATA_ORDER_Q),
        .ACLK_MHZ            (OBS_ACLK_MHZ),
        // AXIL egress: the harness tally path consumes m_axil_*.
        .EGRESS_AXIL         (1'b1),
        .ENABLE_MON_TAPS     (OBS_ENABLE_MON_TAPS),
        // Reporter cones. ENABLE_MON_TAPS arms the CAM; these BUILD the logic
        // that turns a tracked transaction into a packet. Both are needed: with
        // the cones compiled out the observer tracks transactions and emits
        // nothing, which is exactly how both observers sat -- monbus groups
        // wired up, monitors enabled, mon_valid flat at 0 for a whole run.
        // Threshold/debug stay out: their runtime cfg_*_enable is tied low
        // inside the observer, so building them would be dead area.
        .TAP_ENABLE_ERROR_LOGIC   (OBS_ENABLE_MON_TAPS),
        .TAP_ENABLE_TIMEOUT_LOGIC (OBS_ENABLE_MON_TAPS),
        .TAP_ENABLE_COMPL_LOGIC   (OBS_ENABLE_MON_TAPS),
        .ENABLE_BUS_METER    (0),
        .ENABLE_LATENCY_HIST (0),
        .NUM_CHANNELS        (OBS_NUM_CHANNELS),
        .UNIT_ID             (8'h11),
        // Address-range checker: 4 ranges, matching the in-core monitors'
        // MON_N_ADDR_RANGES(4). The default is 0, which compiles the checker
        // OUT -- and since the observer rewire made the tallies observer-fed,
        // a compiled-out checker means NO AddrMatch packet can ever reach a
        // tally. test_stream_mon_profile asserted on exactly those bins and
        // was unsatisfiable by construction, not failing on a bug.
        .N_ADDR_RANGES       (4)
    ) u_slave_observer (
        .aclk    (aclk),
        .aresetn (unit_aresetn),
        .cam_clear(csr_cam_clear),
        .obs_rd_arid     (f_rd_arid),
        .obs_rd_araddr   (f_rd_araddr),
        .obs_rd_arlen    (f_rd_arlen),
        .obs_rd_arsize   (f_rd_arsize),
        .obs_rd_arburst  (f_rd_arburst),
        .obs_rd_arlock   (f_rd_arlock),
        .obs_rd_arcache  (f_rd_arcache),
        .obs_rd_arprot   (f_rd_arprot),
        .obs_rd_arqos    (f_rd_arqos),
        .obs_rd_arregion (f_rd_arregion),
        .obs_rd_aruser   (f_rd_aruser),
        .obs_rd_arvalid  (f_rd_arvalid),
        .obs_rd_arready  (f_rd_arready),
        .obs_rd_rid      (f_rd_rid),
        .obs_rd_rdata    (f_rd_rdata),
        .obs_rd_rresp    (f_rd_rresp),
        .obs_rd_rlast    (f_rd_rlast),
        .obs_rd_ruser    (f_rd_ruser),
        .obs_rd_rvalid   (f_rd_rvalid),
        .obs_rd_rready   (f_rd_rready),
        .obs_wr_awid     (f_wr_awid),
        .obs_wr_awaddr   (f_wr_awaddr),
        .obs_wr_awlen    (f_wr_awlen),
        .obs_wr_awsize   (f_wr_awsize),
        .obs_wr_awburst  (f_wr_awburst),
        .obs_wr_awlock   (f_wr_awlock),
        .obs_wr_awcache  (f_wr_awcache),
        .obs_wr_awprot   (f_wr_awprot),
        .obs_wr_awqos    (f_wr_awqos),
        .obs_wr_awregion (f_wr_awregion),
        .obs_wr_awuser   (f_wr_awuser),
        .obs_wr_awvalid  (f_wr_awvalid),
        .obs_wr_awready  (f_wr_awready),
        .obs_wr_wdata    (f_wr_wdata),
        .obs_wr_wstrb    (f_wr_wstrb),
        .obs_wr_wlast    (f_wr_wlast),
        .obs_wr_wuser    (f_wr_wuser),
        .obs_wr_wvalid   (f_wr_wvalid),
        .obs_wr_wready   (f_wr_wready),
        .obs_wr_bid      (f_wr_bid),
        .obs_wr_bresp    (f_wr_bresp),
        .obs_wr_buser    (f_wr_buser),
        .obs_wr_bvalid   (f_wr_bvalid),
        .obs_wr_bready   (f_wr_bready),
        .s_apb_psel   (slvmon_apb_PSEL),    .s_apb_penable(slvmon_apb_PENABLE),
        .s_apb_pready (slvmon_apb_PREADY),  .s_apb_paddr  (slvmon_apb_PADDR[11:0]),
        .s_apb_pwrite (slvmon_apb_PWRITE),  .s_apb_pwdata (slvmon_apb_PWDATA),
        .s_apb_pstrb  (slvmon_apb_PSTRB),   .s_apb_prdata (slvmon_apb_PRDATA),
        .s_apb_pslverr(slvmon_apb_PSLVERR),
        .s_axil_arvalid(se_arvalid), .s_axil_arready(se_arready),
        .s_axil_araddr (se_araddr),  .s_axil_arprot (se_arprot),
        .s_axil_rvalid (se_rvalid),  .s_axil_rready (se_rready),
        .s_axil_rdata  (se_rdata),   .s_axil_rresp  (se_rresp),
        .m_axil_awvalid(slmon_awvalid), .m_axil_awready(slmon_awready),
        .m_axil_awaddr (slmon_awaddr),  .m_axil_awprot (slmon_awprot),
        .m_axil_wvalid (slmon_wvalid),  .m_axil_wready (slmon_wready),
        .m_axil_wdata  (slmon_wdata),   .m_axil_wstrb  (slmon_wstrb),
        .m_axil_bvalid (slmon_bvalid),  .m_axil_bready (slmon_bready),
        .m_axil_bresp  (slmon_bresp),
        .irq_out       (),
        // Meters and histograms are DISABLED on this observer
        // (ENABLE_BUS_METER=0 / ENABLE_LATENCY_HIST=0) -- the master-role
        // observer already provides them and duplicating costs area on a
        // 325T that is already the reason this build is 4 channels. The
        // ports still exist, so connect them EXPLICITLY: an omitted pin is
        // PINMISSING, which Verilator escalates to an error.
        .cfg_rd_rid_per_channel      (),
        .cfg_rd_rid_per_channel_valid(),
        .i_meter_clear               (),
        .i_meter_freeze              (),
        .m_axi_awaddr                (),
        .m_axi_awburst               (),
        .m_axi_awcache               (),
        .m_axi_awid                  (),
        .m_axi_awlen                 (),
        .m_axi_awlock                (),
        .m_axi_awprot                (),
        .m_axi_awqos                 (),
        .m_axi_awready               (),
        .m_axi_awregion              (),
        .m_axi_awsize                (),
        .m_axi_awuser                (),
        .m_axi_awvalid               (),
        .m_axi_bid                   (),
        .m_axi_bready                (),
        .m_axi_bresp                 (),
        .m_axi_buser                 (),
        .m_axi_bvalid                (),
        .m_axi_wdata                 (),
        .m_axi_wlast                 (),
        .m_axi_wready                (),
        .m_axi_wstrb                 (),
        .m_axi_wuser                 (),
        .m_axi_wvalid                (),
        .obs_wr_active_ch_id         (),
        .obs_wr_active_ch_valid      ()
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
    // Master side of the B resp-delay now feeds the observer's fabric B port
    // (f_wr_b*) instead of STREAM directly; the observer drives wr_b* to STREAM.
    assign {f_wr_bid, f_wr_bresp, f_wr_buser} = m_wr_b_payload;

    axi_response_delay #(
        .DATA_WIDTH (WR_B_PAYLOAD_W),
        .DELAY_W    (16),
        .CAPACITY   (RESP_DELAY_B_CAPACITY)
    ) u_wr_resp_delay (
        .aclk          (aclk),
        .aresetn(unit_aresetn),
        .i_delay_cycles(csr_wr_resp_delay_cyc),
        .s_data        (s_wr_b_payload),
        .s_valid       (s_wr_bvalid),
        .s_ready       (s_wr_bready),
        .m_data        (m_wr_b_payload),
        .m_valid       (f_wr_bvalid),
        .m_ready       (f_wr_bready)
    );


    // Must follow the OBSERVER's channel count, not the build's: it sizes
    // obs_wr_active_ch_id, which connects to a port whose width the observer
    // derives from its own NUM_CHANNELS (now fixed at 8). Deriving it from the
    // build's NUM_CHANNELS made a 4-channel build 2 bits against the
    // observer's 3.
    localparam int OBS_CW            = (OBS_NUM_CHANNELS > 1) ? $clog2(OBS_NUM_CHANNELS) : 1;
    // Observer capacity, derived from what STREAM can actually put in flight.
    // The observer must track everything the DMA can initiate: anything it
    // cannot track it either blocks (perturbing the measurement) or silently
    // drops (corrupting it). Both failure modes are invisible in the numbers
    // the host reads back, which is why these are derived and not chosen.
    localparam int OBS_MAX_OUTSTANDING =
        (AR_MAX_OUTSTANDING > AW_MAX_OUTSTANDING) ? AR_MAX_OUTSTANDING
                                                  : AW_MAX_OUTSTANDING;
    localparam int OBS_TRANS_MARGIN  = 8;   // reporting backlog, not concurrency


    localparam int OBS_HIST_NUM_BINS = 16;
    localparam int OBS_HIST_BINW     = (OBS_HIST_NUM_BINS > 1) ? $clog2(OBS_HIST_NUM_BINS) : 1;

    // ---- Observer measurement-window controller -----------------------------
    // Replicates stream_core's in-core perf-window "arm-gap" controller: open
    // the window on first DMA activity, close it 16 idle cycles after the DMA
    // goes quiet. Driven by STREAM's per-channel scheduler-idle vector (taken
    // out of u_stream's debug_hwif_scheduler_idle just below).
    logic [7:0] obs_sched_idle;  // STREAM scheduler-idle (observability/waves)
    // Busy = any live AXI activity on STREAM's rd/wr bus. This is independent of
    // NUM_CHANNELS (unlike ~scheduler_idle, whose disabled-channel bits read 0 =
    // "active" and would wedge the window open on a <8-channel build), and it
    // freezes cleanly once the workload goes quiet so the cosim gets a stable
    // read. The bucket TOTALS we compare (productive / beats / bursts / byte /
    // histograms) are window-position-independent as long as the window brackets
    // the workload, so the exact window basis vs the in-core one does not matter.
    logic       obs_busy;
    assign obs_busy = rd_arvalid | rd_rvalid | wr_awvalid | wr_wvalid | wr_bvalid;
    logic       obs_win_active, obs_started;
    logic [4:0] obs_settle;
    logic       obs_meter_clear, obs_meter_freeze;
    `ALWAYS_FF_RST(aclk, unit_aresetn,
        if (`RST_ASSERTED(unit_aresetn)) begin
            obs_win_active <= 1'b0; obs_started <= 1'b0; obs_settle <= 5'd0;
        end else begin
            if (obs_busy && !obs_win_active && !obs_started) begin
                obs_win_active <= 1'b1; obs_started <= 1'b1; obs_settle <= 5'd0;
            end else if (obs_win_active) begin
                if (obs_busy) begin
                    obs_settle <= 5'd0;
                end else if (obs_settle != 5'd16) begin
                    obs_settle <= obs_settle + 5'd1;
                end else begin
                    // Settle timeout: 16 idle cycles after the last bus activity
                    // CLOSE the measurement window so obs_meter_freeze asserts and
                    // the starvation/idle buckets stop accumulating during the
                    // post-workload idle (otherwise prod/(bucket-sum) util is
                    // diluted by unbounded idle). prod is unaffected -- it stops
                    // on its own when data transfer ends. obs_started stays set,
                    // so the window reopens only on the next soft-reset: exactly
                    // one clean, frozen window per measured workload, read back by
                    // the host over CSR (CSR_OBS_* @ HARNESS_CSR_BASE + 0x100).
                    obs_win_active <= 1'b0;
                end
            end
        end
    )
    assign obs_meter_clear  = obs_busy && !obs_win_active && !obs_started; // 1-cycle open pulse
    assign obs_meter_freeze = ~obs_win_active;

    // ---- Read-side rid -> channel-id map (STREAM drives arid = channel) -----
    logic [AXI_ID_WIDTH-1:0] obs_cfg_rd_rid       [1][OBS_NUM_CHANNELS];
    logic                    obs_cfg_rd_rid_valid [1][OBS_NUM_CHANNELS];
    always_comb begin
        // Map every readback slot, but mark VALID only the channels this
        // build runs -- slots >= NUM_CHANNELS exist in the map and read 0.
        for (int c = 0; c < OBS_NUM_CHANNELS; c++) begin
            obs_cfg_rd_rid[0][c]       = AXI_ID_WIDTH'(c);
            obs_cfg_rd_rid_valid[0][c] = (c < NUM_CHANNELS);
        end
    end

    // ---- Write-side channel sideband: unused (WR_CH_FROM_AWID=1) -------------
    logic [OBS_CW-1:0] obs_wr_active_ch_id    [1];
    logic              obs_wr_active_ch_valid [1];
    assign obs_wr_active_ch_id[0]    = '0;
    assign obs_wr_active_ch_valid[0] = 1'b0;

    // ---- Histogram readout selectors (driven by harness_csr @ 0x120) --------
    // CSR packs the selector as {bin[5:2], metric[1], bus[0]}: bus picks the
    // read- vs write-side observer port, metric picks which latency metric,
    // and bin indexes the 16-entry log2 histogram. The selected count/total
    // are muxed back to the CSR at 0x124/0x128 (obs_hist_*_mux declared up by
    // the u_csr instance; obs_hist_sel likewise driven from u_csr).
    // obs_hist_{bus,metric,bin} removed with obs_hist_sel: they decoded a
    // selector nothing consumed. The observer selects its own histogram from
    // OBS_STAT_SEL in its regblock.

    // ---- Observer meter + histogram outputs (aggregate nets declared by the
    //      u_csr instance above; per-channel + histogram nets declared here) ---
    logic [15:0]               obs_rd_ch_prod     [1][OBS_NUM_CHANNELS];
    logic [15:0]               obs_rd_ch_bp       [1][OBS_NUM_CHANNELS];
    logic [15:0]               obs_rd_ch_starv    [1][OBS_NUM_CHANNELS];
    logic [15:0]               obs_rd_ch_idle     [1][OBS_NUM_CHANNELS];
    logic [OBS_NUM_CHANNELS*4-1:0] obs_rd_ch_overflow [1];
    logic [15:0]               obs_wr_ch_prod     [1][OBS_NUM_CHANNELS];
    logic [15:0]               obs_wr_ch_bp       [1][OBS_NUM_CHANNELS];
    logic [15:0]               obs_wr_ch_starv    [1][OBS_NUM_CHANNELS];
    logic [15:0]               obs_wr_ch_idle     [1][OBS_NUM_CHANNELS];
    logic [OBS_NUM_CHANNELS*4-1:0] obs_wr_ch_overflow [1];
    logic                      obs_hist_sample_lost;
    // NO harness-side histogram mirror. obs_{rd,wr}_hist_{count,total}[1] and
    // the two muxes that read them used to live here, feeding harness_csr
    // 0x124/0x128.
    //
    // They were dead in three independent ways at once, which is why nothing
    // complained: the arrays were DECLARED AND NEVER CONNECTED (the observer
    // exposes no hist_count/hist_total output ports at all -- its histogram is
    // reachable only through OBS_STAT_SEL/OBS_STAT_DATA in its own regblock);
    // the muxes reading them were consumed NOWHERE; and their destination
    // CSRs had been retired. UNDRIVEN and UNUSED are both in LINT_WAIVERS on a
    // board top, so lint saw none of it.
    //
    // Found in the WAVEFORM, not by reading code: a build-perf dma_4ch run
    // shows obs_wr_hist_total[0] flat at 0 while the observer's own
    // wr_hist_total[0] reaches 256 -- exactly the 256 awlen=15 write bursts on
    // the bus. Anyone reconnecting 0x124/0x128 to these nets would have wired
    // a register to a constant zero.


    // ---- STREAM master <-> fabric, wired STRAIGHT THROUGH ----------------
    // These used to run through u_dma_observer, which meant the instrument
    // was in the datapath and its block_ready could gate the DMA. The
    // observer is a snoop now, so the connection is direct and the
    // observer cannot affect what it measures.
    assign f_rd_arid     = rd_arid;
    assign f_rd_araddr   = rd_araddr;
    assign f_rd_arlen    = rd_arlen;
    assign f_rd_arsize   = rd_arsize;
    assign f_rd_arburst  = rd_arburst;
    assign f_rd_arlock   = rd_arlock;
    assign f_rd_arcache  = rd_arcache;
    assign f_rd_arprot   = rd_arprot;
    assign f_rd_arqos    = rd_arqos;
    assign f_rd_arregion = rd_arregion;
    assign f_rd_aruser   = rd_aruser;
    assign f_rd_arvalid  = rd_arvalid;
    assign rd_arready   = f_rd_arready;
    assign rd_rid      = f_rd_rid;
    assign rd_rdata    = f_rd_rdata;
    assign rd_rresp    = f_rd_rresp;
    assign rd_rlast    = f_rd_rlast;
    assign rd_ruser    = f_rd_ruser;
    assign rd_rvalid   = f_rd_rvalid;
    assign f_rd_rready  = rd_rready;
    assign f_wr_awid     = wr_awid;
    assign f_wr_awaddr   = wr_awaddr;
    assign f_wr_awlen    = wr_awlen;
    assign f_wr_awsize   = wr_awsize;
    assign f_wr_awburst  = wr_awburst;
    assign f_wr_awlock   = wr_awlock;
    assign f_wr_awcache  = wr_awcache;
    assign f_wr_awprot   = wr_awprot;
    assign f_wr_awqos    = wr_awqos;
    assign f_wr_awregion = wr_awregion;
    assign f_wr_awuser   = wr_awuser;
    assign f_wr_awvalid  = wr_awvalid;
    assign f_wr_wdata    = wr_wdata;
    assign f_wr_wstrb    = wr_wstrb;
    assign f_wr_wlast    = wr_wlast;
    assign f_wr_wuser    = wr_wuser;
    assign f_wr_wvalid   = wr_wvalid;
    assign wr_awready   = f_wr_awready;
    assign wr_wready    = f_wr_wready;
    assign wr_bid      = f_wr_bid;
    assign wr_bresp    = f_wr_bresp;
    assign wr_buser    = f_wr_buser;
    assign wr_bvalid   = f_wr_bvalid;
    assign f_wr_bready  = wr_bready;

    axi4_intf_master_observer #(
        .NUM_RD_PORTS        (1),
        .NUM_WR_PORTS        (1),
        .ADDR_WIDTH          (ADDR_WIDTH),
        .DATA_WIDTH          (DATA_WIDTH),
        .AXI_ID_WIDTH        (AXI_ID_WIDTH),
        .AXI_USER_WIDTH      (AXI_USER_WIDTH),
        .OBS_AXI_ID_WIDTH    (4),
        .MAX_BURST_BEATS     (64),
        .USE_COMPRESSION     (0),
        .EGRESS_AXIL         (1'b1),
        // Size to EVERYTHING THE DMA CAN INITIATE, not to a nominal 16.
        //
        // The observer instantiates axi4_master_{rd,wr}_mon with
        // cfg_monitor_enable hardwired to 1, so their block_ready really does
        // gate dma_rd_arready / dma_wr_awready. At 16 that means the observer
        // BACKPRESSURES the DMA at 16 outstanding while STREAM is built for
        // NUM_CHANNELS x {AR,AW}_MAX_OUTSTANDING = 8 x 8 = 64 -- so the perf
        // build was measuring a throttled DMA and calling it the DMA's
        // performance. An instrument must not be the bottleneck.
        //
        // Two ways to stop the observer throttling, and the CAM cannot take the
        // first one: sizing it for the real concurrency means 8*8+8 = 72
        // entries, and this CAM does not scale -- measured 16 entries at
        // WNS +1.018 ns, 40 entries at WNS -25.183 ns. 72 will not close.
        //
        // So the monitor taps are switched OFF here instead
        // (ENABLE_MON_TAPS=0). That removes the command-channel gate entirely,
        // which is what a perf build wants, and the CAM stops being on the
        // critical path. The latency histograms and bus meters sit outside that
        // gate and keep counting, sized per-channel below.
        //
        // MAX_TRANSACTIONS is now only the depth of a disabled tap; kept small.
        // If the error/completion monbus stream is ever wanted from the
        // observer, ENABLE_MON_TAPS must go to 1 AND this must be sized for
        // NUM_CHANNELS * OBS_MAX_OUTSTANDING -- at which point the timing above
        // is the problem to solve, not something to discover in the lab.
        // Tied to the build flavor, NOT hardcoded -- this is the one shared
        // stream_harness.sv and build-mon still wants the observer's monbus
        // stream. USE_AXI_MONITORS=0 (build-perf) => taps off, no gate, no
        // throttle. USE_AXI_MONITORS=1 (build-mon) => taps on, as before.
        .ENABLE_MON_TAPS     (OBS_ENABLE_MON_TAPS),
        // Reporter cones. ENABLE_MON_TAPS arms the CAM; these BUILD the logic
        // that turns a tracked transaction into a packet. Both are needed: with
        // the cones compiled out the observer tracks transactions and emits
        // nothing, which is exactly how both observers sat -- monbus groups
        // wired up, monitors enabled, mon_valid flat at 0 for a whole run.
        // Threshold/debug stay out: their runtime cfg_*_enable is tied low
        // inside the observer, so building them would be dead area.
        .TAP_ENABLE_ERROR_LOGIC   (OBS_ENABLE_MON_TAPS),
        .TAP_ENABLE_TIMEOUT_LOGIC (OBS_ENABLE_MON_TAPS),
        .TAP_ENABLE_COMPL_LOGIC   (OBS_ENABLE_MON_TAPS),
        .MAX_TRANSACTIONS    (OBS_MAX_TRANSACTIONS),
        .NUM_BANKS           (OBS_NUM_BANKS),
        .USE_WDATA_ORDER_Q   (OBS_USE_WDATA_ORDER_Q),
        .ACLK_MHZ            (OBS_ACLK_MHZ),
        .ENABLE_BUS_METER    (1),
        .WR_CH_FROM_AWID     (1),
        .NUM_CHANNELS        (OBS_NUM_CHANNELS),
        .ENABLE_LATENCY_HIST (1),
        .HIST_NUM_BINS       (OBS_HIST_NUM_BINS),
        // Per-channel timestamp FIFO. STREAM drives arid/awid = channel, so
        // this must cover the per-channel outstanding limit, not the total.
        // It happened to equal 8 while both were 8; deriving it keeps them
        // tied if either moves. Undersized here, axi_perf_latency_hist drops
        // the timestamp with no flag and the completion pops someone else's,
        // so totals undercount AND the surviving latencies are misattributed.
        .HIST_MAX_OUTSTANDING(OBS_MAX_OUTSTANDING),
        // Address-range checker: 4 ranges, matching the in-core monitors'
        // MON_N_ADDR_RANGES(4). The default is 0, which compiles the checker
        // OUT -- and since the observer rewire made the tallies observer-fed,
        // a compiled-out checker means NO AddrMatch packet can ever reach a
        // tally. test_stream_mon_profile asserted on exactly those bins and
        // was unsatisfiable by construction, not failing on a bug.
        .N_ADDR_RANGES       (4)
    ) u_dma_observer (
        .aclk    (aclk),
        .aresetn (unit_aresetn),
        .cam_clear (1'b0),

        // ---- Read tap: DMA side = STREAM (rd_*) -----------------------------
        // ---- Observation taps: INPUTS ONLY, all off STREAM's OWN master
        // ---- port (rd_*/wr_*). The slave-role observer hangs off the DMA
        // ---- slaves' port (f_rd_*/f_wr_*) instead, so each observer is
        // ---- attached to exactly ONE endpoint. Those two net groups are a
        // ---- straight wire today, so this is electrically a no-op -- but
        // ---- mixing them would quietly stop being a no-op the moment
        // ---- anything (a crossbar, a width converter) is inserted between
        // ---- STREAM and the slaves, and the two observers would then be
        // ---- reporting the same side of it.
        // ---- The observer no longer
        // ---- sits in the path; it watches the wires assigned below.
        // ---- (vault/handbook/design/observers-do-not-drive.md)
        .obs_rd_arid    (rd_arid),
        .obs_rd_araddr  (rd_araddr),
        .obs_rd_arlen   (rd_arlen),
        .obs_rd_arsize  (rd_arsize),
        .obs_rd_arburst (rd_arburst),
        .obs_rd_arlock  (rd_arlock),
        .obs_rd_arcache (rd_arcache),
        .obs_rd_arprot  (rd_arprot),
        .obs_rd_arqos   (rd_arqos),
        .obs_rd_arregion(rd_arregion),
        .obs_rd_aruser  (rd_aruser),
        .obs_rd_arvalid (rd_arvalid),
        .obs_rd_arready (rd_arready),
        .obs_rd_rid     (rd_rid),
        .obs_rd_rdata   (rd_rdata),
        .obs_rd_rresp   (rd_rresp),
        .obs_rd_rlast   (rd_rlast),
        .obs_rd_ruser   (rd_ruser),
        .obs_rd_rvalid  (rd_rvalid),
        .obs_rd_rready  (rd_rready),
        .obs_wr_awid    (wr_awid),
        .obs_wr_awaddr  (wr_awaddr),
        .obs_wr_awlen   (wr_awlen),
        .obs_wr_awsize  (wr_awsize),
        .obs_wr_awburst (wr_awburst),
        .obs_wr_awlock  (wr_awlock),
        .obs_wr_awcache (wr_awcache),
        .obs_wr_awprot  (wr_awprot),
        .obs_wr_awqos   (wr_awqos),
        .obs_wr_awregion(wr_awregion),
        .obs_wr_awuser  (wr_awuser),
        .obs_wr_awvalid (wr_awvalid),
        .obs_wr_wdata   (wr_wdata),
        .obs_wr_wstrb   (wr_wstrb),
        .obs_wr_wlast   (wr_wlast),
        .obs_wr_wuser   (wr_wuser),
        .obs_wr_wvalid  (wr_wvalid),
        .obs_wr_awready (wr_awready),
        .obs_wr_wready  (wr_wready),
        .obs_wr_bid     (wr_bid),
        .obs_wr_bresp   (wr_bresp),
        .obs_wr_buser   (wr_buser),
        .obs_wr_bvalid  (wr_bvalid),
        .obs_wr_bready  (wr_bready),
        // Channel-active sideband: an INPUT to the observer, not a bus
        // signal. Kept when the pass-through pairs went away.
        .obs_wr_active_ch_id          (obs_wr_active_ch_id),
        .obs_wr_active_ch_valid       (obs_wr_active_ch_valid),
        // Read tap: fabric side = slaves / resp-delay (rd_*)

        // ---- Write tap: DMA side = STREAM (wr_*) ----------------------------
        // Write tap: fabric side = slaves / resp-delay (wr_*)

        // ---- Observability dump path: UNUSED (held idle/legal) --------------
        // AXIL slave-read drain: no host reads -> tie request inputs idle.
        .s_axil_arvalid (1'b0),
        .s_axil_arready (),
        .s_axil_araddr  ('0),
        .s_axil_arprot  ('0),
        .s_axil_rvalid  (),
        .s_axil_rready  (1'b0),
        .s_axil_rdata   (),
        .s_axil_rresp   (),
        // AXI4 bulk-trace master-write: no memory ring -> tie responses idle.
        .m_axi_awid     (),
        .m_axi_awaddr   (),
        .m_axi_awlen    (),
        .m_axi_awsize   (),
        .m_axi_awburst  (),
        .m_axi_awlock   (),
        .m_axi_awcache  (),
        .m_axi_awprot   (),
        .m_axi_awqos    (),
        .m_axi_awregion (),
        .m_axi_awuser   (),
        .m_axi_awvalid  (),
        .m_axi_awready  (1'b0),
        .m_axi_wdata    (),
        .m_axi_wstrb    (),
        .m_axi_wlast    (),
        .m_axi_wuser    (),
        .m_axi_wvalid   (),
        .m_axi_wready   (1'b0),
        .m_axi_bid      ('0),
        .m_axi_bresp    ('0),
        .m_axi_buser    (1'b0),
        .m_axi_bvalid   (1'b0),
        .m_axi_bready   (),
        .irq_out        (),

        // ---- Configuration: the observer's OWN APB regblock ----------------
        // 29 tie-offs used to live here, which meant the harness had to know
        // this block's internals and no host could change any of it at runtime.
        // Config is local to the observer now (obs_regs @ obs_apb); the harness
        // just routes a bridge slave to it.
        .s_apb_psel   (obs_apb_PSEL),    .s_apb_penable(obs_apb_PENABLE),
        .s_apb_pready (obs_apb_PREADY),  .s_apb_paddr  (obs_apb_PADDR[11:0]),
        .s_apb_pwrite (obs_apb_PWRITE),  .s_apb_pwdata (obs_apb_PWDATA),
        .s_apb_pstrb  (obs_apb_PSTRB),   .s_apb_prdata (obs_apb_PRDATA),
        .s_apb_pslverr(obs_apb_PSLVERR),

        // ---- Meter window + channel maps ------------------------------------
        .i_meter_clear        (obs_meter_clear),
        .i_meter_freeze       (obs_meter_freeze),
        .cfg_rd_rid_per_channel       (obs_cfg_rd_rid),
        .cfg_rd_rid_per_channel_valid (obs_cfg_rd_rid_valid),

        // ---- Meter outputs --------------------------------------------------

        // ---- Latency-histogram readout + outputs ----------------------------
        // Sizing self-check: asserts if a latency timestamp was ever dropped,
        // i.e. the observer is too small for what STREAM can initiate and the
        // histogram totals read low. Should be 0 by construction now that the
        // depths are derived; surfaced so it cannot regress silently.
        // AXIL dump master: this observer's monbus group drives u_stream_tally's
        // rec_* port DIRECTLY (see dmamon_*), with no bridge in between. The
        // m_axi_* AXI4 egress is the one tied off here, since EGRESS_AXIL=1
        // builds the AXIL group. Both port sets exist regardless of the
        // parameter, so connect explicitly rather than leaving them PINMISSING.
        .m_axil_awaddr   (dmamon_awaddr),
        .m_axil_awprot   (dmamon_awprot),
        .m_axil_awready  (dmamon_awready),
        .m_axil_awvalid  (dmamon_awvalid),
        .m_axil_bready   (dmamon_bready),
        .m_axil_bresp    (dmamon_bresp),
        .m_axil_bvalid   (dmamon_bvalid),
        .m_axil_wdata    (dmamon_wdata),
        .m_axil_wready   (dmamon_wready),
        .m_axil_wstrb    (dmamon_wstrb),
        .m_axil_wvalid   (dmamon_wvalid)
    );

    // =========================================================================
    // STREAM DUT
    // =========================================================================
    stream_top_ch8 #(
        .NUM_CHANNELS       (NUM_CHANNELS),
        .DATA_WIDTH         (DATA_WIDTH),
        .ADDR_WIDTH         (ADDR_WIDTH),
        .USE_ROW_COL_MAJOR_ADDRESSING (USE_ROW_COL_MAJOR_ADDRESSING),
        .SRAM_DEPTH         (SRAM_DEPTH),
        .APB_ADDR_WIDTH     (APB_ADDR_WIDTH),
        .APB_DATA_WIDTH     (APB_DATA_WIDTH),
        .AXI_ID_WIDTH       (AXI_ID_WIDTH),
        .AXI_USER_WIDTH     (AXI_USER_WIDTH),
        // Monitors compiled OUT of STREAM (param=0). Utilization is measured by
        // the perf-only module in the harness (external to STREAM), so STREAM's
        // in-core AXI monitors, MonBus compression/half-beat, and all DESC-monitor
        // cones (including PERF) are dead weight here -- and at 8 channels with
        // TASK-101 extended addressing enabled they overflow the xc7a100t LUTs.
        // Removing them (param=0) reclaims the LUTs; the addr-gen logic stays.
        .USE_AXI_MONITORS   (USE_AXI_MONITORS),
        .MON_NUM_BANKS      (MON_NUM_BANKS),
        // Monitor-validation harness: build the in-core address-range checker
        // (4 ranges per rd/wr monitor; ranges 2,3 = ERROR allowlist, 0,1 = DEBUG).
        // Harmless when USE_AXI_MONITORS=0 (the monitor wrapper omits the checker).
        .MON_N_ADDR_RANGES  (4),
        .MON_ADDR_RANGE_IS_ERROR (4'b1100),
        .USE_MON_COMPRESSION(0),
        .USE_MON_HALFBEAT   (0),
        .CDC_ENABLE         (0),
        .AR_MAX_OUTSTANDING (AR_MAX_OUTSTANDING),
        .AW_MAX_OUTSTANDING (AW_MAX_OUTSTANDING),
        .GEN_MON            (1'b0),
        // Monitor-VALIDATION flow, "all except error" bitstream: build every
        // packet-class cone EXCEPT error on the rd/wr DATAPATH monitors -> covers
        // completion/timeout/threshold/perf/debug (+ AddrMatch). Error injection
        // is a separate bitstream (addr-range ERROR flavor). The DESC monitor
        // stays perf-only so its trans_mgr CAM is out of the timing path -- the
        // datapath monitors already cover every class.
        .DESC_MON_ENABLE_ERROR_LOGIC     (1'b0),
        .DESC_MON_ENABLE_TIMEOUT_LOGIC   (1'b0),
        .DESC_MON_ENABLE_COMPL_LOGIC     (1'b0),
        .DESC_MON_ENABLE_THRESHOLD_LOGIC (1'b0),
        .DESC_MON_ENABLE_PERF_LOGIC      (1'b1),
        .DESC_MON_ENABLE_DEBUG_LOGIC     (1'b0),
        // Cone set, from DATA_MON_CONE_MODE:
        //   0 -> error OFF, the rest ON   (legacy all-except-error)
        //   1 -> error ON,  the rest OFF  (legacy error-only)
        //   2 -> everything ON            (single-bitstream validation)
        // Expressed as two independent predicates rather than a flavour bit and
        // its inverse, because the union needs both true at once.
        .DATA_MON_ENABLE_ERROR_LOGIC     (w_data_mon_error_cone),
        .DATA_MON_ENABLE_TIMEOUT_LOGIC   (w_data_mon_main_cones),
        .DATA_MON_ENABLE_COMPL_LOGIC     (w_data_mon_main_cones),
        .DATA_MON_ENABLE_THRESHOLD_LOGIC (w_data_mon_main_cones),
        .DATA_MON_ENABLE_PERF_LOGIC      (w_data_mon_main_cones),
        .DATA_MON_ENABLE_DEBUG_LOGIC     (w_data_mon_main_cones)
    ) u_stream (
        .aclk    (aclk),   .aresetn(unit_aresetn),
        .pclk    (aclk),   .presetn(aresetn),
        .cam_clear(csr_cam_clear),

        // Kick-burst fast path (1-cycle pulse from harness_csr KICK_GO,
        // shadow addresses from CH_KICK_ADDR[ch]).

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

        // Monitor data AXIL master. Bridge master monbus_wr -> comp_sram, the
        // capture MEMORY the host downloads and diffs against the Python
        // golden. It does NOT feed a tally: the tallies belong to the observers.
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

        // MonBus compressor statistics -> harness_csr (0x1E0..0x1FC).
        .mon_compressor_stat_tier1_a        (mon_comp_tier1_a),
        .mon_compressor_stat_tier1_b        (mon_comp_tier1_b),
        .mon_compressor_stat_tier1_c        (mon_comp_tier1_c),
        .mon_compressor_stat_tier0          (mon_comp_tier0),
        .mon_compressor_stat_cam_miss       (mon_comp_cam_miss),
        .mon_compressor_stat_delta_ts_ovf   (mon_comp_delta_ts_ovf),
        .mon_compressor_stat_event_data_ovf (mon_comp_event_data_ovf),
        .mon_compressor_stat_ed_delta_ovf   (mon_comp_ed_delta_ovf),

        // Monitor capture region + flush watermark are INTERNAL MON CSRs now
        // (MON_GROUP_BASE_ADDR/LIMIT_ADDR/FLUSH_WATERMARK @ 0x1260/64/68). The
        // RDL defaults (base 0x40000, limit 0x7FFFF, watermark 0 = flush every
        // complete record) reproduce the old capture-at-debug_sram wiring, and
        // the host reprograms them by name. No cfg_mon_* port here anymore.

        // Debug outputs (unconnected at top level)
        .debug_hwif_scheduler_idle  (obs_sched_idle),
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
        // (o_wr_active_channel_* sideband ports removed from stream_top_ch8 in
        //  RFC Stage E.4; the in-core per-channel meter uses the engine sideband
        //  internally to stream_core.)
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

    // =========================================================================
    // AXI bus meters: RETIRED (RFC Stage E option 2, Stage E.4).
    // The per-cycle valid/ready bucket counters for the read R bus and write W
    // bus are now measured IN-CORE by stream_core's datapath monitors and
    // axi_bus_meter blocks, read back via the STREAM regblock perf CSRs
    // (RDMON_PERF_* @ 0x300, WRMON_PERF_* @ 0x330, per-channel @ 0x360, latency
    // histograms @ 0x378). The harness-side meters + their harness_csr readback
    // (0x100 / 0x180) were removed; equivalence to the legacy meter was proven
    // in the Stage E.1/E.2 cosim bring-up.
    // =========================================================================

    // Prevent unused signal warnings. csr_soft_reset is now consumed by
    // the unit_aresetn pulse extender above, so it's removed from here.
    /* verilator lint_off UNUSED */
    wire _unused_ok = &{1'b0,
        read_beat_count,
        csr_start_pulse,
        1'b0};
    /* verilator lint_on UNUSED */

endmodule : stream_harness
