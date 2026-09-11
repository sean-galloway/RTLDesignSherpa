// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: 2026 sean galloway
//
// Module: char_engine_harness
// Purpose: DUT-agnostic characterization harness for the LiteDRAM A/B flow.
//          It is build-perf/rtl/ddr2_char_harness.sv with the controller taken
//          out: the same UART -> AXIL bridge, the same generated 1->6 address
//          bridge (so the host program's address map is IDENTICAL), the same
//          harness_csr, the same trace SRAM slots, the same run timer and LED
//          status, and the SAME char_engine_block (chargen_regs + generator
//          array + perf meters + latency histograms) that ddr2_char_macro
//          wraps around pumice. What comes out is one AXI4 master, which
//          litedram_char_top hands to litedram_core.user_port_axi_0.
//
//          A LiteDRAM number measured through this block and a pumice number
//          measured through build-perf are therefore the same generators, the
//          same meters and the same host program -- only the controller
//          behind the AXI port differs.
//
//   UART -> uart_axil_bridge -> bridge_ddr2_char_axil
//              slave 0 ddr2_apb    : TERMINATED (LiteDRAM self-configures; the
//                                    pumice CSR writes a host may still issue
//                                    complete with PREADY=1, data 0)
//              slave 1 harness_csr : global ctrl / status / timer / perf
//              slave 2 debug_sram  : kept (host clears/reads it)
//              slave 3 dfi_mon_ram : kept (placeholder, as in build-perf)
//              slave 4 obs_apb     : terminated (expansion slot, as build-perf)
//              slave 5 chargen_apb : char_engine_block (per-generator config)
//   char_engine_block -> m_axi (AXI4 master) -> DUT
//
// The host waits on harness_csr STATUS.init_done (<= litedram_core.init_done)
// before launching generators, exactly as it waits on pumice's init.
`timescale 1ns / 1ps

`include "reset_defs.svh"

module char_engine_harness
    import pumice_pkg::*;
#(
    // ---- Board / host ----
    parameter int FPGA_CLK_HZ        = 75_000_000,   // == litedram user_clk (sys_clk_freq)
    parameter int UART_BAUD          = 115_200,
    parameter int LED_UPDATE_HZ      = 200,
    parameter int SEVEN_SEG_REFRESH  = 1_000,

    // ---- Trace SRAM slots (same sizes as build-perf) ----
    parameter int DEBUG_SRAM_WORDS   = 512,
    parameter int DFI_MON_RAM_WORDS  = 512,

    // ---- AXI4 (matches char_engine_block / litedram user port) ----
    parameter int AXI_ADDR_WIDTH     = 32,   // engine addr; top wires [26:0] to litedram
    parameter int AXI_DATA_WIDTH     = 64,
    parameter int AXI_ID_WIDTH       = 8,    // engines slice cfg_axi_id[7:0]; must be 8
    parameter int AXI_USER_WIDTH     = 8,
    parameter int AXI_STRB_WIDTH     = AXI_DATA_WIDTH / 8,

    // ---- APB (chargen window) ----
    parameter int APB_ADDR_WIDTH     = 12,
    parameter int APB_DATA_WIDTH     = 32,
    parameter int APB_STRB_WIDTH     = APB_DATA_WIDTH / 8,
    parameter int APB_PROT_WIDTH     = 3,

    // ---- Engine cfg widths ----
    parameter int STRIDE_WIDTH       = 24,
    parameter int TXN_COUNT_WIDTH    = 16,
    parameter int INDEX_WIDTH        = 16,
    parameter int BURST_LEN_WIDTH    = 8,
    // Legal-AxLEN quantum (AXI beats per DRAM burst). Board x16 BL4 / host-64
    // = 1 (unconstrained). Threaded from the top like build-perf.
    parameter int BURST_LEN_MULTIPLE = 1,
    parameter int NUM_BANKS          = 8,
    parameter int NUM_GEN            = 2,
    // Width of the IDs leaving the harness. char_gen_unit prepends the
    // generator index to every ID (BRIDGE-016 shape), so the m_axi side is one
    // bit wider than the generators' own at NUM_GEN=2. The LiteDRAM user port
    // must be generated at this width -- litedram_hp.yml id_width.
    parameter int M_AXI_ID_WIDTH     = AXI_ID_WIDTH
                                       + ((NUM_GEN > 1) ? $clog2(NUM_GEN) : 0),
    // Per-generator ceiling on bursts in flight (AW/AR issued minus B/RLAST
    // received). 32, not 8, because this is the axis the latency sweep walks:
    // read bandwidth is bounded by outstanding x AxLEN / (latency + AxLEN),
    // so the knee sits near 47/AxLEN transactions -- about 47 at AxLEN=1 and
    // 13 at AxLEN=4. A ceiling of 8 put every knee below the ceiling, which
    // made the harness the limit rather than the DRAM.
    //
    // Build at the ceiling and dial DOWN at runtime: each generator's
    // AXI_ATTR.max_outstanding CSR field caps it live (0 = as built), so one
    // bitstream produces the whole curve. Raising this costs queue depth in
    // the engines and in char_gen_unit's W-order queue, which sizes itself
    // from NUM_GEN x this.
    parameter int GEN_MAX_OUTSTANDING = 32,

    // ---- Build identity, readable through harness_csr ----
    // BUILD_ID is the harness FAMILY. "LDR2" here, "DDR2" on build-perf, so a
    // host can tell WHICH controller is behind the port before it trusts a
    // number. The CFG_* geometry mirrors what litedram_hp.yml generated: 75 MHz
    // sys / 1:2 / BL4 on the x16 MT47H64M16, i.e. the pumice PUMICE_SYS_75
    // operating point.
    parameter logic [31:0] BUILD_ID  = 32'h4C44_5232,   // "LDR2"
    parameter int BUILD_VERSION      = 1,
    parameter int CFG_DFI_RATE       = 2,
    parameter int CFG_DRAM_BL        = 4,
    parameter int CFG_ROW_WIDTH      = 13,
    parameter int CFG_BANK_WIDTH     = 3 * CFG_DFI_RATE,  // = DFI_BANK_BUS_W in build-perf
    parameter int CFG_DRAM_BEAT_W    = 32,
    parameter int CFG_DRAM_DEVICE_W  = 16,

    // ---- Aliases ----
    parameter int IW = AXI_ID_WIDTH,
    parameter int PIW = M_AXI_ID_WIDTH,
    parameter int AW = AXI_ADDR_WIDTH,
    parameter int DW = AXI_DATA_WIDTH,
    parameter int UW = AXI_USER_WIDTH,
    parameter int SW = AXI_STRB_WIDTH
) (
    input  logic                aclk,      // == litedram user_clk
    input  logic                aresetn,   // == ~litedram user_rst

    // Board UART (FTDI) -- the harness console (NOT litedram's BIOS uart)
    input  logic                i_uart_rx,
    output logic                o_uart_tx,

    // Status
    output logic [15:0]         o_led,
    output logic [7:0]          o_seven_seg_an,
    output logic [6:0]          o_seven_seg_seg,
    output logic                o_seven_seg_dp,

    // DUT init handshake (<= litedram_core.init_done / init_error)
    input  logic                i_init_done,
    input  logic                i_init_fail,

    // AXI4 master to the DUT (litedram user_port_axi_0). The sideband
    // (lock/cache/prot/qos/region) is driven for completeness; the litedram
    // port has no such inputs and the top leaves them open.
    output logic [PIW-1:0]       m_axi_awid,
    output logic [AW-1:0]       m_axi_awaddr,
    output logic [7:0]          m_axi_awlen,
    output logic [2:0]          m_axi_awsize,
    output logic [1:0]          m_axi_awburst,
    output logic                m_axi_awlock,
    output logic [3:0]          m_axi_awcache,
    output logic [2:0]          m_axi_awprot,
    output logic [3:0]          m_axi_awqos,
    output logic [3:0]          m_axi_awregion,
    output logic [UW-1:0]       m_axi_awuser,
    output logic                m_axi_awvalid,
    input  logic                m_axi_awready,
    output logic [DW-1:0]       m_axi_wdata,
    output logic [SW-1:0]       m_axi_wstrb,
    output logic                m_axi_wlast,
    output logic [UW-1:0]       m_axi_wuser,
    output logic                m_axi_wvalid,
    input  logic                m_axi_wready,
    input  logic [PIW-1:0]       m_axi_bid,
    input  logic [1:0]          m_axi_bresp,
    input  logic [UW-1:0]       m_axi_buser,
    input  logic                m_axi_bvalid,
    output logic                m_axi_bready,
    output logic [PIW-1:0]       m_axi_arid,
    output logic [AW-1:0]       m_axi_araddr,
    output logic [7:0]          m_axi_arlen,
    output logic [2:0]          m_axi_arsize,
    output logic [1:0]          m_axi_arburst,
    output logic                m_axi_arlock,
    output logic [3:0]          m_axi_arcache,
    output logic [2:0]          m_axi_arprot,
    output logic [3:0]          m_axi_arqos,
    output logic [3:0]          m_axi_arregion,
    output logic [UW-1:0]       m_axi_aruser,
    output logic                m_axi_arvalid,
    input  logic                m_axi_arready,
    input  logic [PIW-1:0]       m_axi_rid,
    input  logic [DW-1:0]       m_axi_rdata,
    input  logic [1:0]          m_axi_rresp,
    input  logic                m_axi_rlast,
    input  logic [UW-1:0]       m_axi_ruser,
    input  logic                m_axi_rvalid,
    output logic                m_axi_rready
);

    localparam int CLKS_PER_BIT = FPGA_CLK_HZ / UART_BAUD;

    // =========================================================================
    // Reset synchroniser (async assert, sync deassert) -- as build-perf
    // =========================================================================
    (* ASYNC_REG = "TRUE" *) logic r_rst_meta, r_rst_sync;
    `ALWAYS_FF_RST(aclk, aresetn,
        if (`RST_ASSERTED(aresetn)) begin
            r_rst_meta <= 1'b0;
            r_rst_sync <= 1'b0;
        end else begin
            r_rst_meta <= 1'b1;
            r_rst_sync <= r_rst_meta;
        end
    )
    logic unit_aresetn;
    assign unit_aresetn = r_rst_sync;

    // =========================================================================
    // UART <-> AXIL bridge
    // =========================================================================
    logic [31:0] uart_awaddr, uart_wdata, uart_araddr, uart_rdata;
    logic [3:0]  uart_wstrb;
    logic [2:0]  uart_awprot, uart_arprot;
    logic [1:0]  uart_bresp, uart_rresp;
    logic        uart_awvalid, uart_awready, uart_wvalid, uart_wready;
    logic        uart_bvalid,  uart_bready;
    logic        uart_arvalid, uart_arready, uart_rvalid, uart_rready;

    uart_axil_bridge #(
        .AXIL_ADDR_WIDTH (32),
        .AXIL_DATA_WIDTH (32),
        .CLKS_PER_BIT    (CLKS_PER_BIT)
    ) u_uart (
        .aclk     (aclk),
        .aresetn  (unit_aresetn),
        .i_uart_rx(i_uart_rx),
        .o_uart_tx(o_uart_tx),
        .m_axil_awaddr (uart_awaddr),  .m_axil_awprot (uart_awprot),
        .m_axil_awvalid(uart_awvalid), .m_axil_awready(uart_awready),
        .m_axil_wdata  (uart_wdata),   .m_axil_wstrb  (uart_wstrb),
        .m_axil_wvalid (uart_wvalid),  .m_axil_wready (uart_wready),
        .m_axil_bresp  (uart_bresp),   .m_axil_bvalid (uart_bvalid),
        .m_axil_bready (uart_bready),
        .m_axil_araddr (uart_araddr),  .m_axil_arprot (uart_arprot),
        .m_axil_arvalid(uart_arvalid), .m_axil_arready(uart_arready),
        .m_axil_rdata  (uart_rdata),   .m_axil_rresp  (uart_rresp),
        .m_axil_rvalid (uart_rvalid),  .m_axil_rready (uart_rready)
    );

    // =========================================================================
    // Bridge slave-side nets (same slot numbering as build-perf)
    // =========================================================================
    // Slave 0 (ddr2_apb) -- pumice CSR window. There is no controller CSR
    // behind it here, so it is terminated the same way the obs slot is:
    // PREADY high, data zero, no error. A host that still writes pumice
    // knobs completes its UART transaction instead of wedging the bus.
    logic        apb_psel, apb_penable, apb_pwrite;
    logic [31:0] apb_paddr_full, apb_pwdata;
    logic [3:0]  apb_pstrb;
    logic [2:0]  apb_pprot;

    // Slave 1 (harness_csr) -- AXIL 32b
    logic [31:0] s1_awaddr, s1_wdata, s1_araddr, s1_rdata;
    logic [3:0]  s1_wstrb;
    logic [2:0]  s1_awprot, s1_arprot;
    logic [1:0]  s1_bresp, s1_rresp;
    logic s1_awvalid, s1_awready, s1_wvalid, s1_wready, s1_bvalid, s1_bready;
    logic s1_arvalid, s1_arready, s1_rvalid, s1_rready;

    // Slave 2 (debug_sram) -- AXIL 64b
    logic [31:0] s2_awaddr, s2_araddr;
    logic [63:0] s2_wdata, s2_rdata;
    logic [7:0]  s2_wstrb;
    logic [2:0]  s2_awprot, s2_arprot;
    logic [1:0]  s2_bresp, s2_rresp;
    logic s2_awvalid, s2_awready, s2_wvalid, s2_wready, s2_bvalid, s2_bready;
    logic s2_arvalid, s2_arready, s2_rvalid, s2_rready;

    // Slave 3 (dfi_mon_ram) -- AXIL 32b
    logic [31:0] s3_awaddr, s3_wdata, s3_araddr, s3_rdata;
    logic [3:0]  s3_wstrb;
    logic [2:0]  s3_awprot, s3_arprot;
    logic [1:0]  s3_bresp, s3_rresp;
    logic s3_awvalid, s3_awready, s3_wvalid, s3_wready, s3_bvalid, s3_bready;
    logic s3_arvalid, s3_arready, s3_rvalid, s3_rready;

    // Slave 4 (obs_apb) -- expansion slot, terminated
    logic        obs_apb_PSEL, obs_apb_PENABLE, obs_apb_PWRITE;
    logic [31:0] obs_apb_PADDR, obs_apb_PWDATA;
    logic [3:0]  obs_apb_PSTRB;
    logic [2:0]  obs_apb_PPROT;

    // Slave 5 (chargen_apb) -- generator config, into char_engine_block
    logic        chargen_apb_PSEL, chargen_apb_PENABLE, chargen_apb_PWRITE;
    logic [31:0] chargen_apb_PADDR, chargen_apb_PWDATA;
    logic [3:0]  chargen_apb_PSTRB;
    logic [2:0]  chargen_apb_PPROT;
    logic [31:0] chargen_apb_PRDATA;
    logic        chargen_apb_PREADY, chargen_apb_PSLVERR;

    // Subtractive-decode hit reporting (unused here, as in build-perf)
    logic        w_unmapped_irq;
    logic [31:0] w_unmapped_addr;
    logic [7:0]  w_unmapped_count;

    // =========================================================================
    // Generated 1 -> 6 bridge (identical address map to build-perf)
    // =========================================================================
    bridge_ddr2_char_axil u_bridge (
        .aclk    (aclk),
        .aresetn (unit_aresetn),

        .host_axi_awaddr  (uart_awaddr),  .host_axi_awprot  (uart_awprot),
        .host_axi_awvalid (uart_awvalid), .host_axi_awready (uart_awready),
        .host_axi_wdata   (uart_wdata),   .host_axi_wstrb   (uart_wstrb),
        .host_axi_wvalid  (uart_wvalid),  .host_axi_wready  (uart_wready),
        .host_axi_bresp   (uart_bresp),   .host_axi_bvalid  (uart_bvalid),
        .host_axi_bready  (uart_bready),
        .host_axi_araddr  (uart_araddr),  .host_axi_arprot  (uart_arprot),
        .host_axi_arvalid (uart_arvalid), .host_axi_arready (uart_arready),
        .host_axi_rdata   (uart_rdata),   .host_axi_rresp   (uart_rresp),
        .host_axi_rvalid  (uart_rvalid),  .host_axi_rready  (uart_rready),

        // Slave 0: ddr2_apb -- terminated (no controller CSR in this flow)
        .ddr2_apb_PSEL    (apb_psel),
        .ddr2_apb_PADDR   (apb_paddr_full),
        .ddr2_apb_PENABLE (apb_penable),
        .ddr2_apb_PWRITE  (apb_pwrite),
        .ddr2_apb_PWDATA  (apb_pwdata),
        .ddr2_apb_PSTRB   (apb_pstrb),
        .ddr2_apb_PPROT   (apb_pprot),
        .ddr2_apb_PRDATA  (32'h0),
        .ddr2_apb_PREADY  (1'b1),
        .ddr2_apb_PSLVERR (1'b0),

        // Slave 1: harness_csr
        .harness_csr_axi_awaddr  (s1_awaddr),  .harness_csr_axi_awprot  (s1_awprot),
        .harness_csr_axi_awvalid (s1_awvalid), .harness_csr_axi_awready (s1_awready),
        .harness_csr_axi_wdata   (s1_wdata),   .harness_csr_axi_wstrb   (s1_wstrb),
        .harness_csr_axi_wvalid  (s1_wvalid),  .harness_csr_axi_wready  (s1_wready),
        .harness_csr_axi_bresp   (s1_bresp),   .harness_csr_axi_bvalid  (s1_bvalid),
        .harness_csr_axi_bready  (s1_bready),
        .harness_csr_axi_araddr  (s1_araddr),  .harness_csr_axi_arprot  (s1_arprot),
        .harness_csr_axi_arvalid (s1_arvalid), .harness_csr_axi_arready (s1_arready),
        .harness_csr_axi_rdata   (s1_rdata),   .harness_csr_axi_rresp   (s1_rresp),
        .harness_csr_axi_rvalid  (s1_rvalid),  .harness_csr_axi_rready  (s1_rready),

        // Slave 2: debug_sram (64b)
        .debug_sram_axi_awaddr  (s2_awaddr),  .debug_sram_axi_awprot  (s2_awprot),
        .debug_sram_axi_awvalid (s2_awvalid), .debug_sram_axi_awready (s2_awready),
        .debug_sram_axi_wdata   (s2_wdata),   .debug_sram_axi_wstrb   (s2_wstrb),
        .debug_sram_axi_wvalid  (s2_wvalid),  .debug_sram_axi_wready  (s2_wready),
        .debug_sram_axi_bresp   (s2_bresp),   .debug_sram_axi_bvalid  (s2_bvalid),
        .debug_sram_axi_bready  (s2_bready),
        .debug_sram_axi_araddr  (s2_araddr),  .debug_sram_axi_arprot  (s2_arprot),
        .debug_sram_axi_arvalid (s2_arvalid), .debug_sram_axi_arready (s2_arready),
        .debug_sram_axi_rdata   (s2_rdata),   .debug_sram_axi_rresp   (s2_rresp),
        .debug_sram_axi_rvalid  (s2_rvalid),  .debug_sram_axi_rready  (s2_rready),

        // Slave 3: dfi_mon_ram
        .dfi_mon_ram_axi_awaddr  (s3_awaddr),  .dfi_mon_ram_axi_awprot  (s3_awprot),
        .dfi_mon_ram_axi_awvalid (s3_awvalid), .dfi_mon_ram_axi_awready (s3_awready),
        .dfi_mon_ram_axi_wdata   (s3_wdata),   .dfi_mon_ram_axi_wstrb   (s3_wstrb),
        .dfi_mon_ram_axi_wvalid  (s3_wvalid),  .dfi_mon_ram_axi_wready  (s3_wready),
        .dfi_mon_ram_axi_bresp   (s3_bresp),   .dfi_mon_ram_axi_bvalid  (s3_bvalid),
        .dfi_mon_ram_axi_bready  (s3_bready),
        .dfi_mon_ram_axi_araddr  (s3_araddr),  .dfi_mon_ram_axi_arprot  (s3_arprot),
        .dfi_mon_ram_axi_arvalid (s3_arvalid), .dfi_mon_ram_axi_arready (s3_arready),
        .dfi_mon_ram_axi_rdata   (s3_rdata),   .dfi_mon_ram_axi_rresp   (s3_rresp),
        .dfi_mon_ram_axi_rvalid  (s3_rvalid),  .dfi_mon_ram_axi_rready  (s3_rready),

        // Slave 4: obs_apb -- expansion slot, terminated
        .obs_apb_PSEL     (obs_apb_PSEL),
        .obs_apb_PADDR    (obs_apb_PADDR),
        .obs_apb_PENABLE  (obs_apb_PENABLE),
        .obs_apb_PWRITE   (obs_apb_PWRITE),
        .obs_apb_PWDATA   (obs_apb_PWDATA),
        .obs_apb_PSTRB    (obs_apb_PSTRB),
        .obs_apb_PPROT    (obs_apb_PPROT),
        .obs_apb_PRDATA   (32'h0),
        .obs_apb_PREADY   (1'b1),
        .obs_apb_PSLVERR  (1'b0),

        // Slave 5: chargen_apb -> char_engine_block
        .chargen_apb_PSEL     (chargen_apb_PSEL),
        .chargen_apb_PADDR    (chargen_apb_PADDR),
        .chargen_apb_PENABLE  (chargen_apb_PENABLE),
        .chargen_apb_PWRITE   (chargen_apb_PWRITE),
        .chargen_apb_PWDATA   (chargen_apb_PWDATA),
        .chargen_apb_PSTRB    (chargen_apb_PSTRB),
        .chargen_apb_PPROT    (chargen_apb_PPROT),
        .chargen_apb_PRDATA   (chargen_apb_PRDATA),
        .chargen_apb_PREADY   (chargen_apb_PREADY),
        .chargen_apb_PSLVERR  (chargen_apb_PSLVERR),

        .unmapped_irq   (w_unmapped_irq),
        .unmapped_addr  (w_unmapped_addr),
        .unmapped_count (w_unmapped_count),
        .unmapped_clear (1'b0)
    );

    // =========================================================================
    // harness_csr -- global ctrl / status / timer / perf
    // =========================================================================
    logic         w_start_wr_pulse, w_start_rd_pulse;
    logic         w_clear_stats_pulse, w_freeze_trace, w_soft_reset_pulse;
    logic         w_wr_done, w_rd_done;
    logic         w_wr_error, w_rd_error;
    logic         w_init_done, w_init_fail;
    logic [31:0]  w_dbg_wr_ptr;
    logic         w_dbg_overflow, w_dbg_clear_busy;
    logic         w_gen_any_error, w_gen_crc_match;

    logic         w_timer_clear_pulse;
    logic [31:0]  w_timer_expected_beats;
    logic         w_timer_done, w_timer_running, w_timer_pass;
    logic [63:0]  w_timer_cycles;
    logic [63:0]  w_timer_r_first, w_timer_r_last;
    logic [63:0]  w_timer_w_first, w_timer_w_last;

    logic [15:0]  w_rd_resp_delay_cyc, w_wr_resp_delay_cyc;

    logic         w_perf_clear, w_perf_freeze;
    logic [31:0]  w_obs_rd_prod, w_obs_rd_bp, w_obs_rd_starv, w_obs_rd_idle;
    logic [31:0]  w_obs_wr_prod, w_obs_wr_bp, w_obs_wr_starv, w_obs_wr_idle;
    logic         w_obs_hist_metric, w_obs_hist_bus_sel;
    logic [3:0]   w_obs_hist_bin;
    logic [31:0]  w_obs_rd_hist_count, w_obs_rd_hist_total;
    logic [31:0]  w_obs_wr_hist_count, w_obs_wr_hist_total;

    // Controller runtime knobs. Programmed by the host exactly as on pumice,
    // read by nothing here: LiteDRAM's BIOS owns its own configuration.
    memtype_e     w_memtype;
    logic [7:0]   w_t_phy_wrlat, w_t_rddata_en;
    logic         w_rd_in_order;
    logic [3:0]   w_cap_lookahead_max, w_cap_synth_mask;
    logic [3:0]   w_cmd_delay_sel, w_rddata_delay_sel;
    logic [9:0]   w_phy_csr_adr;
    logic         w_phy_csr_we;
    logic [31:0]  w_phy_csr_dat_w;

    assign w_init_done = i_init_done;
    assign w_init_fail = i_init_fail;

    harness_csr #(
        .AW              (32),
        .DW              (32),
        .AXI_ID_WIDTH    (AXI_ID_WIDTH),
        .STRIDE_WIDTH    (STRIDE_WIDTH),
        .TXN_COUNT_WIDTH (TXN_COUNT_WIDTH),
        .BURST_LEN_WIDTH (BURST_LEN_WIDTH),
        .BUILD_ID          (BUILD_ID),
        .BUILD_VERSION     (BUILD_VERSION),
        .CFG_DFI_RATE      (CFG_DFI_RATE),
        .CFG_DRAM_BL       (CFG_DRAM_BL),
        .CFG_ROW_WIDTH     (CFG_ROW_WIDTH),
        .CFG_BANK_WIDTH    (CFG_BANK_WIDTH),
        .CFG_AXI_DATA_W    (AXI_DATA_WIDTH),
        .CFG_DRAM_BEAT_W   (CFG_DRAM_BEAT_W),
        .CFG_DRAM_DEVICE_W (CFG_DRAM_DEVICE_W)
    ) u_harness_csr (
        .aclk    (aclk),
        .aresetn (unit_aresetn),

        .s_awaddr  (s1_awaddr),  .s_awprot (s1_awprot),
        .s_awvalid (s1_awvalid), .s_awready(s1_awready),
        .s_wdata   (s1_wdata),   .s_wstrb  (s1_wstrb),
        .s_wvalid  (s1_wvalid),  .s_wready (s1_wready),
        .s_bresp   (s1_bresp),   .s_bvalid (s1_bvalid),  .s_bready (s1_bready),
        .s_araddr  (s1_araddr),  .s_arprot (s1_arprot),
        .s_arvalid (s1_arvalid), .s_arready(s1_arready),
        .s_rdata   (s1_rdata),   .s_rresp  (s1_rresp),
        .s_rvalid  (s1_rvalid),  .s_rready (s1_rready),

        .o_clear_stats_pulse (w_clear_stats_pulse),
        .o_freeze_trace      (w_freeze_trace),
        .o_soft_reset_pulse  (w_soft_reset_pulse),

        .i_wr_done         (w_wr_done),
        .i_rd_done         (w_rd_done),
        .i_wr_error        (w_wr_error),
        .i_rd_error        (w_rd_error),
        .i_init_done       (w_init_done),
        .i_init_fail       (w_init_fail),
        .i_dbg_wr_ptr      (w_dbg_wr_ptr),
        .i_dbg_overflow    (w_dbg_overflow),
        .i_dbg_clear_busy  (w_dbg_clear_busy),
        .i_crc_match       (w_gen_crc_match),

        .o_timer_clear_pulse    (w_timer_clear_pulse),
        .o_timer_expected_beats (w_timer_expected_beats),
        .i_timer_done           (w_timer_done),
        .i_timer_running        (w_timer_running),
        .i_timer_pass           (w_timer_pass),
        .i_timer_cycles         (w_timer_cycles),
        .i_timer_r_first        (w_timer_r_first),
        .i_timer_r_last         (w_timer_r_last),
        .i_timer_w_first        (w_timer_w_first),
        .i_timer_w_last         (w_timer_w_last),

        .o_rd_resp_delay_cyc (w_rd_resp_delay_cyc),
        .o_wr_resp_delay_cyc (w_wr_resp_delay_cyc),

        .o_perf_clear         (w_perf_clear),
        .o_perf_freeze        (w_perf_freeze),
        .i_obs_rd_prod        (w_obs_rd_prod),
        .i_obs_rd_bp          (w_obs_rd_bp),
        .i_obs_rd_starv       (w_obs_rd_starv),
        .i_obs_rd_idle        (w_obs_rd_idle),
        .i_obs_wr_prod        (w_obs_wr_prod),
        .i_obs_wr_bp          (w_obs_wr_bp),
        .i_obs_wr_starv       (w_obs_wr_starv),
        .i_obs_wr_idle        (w_obs_wr_idle),
        .o_obs_hist_metric    (w_obs_hist_metric),
        .o_obs_hist_bin       (w_obs_hist_bin),
        .o_obs_hist_bus_sel   (w_obs_hist_bus_sel),
        .i_obs_rd_hist_count  (w_obs_rd_hist_count),
        .i_obs_rd_hist_total  (w_obs_rd_hist_total),
        .i_obs_wr_hist_count  (w_obs_wr_hist_count),
        .i_obs_wr_hist_total  (w_obs_wr_hist_total),

        .o_memtype           (w_memtype),
        .o_t_phy_wrlat       (w_t_phy_wrlat),
        .o_t_rddata_en       (w_t_rddata_en),
        .o_rd_in_order       (w_rd_in_order),
        .o_cap_lookahead_max (w_cap_lookahead_max),
        .o_cap_synth_mask    (w_cap_synth_mask),
        .o_cmd_delay         (w_cmd_delay_sel),
        .o_rddata_delay      (w_rddata_delay_sel),

        // a7ddrphy leveling CSR: LiteDRAM calibrates itself, nothing to drive.
        .o_phy_csr_adr       (w_phy_csr_adr),
        .o_phy_csr_we        (w_phy_csr_we),
        .o_phy_csr_dat_w     (w_phy_csr_dat_w),
        .i_phy_csr_dat_r     (32'd0)
    );

    // =========================================================================
    // debug_sram -- 64b AXIL SRAM (kept so the host's clear/read path is live)
    // =========================================================================
    logic w_debug_sram_dbg_bram_wr_pulse;
    logic w_debug_sram_dbg_busy_wr;
    sdpram_slave_axil_axil #(
        .ADDR_WIDTH (32),
        .DATA_WIDTH (64),
        .MEM_DEPTH  (DEBUG_SRAM_WORDS / 2)
    ) u_debug_sram (
        .aclk(aclk), .aresetn(unit_aresetn),
        .s_axil_awaddr (s2_awaddr), .s_axil_awprot(s2_awprot),
        .s_axil_awvalid(s2_awvalid), .s_axil_awready(s2_awready),
        .s_axil_wdata  (s2_wdata),  .s_axil_wstrb (s2_wstrb),
        .s_axil_wvalid (s2_wvalid), .s_axil_wready(s2_wready),
        .s_axil_bresp  (s2_bresp), .s_axil_bvalid(s2_bvalid), .s_axil_bready(s2_bready),
        .s_axil_araddr (s2_araddr), .s_axil_arprot(s2_arprot),
        .s_axil_arvalid(s2_arvalid), .s_axil_arready(s2_arready),
        .s_axil_rdata  (s2_rdata), .s_axil_rresp (s2_rresp),
        .s_axil_rvalid (s2_rvalid), .s_axil_rready(s2_rready),
        .i_cfg_start_clear (w_clear_stats_pulse & ~w_freeze_trace),
        .o_cfg_done_clear  (),
        .o_dbg_vr(), .o_dbg_fub_vr(),
        .o_dbg_bram_wr(w_debug_sram_dbg_bram_wr_pulse),
        .o_dbg_bram_rd(),
        .o_dbg_busy_wr(w_debug_sram_dbg_busy_wr),
        .o_dbg_busy_rd()
    );

    logic [31:0] r_dbg_wr_ptr;
    logic        r_dbg_overflow;
    `ALWAYS_FF_RST(aclk, unit_aresetn,
        if (`RST_ASSERTED(unit_aresetn)) begin
            r_dbg_wr_ptr   <= '0;
            r_dbg_overflow <= 1'b0;
        end else if (w_clear_stats_pulse) begin
            r_dbg_wr_ptr   <= '0;
            r_dbg_overflow <= 1'b0;
        end else if (w_debug_sram_dbg_bram_wr_pulse && !w_freeze_trace) begin
            if (r_dbg_wr_ptr == 32'hFFFF_FFFF) r_dbg_overflow <= 1'b1;
            else                                r_dbg_wr_ptr <= r_dbg_wr_ptr + 32'd1;
        end
    )
    assign w_dbg_wr_ptr     = r_dbg_wr_ptr;
    assign w_dbg_overflow   = r_dbg_overflow;
    assign w_dbg_clear_busy = w_debug_sram_dbg_busy_wr;

    // =========================================================================
    // dfi_mon_ram -- AXIL 32b SRAM (placeholder, as build-perf)
    // =========================================================================
    sdpram_slave_axil_axil #(
        .ADDR_WIDTH (32),
        .DATA_WIDTH (32),
        .MEM_DEPTH  (DFI_MON_RAM_WORDS)
    ) u_dfi_mon_ram (
        .aclk(aclk), .aresetn(unit_aresetn),
        .s_axil_awaddr (s3_awaddr), .s_axil_awprot(s3_awprot),
        .s_axil_awvalid(s3_awvalid), .s_axil_awready(s3_awready),
        .s_axil_wdata  (s3_wdata),  .s_axil_wstrb (s3_wstrb),
        .s_axil_wvalid (s3_wvalid), .s_axil_wready(s3_wready),
        .s_axil_bresp  (s3_bresp), .s_axil_bvalid(s3_bvalid), .s_axil_bready(s3_bready),
        .s_axil_araddr (s3_araddr), .s_axil_arprot(s3_arprot),
        .s_axil_arvalid(s3_arvalid), .s_axil_arready(s3_arready),
        .s_axil_rdata  (s3_rdata), .s_axil_rresp (s3_rresp),
        .s_axil_rvalid (s3_rvalid), .s_axil_rready(s3_rready),
        .i_cfg_start_clear (1'b0),
        .o_cfg_done_clear  (),
        .o_dbg_vr(), .o_dbg_fub_vr(), .o_dbg_bram_wr(), .o_dbg_bram_rd(),
        .o_dbg_busy_wr(), .o_dbg_busy_rd()
    );

    // =========================================================================
    // Datapath soft-reset (CTRL.soft_reset), stretched as in build-perf. It
    // re-resets the generators AND chargen_regs (both on mc_rst_n inside the
    // block), so the host must re-program every generator before the next GO
    // -- a GO after a bare soft_reset runs a zero-address, zero-count workload
    // and reports a near-empty timer window that measures nothing.
    //
    // One difference from build-perf, where the same reset also resets pumice
    // so both ends of the AXI bus restart together: litedram_core has no reset
    // input on its user port. Resetting only the master mid-burst would leave
    // the core waiting for the tail of an abandoned write burst, and every
    // later W beat would land one burst late for the rest of the session. So
    // the reset window is held off until the write side is quiescent -- no
    // burst with AW accepted but WLAST not yet sent (or the reverse), no beat
    // of a partial burst on the wire, and no address valid pending -- with a
    // bound (QUIESCE_MAX cycles) so a genuinely wedged bus still gets its reset.
    // Reads need no guard: axi4_master_rd_crc_check drains orphan R beats as
    // strays after reset.
    // =========================================================================
    localparam int QUIESCE_MAX = 4096;
    logic [5:0]  r_wr_balance;     // AW handshakes minus WLAST handshakes
    logic        r_w_inburst;      // a W beat seen since the last WLAST
    logic        w_aw_hs, w_wlast_hs, w_w_hs, w_wr_quiet;
    assign w_aw_hs    = m_axi_awvalid & m_axi_awready;
    assign w_w_hs     = m_axi_wvalid  & m_axi_wready;
    assign w_wlast_hs = w_w_hs & m_axi_wlast;
    assign w_wr_quiet = (r_wr_balance == '0) & ~r_w_inburst
                      & ~m_axi_awvalid & ~m_axi_wvalid & ~m_axi_arvalid;

    `ALWAYS_FF_RST(aclk, aresetn,
        if (!aresetn) begin
            r_wr_balance <= '0;
            r_w_inburst  <= 1'b0;
        end else begin
            case ({w_aw_hs, w_wlast_hs})
                2'b10:   r_wr_balance <= r_wr_balance + 6'd1;
                2'b01:   r_wr_balance <= r_wr_balance - 6'd1;
                default: ;
            endcase
            if (w_wlast_hs)  r_w_inburst <= 1'b0;
            else if (w_w_hs) r_w_inburst <= 1'b1;
        end
    )

    logic        r_soft_rst_pend;
    logic [12:0] r_quiesce_cnt;
    logic [3:0]  r_soft_rst_cnt;
    logic        w_soft_rst_go;
    assign w_soft_rst_go = r_soft_rst_pend & (w_wr_quiet | (r_quiesce_cnt == 13'(QUIESCE_MAX)));

    `ALWAYS_FF_RST(aclk, aresetn,
        if (!aresetn) begin
            r_soft_rst_pend <= 1'b0;
            r_quiesce_cnt   <= '0;
            r_soft_rst_cnt  <= 4'd0;
        end else begin
            if (w_soft_reset_pulse) begin
                r_soft_rst_pend <= 1'b1;
                r_quiesce_cnt   <= '0;
            end else if (r_soft_rst_pend) begin
                r_quiesce_cnt <= r_quiesce_cnt + 13'd1;
            end
            if (w_soft_rst_go) begin
                r_soft_rst_pend <= 1'b0;
                r_soft_rst_cnt  <= 4'd15;   // stretch
            end else if (r_soft_rst_cnt != 4'd0) begin
                r_soft_rst_cnt  <= r_soft_rst_cnt - 4'd1;
            end
        end
    )
    logic dp_aresetn;
    assign dp_aresetn = unit_aresetn & (r_soft_rst_cnt == 4'd0);

    // =========================================================================
    // char_engine_block -- the SAME generators / config / perf as pumice's macro
    // =========================================================================
    logic                      w_rd_dbg_valid, w_rd_dbg_mismatch;
    logic [AXI_DATA_WIDTH-1:0] w_rd_dbg_actual, w_rd_dbg_expected;

    char_engine_block #(
        .AXI_ADDR_WIDTH     (AXI_ADDR_WIDTH),
        .AXI_DATA_WIDTH     (AXI_DATA_WIDTH),
        .AXI_ID_WIDTH       (AXI_ID_WIDTH),
        .AXI_USER_WIDTH     (AXI_USER_WIDTH),
        .AXI_STRB_WIDTH     (AXI_STRB_WIDTH),
        .BURST_LEN_WIDTH    (BURST_LEN_WIDTH),
        .BURST_LEN_MULTIPLE (BURST_LEN_MULTIPLE),
        .APB_ADDR_WIDTH     (APB_ADDR_WIDTH),
        .APB_DATA_WIDTH     (APB_DATA_WIDTH),
        .APB_STRB_WIDTH     (APB_STRB_WIDTH),
        .APB_PROT_WIDTH     (APB_PROT_WIDTH),
        .NUM_BANKS          (NUM_BANKS),
        .NUM_GEN            (NUM_GEN),
        .GEN_MAX_OUTSTANDING(GEN_MAX_OUTSTANDING),
        .TXN_COUNT_WIDTH    (TXN_COUNT_WIDTH),
        .INDEX_WIDTH        (INDEX_WIDTH),
        .STRIDE_WIDTH       (STRIDE_WIDTH),
        .RD_DBG_FIFO_DEPTH  (0)
    ) u_engines (
        .mc_clk   (aclk),
        .mc_rst_n (dp_aresetn),
        .pclk     (aclk),
        .presetn  (unit_aresetn),

        .s_chargen_apb_PSEL    (chargen_apb_PSEL),
        .s_chargen_apb_PENABLE (chargen_apb_PENABLE),
        .s_chargen_apb_PREADY  (chargen_apb_PREADY),
        .s_chargen_apb_PADDR   (chargen_apb_PADDR[APB_ADDR_WIDTH-1:0]),
        .s_chargen_apb_PWRITE  (chargen_apb_PWRITE),
        .s_chargen_apb_PWDATA  (chargen_apb_PWDATA),
        .s_chargen_apb_PSTRB   (chargen_apb_PSTRB[APB_STRB_WIDTH-1:0]),
        .s_chargen_apb_PPROT   (chargen_apb_PPROT[APB_PROT_WIDTH-1:0]),
        .s_chargen_apb_PRDATA  (chargen_apb_PRDATA),
        .s_chargen_apb_PSLVERR (chargen_apb_PSLVERR),

        .gen_wr_started (w_start_wr_pulse),
        .gen_rd_started (w_start_rd_pulse),
        .gen_wr_done    (w_wr_done),
        .gen_rd_done    (w_rd_done),
        .gen_any_error  (w_gen_any_error),
        .gen_crc_match  (w_gen_crc_match),

        .rd_dbg_valid   (w_rd_dbg_valid),
        .rd_dbg_ready   (1'b1),
        .rd_dbg_actual  (w_rd_dbg_actual),
        .rd_dbg_expected(w_rd_dbg_expected),
        .rd_dbg_mismatch(w_rd_dbg_mismatch),

        .perf_clear     (w_perf_clear),
        .perf_freeze    (w_perf_freeze),
        .perf_wr_prod   (w_obs_wr_prod),
        .perf_wr_bp     (w_obs_wr_bp),
        .perf_wr_starv  (w_obs_wr_starv),
        .perf_wr_idle   (w_obs_wr_idle),
        .perf_rd_prod   (w_obs_rd_prod),
        .perf_rd_bp     (w_obs_rd_bp),
        .perf_rd_starv  (w_obs_rd_starv),
        .perf_rd_idle   (w_obs_rd_idle),
        .i_hist_metric  (w_obs_hist_metric),
        .i_hist_bin     (w_obs_hist_bin),
        .perf_wr_hist_count(w_obs_wr_hist_count),
        .perf_wr_hist_total(w_obs_wr_hist_total),
        .perf_rd_hist_count(w_obs_rd_hist_count),
        .perf_rd_hist_total(w_obs_rd_hist_total),

        .m_axi_awid   (m_axi_awid),   .m_axi_awaddr  (m_axi_awaddr),
        .m_axi_awlen  (m_axi_awlen),  .m_axi_awsize  (m_axi_awsize),
        .m_axi_awburst(m_axi_awburst),.m_axi_awlock  (m_axi_awlock),
        .m_axi_awcache(m_axi_awcache),.m_axi_awprot  (m_axi_awprot),
        .m_axi_awqos  (m_axi_awqos),  .m_axi_awregion(m_axi_awregion),
        .m_axi_awuser (m_axi_awuser), .m_axi_awvalid (m_axi_awvalid),
        .m_axi_awready(m_axi_awready),
        .m_axi_wdata  (m_axi_wdata),  .m_axi_wstrb   (m_axi_wstrb),
        .m_axi_wlast  (m_axi_wlast),  .m_axi_wuser   (m_axi_wuser),
        .m_axi_wvalid (m_axi_wvalid), .m_axi_wready  (m_axi_wready),
        .m_axi_bid    (m_axi_bid),    .m_axi_bresp   (m_axi_bresp),
        .m_axi_buser  (m_axi_buser),  .m_axi_bvalid  (m_axi_bvalid),
        .m_axi_bready (m_axi_bready),
        .m_axi_arid   (m_axi_arid),   .m_axi_araddr  (m_axi_araddr),
        .m_axi_arlen  (m_axi_arlen),  .m_axi_arsize  (m_axi_arsize),
        .m_axi_arburst(m_axi_arburst),.m_axi_arlock  (m_axi_arlock),
        .m_axi_arcache(m_axi_arcache),.m_axi_arprot  (m_axi_arprot),
        .m_axi_arqos  (m_axi_arqos),  .m_axi_arregion(m_axi_arregion),
        .m_axi_aruser (m_axi_aruser), .m_axi_arvalid (m_axi_arvalid),
        .m_axi_arready(m_axi_arready),
        .m_axi_rid    (m_axi_rid),    .m_axi_rdata   (m_axi_rdata),
        .m_axi_rresp  (m_axi_rresp),  .m_axi_rlast   (m_axi_rlast),
        .m_axi_ruser  (m_axi_ruser),  .m_axi_rvalid  (m_axi_rvalid),
        .m_axi_rready (m_axi_rready)
    );

    // Same roll-up as build-perf: one error bit for the array.
    assign w_wr_error = w_gen_any_error;
    assign w_rd_error = w_gen_any_error | w_rd_dbg_mismatch;

    // =========================================================================
    // Characterization timer (verbatim from build-perf)
    // =========================================================================
    logic [63:0] r_cycles;
    logic        r_running, r_done;
    logic [63:0] r_w_first, r_w_last, r_r_first, r_r_last;
    logic        r_w_first_valid, r_r_first_valid;
    logic        r_w_last_valid, r_r_last_valid;
    logic        r_wr_kicked, r_rd_kicked;

    logic run_start;
    assign run_start = w_start_wr_pulse | w_start_rd_pulse;

    logic w_all_kicked_done;
    assign w_all_kicked_done = (r_wr_kicked | r_rd_kicked)
                             & (~r_wr_kicked | w_wr_done)
                             & (~r_rd_kicked | w_rd_done);

    `ALWAYS_FF_RST(aclk, unit_aresetn,
        if (`RST_ASSERTED(unit_aresetn)) begin
            r_cycles        <= '0;
            r_running       <= 1'b0;
            r_done          <= 1'b0;
            r_w_first       <= '0; r_w_last <= '0;
            r_r_first       <= '0; r_r_last <= '0;
            r_w_first_valid <= 1'b0;
            r_r_first_valid <= 1'b0;
            r_w_last_valid  <= 1'b0;
            r_r_last_valid  <= 1'b0;
            r_wr_kicked     <= 1'b0;
            r_rd_kicked     <= 1'b0;
        end else if (w_timer_clear_pulse) begin
            r_cycles        <= '0;
            r_running       <= 1'b0;
            r_done          <= 1'b0;
            r_w_first       <= '0; r_w_last <= '0;
            r_r_first       <= '0; r_r_last <= '0;
            r_w_first_valid <= 1'b0;
            r_r_first_valid <= 1'b0;
            r_w_last_valid  <= 1'b0;
            r_r_last_valid  <= 1'b0;
            r_wr_kicked     <= 1'b0;
            r_rd_kicked     <= 1'b0;
        end else begin
            if (w_start_wr_pulse) r_wr_kicked <= 1'b1;
            if (w_start_rd_pulse) r_rd_kicked <= 1'b1;
            if (run_start && !r_running) r_running <= 1'b1;
            if (w_start_wr_pulse && !r_w_first_valid) begin
                r_w_first       <= r_cycles;
                r_w_first_valid <= 1'b1;
            end
            if (w_start_rd_pulse && !r_r_first_valid) begin
                r_r_first       <= r_cycles;
                r_r_first_valid <= 1'b1;
            end
            if (r_running) begin
                r_cycles <= r_cycles + 64'd1;
                if (w_wr_done && !r_w_last_valid) begin
                    r_w_last       <= r_cycles;
                    r_w_last_valid <= 1'b1;
                end
                if (w_rd_done && !r_r_last_valid) begin
                    r_r_last       <= r_cycles;
                    r_r_last_valid <= 1'b1;
                end
                if (w_all_kicked_done) begin
                    r_running <= 1'b0;
                    r_done    <= 1'b1;
                end
            end
        end
    )

    assign w_timer_cycles   = r_cycles;
    assign w_timer_running  = r_running;
    assign w_timer_done     = r_done;
    assign w_timer_pass     = r_done & ~w_wr_error & ~w_rd_error & w_gen_crc_match;
    assign w_timer_w_first  = r_w_first;
    assign w_timer_w_last   = r_w_last;
    assign w_timer_r_first  = r_r_first;
    assign w_timer_r_last   = r_r_last;

    // =========================================================================
    // LED status + 7-segment (same bit map as build-perf)
    // =========================================================================
    logic [15:0] w_led_status;
    always_comb begin
        w_led_status        = '0;
        w_led_status[0]     = w_init_done;
        w_led_status[1]     = w_wr_error | w_rd_error;
        w_led_status[2]     = w_dbg_overflow;
        w_led_status[3]     = w_timer_done;
        w_led_status[4]     = w_timer_pass;
        w_led_status[5]     = w_timer_running;
        w_led_status[6]     = w_wr_done;
        w_led_status[7]     = w_rd_done;
        w_led_status[8]     = w_gen_crc_match;
        w_led_status[9]     = w_gen_any_error;
        w_led_status[10]    = w_dbg_clear_busy;
        w_led_status[11]    = w_init_fail;
    end

    led_status_driver #(
        .FPGA_CLK_HZ   (FPGA_CLK_HZ),
        .LED_UPDATE_HZ (LED_UPDATE_HZ),
        .NUM_LEDS      (16)
    ) u_led_status_driver (
        .aclk    (aclk),
        .aresetn (unit_aresetn),
        .i_status(w_led_status),
        .o_led   (o_led)
    );

    seven_seg_4digit #(
        .FPGA_CLK_HZ (FPGA_CLK_HZ),
        .REFRESH_HZ  (SEVEN_SEG_REFRESH)
    ) u_seven_seg (
        .aclk    (aclk),
        .aresetn (unit_aresetn),
        .i_hex   (r_cycles[15:0]),
        .i_enable(1'b1),
        .o_an    (o_seven_seg_an),
        .o_seg   (o_seven_seg_seg),
        .o_dp    (o_seven_seg_dp)
    );

    // =========================================================================
    // Tie-offs / unused hooks. Everything the pumice harness consumes but this
    // flow has no controller for stays observable rather than dangling.
    // =========================================================================
    // Guarded slice, as build-perf: at APB_ADDR_WIDTH == 32 the bare
    // [31:32] is a reversed part-select Vivado rejects (verilator: zero-width).
    generate
        if (APB_ADDR_WIDTH < 32) begin : g_chargen_addr_unused
            /* verilator lint_off UNUSED */
            wire _unused_chargen_addr = &{1'b0, chargen_apb_PADDR[31:APB_ADDR_WIDTH]};
            /* verilator lint_on UNUSED */
        end
    endgenerate
    /* verilator lint_off UNUSED */
    wire _unused_ok = &{1'b0,
        apb_psel, apb_penable, apb_pwrite, apb_paddr_full, apb_pwdata,
        apb_pstrb, apb_pprot,
        obs_apb_PSEL, obs_apb_PENABLE, obs_apb_PWRITE, obs_apb_PADDR,
        obs_apb_PWDATA, obs_apb_PSTRB, obs_apb_PPROT,
        w_unmapped_irq, w_unmapped_addr, w_unmapped_count,
        w_timer_expected_beats,
        w_rd_resp_delay_cyc, w_wr_resp_delay_cyc,
        w_memtype, w_t_phy_wrlat, w_t_rddata_en, w_rd_in_order,
        w_cap_lookahead_max, w_cap_synth_mask, w_cmd_delay_sel, w_rddata_delay_sel,
        w_phy_csr_adr, w_phy_csr_we, w_phy_csr_dat_w,
        w_rd_dbg_valid, w_rd_dbg_actual, w_rd_dbg_expected,
        1'b0};
    /* verilator lint_on UNUSED */

endmodule : char_engine_harness
