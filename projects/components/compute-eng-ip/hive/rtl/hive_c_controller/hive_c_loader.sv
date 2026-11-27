// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: 2026 sean galloway
//
// RTL Design Sherpa - Industry-Standard RTL Design and Verification
// https://github.com/sean-galloway/RTLDesignSherpa
//
// Module: hive_c_loader
// Purpose: HIVE-C's core, its two 32 KB block-RAM banks (I-mem at
//          0x0000_0000, D-mem at 0x0000_8000) and the kestrel-pattern
//          AXI4-Lite load-then-run window (MAS ch02 hive_c_controller,
//          owner decision 2026-10-13).  The core is selected by CORE_FLAVOR;
//          everything outside the core glue is flavor-independent.
//
// Documentation: projects/components/compute-eng-ip/hive/docs/hive_mas/ch02_blocks/02_hive_c_controller.md
// Subsystem: hive
//
// Author: sean galloway
// Created: 2026-11-27
//
// Parameters:
//   - CORE_FLAVOR: "vexriscv" (default; vendor/vexriscv, hive_c_core_vexriscv).
//     "peregrine" (riscv-ip/peregrine-rv32im) is the PRD 10.3 successor; its
//     glue is not built yet and selecting it stops elaboration.
//   - AXIL_ADDR_WIDTH: >= 18.  Bits above 17 must be zero (else SLVERR).
//   - BANK_WORDS: words per bank, 8192 (32 KB, HAS 4.3).  Power of two.
//   - SKID_DEPTH_*: the AXIL leaf slaves' skid depths.
//
// Address map (AXIL byte address; every access a full aligned word, a
// nonzero addr[1:0] is SLVERR):
//   addr[17:16] = 00 memory, the firmware map exactly:
//                    0x0_0000 - 0x0_7FFF  I-mem bank
//                    0x0_8000 - 0x0_FFFF  D-mem bank
//                 Writes: load mode only; in run mode SLVERR and dropped.
//                 Reads: any time; the core's data access to either bank
//                 wins the cycle, the loader read waits.
//   addr[17:16] = 01 unmapped: SLVERR
//   addr[17]    = 1  registers (any other offset SLVERR):
//     0x2_0000  CTRL      W   bit 0 run: 1 releases the core from reset at
//                             0x0000_0000; 0 holds it (load mode, the reset
//                             default).  Writable in either mode.
//                         R   {active[1], run[0]}: active = the glue's
//                             core_active (below); a host waits for it to
//                             fall before loading after clearing run.
//     0x2_0004  BUILD_ID  RO  "HCVX" (vexriscv) / "HCPG" (peregrine);
//                             a write is SLVERR.
//
// Core ports (the flavor-neutral seam every glue maps onto):
//   - fetch port f_*: read only, port A of the addressed bank.
//   - data port d_*:  read / byte-masked write, port B of the addressed bank.
//   Both accept a request in the cycle it is presented and return a read's
//   word one cycle later with an rvalid pulse.  Addresses outside
//   0x0000_0000 - 0x0000_FFFF read 0 and drop writes (the 0x4000_0000
//   peripheral windows belong to hive_c_controller, not this block).
//
// Notes:
//   - Run and the glue: the glue takes `run` and returns `core_active`, high
//     from the release until the core can no longer touch memory.  The
//     loader gates its write window and the core's requests on core_active,
//     never on run, so a flavor that needs to finish work after run falls
//     (peregrine: clean its write-back D$ before reset) does it inside its
//     glue.  vexriscv: core_active = run, reset = !run.
//   - Mutual exclusion between loader writes and the core is by protocol,
//     as in kestrel: memory writes need core_active = 0, which means the
//     core is held, so the two never meet on port B.  Loader reads and core
//     data accesses can meet; the core wins (arready drops for the cycle).
//   - Departure from kestrel_mem_loader / gatling_mem_bram: they ack and
//     drop a run-mode write with OKAY; here it is SLVERR, and unmapped or
//     unaligned accesses are SLVERR too, so a host loader sees its mistakes.
//   - core_ibus_* / core_dbus_* are observation nets for the TB (the glue's
//     accepted requests): the LDR testplan reads them.

`timescale 1ns / 1ps

`include "reset_defs.svh"

module hive_c_loader #(
    parameter string CORE_FLAVOR     = "vexriscv",
    parameter int    AXIL_ADDR_WIDTH = 18,
    parameter int    BANK_WORDS      = 8192,
    parameter int    SKID_DEPTH_AW   = 2,
    parameter int    SKID_DEPTH_W    = 2,
    parameter int    SKID_DEPTH_B    = 2,
    parameter int    SKID_DEPTH_AR   = 2,
    parameter int    SKID_DEPTH_R    = 4
) (
    input  logic                       clk,
    input  logic                       rst_n,

    // AXI4-Lite slave: loader window + registers
    input  logic [AXIL_ADDR_WIDTH-1:0] s_axil_awaddr,
    input  logic [2:0]                 s_axil_awprot,
    input  logic                       s_axil_awvalid,
    output logic                       s_axil_awready,
    input  logic [31:0]                s_axil_wdata,
    input  logic [3:0]                 s_axil_wstrb,
    input  logic                       s_axil_wvalid,
    output logic                       s_axil_wready,
    output logic [1:0]                 s_axil_bresp,
    output logic                       s_axil_bvalid,
    input  logic                       s_axil_bready,
    input  logic [AXIL_ADDR_WIDTH-1:0] s_axil_araddr,
    input  logic [2:0]                 s_axil_arprot,
    input  logic                       s_axil_arvalid,
    output logic                       s_axil_arready,
    output logic [31:0]                s_axil_rdata,
    output logic [1:0]                 s_axil_rresp,
    output logic                       s_axil_rvalid,
    input  logic                       s_axil_rready,

    // Interrupts into the core
    input  logic                       irq_external,
    input  logic                       irq_timer,
    input  logic                       irq_software,

    // Run state (1 = core released)
    output logic                       o_run
);

    // =========================================================================
    // Constants and the fixed address map
    // =========================================================================
    localparam int          IDX_W      = $clog2(BANK_WORDS);
    localparam int          BANK_BIT   = IDX_W + 2;          // 15: I vs D bank
    localparam int          WIN_BIT    = BANK_BIT + 1;       // 16: above the memory
    localparam int          REG_BIT    = 17;
    localparam int          NUM_BANKS  = 2;
    localparam int          REG_CTRL   = 0;                  // word offsets in the register block
    localparam int          REG_BUILD  = 1;
    localparam logic [1:0]  RESP_OKAY  = 2'b00;
    localparam logic [1:0]  RESP_SLVERR = 2'b10;
    localparam logic [3:0]  WE_NONE    = 4'b0000;
    localparam logic [31:0] BUILD_ID   = (CORE_FLAVOR == "peregrine") ? 32'h4843_5047   // "HCPG"
                                                                      : 32'h4843_5658;  // "HCVX"

`ifndef SYNTHESIS
    initial begin : param_check
        if (AXIL_ADDR_WIDTH < REG_BIT + 1)
            $error("hive_c_loader: AXIL_ADDR_WIDTH (%0d) must be >= %0d", AXIL_ADDR_WIDTH, REG_BIT + 1);
        if (WIN_BIT > REG_BIT - 1)
            $error("hive_c_loader: two banks of %0d words do not fit below the 0x1_0000 window bound",
                   BANK_WORDS);
    end
`endif

    // =========================================================================
    // AXIL address decode (shared by the write and read sides)
    // =========================================================================
    typedef struct packed {
        logic             mem;       // inside the two banks
        logic             ctrl;      // CTRL register
        logic             build;     // BUILD_ID register
        logic             bank;      // bank select for mem
        logic [IDX_W-1:0] idx;       // word in bank
    } axil_dec_t;

    function automatic axil_dec_t decode(input logic [AXIL_ADDR_WIDTH-1:0] a);
        axil_dec_t d;
        logic      ok;
        ok      = (a[1:0] == 2'b00) && ((a >> (REG_BIT + 1)) == '0);
        d.mem   = ok && !a[REG_BIT] && (a[REG_BIT-1:WIN_BIT] == '0);
        d.ctrl  = ok &&  a[REG_BIT] && (a[REG_BIT-1:2] == (REG_BIT-2)'(REG_CTRL));
        d.build = ok &&  a[REG_BIT] && (a[REG_BIT-1:2] == (REG_BIT-2)'(REG_BUILD));
        d.bank  = a[BANK_BIT];
        d.idx   = a[BANK_BIT-1:2];
        return d;
    endfunction

    // =========================================================================
    // AXIL leaf slaves (the kestrel / gatling composition)
    // =========================================================================
    logic [AXIL_ADDR_WIDTH-1:0] fub_awaddr, fub_araddr;
    /* verilator lint_off UNUSEDSIGNAL */
    logic [2:0]                 fub_awprot, fub_arprot;
    /* verilator lint_on UNUSEDSIGNAL */
    logic                       fub_awvalid, fub_awready, fub_wvalid, fub_wready;
    logic [31:0]                fub_wdata, fub_rdata;
    logic [3:0]                 fub_wstrb;
    logic [1:0]                 fub_bresp, fub_rresp;
    logic                       fub_bvalid, fub_bready, fub_arvalid, fub_arready;
    logic                       fub_rvalid, fub_rready;
    /* verilator lint_off UNUSEDSIGNAL */
    logic                       w_axil_wr_busy, w_axil_rd_busy;
    /* verilator lint_on UNUSEDSIGNAL */

    axil4_slave_wr #(
        .AXIL_ADDR_WIDTH(AXIL_ADDR_WIDTH), .AXIL_DATA_WIDTH(32),
        .SKID_DEPTH_AW(SKID_DEPTH_AW), .SKID_DEPTH_W(SKID_DEPTH_W), .SKID_DEPTH_B(SKID_DEPTH_B)
    ) u_axil_wr (
        .aclk(clk), .aresetn(rst_n),
        .s_axil_awaddr(s_axil_awaddr), .s_axil_awprot(s_axil_awprot),
        .s_axil_awvalid(s_axil_awvalid), .s_axil_awready(s_axil_awready),
        .s_axil_wdata(s_axil_wdata), .s_axil_wstrb(s_axil_wstrb),
        .s_axil_wvalid(s_axil_wvalid), .s_axil_wready(s_axil_wready),
        .s_axil_bresp(s_axil_bresp), .s_axil_bvalid(s_axil_bvalid), .s_axil_bready(s_axil_bready),
        .fub_awaddr(fub_awaddr), .fub_awprot(fub_awprot),
        .fub_awvalid(fub_awvalid), .fub_awready(fub_awready),
        .fub_wdata(fub_wdata), .fub_wstrb(fub_wstrb),
        .fub_wvalid(fub_wvalid), .fub_wready(fub_wready),
        .fub_bresp(fub_bresp), .fub_bvalid(fub_bvalid), .fub_bready(fub_bready),
        .busy(w_axil_wr_busy));

    axil4_slave_rd #(
        .AXIL_ADDR_WIDTH(AXIL_ADDR_WIDTH), .AXIL_DATA_WIDTH(32),
        .SKID_DEPTH_AR(SKID_DEPTH_AR), .SKID_DEPTH_R(SKID_DEPTH_R)
    ) u_axil_rd (
        .aclk(clk), .aresetn(rst_n),
        .s_axil_araddr(s_axil_araddr), .s_axil_arprot(s_axil_arprot),
        .s_axil_arvalid(s_axil_arvalid), .s_axil_arready(s_axil_arready),
        .s_axil_rdata(s_axil_rdata), .s_axil_rresp(s_axil_rresp),
        .s_axil_rvalid(s_axil_rvalid), .s_axil_rready(s_axil_rready),
        .fub_araddr(fub_araddr), .fub_arprot(fub_arprot),
        .fub_arvalid(fub_arvalid), .fub_arready(fub_arready),
        .fub_rdata(fub_rdata), .fub_rresp(fub_rresp),
        .fub_rvalid(fub_rvalid), .fub_rready(fub_rready),
        .busy(w_axil_rd_busy));

    // =========================================================================
    // Run bit (to the glue) and the glue's core_active (back)
    // =========================================================================
    logic r_run;
    logic w_core_active;

    assign o_run = r_run;

    // =========================================================================
    // Core ports (driven by the flavor glue below)
    // =========================================================================
    logic        w_f_req, w_d_req, w_d_wr;
    logic [31:0] w_f_addr, w_d_addr, w_d_wdata, w_f_rdata, w_d_rdata;
    logic [3:0]  w_d_mask;
    logic        r_f_rvalid, r_d_rvalid;

    // Requests count only while the core is active, so in load mode the
    // loader owns port B by construction (the core is held there anyway).
    logic w_f_go, w_d_go, w_f_hit, w_d_hit;
    assign w_f_go  = w_core_active && w_f_req;
    assign w_d_go  = w_core_active && w_d_req;
    assign w_f_hit = (w_f_addr[31:WIN_BIT] == '0);
    assign w_d_hit = (w_d_addr[31:WIN_BIT] == '0);

    // =========================================================================
    // Write side: AW holding register + B holding register (loader pattern)
    // =========================================================================
    logic [AXIL_ADDR_WIDTH-1:0] r_wr_addr;
    logic                       r_wr_pend, r_b_pend;
    logic [1:0]                 r_b_resp;
    logic                       w_aw_fire, w_w_fire, w_b_fire;
    /* verilator lint_off UNUSEDSIGNAL */
    axil_dec_t                  w_wr_dec;   // .build unused: a BUILD_ID write is SLVERR as "not mem/ctrl"
    /* verilator lint_on UNUSEDSIGNAL */
    logic                       w_wr_err, w_ld_wr, w_ctrl_wr;

    assign w_aw_fire   = fub_awvalid && fub_awready;
    assign w_w_fire    = fub_wvalid  && fub_wready;
    assign w_b_fire    = fub_bvalid  && fub_bready;
    assign fub_awready = !r_wr_pend || w_w_fire;
    assign fub_wready  = r_wr_pend && !r_b_pend;
    assign fub_bvalid  = r_b_pend;
    assign fub_bresp   = r_b_resp;

    assign w_wr_dec  = decode(r_wr_addr);
    assign w_wr_err  = !(w_wr_dec.mem || w_wr_dec.ctrl) || (w_wr_dec.mem && w_core_active);
    assign w_ld_wr   = w_w_fire && w_wr_dec.mem && !w_core_active;
    assign w_ctrl_wr = w_w_fire && w_wr_dec.ctrl && fub_wstrb[0];

    `ALWAYS_FF_RST(clk, rst_n,
        if (`RST_ASSERTED(rst_n)) begin
            r_wr_addr <= '0;
            r_wr_pend <= 1'b0;
            r_b_pend  <= 1'b0;
            r_b_resp  <= RESP_OKAY;
            r_run     <= 1'b0;
        end else begin
            if (w_aw_fire) r_wr_addr <= fub_awaddr;
            case ({w_aw_fire, w_w_fire})
                2'b10:   r_wr_pend <= 1'b1;
                2'b01:   r_wr_pend <= 1'b0;
                default: ;
            endcase
            if (w_w_fire) begin
                r_b_pend <= 1'b1;
                r_b_resp <= w_wr_err ? RESP_SLVERR : RESP_OKAY;
            end else if (w_b_fire) begin
                r_b_pend <= 1'b0;
            end
            if (w_ctrl_wr) r_run <= fub_wdata[0];
        end
    )

    // =========================================================================
    // Read side: address -> block RAM -> holding register
    // =========================================================================
    logic        r_rd_wait, r_rd_full, r_rd_mem, r_rd_err, r_rd_bank;
    logic [31:0] r_rd_reg, r_rd_data;
    logic [1:0]  r_rd_resp;
    logic        w_ar_fire, w_core_d_mem;
    axil_dec_t   w_ar_dec;
    logic [31:0] w_reg_rdata;
    logic [31:0] w_b_dout [NUM_BANKS];
    logic [31:0] w_a_dout [NUM_BANKS];

    assign w_ar_dec     = decode(fub_araddr);
    assign w_core_d_mem = w_d_go && w_d_hit;
    assign fub_arready  = !r_rd_wait && !r_rd_full && !w_ld_wr && !w_core_d_mem;
    assign w_ar_fire    = fub_arvalid && fub_arready;
    assign fub_rvalid   = r_rd_full;
    assign fub_rdata    = r_rd_data;
    assign fub_rresp    = r_rd_resp;

    assign w_reg_rdata  = w_ar_dec.build ? BUILD_ID : {30'd0, w_core_active, r_run};

    `ALWAYS_FF_RST(clk, rst_n,
        if (`RST_ASSERTED(rst_n)) begin
            r_rd_wait <= 1'b0;
            r_rd_full <= 1'b0;
            r_rd_mem  <= 1'b0;
            r_rd_err  <= 1'b0;
            r_rd_bank <= 1'b0;
            r_rd_reg  <= '0;
            r_rd_data <= '0;
            r_rd_resp <= RESP_OKAY;
        end else begin
            if (w_ar_fire) begin
                r_rd_wait <= 1'b1;
                r_rd_mem  <= w_ar_dec.mem;
                r_rd_err  <= !(w_ar_dec.mem || w_ar_dec.ctrl || w_ar_dec.build);
                r_rd_bank <= w_ar_dec.bank;
                r_rd_reg  <= w_reg_rdata;
            end else if (r_rd_wait) begin
                r_rd_wait <= 1'b0;
                r_rd_full <= 1'b1;
                r_rd_resp <= r_rd_err ? RESP_SLVERR : RESP_OKAY;
                r_rd_data <= r_rd_err ? '0 : (r_rd_mem ? w_b_dout[r_rd_bank] : r_rd_reg);
            end else if (r_rd_full && fub_rready) begin
                r_rd_full <= 1'b0;
            end
        end
    )

    // =========================================================================
    // The two banks.  Port A: core fetch.  Port B: core data access, else the
    // loader (write in load mode, or read).
    // =========================================================================
    for (genvar k = 0; k < NUM_BANKS; k++) begin : g_bank
        logic             w_a_en, w_b_en, w_core_b;
        logic [3:0]       w_b_we;
        logic [IDX_W-1:0] w_b_idx;
        logic [31:0]      w_b_din;

        assign w_a_en   = w_f_go && w_f_hit && (w_f_addr[BANK_BIT] == 1'(k));
        assign w_core_b = w_core_d_mem && (w_d_addr[BANK_BIT] == 1'(k));

        always_comb begin
            if (w_core_b) begin
                w_b_en  = 1'b1;
                w_b_we  = w_d_wr ? w_d_mask : WE_NONE;
                w_b_idx = w_d_addr[BANK_BIT-1:2];
                w_b_din = w_d_wdata;
            end else begin
                w_b_en  = (w_ld_wr   && (w_wr_dec.bank == 1'(k))) ||
                          (w_ar_fire && w_ar_dec.mem && (w_ar_dec.bank == 1'(k)));
                w_b_we  = w_ld_wr ? fub_wstrb : WE_NONE;
                w_b_idx = w_ld_wr ? w_wr_dec.idx : w_ar_dec.idx;
                w_b_din = fub_wdata;
            end
        end

        hive_c_bram #(
            .WORDS(BANK_WORDS)
        ) u_bram (
            .clk    (clk),
            .a_en   (w_a_en),
            .a_idx  (w_f_addr[BANK_BIT-1:2]),
            .a_dout (w_a_dout[k]),
            .b_en   (w_b_en),
            .b_we   (w_b_we),
            .b_idx  (w_b_idx),
            .b_din  (w_b_din),
            .b_dout (w_b_dout[k])
        );
    end : g_bank

    // =========================================================================
    // Core responses: one cycle after the request, from the bank it named
    // =========================================================================
    logic r_f_hit, r_f_bank, r_d_hit, r_d_bank;

    `ALWAYS_FF_RST(clk, rst_n,
        if (`RST_ASSERTED(rst_n)) begin
            r_f_rvalid <= 1'b0;
            r_f_hit    <= 1'b0;
            r_f_bank   <= 1'b0;
            r_d_rvalid <= 1'b0;
            r_d_hit    <= 1'b0;
            r_d_bank   <= 1'b0;
        end else begin
            r_f_rvalid <= w_f_go;
            r_d_rvalid <= w_d_go && !w_d_wr;
            if (w_f_go) begin
                r_f_hit  <= w_f_hit;
                r_f_bank <= w_f_addr[BANK_BIT];
            end
            if (w_d_go) begin
                r_d_hit  <= w_d_hit;
                r_d_bank <= w_d_addr[BANK_BIT];
            end
        end
    )

    assign w_f_rdata = r_f_hit ? w_a_dout[r_f_bank] : '0;
    assign w_d_rdata = r_d_hit ? w_b_dout[r_d_bank] : '0;

    // =========================================================================
    // Core glue, by flavor
    // =========================================================================
    // Observation nets, read by the TB only (no logic consumes them)
    /* verilator lint_off UNUSEDSIGNAL */
    logic        core_ibus_cmd_valid;
    logic [31:0] core_ibus_pc;
    logic        core_dbus_cmd_valid;
    logic        core_dbus_wr;
    logic [31:0] core_dbus_addr;
    logic [31:0] core_dbus_data;
    logic [3:0]  core_dbus_mask;
    /* verilator lint_on UNUSEDSIGNAL */

    if (CORE_FLAVOR == "vexriscv") begin : g_vexriscv
        hive_c_core_vexriscv u_core (
            .clk             (clk),
            .rst_n           (rst_n),
            .run             (r_run),
            .core_active     (w_core_active),
            .irq_external    (irq_external),
            .irq_timer       (irq_timer),
            .irq_software    (irq_software),
            .f_req           (w_f_req),
            .f_addr          (w_f_addr),
            .f_rvalid        (r_f_rvalid),
            .f_rdata         (w_f_rdata),
            .d_req           (w_d_req),
            .d_wr            (w_d_wr),
            .d_mask          (w_d_mask),
            .d_addr          (w_d_addr),
            .d_wdata         (w_d_wdata),
            .d_rvalid        (r_d_rvalid),
            .d_rdata         (w_d_rdata),
            .obs_fetch_valid (core_ibus_cmd_valid),
            .obs_fetch_pc    (core_ibus_pc),
            .obs_data_valid  (core_dbus_cmd_valid),
            .obs_data_wr     (core_dbus_wr),
            .obs_data_addr   (core_dbus_addr),
            .obs_data_wdata  (core_dbus_data),
            .obs_data_mask   (core_dbus_mask)
        );
    end else begin : g_flavor_unsupported
        // "peregrine" lands here until its glue (hive_c_core_peregrine) is built.
`ifndef SYNTHESIS
        initial $error("hive_c_loader: CORE_FLAVOR \"%s\" is not built (supported: \"vexriscv\")",
                       CORE_FLAVOR);
`endif
        assign w_core_active       = 1'b0;
        assign w_f_req             = 1'b0;
        assign w_f_addr            = '0;
        assign w_d_req             = 1'b0;
        assign w_d_wr              = 1'b0;
        assign w_d_mask            = '0;
        assign w_d_addr            = '0;
        assign w_d_wdata           = '0;
        assign core_ibus_cmd_valid = 1'b0;
        assign core_ibus_pc        = '0;
        assign core_dbus_cmd_valid = 1'b0;
        assign core_dbus_wr        = 1'b0;
        assign core_dbus_addr      = '0;
        assign core_dbus_data      = '0;
        assign core_dbus_mask      = '0;
    end

endmodule : hive_c_loader
