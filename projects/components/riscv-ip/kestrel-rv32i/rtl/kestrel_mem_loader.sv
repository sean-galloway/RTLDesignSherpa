// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: 2026 sean galloway
//
// RTL Design Sherpa - Industry-Standard RTL Design and Verification
// https://github.com/sean-galloway/RTLDesignSherpa
//
// Module: kestrel_mem_loader
// Purpose: AXIL-slave board loader for kestrel_core: two 64 KB async-read
//          LUTRAM arrays (imem, dmem) plus a CTRL register, wrapped in the
//          amba axil4_slave_wr/axil4_slave_rd skid leaf slaves exactly as
//          rtl/amba/shared/sdpram_slave_axil_axil.sv composes them.  The
//          loader owns the RAM write ports while CTRL.run == 0 (load mode:
//          the core is held in reset via core_rst_n); writing CTRL.run = 1
//          hands the write ports to the core through muxes.  Mutual
//          exclusion is by protocol -- there is no contention arbiter and
//          no FSM in the datapath; the leaf slaves supply all handshake
//          sequencing and only two holding bits (AW address, B response)
//          plus the run register exist on the write side.
//
// Address map (s_axil addr[17:0]):
//   addr[17]    = 1 -> CTRL register (bit 0 = run; writing 1 releases the
//                      core reset; power-on default is load mode)
//   addr[16]    = 1 -> dmem region, else imem region
//   addr[15:2]  = word index within the selected 16K-word region
// Byte strobes (wstrb) are honored per byte on loader writes.
//
// The two regions are one unified address space on the core side: every
// port (AXIL and core) selects imem vs dmem by address bit 16, so a flat
// image -- code, .tohost and .data interleaved by address, as the riscv-tests
// p-env links them -- behaves exactly like the unified memory of
// kestrel_tb_top (this is what keeps rv32ui-p-fence_i self-modifying code
// and any .data access coherent across the fetch and L/S ports).
//
// Memory arrays carry (* ram_style = "distributed" *) so reads stay
// combinational: a block RAM's synchronous read would break kestrel's
// single-cycle contract.  Each array has one write port and, under the
// unified address map, up to three combinational read ports: the core
// fetch, the core L/S cross read, and the AXIL readback.  Distributed RAM
// read replication absorbs that in synthesis.
//
// Documentation: projects/components/riscv-ip/README.md
// Subsystem: riscv-ip/kestrel-rv32i
//
// Author: sean galloway
// Created: 2026-10-07

`timescale 1ns / 1ps

`include "reset_defs.svh"

module kestrel_mem_loader #(
    parameter int AXIL_ADDR_WIDTH = 18,
    parameter int AXIL_DATA_WIDTH = 32,
    parameter int MEM_WORDS       = 16384,   // 64 KB of 32-bit words per region
    parameter int SKID_DEPTH_AW   = 2,
    parameter int SKID_DEPTH_W    = 2,
    parameter int SKID_DEPTH_B    = 2,
    parameter int SKID_DEPTH_AR   = 2,
    parameter int SKID_DEPTH_R    = 4
) (
    input  logic                         aclk,
    input  logic                         aresetn,

    // ---------------------------------------------------------------
    // AXIL slave write channels (AW + W + B)
    // ---------------------------------------------------------------
    input  logic [AXIL_ADDR_WIDTH-1:0]   s_axil_awaddr,
    input  logic [2:0]                   s_axil_awprot,
    input  logic                         s_axil_awvalid,
    output logic                         s_axil_awready,

    input  logic [AXIL_DATA_WIDTH-1:0]   s_axil_wdata,
    input  logic [AXIL_DATA_WIDTH/8-1:0] s_axil_wstrb,
    input  logic                         s_axil_wvalid,
    output logic                         s_axil_wready,

    output logic [1:0]                   s_axil_bresp,
    output logic                         s_axil_bvalid,
    input  logic                         s_axil_bready,

    // ---------------------------------------------------------------
    // AXIL slave read channels (AR + R)
    // ---------------------------------------------------------------
    input  logic [AXIL_ADDR_WIDTH-1:0]   s_axil_araddr,
    input  logic [2:0]                   s_axil_arprot,
    input  logic                         s_axil_arvalid,
    output logic                         s_axil_arready,

    output logic [AXIL_DATA_WIDTH-1:0]   s_axil_rdata,
    output logic [1:0]                   s_axil_rresp,
    output logic                         s_axil_rvalid,
    input  logic                         s_axil_rready,

    // ---------------------------------------------------------------
    // Core side (mirrors kestrel_core's memory interface)
    // ---------------------------------------------------------------
    input  logic [31:0]                  imem_addr,
    output logic [31:0]                  imem_rdata,
    input  logic                         dmem_req,
    input  logic [31:0]                  dmem_addr,
    output logic [31:0]                  dmem_rdata,
    input  logic [3:0]                   dmem_wstrb,
    input  logic [31:0]                  dmem_wdata,
    output logic                         core_rst_n,

    // ---------------------------------------------------------------
    // Debug (leaf-slave busy taps)
    // ---------------------------------------------------------------
    output logic                         o_dbg_busy_wr,
    output logic                         o_dbg_busy_rd
);

    // ---------------------------------------------------------------
    // Derived constants and the fixed address map
    // ---------------------------------------------------------------
    localparam int STRB_W       = AXIL_DATA_WIDTH / 8;
    localparam int WORD_IDX_W   = $clog2(MEM_WORDS);
    localparam int CTRL_BIT     = 17;   // addr[17] = 1 -> CTRL register
    localparam int DMEM_BIT     = 16;   // addr[16] = 1 -> dmem, else imem
    localparam int BYTE_LANES   = 4;
    localparam int BYTE_WIDTH   = 8;
    localparam logic [1:0] AXIL_RESP_OKAY = 2'b00;
    localparam logic [3:0] CORE_STRB_NONE = 4'b0000;

    // ---------------------------------------------------------------
    // Memory arrays: distributed RAM keeps the read combinational
    // ---------------------------------------------------------------
    (* ram_style = "distributed" *) logic [31:0] imem [0:MEM_WORDS-1];
    (* ram_style = "distributed" *) logic [31:0] dmem [0:MEM_WORDS-1];

    // Power-up content is undefined in hardware; the loader protocol does
    // not depend on it (an image is always loaded before run).  The sim
    // zero-init mirrors kestrel_tb_top so pre-load reads are deterministic.
    initial begin
        for (int i = 0; i < MEM_WORDS; i++) begin
            imem[i] = '0;
            dmem[i] = '0;
        end
    end

    // ---------------------------------------------------------------
    // AXIL FUB nets between the skid leaf slaves and this wrapper
    // ---------------------------------------------------------------
    logic [AXIL_ADDR_WIDTH-1:0]     fub_awaddr;
    /* verilator lint_off UNUSED */
    logic [2:0]                     fub_awprot;
    logic [2:0]                     fub_arprot;
    /* verilator lint_on UNUSED */
    logic                           fub_awvalid, fub_awready;
    logic [AXIL_DATA_WIDTH-1:0]     fub_wdata;
    logic [STRB_W-1:0]              fub_wstrb;
    logic                           fub_wvalid,  fub_wready;
    logic [1:0]                     fub_bresp;
    logic                           fub_bvalid,  fub_bready;

    logic [AXIL_ADDR_WIDTH-1:0]     fub_araddr;
    logic                           fub_arvalid, fub_arready;
    logic [AXIL_DATA_WIDTH-1:0]     fub_rdata;
    logic [1:0]                     fub_rresp;
    logic                           fub_rvalid,  fub_rready;

    // ---------------------------------------------------------------
    // CTRL register: bit 0 = run (sticky until reset).  Load mode is the
    // power-on default; core_rst_n IS the run bit inverted role -- low in
    // load mode (core held), high once run is written.
    // ---------------------------------------------------------------
    logic run_q;

    assign core_rst_n = run_q;

    // ---------------------------------------------------------------
    // Write side: AW-address holding register + B-response holding bit.
    // W is consumed only when an address is pending (AXIL pairs W with the
    // oldest AW); the B response returns OKAY one holding bit deep, which
    // the leaf's B skid buffers against the master.
    // ---------------------------------------------------------------
    logic [AXIL_ADDR_WIDTH-1:0] wr_addr_q;
    logic                       wr_addr_pending_q;
    logic                       b_pending_q;

    logic aw_fire;
    logic w_fire;
    logic b_fire;

    assign aw_fire = fub_awvalid && fub_awready;
    assign w_fire  = fub_wvalid  && fub_wready;
    assign b_fire  = fub_bvalid  && fub_bready;

    // A new AW is accepted when no address is pending, or when the pending
    // one is consumed by a W beat in the same cycle.
    assign fub_awready = !wr_addr_pending_q || w_fire;
    // W is accepted only with a pending address and an empty B slot, so
    // writes complete in order and at most one B is outstanding.
    assign fub_wready  = wr_addr_pending_q && !b_pending_q;
    assign fub_bvalid  = b_pending_q;
    assign fub_bresp   = AXIL_RESP_OKAY;

    `ALWAYS_FF_RST(aclk, aresetn,
        if (`RST_ASSERTED(aresetn)) begin
            wr_addr_q         <= '0;
            wr_addr_pending_q <= 1'b0;
            b_pending_q       <= 1'b0;
            run_q             <= 1'b0;
        end else begin
            if (aw_fire) begin
                wr_addr_q <= fub_awaddr;
            end
            unique case ({aw_fire, w_fire})
                2'b10:   wr_addr_pending_q <= 1'b1;
                2'b01:   wr_addr_pending_q <= 1'b0;
                2'b11:   wr_addr_pending_q <= 1'b1;  // swap: new AW in as old W fires
                default: ;
            endcase
            if (w_fire) begin
                b_pending_q <= 1'b1;
                if (wr_addr_q[CTRL_BIT] && fub_wstrb[0] && fub_wdata[0]) begin
                    run_q <= 1'b1;
                end
            end else if (b_fire) begin
                b_pending_q <= 1'b0;
            end
        end
    )

    // ---------------------------------------------------------------
    // Write-port clients
    // ---------------------------------------------------------------
    logic                       ld_wr_fire;
    logic                       ld_wr_imem;
    logic                       ld_wr_dmem;
    logic [WORD_IDX_W-1:0]      ld_wr_idx;
    logic                       core_wr_fire;
    logic                       core_wr_imem;
    logic                       core_wr_dmem;
    logic [WORD_IDX_W-1:0]      core_wr_idx;

    // Loader writes land while in load mode and the address maps to a
    // memory region (CTRL writes only touch the register).  The !run_q
    // term makes "the loader owns the write ports only in load mode" true
    // by construction -- writes in run mode were already unreachable by
    // protocol, this just says so in logic.
    assign ld_wr_fire = w_fire && !wr_addr_q[CTRL_BIT] && !run_q;
    assign ld_wr_idx  = wr_addr_q[WORD_IDX_W-1:0];
    assign ld_wr_imem = ld_wr_fire && !wr_addr_q[DMEM_BIT];
    assign ld_wr_dmem = ld_wr_fire &&  wr_addr_q[DMEM_BIT];

    // Core stores own both write ports in run mode; the array is selected
    // by the store address (unified address space, see header).
    assign core_wr_fire = run_q && dmem_req && (dmem_wstrb != CORE_STRB_NONE);
    assign core_wr_idx  = dmem_addr[WORD_IDX_W-1:0];
    assign core_wr_imem = core_wr_fire && !dmem_addr[DMEM_BIT];
    assign core_wr_dmem = core_wr_fire &&  dmem_addr[DMEM_BIT];

    // Both clients merge per byte lane, exactly the rotated-strobe contract
    // of kestrel_tb_top's store port.  Reset-gated like the TB store port:
    // in load mode the mux already hands the ports to the loader, this only
    // additionally fences writes during reset assertion.
    `ALWAYS_FF_RST(aclk, aresetn,
        begin
            if (!`RST_ASSERTED(aresetn)) begin
                if (ld_wr_imem) begin
                    for (int b = 0; b < BYTE_LANES; b++) begin
                        if (fub_wstrb[b]) begin
                            imem[ld_wr_idx][b*BYTE_WIDTH +: BYTE_WIDTH]
                                <= fub_wdata[b*BYTE_WIDTH +: BYTE_WIDTH];
                        end
                    end
                end
                if (core_wr_imem) begin
                    for (int b = 0; b < BYTE_LANES; b++) begin
                        if (dmem_wstrb[b]) begin
                            imem[core_wr_idx][b*BYTE_WIDTH +: BYTE_WIDTH]
                                <= dmem_wdata[b*BYTE_WIDTH +: BYTE_WIDTH];
                        end
                    end
                end
                if (ld_wr_dmem) begin
                    for (int b = 0; b < BYTE_LANES; b++) begin
                        if (fub_wstrb[b]) begin
                            dmem[ld_wr_idx][b*BYTE_WIDTH +: BYTE_WIDTH]
                                <= fub_wdata[b*BYTE_WIDTH +: BYTE_WIDTH];
                        end
                    end
                end
                if (core_wr_dmem) begin
                    for (int b = 0; b < BYTE_LANES; b++) begin
                        if (dmem_wstrb[b]) begin
                            dmem[core_wr_idx][b*BYTE_WIDTH +: BYTE_WIDTH]
                                <= dmem_wdata[b*BYTE_WIDTH +: BYTE_WIDTH];
                        end
                    end
                end
            end
        end
    )

    // ---------------------------------------------------------------
    // Read side: combinational.  The core fetch and L/S ports select the
    // array by address bit 16; the AXIL read channel gets its own port and
    // answers in the cycle AR presents (the leaf's R skid registers it).
    // ---------------------------------------------------------------
    assign imem_rdata = imem_addr[DMEM_BIT] ? dmem[imem_addr[WORD_IDX_W-1:0]]
                                            : imem[imem_addr[WORD_IDX_W-1:0]];
    assign dmem_rdata = dmem_addr[DMEM_BIT] ? dmem[dmem_addr[WORD_IDX_W-1:0]]
                                            : imem[dmem_addr[WORD_IDX_W-1:0]];

    // AR is accepted exactly when the leaf's R skid can take the response
    // beat (fub_rready is the leaf's output); the AR skid then holds
    // addr/valid stable until the skid drains.  The response itself is a
    // single-cycle combinational beat: fub_arvalid qualifies fub_rdata.
    assign fub_arready = fub_rready;
    assign fub_rvalid  = fub_arvalid;
    assign fub_rresp   = AXIL_RESP_OKAY;

    always_comb begin
        if (fub_araddr[CTRL_BIT]) begin
            fub_rdata = {{(AXIL_DATA_WIDTH-1){1'b0}}, run_q};
        end else if (fub_araddr[DMEM_BIT]) begin
            fub_rdata = dmem[fub_araddr[WORD_IDX_W-1:0]];
        end else begin
            fub_rdata = imem[fub_araddr[WORD_IDX_W-1:0]];
        end
    end

    // ---------------------------------------------------------------
    // AXIL skid leaf slaves (identical composition to
    // sdpram_slave_axil_axil.sv)
    // ---------------------------------------------------------------
    axil4_slave_wr #(
        .AXIL_ADDR_WIDTH (AXIL_ADDR_WIDTH),
        .AXIL_DATA_WIDTH (AXIL_DATA_WIDTH),
        .SKID_DEPTH_AW   (SKID_DEPTH_AW),
        .SKID_DEPTH_W    (SKID_DEPTH_W),
        .SKID_DEPTH_B    (SKID_DEPTH_B)
    ) u_axil_wr (
        .aclk           (aclk),
        .aresetn        (aresetn),

        .s_axil_awaddr  (s_axil_awaddr),
        .s_axil_awprot  (s_axil_awprot),
        .s_axil_awvalid (s_axil_awvalid),
        .s_axil_awready (s_axil_awready),

        .s_axil_wdata   (s_axil_wdata),
        .s_axil_wstrb   (s_axil_wstrb),
        .s_axil_wvalid  (s_axil_wvalid),
        .s_axil_wready  (s_axil_wready),

        .s_axil_bresp   (s_axil_bresp),
        .s_axil_bvalid  (s_axil_bvalid),
        .s_axil_bready  (s_axil_bready),

        .fub_awaddr     (fub_awaddr),
        .fub_awprot     (fub_awprot),
        .fub_awvalid    (fub_awvalid),
        .fub_awready    (fub_awready),

        .fub_wdata      (fub_wdata),
        .fub_wstrb      (fub_wstrb),
        .fub_wvalid     (fub_wvalid),
        .fub_wready     (fub_wready),

        .fub_bresp      (fub_bresp),
        .fub_bvalid     (fub_bvalid),
        .fub_bready     (fub_bready),

        .busy           (o_dbg_busy_wr)
    );

    axil4_slave_rd #(
        .AXIL_ADDR_WIDTH (AXIL_ADDR_WIDTH),
        .AXIL_DATA_WIDTH (AXIL_DATA_WIDTH),
        .SKID_DEPTH_AR   (SKID_DEPTH_AR),
        .SKID_DEPTH_R    (SKID_DEPTH_R)
    ) u_axil_rd (
        .aclk           (aclk),
        .aresetn        (aresetn),

        .s_axil_araddr  (s_axil_araddr),
        .s_axil_arprot  (s_axil_arprot),
        .s_axil_arvalid (s_axil_arvalid),
        .s_axil_arready (s_axil_arready),

        .s_axil_rdata   (s_axil_rdata),
        .s_axil_rresp   (s_axil_rresp),
        .s_axil_rvalid  (s_axil_rvalid),
        .s_axil_rready  (s_axil_rready),

        .fub_araddr     (fub_araddr),
        .fub_arprot     (fub_arprot),
        .fub_arvalid    (fub_arvalid),
        .fub_arready    (fub_arready),

        .fub_rdata      (fub_rdata),
        .fub_rresp      (fub_rresp),
        .fub_rvalid     (fub_rvalid),
        .fub_rready     (fub_rready),

        .busy           (o_dbg_busy_rd)
    );

endmodule : kestrel_mem_loader
