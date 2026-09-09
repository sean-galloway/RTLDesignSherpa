// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: 2024-2025 sean galloway
//
// RTL Design Sherpa - Industry-Standard RTL Design and Verification
// https://github.com/sean-galloway/RTLDesignSherpa
//
// Module: pit_config_regs
// Purpose: Register wrapper for the 8254 PIT - PeakRDL block plus the strict
//          address decode and the aligned command strobes the core needs
//
// ARCHITECTURE:
//   cmd/rsp --> peakrdl_to_cmdrsp adapter --> decode gate --> pit_regs
//               (PeakRDL) --> hwif --> mapping --> pit_core
//
// ============================================================================
// STRICT ADDRESS DECODE  (GitHub #52 qc round_2, item 1)
// ============================================================================
// pit_regs decodes FIVE address bits, so without qualification every address in
// the 4 KB window aliased into the 32-byte register map: 0x800 read PIT_CONFIG,
// 0x024 wrote PIT_CONTROL, 0x210 wrote COUNTER0_DATA. Worse, the side-effect
// strobes in this file compared the full 12 bits while the register block
// compared five, so an aliased write stored the value WITHOUT executing it -
// two decodes that disagreed, which is the shape of defect a mirrored-decode
// assertion exists to catch.
//
// The policy now matches the ioapic and pic_8259 blocks: ONLY the seven mapped
// registers are software-visible, by equality on the whole 12-bit address.
// Everything else in the window is dropped - write ignored, read returns zero -
// and answers with PSLVERR (which used to be tied off entirely). The strobes
// below compare exactly the five bits the register block decodes, and are
// reached only from an address this file has already accepted.
//
// Dropped accesses are acknowledged locally and combinationally, in the same
// shape the register block acks: peakrdl_to_cmdrsp HOLDS its request until an
// ack, so gating the request off without one would hang the APB.
//
// ============================================================================
// COMMAND STROBES ARE ONE CYCLE, ALIGNED, AND BYTE-ENABLE QUALIFIED
// ============================================================================
// peakrdl_to_cmdrsp holds regblk_req from the accept cycle through
// CMD_WAIT_ACK, so anything derived from the register decode is a two-cycle
// LEVEL, not a pulse (handbook: generated-rtl-discipline, "swmod behind
// peakrdl_to_cmdrsp is a LEVEL"). Taken at face value every COUNTERx_DATA write
// loaded the counter TWICE - cycle one with the stale capture, cycle two with
// the real value - so a running counter passed through a bogus intermediate
// count, and a stale 0 with GATE high could pulse OUT and the interrupt
// (GitHub #52 qc round_3, item 1).
//
// So: rising-edge detect the level (one transaction, one event), then delay the
// pulse ONE flop. The delay is what makes the strobe usable as a data strobe -
// the field storage loads at the end of the FIRST request cycle, so only in the
// delayed cycle does the field hold the value that was just written.
//
// The load data is therefore taken from the FIELD VALUE (hwif_out), not from
// regblk_wr_data. That is what makes byte strobes work: the register block
// merges the write into the field per bit-enable, so the unstrobed lanes carry
// the field's value instead of whatever garbage rode on those lanes of PWDATA
// (GitHub #52 qc round_2, item 3). The same argument is why hpet takes its
// byte-strobed data from the field value.
//
// BE PRECISE ABOUT WHAT IT MERGES WITH. These fields are hw = rw and
// hwif_in.next is the LIVE counter read-back, so outside the one cycle a
// software write owns, the field mirrors the counter's current count - it is
// not a shadow of the last value written. A byte-strobed write to a RUNNING
// counter therefore merges the new byte with that counter's value as of the
// write cycle, and the result is only as stable as the count was: a partial
// load is deterministic when the PIT is disabled (or the counter otherwise
// stopped), and any full 16-bit write is deterministic always because no lane
// comes from the mirror. Software that wants a defined partial load of a
// running counter must stop it first, or write all 16 bits.
//
// The byte-enable qualifier on the strobe itself (`|biten` over the field's own
// lanes) is the other half: a write that enables NO byte of a register changes
// nothing in storage, so firing a strobe on it would make the core re-execute
// the value already there.
//
// The three COUNTERx_DATA READ strobes exist for the counter latch: a read
// returns the latched count and RELEASES the latch (pit_counter.sv). They are
// edge-detected and delayed the same way, which puts the release one cycle
// after the adapter captured the read data - the access that releases the latch
// is still the access that sees the latched value.
//
// Documentation: projects/components/retro_legacy_blocks/rtl/pit_8254/README.md
// Subsystem: retro_legacy_blocks/pit_8254
//
// Updated: 2026-09-09 - GitHub #52: strict decode with PSLVERR, one-cycle
//                       aligned strobes, field-value load data, counter read
//                       strobes for the latch
//          2026-09-09 - #52 review follow-up: byte-merge contract restated
//                       against the LIVE count the field mirrors

`timescale 1ns / 1ps

`include "reset_defs.svh"

module pit_config_regs
    import pit_regs_pkg::*;
(
    input wire clk,
    input wire rst_n,  // Active-low asynchronous reset

    // Command/Response Interface (from apb4_slave / apb4_slave_cdc)
    input  wire        cmd_valid,
    output wire        cmd_ready,
    input  wire        cmd_pwrite,
    input  wire [11:0] cmd_paddr,
    input  wire [31:0] cmd_pwdata,
    input  wire [3:0]  cmd_pstrb,

    output wire        rsp_valid,
    input  wire        rsp_ready,
    output wire [31:0] rsp_prdata,
    output wire        rsp_pslverr,

    // PIT Core Interface
    output wire        pit_enable,
    output wire        clock_select,

    output wire        control_wr,          // One cycle per control word write
    output wire        bcd,
    output wire [2:0]  mode,
    output wire [1:0]  rw_mode,
    output wire [1:0]  counter_select,

    output wire        counter0_data_wr,    // One cycle per COUNTER0_DATA write
    output wire        counter0_data_rd,    // One cycle per COUNTER0_DATA read
    output wire [15:0] counter0_data,       // Field value - byte-enable merged
    input  wire [15:0] counter0_readback,   // Current counter 0 value
    output wire        counter1_data_wr,
    output wire        counter1_data_rd,
    output wire [15:0] counter1_data,
    input  wire [15:0] counter1_readback,
    output wire        counter2_data_wr,
    output wire        counter2_data_rd,
    output wire [15:0] counter2_data,
    input  wire [15:0] counter2_readback,

    input  wire [7:0]  counter0_status,
    input  wire [7:0]  counter1_status,
    input  wire [7:0]  counter2_status
);

    //========================================================================
    // Local Parameters
    //========================================================================

    // Register-block addresses. These MUST track pit_regs.rdl - the mirrored
    // decode assertion at the bottom of this file is what says so out loud.
    localparam logic [4:0] ADDR_CONFIG   = 5'h00;
    localparam logic [4:0] ADDR_CONTROL  = 5'h04;
    localparam logic [4:0] ADDR_STATUS   = 5'h08;
    localparam logic [4:0] ADDR_RSVD_0C  = 5'h0C;
    localparam logic [4:0] ADDR_COUNTER0 = 5'h10;
    localparam logic [4:0] ADDR_COUNTER1 = 5'h14;
    localparam logic [4:0] ADDR_COUNTER2 = 5'h18;

    // Strobe vector indices
    localparam int STB_CONTROL  = 0;
    localparam int STB_COUNTER0 = 1;
    localparam int STB_COUNTER1 = 2;
    localparam int STB_COUNTER2 = 3;
    localparam int STB_COUNT    = 4;

    localparam int RD_COUNT     = 3;   // one read strobe per counter

    //========================================================================
    // Signals
    //========================================================================

    // From the adapter, before the decode gate
    logic        adapter_req;
    logic        adapter_req_is_wr;
    logic [11:0] adapter_addr;
    logic [31:0] adapter_wr_data;
    logic [31:0] adapter_wr_biten;
    logic        adapter_req_stall_wr;
    logic        adapter_req_stall_rd;
    logic        adapter_rd_ack;
    logic        adapter_rd_err;
    logic [31:0] adapter_rd_data;
    logic        adapter_wr_ack;
    logic        adapter_wr_err;

    // To the register block, after the decode gate
    logic        regblk_req;
    logic [4:0]  regblk_addr;
    logic        regblk_req_stall_wr;
    logic        regblk_req_stall_rd;
    logic        regblk_rd_ack;
    logic        regblk_rd_err;
    logic [31:0] regblk_rd_data;
    logic        regblk_wr_ack;
    logic        regblk_wr_err;

    // Decode
    logic        w_addr_mapped;
    logic        w_drop;
    logic        w_drop_ack;

    // Write strobes: level, delayed level, edge, aligned pulse
    logic                 w_wr_byte0;    // write enabled byte 0 (control word)
    logic                 w_wr_half;     // write enabled a counter data byte
    logic [STB_COUNT-1:0] w_wr_level;
    logic [STB_COUNT-1:0] r_wr_level_d;
    logic [STB_COUNT-1:0] w_wr_edge;
    logic [STB_COUNT-1:0] r_wr_stb;

    // Counter data read strobes, same shape
    logic [RD_COUNT-1:0]  w_rd_level;
    logic [RD_COUNT-1:0]  r_rd_level_d;
    logic [RD_COUNT-1:0]  w_rd_edge;
    logic [RD_COUNT-1:0]  r_rd_stb;

    // Hardware interface structs
    pit_regs__in_t  hwif_in;
    pit_regs__out_t hwif_out;

    //========================================================================
    // CMD/RSP to PeakRDL Adapter
    //========================================================================

    peakrdl_to_cmdrsp #(
        .ADDR_WIDTH(12),
        .DATA_WIDTH(32)
    ) u_adapter (
        .aclk               (clk),
        .aresetn            (rst_n),

        // CMD/RSP interface (external)
        .cmd_valid          (cmd_valid),
        .cmd_ready          (cmd_ready),
        .cmd_pwrite         (cmd_pwrite),
        .cmd_paddr          (cmd_paddr),
        .cmd_pwdata         (cmd_pwdata),
        .cmd_pstrb          (cmd_pstrb),

        .rsp_valid          (rsp_valid),
        .rsp_ready          (rsp_ready),
        .rsp_prdata         (rsp_prdata),
        .rsp_pslverr        (rsp_pslverr),

        // PeakRDL passthrough interface (to the decode gate)
        .regblk_req         (adapter_req),
        .regblk_req_is_wr   (adapter_req_is_wr),
        .regblk_addr        (adapter_addr),
        .regblk_wr_data     (adapter_wr_data),
        .regblk_wr_biten    (adapter_wr_biten),
        .regblk_req_stall_wr(adapter_req_stall_wr),
        .regblk_req_stall_rd(adapter_req_stall_rd),
        .regblk_rd_ack      (adapter_rd_ack),
        .regblk_rd_err      (adapter_rd_err),
        .regblk_rd_data     (adapter_rd_data),
        .regblk_wr_ack      (adapter_wr_ack),
        .regblk_wr_err      (adapter_wr_err)
    );

    //========================================================================
    // Strict Address Decode
    //========================================================================
    // Equality on the WHOLE 12-bit address, register by register. An alias such
    // as 0x024 shares its low five bits with PIT_CONTROL and is exactly what
    // this rejects.

    always_comb begin
        w_addr_mapped = (adapter_addr == {7'h00, ADDR_CONFIG})   ||
                        (adapter_addr == {7'h00, ADDR_CONTROL})  ||
                        (adapter_addr == {7'h00, ADDR_STATUS})   ||
                        (adapter_addr == {7'h00, ADDR_RSVD_0C})  ||
                        (adapter_addr == {7'h00, ADDR_COUNTER0}) ||
                        (adapter_addr == {7'h00, ADDR_COUNTER1}) ||
                        (adapter_addr == {7'h00, ADDR_COUNTER2});
    end

    assign w_drop      = !w_addr_mapped;
    assign regblk_req  = adapter_req && !w_drop;
    assign regblk_addr = adapter_addr[4:0];

    // Local acknowledge for a dropped access, in the same combinational form
    // the register block uses. The adapter holds its request until acked.
    assign w_drop_ack = adapter_req && w_drop;

    assign adapter_req_stall_wr = regblk_req_stall_wr;
    assign adapter_req_stall_rd = regblk_req_stall_rd;
    assign adapter_rd_ack  = regblk_rd_ack | (w_drop_ack & ~adapter_req_is_wr);
    assign adapter_rd_err  = regblk_rd_err | (w_drop_ack & ~adapter_req_is_wr);
    assign adapter_rd_data = w_drop_ack ? 32'h0 : regblk_rd_data;
    assign adapter_wr_ack  = regblk_wr_ack | (w_drop_ack & adapter_req_is_wr);
    assign adapter_wr_err  = regblk_wr_err | (w_drop_ack & adapter_req_is_wr);

    //========================================================================
    // Command Strobes - mirror the regblock decode, edge-detect, then align
    //========================================================================

    // Byte-enable terms. The control word lives entirely in byte 0; a counter
    // value occupies the low half-word.
    assign w_wr_byte0 = |adapter_wr_biten[7:0];
    assign w_wr_half  = |adapter_wr_biten[15:0];

    always_comb begin
        w_wr_level = '0;
        w_wr_level[STB_CONTROL]  = regblk_req && adapter_req_is_wr && w_wr_byte0 &&
                                   (regblk_addr == ADDR_CONTROL);
        w_wr_level[STB_COUNTER0] = regblk_req && adapter_req_is_wr && w_wr_half &&
                                   (regblk_addr == ADDR_COUNTER0);
        w_wr_level[STB_COUNTER1] = regblk_req && adapter_req_is_wr && w_wr_half &&
                                   (regblk_addr == ADDR_COUNTER1);
        w_wr_level[STB_COUNTER2] = regblk_req && adapter_req_is_wr && w_wr_half &&
                                   (regblk_addr == ADDR_COUNTER2);
    end

    always_comb begin
        w_rd_level = '0;
        w_rd_level[0] = regblk_req && !adapter_req_is_wr && (regblk_addr == ADDR_COUNTER0);
        w_rd_level[1] = regblk_req && !adapter_req_is_wr && (regblk_addr == ADDR_COUNTER1);
        w_rd_level[2] = regblk_req && !adapter_req_is_wr && (regblk_addr == ADDR_COUNTER2);
    end

    assign w_wr_edge = w_wr_level & ~r_wr_level_d;
    assign w_rd_edge = w_rd_level & ~r_rd_level_d;

    `ALWAYS_FF_RST(clk, rst_n,
        if (`RST_ASSERTED(rst_n)) begin
            r_wr_level_d <= '0;
            r_wr_stb     <= '0;
            r_rd_level_d <= '0;
            r_rd_stb     <= '0;
        end else begin
            r_wr_level_d <= w_wr_level;
            r_wr_stb     <= w_wr_edge;
            r_rd_level_d <= w_rd_level;
            r_rd_stb     <= w_rd_edge;
        end
    )

    //========================================================================
    // Hardware Interface Inputs
    //========================================================================

    assign hwif_in.PIT_STATUS.counter0_status.next = counter0_status;
    assign hwif_in.PIT_STATUS.counter1_status.next = counter1_status;
    assign hwif_in.PIT_STATUS.counter2_status.next = counter2_status;

    // The counter data fields are hw = rw: hardware feeds back the live count
    // so a read returns it, and a software write wins for the cycle it lands
    // in - which is what gives the byte-enable merge a stored value to merge
    // WITH (see the header).
    assign hwif_in.COUNTER0_DATA.counter0_data.next = counter0_readback;
    assign hwif_in.COUNTER1_DATA.counter1_data.next = counter1_readback;
    assign hwif_in.COUNTER2_DATA.counter2_data.next = counter2_readback;

    //========================================================================
    // PeakRDL Generated Register File
    //========================================================================

    pit_regs u_pit_regs (
        .clk                   (clk),
        .rst                   (~rst_n),   // PeakRDL uses active-high reset
        .s_cpuif_req           (regblk_req),
        .s_cpuif_req_is_wr     (adapter_req_is_wr),
        .s_cpuif_addr          (regblk_addr),
        .s_cpuif_wr_data       (adapter_wr_data),
        .s_cpuif_wr_biten      (adapter_wr_biten),
        .s_cpuif_req_stall_wr  (regblk_req_stall_wr),
        .s_cpuif_req_stall_rd  (regblk_req_stall_rd),
        .s_cpuif_rd_ack        (regblk_rd_ack),
        .s_cpuif_rd_err        (regblk_rd_err),
        .s_cpuif_rd_data       (regblk_rd_data),
        .s_cpuif_wr_ack        (regblk_wr_ack),
        .s_cpuif_wr_err        (regblk_wr_err),
        .hwif_in               (hwif_in),
        .hwif_out              (hwif_out)
    );

    //========================================================================
    // Outputs to the PIT Core
    //========================================================================

    assign pit_enable   = hwif_out.PIT_CONFIG.pit_enable.value;
    assign clock_select = hwif_out.PIT_CONFIG.clock_select.value;

    assign bcd            = hwif_out.PIT_CONTROL.bcd.value;
    assign mode           = hwif_out.PIT_CONTROL.mode.value;
    assign rw_mode        = hwif_out.PIT_CONTROL.rw_mode.value;
    assign counter_select = hwif_out.PIT_CONTROL.counter_select.value;
    assign control_wr     = r_wr_stb[STB_CONTROL];

    // Load data is the FIELD value, byte-enable merged by the register block,
    // sampled in the aligned strobe cycle. It is NOT regblk_wr_data - that is
    // the raw bus word, unstrobed lanes and all.
    assign counter0_data    = hwif_out.COUNTER0_DATA.counter0_data.value;
    assign counter1_data    = hwif_out.COUNTER1_DATA.counter1_data.value;
    assign counter2_data    = hwif_out.COUNTER2_DATA.counter2_data.value;

    assign counter0_data_wr = r_wr_stb[STB_COUNTER0];
    assign counter1_data_wr = r_wr_stb[STB_COUNTER1];
    assign counter2_data_wr = r_wr_stb[STB_COUNTER2];

    assign counter0_data_rd = r_rd_stb[0];
    assign counter1_data_rd = r_rd_stb[1];
    assign counter2_data_rd = r_rd_stb[2];

    //========================================================================
    // Simulation-only contract checks
    //========================================================================
`ifndef SYNTHESIS
`ifndef VERILATOR
    // Mirrored-decode drift guard. Every address presented to the register
    // block must be one its own generated decode recognises. If the RDL moves
    // or adds a register, this trips instead of the access silently reading
    // zero and writing nowhere - which is how the 0x024 alias hid.
    logic w_regblk_addr_mapped;
    always_comb begin
        w_regblk_addr_mapped = (regblk_addr == ADDR_CONFIG)   ||
                               (regblk_addr == ADDR_CONTROL)  ||
                               (regblk_addr == ADDR_STATUS)   ||
                               (regblk_addr == ADDR_RSVD_0C)  ||
                               (regblk_addr == ADDR_COUNTER0) ||
                               (regblk_addr == ADDR_COUNTER1) ||
                               (regblk_addr == ADDR_COUNTER2);
    end

    a_regblk_addr_mapped: assert property (
        @(posedge clk) disable iff (`RST_ASSERTED(rst_n))
        regblk_req |-> w_regblk_addr_mapped
    ) else $error({"pit_config_regs: presented 0x%02h to the register block, which ",
                   "the generated decode does not recognise - the RDL has drifted ",
                   "from the localparams in this file"}, regblk_addr);

    // One transaction, one strobe. The bridge holds its request for exactly two
    // cycles; a longer level would mean the edge detect is no longer enough.
    a_wr_level_max_two: assert property (
        @(posedge clk) disable iff (`RST_ASSERTED(rst_n))
        (|w_wr_edge) |-> ##2 (w_wr_level == '0)
    ) else $error("pit_config_regs: a register write level lasted more than two cycles");

    a_rd_level_max_two: assert property (
        @(posedge clk) disable iff (`RST_ASSERTED(rst_n))
        (|w_rd_edge) |-> ##2 (w_rd_level == '0)
    ) else $error("pit_config_regs: a counter read level lasted more than two cycles");

    // A dropped access must never reach the register block, and must always be
    // answered - the adapter holds its request until it is.
    a_drop_never_reaches_regblk: assert property (
        @(posedge clk) disable iff (`RST_ASSERTED(rst_n))
        (adapter_req && w_drop) |-> !regblk_req
    ) else $error("pit_config_regs: a dropped access reached the register block");

    a_drop_is_acked: assert property (
        @(posedge clk) disable iff (`RST_ASSERTED(rst_n))
        (adapter_req && w_drop) |-> (adapter_rd_ack || adapter_wr_ack)
    ) else $error("pit_config_regs: a dropped access was not acknowledged");
`endif
`endif

endmodule
