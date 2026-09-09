// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: 2024-2025 sean galloway
//
// RTL Design Sherpa - Industry-Standard RTL Design and Verification
// https://github.com/sean-galloway/RTLDesignSherpa
//
// Module: hpet_config_regs
// Purpose: HPET Configuration Registers - PeakRDL wrapper
//
// Documentation: projects/components/retro_legacy_blocks/rtl/hpet/README.md
// Subsystem: hpet
//
// Author: sean galloway
// Created: 2025-10-18
// Updated: 2026-09-09 - issue #46 review: simulation-time NUM_TIMERS guard

/**
* ============================================================================
* HPET Configuration Registers - PeakRDL Wrapper
* ============================================================================
*
* DESCRIPTION:
*   Wrapper that instantiates the PeakRDL-generated register block and the
*   cmd/rsp protocol adapter, and maps between the generated hwif signals and
*   the hpet_core interface.
*
* ARCHITECTURE:
*   cmd/rsp --> peakrdl_to_cmdrsp --> hpet_regs (PeakRDL) --> hwif --> hpet_core
*
* WRITE-STROBE CONTRACT (issue #46)
*   Everything this block hands to hpet_core is driven by the register WRITE
*   STROBE, never by a change in a stored value. The regblock exports `swmod`
*   for HPET_STATUS, HPET_COUNTER_LO/HI and every TIMER_COMPARATOR_LO/HI, and
*   two corrections are needed before it can be used as an operation pulse:
*
*     1. It is a LEVEL, not a pulse. peakrdl_to_cmdrsp deliberately HOLDS
*        regblk_req from the accept cycle through CMD_WAIT_ACK (see the
*        warning in that file - shortening it broke every register read), so
*        swmod is asserted for the whole transaction, at least two cycles.
*     2. It leads the field storage by one cycle: it is asserted while the
*        field is still taking the written value.
*
*   So each strobe here is a RISING-EDGE detect on the swmod level (one
*   transaction, one pulse) delayed ONE flop, which lands it in the cycle
*   where the field presents the newly written value. The strobe's data is
*   then read straight out of the field, which is what makes byte strobes
*   work: the regblock has already merged `(value & ~biten) | (wr_data &
*   biten)` for us, where sampling regblk_wr_data raw would write whole
*   32-bit words on a partial-byte write.
*
*   REQUIREMENT on the upstream cpuif: regblk_req must DE-ASSERT between
*   transactions, or two back-to-back writes to one register look like one
*   long level and produce a single strobe. That holds for apb4_slave and
*   apb4_slave_cdc (both strictly one-outstanding); the a_*_swmod_len
*   assertions at the bottom of this file trip if it ever stops holding.
*
* HPET_STATUS W1C (issue #46 C1 / C2 / round_2)
*   hpet_core OWNS the sticky interrupt status. HPET_STATUS is a mirror: its
*   field is driven from the core's live level every cycle (hw = w), and the
*   software write is turned into a PER-BIT clear pulse into the core.
*
*   The clear mask comes from the write itself - `regblk_wr_data &
*   regblk_wr_biten`, masked to NUM_TIMERS bits - so a bit clears only if
*   software wrote a 1 to it, and a write of 0x0 is the no-op that W1C
*   requires. The write is detected by MIRRORING the regblock's own decode
*   rather than by using swmod, for the reason gpio_config_regs documents:
*   swmod carries an extra `|biten` term that the regblock's write branch
*   does not, so the two are not interchangeable as a decode. The
*   a_status_swmod_mirrored assertion is the drift guard.
*
*   The clear is narrowed to ONE cycle (rising edge of the mirrored decode)
*   even though the mask makes it idempotent. The two-cycle level would
*   otherwise eat a fire that landed in its FIRST cycle: hpet_core sets the
*   status bit, and the level's second cycle clears it again. One cycle plus
*   fire-over-clear priority in the core closes that window.
*
* HPET_ID
*   num_tim_cap, vendor_id and rev_id are all hw = w and driven from this
*   module's parameters, so one generated regblock (NUM_TIMERS = 8) serves
*   every instantiation. vendor_id/rev_id are 8-bit fields here, so only the
*   low byte of a wider VENDOR_ID/REVISION_ID parameter is visible.
* ============================================================================
*/

`timescale 1ns / 1ps

/* verilator lint_off SYNCASYNCNET */
// Note: rst_n connects to both async reset (the ALWAYS_FF_RST flops here) and
// peakrdl_to_cmdrsp (sync reset via macros). This is intentional - both uses
// are in the same clock domain.

`include "reset_defs.svh"

module hpet_config_regs #(
    parameter int VENDOR_ID = 1,
    parameter int REVISION_ID = 1,
    parameter int NUM_TIMERS = 2
)(
    // Clock and Reset
    input  logic                    clk,
    input  logic                    rst_n,

    // Command/Response Interface
    input  logic                    cmd_valid,
    output logic                    cmd_ready,
    input  logic                    cmd_pwrite,
    input  logic [11:0]             cmd_paddr,
    input  logic [31:0]             cmd_pwdata,
    input  logic [3:0]              cmd_pstrb,

    output logic                    rsp_valid,
    input  logic                    rsp_ready,
    output logic [31:0]             rsp_prdata,
    output logic                    rsp_pslverr,

    // HPET Core Interface
    output logic                    hpet_enable,
    output logic                    legacy_replacement,

    output logic                    counter_write_lo,
    output logic                    counter_write_hi,
    output logic [63:0]             counter_wdata,
    input  logic [63:0]             counter_rdata,

    output logic [NUM_TIMERS-1:0]   timer_enable,
    output logic [NUM_TIMERS-1:0]   timer_int_enable,
    output logic [NUM_TIMERS-1:0]   timer_type,
    output logic [NUM_TIMERS-1:0]   timer_size,
    output logic [NUM_TIMERS-1:0]   timer_value_set,

    output logic [NUM_TIMERS-1:0]   timer_comp_write_lo,
    output logic [NUM_TIMERS-1:0]   timer_comp_write_hi,
    output logic [63:0]             timer_comp_wdata [NUM_TIMERS],  // Per-timer bus

    input  logic [NUM_TIMERS-1:0]   timer_int_status,
    output logic [NUM_TIMERS-1:0]   timer_int_clear
);

    // ========================================================================
    // Local Parameters
    // ========================================================================
    // Register offsets, as decoded by the generated regblock (it is handed
    // regblk_addr[8:0], so these are the 9-bit forms that appear in
    // hpet_regs.sv's decoded_reg_strb).
    localparam logic [8:0] ADDR_HPET_STATUS = 9'h008;

    // The generated regblock is always built for 8 timers and a 32-bit
    // register width, independent of NUM_TIMERS.
    localparam int REG_TIMERS = 8;

    // ========================================================================
    // Simulation-time parameter validation
    // ========================================================================
    // NUM_TIMERS indexes hwif_out.TIMER[] in the generated regblock, which is
    // built for REG_TIMERS timers, and drives HPET_ID.num_tim_cap as
    // NUM_TIMERS-1 in a 5-bit field. More timers than the regblock has is an
    // out-of-range index; fewer than one has no legal [NUM_TIMERS-1:0] slice.
    //
    // This is an `initial` block, so it runs at time 0 in SIMULATION - it is
    // not an elaboration-time check and cannot stop a synthesis run. Gated by
    // `ifndef SYNTHESIS` for the same reason every other sim-only construct in
    // this block is.
`ifndef SYNTHESIS
    initial begin : param_check
        if (NUM_TIMERS < 1 || NUM_TIMERS > REG_TIMERS) begin
            $error("hpet_config_regs: NUM_TIMERS=%0d out of range [1,%0d]",
                   NUM_TIMERS, REG_TIMERS);
        end
    end
`endif

    // ========================================================================
    // Signal Declarations
    // ========================================================================

    // PeakRDL passthrough interface
    logic                regblk_req;
    logic                regblk_req_is_wr;
    logic [11:0]         regblk_addr;
    logic [31:0]         regblk_wr_data;
    logic [31:0]         regblk_wr_biten;
    logic                regblk_req_stall_wr;
    logic                regblk_req_stall_rd;
    logic                regblk_rd_ack;
    logic                regblk_rd_err;
    logic [31:0]         regblk_rd_data;
    logic                regblk_wr_ack;
    logic                regblk_wr_err;

    // Hardware interface structs
    hpet_regs_pkg::hpet_regs__in_t  hwif_in;
    hpet_regs_pkg::hpet_regs__out_t hwif_out;

    // Counter write strobes: swmod level, its delayed copy, and the aligned
    // strobe handed to the core.
    logic                  w_counter_lo_swmod;
    logic                  w_counter_hi_swmod;
    logic                  r_counter_lo_swmod_d;
    logic                  r_counter_hi_swmod_d;

    // Comparator write strobes, per timer
    logic [NUM_TIMERS-1:0] w_comp_lo_swmod;
    logic [NUM_TIMERS-1:0] w_comp_hi_swmod;
    logic [NUM_TIMERS-1:0] r_comp_lo_swmod_d;
    logic [NUM_TIMERS-1:0] r_comp_hi_swmod_d;

    // HPET_STATUS write decode (mirror of the regblock's own decode) and the
    // one-cycle clear it produces
    logic                  w_status_sw_wr;
    logic                  r_status_sw_wr_d;
    logic                  w_status_wr_event;
    logic [NUM_TIMERS-1:0] w_status_w1c_mask;

    // Zero-extended views of the NUM_TIMERS-wide core signals for the 8-bit
    // HPET_STATUS field
    logic [REG_TIMERS-1:0] w_timer_int_status_reg;

    // ========================================================================
    // Instantiate Protocol Adapter
    // ========================================================================

    peakrdl_to_cmdrsp #(
        .ADDR_WIDTH(12),
        .DATA_WIDTH(32)
    ) u_adapter (
        .aclk               (clk),
        .aresetn            (rst_n),

        // cmd/rsp interface (external)
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

        // PeakRDL passthrough interface (to register block)
        .regblk_req         (regblk_req),
        .regblk_req_is_wr   (regblk_req_is_wr),
        .regblk_addr        (regblk_addr),  // Full 12-bit address
        .regblk_wr_data     (regblk_wr_data),
        .regblk_wr_biten    (regblk_wr_biten),
        .regblk_req_stall_wr(regblk_req_stall_wr),
        .regblk_req_stall_rd(regblk_req_stall_rd),
        .regblk_rd_ack      (regblk_rd_ack),
        .regblk_rd_err      (regblk_rd_err),
        .regblk_rd_data     (regblk_rd_data),
        .regblk_wr_ack      (regblk_wr_ack),
        .regblk_wr_err      (regblk_wr_err)
    );

    // ========================================================================
    // Instantiate PeakRDL-Generated Register Block
    // ========================================================================
    // Note: the register block is generated once for the maximum
    // configuration (8 timers); VENDOR_ID / REVISION_ID / NUM_TIMERS are
    // localparams in hpet_regs_pkg and cannot be overridden at
    // instantiation, which is why the ID fields are driven through hwif_in
    // from this module's parameters instead.

    hpet_regs u_hpet_regs (
        .clk                (clk),
        .rst                (~rst_n),  // PeakRDL uses active-high reset

        // Passthrough CPU interface
        .s_cpuif_req        (regblk_req),
        .s_cpuif_req_is_wr  (regblk_req_is_wr),
        .s_cpuif_addr       (regblk_addr[8:0]),
        .s_cpuif_wr_data    (regblk_wr_data),
        .s_cpuif_wr_biten   (regblk_wr_biten),
        .s_cpuif_req_stall_wr(regblk_req_stall_wr),
        .s_cpuif_req_stall_rd(regblk_req_stall_rd),
        .s_cpuif_rd_ack     (regblk_rd_ack),
        .s_cpuif_rd_err     (regblk_rd_err),
        .s_cpuif_rd_data    (regblk_rd_data),
        .s_cpuif_wr_ack     (regblk_wr_ack),
        .s_cpuif_wr_err     (regblk_wr_err),

        // Hardware interface
        .hwif_in            (hwif_in),
        .hwif_out           (hwif_out)
    );

    // ========================================================================
    // Global Config - direct mapping
    // ========================================================================
    assign hpet_enable = hwif_out.HPET_CONFIG.hpet_enable.value;

    // NOTE: legacy_replacement is storage only. Nothing in hpet_core routes
    // timer 0/1 to the legacy 8254/RTC interrupt lines, which is why
    // HPET_ID.leg_rt_cap reports 0 (see hpet_regs.rdl).
    assign legacy_replacement = hwif_out.HPET_CONFIG.legacy_replacement.value;

    // ========================================================================
    // Main Counter Write Strobes (issue #46 C3)
    // ========================================================================
    // Each half is loaded on its OWN aligned strobe, from its OWN field, so a
    // "write LO then write HI" sequence lands both halves. The previous
    // scheme captured both halves into flops and re-applied the pair on
    // either strobe, which meant the second write always shipped the first
    // write's stale partner.

    assign w_counter_lo_swmod = hwif_out.HPET_COUNTER_LO.counter_lo.swmod;
    assign w_counter_hi_swmod = hwif_out.HPET_COUNTER_HI.counter_hi.swmod;

    `ALWAYS_FF_RST(clk, rst_n,
        if (`RST_ASSERTED(rst_n)) begin
            r_counter_lo_swmod_d <= 1'b0;
            r_counter_hi_swmod_d <= 1'b0;
            counter_write_lo     <= 1'b0;
            counter_write_hi     <= 1'b0;
        end else begin
            r_counter_lo_swmod_d <= w_counter_lo_swmod;
            r_counter_hi_swmod_d <= w_counter_hi_swmod;
            counter_write_lo     <= w_counter_lo_swmod & ~r_counter_lo_swmod_d;
            counter_write_hi     <= w_counter_hi_swmod & ~r_counter_hi_swmod_d;
        end
    )

    // In the aligned strobe cycle the field holds the value the write just
    // committed (byte strobes already merged by the regblock); one cycle
    // later the hardware write-back resumes mirroring the live counter.
    assign counter_wdata = {hwif_out.HPET_COUNTER_HI.counter_hi.value,
                            hwif_out.HPET_COUNTER_LO.counter_lo.value};

    // ========================================================================
    // Timer Config and Comparator Write Strobes
    // ========================================================================
    generate
        for (genvar i = 0; i < NUM_TIMERS; i++) begin : g_timer_mapping
            assign timer_enable[i]     = hwif_out.TIMER[i].TIMER_CONFIG.timer_enable.value;
            assign timer_int_enable[i] = hwif_out.TIMER[i].TIMER_CONFIG.timer_int_enable.value;
            assign timer_type[i]       = hwif_out.TIMER[i].TIMER_CONFIG.timer_type.value;
            assign timer_size[i]       = hwif_out.TIMER[i].TIMER_CONFIG.timer_size.value;

            // timer_value_set has NO effect: nothing downstream consumes it.
            // See the field description in hpet_regs.rdl.
            assign timer_value_set[i]  = hwif_out.TIMER[i].TIMER_CONFIG.timer_value_set.value;

            assign w_comp_lo_swmod[i] =
                hwif_out.TIMER[i].TIMER_COMPARATOR_LO.timer_comp_lo.swmod;
            assign w_comp_hi_swmod[i] =
                hwif_out.TIMER[i].TIMER_COMPARATOR_HI.timer_comp_hi.swmod;

            // Comparator fields are hw = r, so the value is simply whatever
            // software last wrote; the strobe is what tells the core to
            // reload it, which is what makes rewriting the SAME value work.
            assign timer_comp_wdata[i] = {
                hwif_out.TIMER[i].TIMER_COMPARATOR_HI.timer_comp_hi.value,
                hwif_out.TIMER[i].TIMER_COMPARATOR_LO.timer_comp_lo.value
            };
        end
    endgenerate

    `ALWAYS_FF_RST(clk, rst_n,
        if (`RST_ASSERTED(rst_n)) begin
            r_comp_lo_swmod_d   <= '0;
            r_comp_hi_swmod_d   <= '0;
            timer_comp_write_lo <= '0;
            timer_comp_write_hi <= '0;
        end else begin
            r_comp_lo_swmod_d   <= w_comp_lo_swmod;
            r_comp_hi_swmod_d   <= w_comp_hi_swmod;
            timer_comp_write_lo <= w_comp_lo_swmod & ~r_comp_lo_swmod_d;
            timer_comp_write_hi <= w_comp_hi_swmod & ~r_comp_hi_swmod_d;
        end
    )

    // ========================================================================
    // HPET_ID - driven from this module's parameters
    // ========================================================================
    assign hwif_in.HPET_ID.num_tim_cap.next = 5'(NUM_TIMERS - 1);
    assign hwif_in.HPET_ID.vendor_id.next   = 8'(VENDOR_ID);
    assign hwif_in.HPET_ID.rev_id.next      = 8'(REVISION_ID);

    // ========================================================================
    // Counter Readback
    // ========================================================================
    // hw = w + precedence = sw: hardware writes the live counter every cycle,
    // a software write wins in its own cycle.
    assign hwif_in.HPET_COUNTER_LO.counter_lo.next = counter_rdata[31:0];
    assign hwif_in.HPET_COUNTER_HI.counter_hi.next = counter_rdata[63:32];

    // ========================================================================
    // HPET_STATUS - mirror out, per-bit W1C in
    // ========================================================================
    // The field is 8 bits wide in the generated regblock regardless of
    // NUM_TIMERS. Zero-extending here is what keeps bits >= NUM_TIMERS - which
    // have no corresponding timer - reading as 0 forever.
    always_comb begin
        w_timer_int_status_reg                  = '0;
        w_timer_int_status_reg[NUM_TIMERS-1:0]  = timer_int_status;
    end

    assign hwif_in.HPET_STATUS.timer_int_status.next = w_timer_int_status_reg;

    // Mirror of the regblock's own write decode. hpet_regs.sv decodes
    //   decoded_reg_strb.HPET_STATUS = cpuif_req_masked & (cpuif_addr == 9'h8)
    // on the same 9 address bits this module feeds it, and both cpuif stalls
    // are tied low inside the regblock, so cpuif_req_masked == regblk_req.
    // a_status_swmod_mirrored below fires if a regenerated regblock changes
    // that decode.
    assign w_status_sw_wr = regblk_req && regblk_req_is_wr &&
                            (regblk_addr[8:0] == ADDR_HPET_STATUS);

    // One event per transaction: the request is held for the whole
    // transaction, and a clear that spans two cycles would undo a fire that
    // hpet_core accepted in the first of them.
    assign w_status_wr_event = w_status_sw_wr & ~r_status_sw_wr_d;

    `ALWAYS_FF_RST(clk, rst_n,
        if (`RST_ASSERTED(rst_n)) begin
            r_status_sw_wr_d <= 1'b0;
        end else begin
            r_status_sw_wr_d <= w_status_sw_wr;
        end
    )

    // Per-bit W1C: regblk_wr_data/regblk_wr_biten are combinational into the
    // regblock's decode, so during the request they ARE the mask of the write
    // the regblock is committing. A bit clears only if software wrote a 1 to
    // it; a write of 0x0 clears nothing, as W1C requires.
    assign w_status_w1c_mask = regblk_wr_data[NUM_TIMERS-1:0] &
                               regblk_wr_biten[NUM_TIMERS-1:0];

    assign timer_int_clear = w_status_wr_event ? w_status_w1c_mask : '0;

    // ========================================================================
    // Simulation-only contract checks
    // ========================================================================
`ifndef SYNTHESIS
`ifndef VERILATOR
    // Drift guard for the mirrored HPET_STATUS write decode. swmod is that
    // same decode ANDed with |wr_biten, so swmod high with the mirror low is
    // impossible unless the generated regblock's decode has changed under
    // this module - at which point W1C silently stops reaching hpet_core.
    a_status_swmod_mirrored: assert property (
        @(posedge clk) disable iff (`RST_ASSERTED(rst_n))
        hwif_out.HPET_STATUS.timer_int_status.swmod |-> w_status_sw_wr
    ) else $error("hpet_config_regs: HPET_STATUS swmod asserted without the ",
                  "mirrored regblock decode -- w_status_sw_wr has drifted ",
                  "from hpet_regs.sv and the per-bit W1C no longer reaches ",
                  "hpet_core");

    // The write strobes are rising-edge detects on a swmod level. The
    // upstream bridge holds regblk_req for the accept cycle plus
    // CMD_WAIT_ACK - two cycles - and then drops it, so three consecutive
    // cycles means the cpuif has become pipelined and two writes are being
    // merged into one strobe.
    property p_swmod_max_two(logic swmod_level);
        @(posedge clk) disable iff (`RST_ASSERTED(rst_n))
        not (swmod_level [*3]);
    endproperty

    a_counter_lo_swmod_len: assert property (p_swmod_max_two(w_counter_lo_swmod))
        else $error("hpet_config_regs: HPET_COUNTER_LO swmod held >2 cycles -- ",
                    "the cpuif no longer drops regblk_req between writes, so ",
                    "the rising-edge detect merges them");
    a_counter_hi_swmod_len: assert property (p_swmod_max_two(w_counter_hi_swmod))
        else $error("hpet_config_regs: HPET_COUNTER_HI swmod held >2 cycles -- ",
                    "the cpuif no longer drops regblk_req between writes, so ",
                    "the rising-edge detect merges them");
    a_status_wr_len: assert property (p_swmod_max_two(w_status_sw_wr))
        else $error("hpet_config_regs: HPET_STATUS write request held >2 ",
                    "cycles -- the cpuif no longer drops regblk_req between ",
                    "writes, so the rising-edge detect merges them");

    for (genvar gi = 0; gi < NUM_TIMERS; gi++) begin : g_comp_swmod_assert
        a_comp_lo_swmod_len: assert property (p_swmod_max_two(w_comp_lo_swmod[gi]))
            else $error("hpet_config_regs: TIMER_COMPARATOR_LO swmod held >2 ",
                        "cycles -- the cpuif no longer drops regblk_req ",
                        "between writes, so the rising-edge detect merges them");
        a_comp_hi_swmod_len: assert property (p_swmod_max_two(w_comp_hi_swmod[gi]))
            else $error("hpet_config_regs: TIMER_COMPARATOR_HI swmod held >2 ",
                        "cycles -- the cpuif no longer drops regblk_req ",
                        "between writes, so the rising-edge detect merges them");
    end
`endif
`endif

/* verilator lint_on SYNCASYNCNET */
endmodule : hpet_config_regs
