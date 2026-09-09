// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: 2024-2025 sean galloway
//
// RTL Design Sherpa - Industry-Standard RTL Design and Verification
// https://github.com/sean-galloway/RTLDesignSherpa
//
// Module: pit_counter
// Purpose: One Intel 8254 counter - 16-bit, binary or BCD, Mode 0
//
// ============================================================================
// WHAT THIS COUNTER IMPLEMENTS
// ============================================================================
// MODE 0 (interrupt on terminal count) ONLY. cfg_mode is captured into the
// status shadow so read-back reports what software programmed, but there is
// no `case (cfg_mode)` anywhere in the counting logic: modes 1-5 count exactly
// like mode 0. That is a stated deviation, not an oversight; the block's full
// deviation list is in README.md.
//
// ============================================================================
// GATE  (GitHub #52, C1)
// ============================================================================
// Mode 0 GATE is an ENABLE, not a trigger and not a reload:
//
//   GATE low   -> counting SUSPENDS, the count holds its current value
//   GATE high  -> counting RESUMES from that value (no reload, no restart)
//   Load       -> unaffected by GATE. The value lands whatever GATE is doing;
//                 only the decrement is gated.
//
// GATE therefore appears in the decrement condition (`w_tick`), which is the
// whole fix for C1. It used to appear ONLY at load time and in a bogus re-arm
// branch, so once the counter was running a GATE transition did nothing at all
// until terminal count - the MAS documented pause/resume that did not exist.
//
// i_gate arrives ALREADY SYNCHRONIZED to clk (pit_core owns the synchronizer);
// nothing in this file may sample a raw pin.
//
// ============================================================================
// COUNT 0 MEANS 65536  (GitHub #52 re-verification comment)
// ============================================================================
// Terminal count is detected on the DECREMENTED value, never on the loaded
// one. So a load of N counts N-1, N-2, ... 1, 0 and asserts OUT as it reaches
// 0 - N decrements - and a load of 0 counts 0xFFFF, 0xFFFE, ... 0, i.e. a full
// 65536 (BCD: 10000) before OUT, exactly as the 8254 defines it. Testing
// `r_count == 0` BEFORE decrementing, which is what this used to do, made a
// load of 0 an immediate terminal count.
//
// ============================================================================
// ONE STEADY STATE AFTER TERMINAL COUNT  (GitHub #52, recurring)
// ============================================================================
// At terminal count the counter STOPS: r_counting clears and nothing re-arms
// it except a new load (count_reg_wr). The single steady state is
//
//     r_counting = 0,  r_count = 0,  r_out = 1
//
// and it holds until software loads a new count or writes a control word.
// There is deliberately no "GATE went high, so start again" branch: that
// branch is what made r_counting oscillate 0,1,0,1,... forever after terminal
// count, because it re-armed on the same GATE that was still high, and the
// terminal branch stopped it again one cycle later.
//
// DEVIATION from the 8254, stated: a real 8254 counter keeps decrementing past
// terminal count and wraps (OUT stays high until reprogrammed). Here it parks
// at 0. Mode 0 has no consumer for the post-terminal count - OUT and the
// status byte carry everything software can act on - and a parked counter
// makes "0 and stopped" unambiguous evidence of terminal count instead of a
// value that depends on when you looked.
//
// ============================================================================
// ONE PRIORITY CHAIN IN THE COUNTING BLOCK
// ============================================================================
//     cfg_control_wr  >  count_reg_wr  >  w_tick
//
// A control word ABORTS the count: OUT low, NULL COUNT set, and no tick that
// cycle. A load starts a new count. Only when neither happened does the counter
// decrement. The three are mutually exclusive branches of ONE if/else-if chain,
// which is the whole point: as two sequential `if`s a control word arriving on
// the terminal tick had its `r_out <= 1'b0` overwritten by the tick's
// `r_out <= 1'b1`, raising a spurious interrupt with NULL COUNT set, and on a
// non-terminal tick the abort still lost one extra count.
//
// cfg_control_wr and count_reg_wr cannot arrive together (they are different
// APB transactions and APB is one-outstanding), so their relative order is a
// stated tiebreak rather than a resolved race; the tick, which is free-running,
// is the one that genuinely had to be subordinated.
//
// ============================================================================
// LATCH IS A COMMAND, LOADS ARE WRITES  (GitHub #52 qc round_2, item 2)
// ============================================================================
// cfg_latch_cmd (a control word with RW = 00, decoded in pit_core) latches the
// CURRENT count. The counter keeps running underneath the latch. The next READ
// of this counter's data register (count_reg_rd) returns the frozen value and
// RELEASES the latch; reads after that see the live count again. A second
// latch command before the read is ignored, so the first latched value
// survives - the 8254 rule.
//
// The latch is held until it is read OR until the counter is REPROGRAMMED: a
// program control word (cfg_control_wr) and a load (count_reg_wr) both release
// it, because the count the snapshot describes has ceased to exist. A latch
// that outlived a reprogram would hand software a stale snapshot of the old
// program on its next read, indistinguishable from a live count.
//
// A DATA WRITE NEVER LATCHES. It used to: the RW = 00 case in the write path
// latched instead of loading, and since RW resets to 00 a counter that had
// never seen a control word could not be loaded at all. RW = 00 is not a
// programmable read/write mode on the 8254 - it is the latch OPCODE in the
// control word - so out of reset it is treated here as "16-bit load", which is
// the only useful reading of it on the write side.
//
// ============================================================================
// BYTE LANES  (GitHub #52 qc round_2, items 3-4)
// ============================================================================
// count_reg_in is the register block's FIELD value, already byte-enable merged
// by the regblock (pit_config_regs takes it at the aligned strobe). This file
// only picks lanes out of it:
//
//   RW = 11 / 00 : load all 16 bits
//   RW = 01      : load {8'h00, in[7:0]}      (LSB only)
//   RW = 10      : load {in[15:8], 8'h00}     (MSB only, from the NATURAL
//                                              high lane - it used to take
//                                              in[7:0], so a 0xAB00 write
//                                              loaded zero)
//
// READ lanes mirror the write lanes: RW = 10 reads return {count[15:8], 8'h00},
// the high byte on the lane it was written on, and RW = 01 returns
// {8'h00, count[7:0]}. An 8254 presents the selected byte on its 8-bit bus;
// on this 16-bit register one lane per byte in both directions is the
// convention (a write of 0xAB00 reads back 0xAB00), and
// dv/tbclasses/pit_8254/pit_tests_medium.py asserts it.
//
// Documentation: projects/components/retro_legacy_blocks/rtl/pit_8254/README.md
// Subsystem: retro_legacy_blocks/pit_8254
//
// Updated: 2026-09-09 - GitHub #52: GATE pause/resume, count 0 = 65536,
//                       latch-as-command, byte lanes, single post-terminal
//                       steady state, dead byte-state machines removed
//          2026-09-09 - #52 review follow-up: one priority chain
//                       (control word > load > tick) so a control word on the
//                       terminal tick cannot raise OUT; latch released by a
//                       reprogram as well as by a read

`timescale 1ns / 1ps

`include "reset_defs.svh"

module pit_counter (
    input  wire        clk,
    input  wire        rst_n,             // Active-low asynchronous reset

    // Configuration inputs (from the control word register)
    input  wire        cfg_bcd,           // 0 = binary, 1 = BCD counting
    input  wire [2:0]  cfg_mode,          // Counter mode (0-5); only 0 is implemented
    input  wire [1:0]  cfg_rw_mode,       // Read/write mode from the control word
    input  wire        cfg_control_wr,    // Control word PROGRAM strobe (RW != 00)
    input  wire        cfg_latch_cmd,     // Control word LATCH command (RW == 00)

    // Counter data interface
    input  wire [15:0] count_reg_in,      // Load data - regblock field value
    input  wire        count_reg_wr,      // One-cycle aligned load strobe
    input  wire        count_reg_rd,      // One-cycle aligned data-read strobe
    output logic [15:0] count_reg_out,    // Count presented for read-back

    // Hardware interface
    input  wire        i_gate,            // GATE, synchronized by pit_core
    input  wire        i_clk_en,          // Counting clock enable (PIT enable)
    output wire        o_out,             // OUT / interrupt

    // Status outputs (for the status register)
    output wire        o_null_count,      // NULL COUNT - no value loaded yet
    output wire [1:0]  o_status_rw_mode,
    output wire [2:0]  o_status_mode,
    output wire        o_status_bcd
);

    //========================================================================
    // Local Parameters
    //========================================================================

    // Control word RW field. There is deliberately no RW_LATCH constant here:
    // 2'b00 is the latch OPCODE, decoded in pit_core into cfg_latch_cmd, so it
    // never arrives as a programmed cfg_rw_mode. Where it does appear - the
    // reset value of the shadow - it falls into the `default` lane below and
    // means "16-bit", which is the only useful reading of it on the data path.
    localparam logic [1:0] RW_LSB = 2'b01;
    localparam logic [1:0] RW_MSB = 2'b10;

    //========================================================================
    // Internal State
    //========================================================================

    logic [15:0] r_count;          // Live count
    logic [15:0] r_count_latch;    // Frozen count for an atomic read
    logic        r_count_latched;  // Latch holds a value not yet read

    logic        r_null_count;     // 1 = control word written, no count loaded
    logic        r_counting;       // 1 = a count is in progress (GATE gates it)
    logic        r_out;            // OUT state

    // Configuration shadow - what read-back reports for this counter
    logic        r_cfg_bcd;
    logic [2:0]  r_cfg_mode;
    logic [1:0]  r_cfg_rw_mode;

    //========================================================================
    // Combinational
    //========================================================================

    logic [15:0] w_read_source;    // Latched value if latched, else live count
    logic [15:0] w_load_value;     // count_reg_in after RW lane selection
    logic [15:0] w_next_count;     // r_count decremented (binary or BCD)
    logic        w_tick;           // This cycle actually counts

    //========================================================================
    // Decrement (binary or BCD)
    //========================================================================

    function automatic logic [15:0] decrement_count(input logic [15:0] count,
                                                    input logic        bcd_mode);
        logic [15:0] result;
        result = count;
        if (bcd_mode) begin
            // 4-decade BCD borrow chain: 0000 -> 9999
            if (result[3:0] == 4'h0) begin
                result[3:0] = 4'h9;
                if (result[7:4] == 4'h0) begin
                    result[7:4] = 4'h9;
                    if (result[11:8] == 4'h0) begin
                        result[11:8] = 4'h9;
                        if (result[15:12] == 4'h0) begin
                            result[15:12] = 4'h9;
                        end else begin
                            result[15:12] = result[15:12] - 4'h1;
                        end
                    end else begin
                        result[11:8] = result[11:8] - 4'h1;
                    end
                end else begin
                    result[7:4] = result[7:4] - 4'h1;
                end
            end else begin
                result[3:0] = result[3:0] - 4'h1;
            end
        end else begin
            // Binary, and the 0 -> 0xFFFF wrap is what makes a load of 0 count
            // 65536 times instead of terminating immediately.
            result = count - 16'h1;
        end
        return result;
    endfunction

    //========================================================================
    // Status and Read-back
    //========================================================================

    assign o_null_count     = r_null_count;
    assign o_status_rw_mode = r_cfg_rw_mode;
    assign o_status_mode    = r_cfg_mode;
    assign o_status_bcd     = r_cfg_bcd;
    assign o_out            = r_out;

    assign w_read_source = r_count_latched ? r_count_latch : r_count;

    // Read lanes - one lane per byte in both directions: RW = 10 reads the
    // high byte back in [15:8], the lane it was written on (see BYTE LANES
    // in the header).
    always_comb begin
        case (r_cfg_rw_mode)
            RW_LSB:  count_reg_out = {8'h00, w_read_source[7:0]};
            RW_MSB:  count_reg_out = {w_read_source[15:8], 8'h00};
            default: count_reg_out = w_read_source;   // RW = 11 and RW = 00
        endcase
    end

    // Write lanes
    always_comb begin
        case (r_cfg_rw_mode)
            RW_LSB:  w_load_value = {8'h00, count_reg_in[7:0]};
            RW_MSB:  w_load_value = {count_reg_in[15:8], 8'h00};
            default: w_load_value = count_reg_in;     // RW = 11 and RW = 00
        endcase
    end

    // A cycle counts only when a count is in progress, the PIT is enabled, and
    // GATE is high. This is the C1 fix in one line.
    assign w_tick       = r_counting && i_clk_en && i_gate;
    assign w_next_count = decrement_count(r_count, r_cfg_bcd);

    //========================================================================
    // Configuration Shadow (control word PROGRAM write)
    //========================================================================
    // A latch command carries no mode/RW/BCD programming and must NOT disturb
    // this shadow - on the 8254 RW = 00 is the latch opcode, and latching a
    // counter does not reprogram it.

    `ALWAYS_FF_RST(clk, rst_n,
        if (`RST_ASSERTED(rst_n)) begin
            r_cfg_bcd     <= 1'b0;
            r_cfg_mode    <= 3'h0;
            r_cfg_rw_mode <= 2'h0;
        end else if (cfg_control_wr) begin
            r_cfg_bcd     <= cfg_bcd;
            r_cfg_mode    <= cfg_mode;
            r_cfg_rw_mode <= cfg_rw_mode;
        end
    )

    //========================================================================
    // Counter Latch (RW = 00 control word command)
    //========================================================================
    // ONE always_ff owns both latch flops. They used to be driven from two
    // separate blocks - the write path set them, the read path cleared them -
    // which is a MULTIDRIVEN violation that only survived because the flow
    // waives MULTIDRIVEN and the two conditions happened to be exclusive
    // (GitHub #52 qc round_3, item 2). r_count_latch also had no reset.
    //
    // LATCH LIFETIME (8254): a latched count is held until it is READ, or until
    // the counter is REPROGRAMMED. Release therefore has three sources:
    //
    //   count_reg_rd   - software read it (the point of latching)
    //   cfg_control_wr - a control word REPROGRAMMED this counter, so the count
    //                    the snapshot describes no longer exists
    //   count_reg_wr   - a new count was loaded, same argument
    //
    // Without the last two, a latch armed and never read survived a reprogram
    // and the NEXT read returned a snapshot of the OLD program - stale by an
    // arbitrary amount and indistinguishable, to software, from a live count.
    //
    // The SET and the RELEASE are separate statements, not an if/else chain, so
    // a release can never be suppressed by a coincident latch command: the set
    // keeps its "first latch wins" guard (`!r_count_latched`, the 8254 rule
    // that a second latch before the read is ignored), and the release, being
    // the later non-blocking assignment, always wins the cycle they collide in.
    // Today's bridge cannot actually produce that collision - a latch command
    // is a PIT_CONTROL write and every release source is a different
    // transaction, and APB is strictly one-outstanding - so this is ordering
    // stated on purpose rather than a race being resolved.
    //
    // Release on a read is one cycle AFTER the read data was presented (the
    // strobe is aligned in pit_config_regs), so the access that releases the
    // latch is still the access that sees the latched value.

    `ALWAYS_FF_RST(clk, rst_n,
        if (`RST_ASSERTED(rst_n)) begin
            r_count_latch   <= 16'h0;
            r_count_latched <= 1'b0;
        end else begin
            if (cfg_latch_cmd && !r_count_latched) begin
                r_count_latch   <= r_count;
                r_count_latched <= 1'b1;
            end

            if (count_reg_rd || cfg_control_wr || count_reg_wr) begin
                r_count_latched <= 1'b0;
            end
        end
    )

    //========================================================================
    // Counter Core - Mode 0
    //========================================================================

    `ALWAYS_FF_RST(clk, rst_n,
        if (`RST_ASSERTED(rst_n)) begin
            r_count      <= 16'h0;
            r_null_count <= 1'b1;
            r_counting   <= 1'b0;
            r_out        <= 1'b0;
        end else if (cfg_control_wr) begin
            // Programming a counter ABORTS the count in progress: OUT low,
            // NULL COUNT set, and NO tick this cycle - the count freezes at the
            // value the abort caught.
            //
            // This branch has to OUTRANK the tick, and it did not: the control
            // word and the count used to be two sequential `if` statements in
            // this block, so a control word landing in the same cycle as the
            // terminal tick let the tick's `r_out <= 1'b1` overwrite the
            // control word's `r_out <= 1'b0` (last non-blocking assignment
            // wins). The result was OUT high WITH NULL COUNT set - a
            // self-contradictory spurious interrupt that never cleared, because
            // r_counting was correctly aborted and nothing else touches r_out.
            // On a non-terminal tick the same shape stole one extra decrement
            // after the abort.
            r_null_count <= 1'b1;
            r_counting   <= 1'b0;
            r_out        <= 1'b0;
        end else if (count_reg_wr) begin
            // ONE strobe, ONE load: count_reg_wr is already edge-detected and
            // aligned with the field storage in pit_config_regs, so the count
            // goes old -> new with no stale intermediate value and no spurious
            // OUT (GitHub #52 qc round_3, item 1). The load is not gated by
            // GATE or by the PIT enable - only counting is.
            r_count      <= w_load_value;
            r_null_count <= 1'b0;
            r_counting   <= 1'b1;
            r_out        <= 1'b0;
        end else if (w_tick) begin
            r_count <= w_next_count;
            if (w_next_count == 16'h0) begin
                r_out      <= 1'b1;
                r_counting <= 1'b0;
            end
        end
    )

    //========================================================================
    // Simulation-only contract checks
    //========================================================================
`ifndef SYNTHESIS
`ifndef VERILATOR
    // The steady state named in the header. Nothing but a load may restart a
    // stopped counter - this is the oscillation guard.
    a_no_self_rearm: assert property (
        @(posedge clk) disable iff (`RST_ASSERTED(rst_n))
        (!r_counting && !count_reg_wr) |=> !r_counting
    ) else $error("pit_counter: r_counting re-armed with no load");

    // GATE low may not move the count.
    a_gate_holds: assert property (
        @(posedge clk) disable iff (`RST_ASSERTED(rst_n))
        (!i_gate && !count_reg_wr) |=> $stable(r_count)
    ) else $error("pit_counter: count moved with GATE low");

    // A data write never latches, and a latch never loads.
    a_latch_is_a_command: assert property (
        @(posedge clk) disable iff (`RST_ASSERTED(rst_n))
        (count_reg_wr && !r_count_latched) |=> !r_count_latched
    ) else $error("pit_counter: a data write latched the counter");

    // The priority chain, stated as properties. A control word drives OUT low
    // in the very next cycle no matter what the counter was doing - including
    // reaching terminal count in that same cycle, which is the case that used
    // to raise a spurious interrupt.
    a_ctrl_word_clears_out: assert property (
        @(posedge clk) disable iff (`RST_ASSERTED(rst_n))
        cfg_control_wr |=> !r_out
    ) else $error("pit_counter: OUT still high the cycle after a control word");

    // ...and OUT cannot RISE again until a load re-arms the counter, because
    // the only thing that raises it is the tick branch and that needs
    // r_counting. (cfg_control_wr is excluded because it legitimately drives
    // OUT low, which is not stability.)
    a_out_needs_an_armed_count: assert property (
        @(posedge clk) disable iff (`RST_ASSERTED(rst_n))
        (!r_counting && !count_reg_wr && !cfg_control_wr) |=> $stable(r_out)
    ) else $error("pit_counter: OUT moved with no count armed and no load");

    // Reprogramming releases the latch - both halves of "reprogram".
    a_ctrl_word_clears_latch: assert property (
        @(posedge clk) disable iff (`RST_ASSERTED(rst_n))
        cfg_control_wr |=> !r_count_latched
    ) else $error("pit_counter: a stale latch survived a control word");

    a_load_clears_latch: assert property (
        @(posedge clk) disable iff (`RST_ASSERTED(rst_n))
        count_reg_wr |=> !r_count_latched
    ) else $error("pit_counter: a stale latch survived a counter load");
`endif
`endif

endmodule
