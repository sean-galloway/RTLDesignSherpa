// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: 2024-2025 sean galloway
//
// RTL Design Sherpa - Industry-Standard RTL Design and Verification
// https://github.com/sean-galloway/RTLDesignSherpa
//
// Module: simple_fifo
// Purpose: Simple FIFO wrapper for SMBus with count output
//
// Wraps the existing fifo_sync module and adds a count tracker
// for the SMBus controller. Simplified interface with count output.

`timescale 1ns / 1ps

`include "reset_defs.svh"
`include "fifo_defs.svh"

module simple_fifo #(
    parameter int DATA_WIDTH = 8,
    parameter int DEPTH = 32,
    parameter int LEVEL_WIDTH = 6
) (
    input  logic                    clk,
    input  logic                    rst_n,
    // Synchronous flush. fifo_sync has no flush input, so this has to reach
    // its reset - but REGISTERED and with the polarity the build defines,
    // never as a hand-written AND of rst_n with a decoded register bit. A
    // hand-composed `rst_n && !clear` de-asserts reset under
    // RESET_ACTIVE_HIGH, which is the opposite of what the write meant.
    input  logic                    clear,

    // Write interface
    input  logic                    wr_en,
    input  logic [DATA_WIDTH-1:0]   wr_data,

    // Read interface
    input  logic                    rd_en,
    output logic [DATA_WIDTH-1:0]   rd_data,

    // Status
    output logic                    full,
    output logic                    empty,
    // Sized by the CONSUMER, not by DEPTH: this level goes into a fixed
    // 6-bit register field, and a port whose width follows $clog2(DEPTH)
    // mismatches that field at every depth except 32.
    output logic [LEVEL_WIDTH-1:0]  count
);

    //========================================================================
    // Local Parameters
    //========================================================================
    localparam int COUNT_WIDTH = $clog2(DEPTH) + 1;

    // The level output is LEVEL_WIDTH bits and the count runs to DEPTH, so the
    // ceiling is a VALUE range, not a width comparison: COUNT_WIDTH exceeds
    // LEVEL_WIDTH from DEPTH=33 upward (clog2(33)+1 = 7) while 33..63 still
    // fit six bits perfectly well. Keying the guard on the widths would reject
    // two depths this block supports and the lint sweep covers.
    //
    // Guarding HERE and not only in apb4_smbus because smbus_byte_fifos.f is a
    // standalone sub-block filelist: a DV or formal harness can elaborate the
    // FIFO pair on its own, and at DEPTH=64 the level truncates to 0 while
    // full reads 1 - a silently empty FIFO that is also full.
    initial begin : param_check
        if (DEPTH < 2) begin
            $fatal(1, "simple_fifo: DEPTH must be >= 2, got %0d", DEPTH);
        end
        if (DEPTH > ((1 << LEVEL_WIDTH) - 1)) begin
            $fatal(1, "simple_fifo: DEPTH %0d does not fit LEVEL_WIDTH %0d (max %0d)",
                   DEPTH, LEVEL_WIDTH, (1 << LEVEL_WIDTH) - 1);
        end
    end

    //========================================================================
    // Internal Signals
    //========================================================================
    // The asserted level of a reset in THIS build. reset_defs.svh gives
    // RST_ASSERTED() for testing a reset but no constant for driving one, and
    // driving one is exactly what a composite reset has to do.
    //
    // THIS COVERS THIS WRAPPER'S OWN FLOPS ONLY. It does not make the sink
    // polarity-correct: rtl/common's fifo_control.sv and counter_bin.sv
    // hardcode active-low in their bodies, so fifo_sync itself does not
    // follow RESET_ACTIVE_HIGH (filed as COMMON-026). Driving w_rst_n at the
    // build's asserted level is right for this module and is what a fixed
    // fifo_sync will want; until COMMON-026 lands, the active-high build of
    // the FIFO is broken below this line, not at it.
`ifdef RESET_ACTIVE_HIGH
    localparam logic RST_ON = 1'b1;
`else
    localparam logic RST_ON = 1'b0;
`endif

    logic                    w_rst_n;
    logic                    r_clr_hold;
    logic                    w_in_clear;
    logic                    w_wr;
    logic                    w_rd;
    logic                    w_wr_full;
    logic                    w_rd_empty;
    // fifo_sync's almost-full/empty flags are not part of this wrapper's
    // interface - the SMBus engine works on levels, not watermarks - but the
    // pins have to go somewhere, so they are named and left unread rather
    // than tied off by name, which would hide a future rename.
    /* verilator lint_off UNUSEDSIGNAL */
    logic                    w_wr_almost_full;
    logic                    w_rd_almost_empty;
    /* verilator lint_on UNUSEDSIGNAL */

    // Count tracking
    logic [COUNT_WIDTH-1:0]  r_count;

    //========================================================================
    // Clear window
    //========================================================================
    // fifo_sync has no flush input, so a clear has to reach its reset - from a
    // FLOP, so that no decoded register bit is ever combinational on an
    // asynchronous input.
    //
    // That flop makes the two halves DIFFERENT LENGTHS, and being sloppy about
    // which is which is exactly the defect this window exists to close:
    //   - the WRITE/READ GATE and the forced outputs are w_in_clear, two
    //     cycles wide for a one-cycle clear (the request cycle, then
    //     r_clr_hold);
    //   - the STORAGE'S RESET is r_clr_hold alone, ONE cycle for a one-cycle
    //     clear, and in the first window cycle the storage is not in reset at
    //     all - a probe there still shows rd_empty=0 and the old count.
    // The gate is the longer of the two on purpose: it covers the cycle the
    // storage has not yet reacted to.
    //
    // They did not. The count cleared on `clear` while the memory was held in
    // reset one cycle later, so a push landing in the shadow was counted but
    // never stored: level read 1 with empty=1 forever, and a drain loop that
    // trusts the level span on a stale head.
    //
    // So w_in_clear is the ONE window. Nothing is written or read across it,
    // the count is held at zero through it, and the level and flags the
    // sequencer sees are forced to "empty" for its whole duration - including
    // the first cycle, before any flop has moved. A fifo_reset landing during
    // an active receive therefore discards the byte in flight along with the
    // rest, which is what software asked for; the transfer itself still
    // completes or aborts through the normal paths.
    //========================================================================
    assign w_in_clear = clear || r_clr_hold;
    assign w_wr       = wr_en && !w_in_clear;
    assign w_rd       = rd_en && !w_in_clear;
    // r_clr_hold resets to 1, so the FIFO is held for one more cycle after
    // rst_n releases. Harmless - it only guarantees the FIFO leaves reset
    // empty - and it is why the window is closed rather than open at t=0.
    `ALWAYS_FF_RST(clk, rst_n,
        if (`RST_ASSERTED(rst_n)) begin
            r_clr_hold <= 1'b1;
        end else begin
            r_clr_hold <= clear;
        end
    )

    assign w_rst_n = r_clr_hold ? RST_ON : rst_n;

    //========================================================================
    // FIFO Instance (Using Project's fifo_sync)
    //========================================================================
    fifo_sync #(
        .MEM_STYLE(FIFO_AUTO),
        .REGISTERED(0),              // Mux mode for lowest latency
        .DATA_WIDTH(DATA_WIDTH),
        .DEPTH(DEPTH),
        .ALMOST_WR_MARGIN(1),
        .ALMOST_RD_MARGIN(1)
    ) u_fifo_sync (
        .clk             (clk),
        .rst_n           (w_rst_n),
        .write           (w_wr),
        .wr_data         (wr_data),
        .wr_full         (w_wr_full),
        .wr_almost_full  (w_wr_almost_full),
        .read            (w_rd),
        .rd_data         (rd_data),
        .rd_empty        (w_rd_empty),
        .rd_almost_empty (w_rd_almost_empty)
    );

    //========================================================================
    // Count Tracker
    //========================================================================
    // Track number of entries in FIFO
    `ALWAYS_FF_RST(clk, rst_n,
        if (`RST_ASSERTED(rst_n) || w_in_clear) begin
            r_count <= '0;
        end else begin
            case ({w_wr && !w_wr_full, w_rd && !w_rd_empty})
                2'b10: r_count <= r_count + 1'b1;  // Write only
                2'b01: r_count <= r_count - 1'b1;  // Read only
                default: r_count <= r_count;        // Both or neither
            endcase
        end
    )

    //========================================================================
    // Output Assignments
    //========================================================================
    // ONE consistent source across the clear window. r_count and fifo_sync's
    // own flags both take a cycle to catch up, and they do not take the SAME
    // cycle, so through the window all three are forced to the answer the
    // window guarantees: empty, not full, nothing in it - including the first
    // cycle, before any flop has moved. Outside the window they are what they
    // always were.
    //
    // THAT CONSISTENCY IS AN ACTIVE-LOW-BUILD PROPERTY. Under
    // RESET_ACTIVE_HIGH the storage never leaves reset (COMMON-026), so the
    // count runs past the depth against a permanently empty memory and no
    // amount of care here can reconcile them.
    assign full  = w_in_clear ? 1'b0 : w_wr_full;
    assign empty = w_in_clear ? 1'b1 : w_rd_empty;
    assign count = w_in_clear ? '0   : LEVEL_WIDTH'(r_count);

endmodule
