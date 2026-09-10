// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: 2024-2025 sean galloway
//
// RTL Design Sherpa - Industry-Standard RTL Design and Verification
// https://github.com/sean-galloway/RTLDesignSherpa
//
// Module: smbus_abort_track
// Purpose: Tell the sequencer when the ABORT'S OWN STOP has finished - and
//          not when anything else has.
//
// An abort restarts the bit PHY as a STOP while some other primitive is still
// running. Three different events look like "the abort finished" and two of
// them are lies:
//
//   - the op_done of the primitive being ABORTED, which can retire in the
//     same cycle the abort is requested;
//   - the PHY's timeout LEVEL, which it only clears the cycle after it
//     accepts the abort;
//   - the op_done of the abort's own STOP, which is the only true one.
//
// Acting on either of the first two dropped busy while the STOP was still
// driving SCL low, and a start written into that window was swallowed,
// because the PHY only samples op_req while it is idle. The address byte then
// went out with no START in front of it, and the STOP's own op_done was
// consumed by the START state as "START complete".
//
// So: PEND from the request until the PHY visibly picks it up, RUN until that
// primitive's op_done. busy=0 is allowed only on abort_done, and by then the
// PHY has released both lines - including on the path where the STOP could
// not complete either and the PHY abandoned it.

`timescale 1ns / 1ps

`include "reset_defs.svh"

module smbus_abort_track (
    input  wire clk,
    input  wire rst_n,
    input  wire soft_reset,

    input  wire abort_req,     // the cycle the sequencer asks for an abort
    input  wire phy_busy,
    input  wire phy_done,
    input  wire phy_req,       // an ordinary primitive request is outstanding

    output wire abort_active,  // an abort is requested or running
    output wire abort_done,    // the abort's OWN stop just finished
    output wire quiescent      // nothing in flight at all
);

    logic r_pend;
    logic r_run;

    assign abort_active = r_pend || r_run;
    assign abort_done   = r_run && phy_done;
    assign quiescent    = !r_pend && !r_run && !abort_req && !phy_busy && !phy_req;

    `ALWAYS_FF_RST(clk, rst_n,
        if (`RST_ASSERTED(rst_n) || soft_reset) begin
            r_pend <= 1'b0;
            r_run  <= 1'b0;
        end else if (abort_req) begin
            r_pend <= 1'b1;
            r_run  <= 1'b0;
        end else if (r_pend && phy_busy) begin
            r_pend <= 1'b0;
            r_run  <= 1'b1;
        end else if (abort_done) begin
            r_run  <= 1'b0;
        end
    )

endmodule
