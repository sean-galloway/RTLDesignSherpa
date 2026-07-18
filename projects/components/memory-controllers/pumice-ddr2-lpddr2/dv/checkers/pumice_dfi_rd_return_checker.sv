// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: 2024-2026 sean galloway
//
// pumice_dfi_rd_return_checker — param-gated DFI read-return scoreboard.
//
// The DATA-PATH counterpart to pumice_cmd_history_checker (which audits command
// SEQUENCING). It reconciles reads ISSUED by the scheduler against read DATA
// RETURNED on the DFI read path, and correlates anomalies with refresh — the
// class of bug where a read in flight around a refresh loses its data (returns
// late / never / as zero) even though the command sequencing is legal.
//
// Two control levels (the "turn on/off" the design asks for):
//   * COMPILE-TIME: DEBUG_EN=0 => the whole thing is `generate`d away (zero area/
//     timing in production). DEBUG_EN=1 => full instrument.
//   * RUNTIME: the dbg_* counter/flag outputs are meant to feed a CSR (cleared by
//     a dbg_clear pulse at the wrapper), so the SAME instrument works in sim
//     (assertions) AND on silicon (read the counters over UART — no ILA rebuild).
//
// What it catches:
//   * DROP  — a read issued but not returned within TIMEOUT cycles (watchdog).
//   * ZERO  — a read whose returned data is all-zero while a refresh is recent
//             (the refresh-drain data-drop fingerprint).
//   * REF-IN-FLIGHT — count of refreshes issued while any read was outstanding
//             (the correlation signal that localizes the interaction).

`timescale 1ns / 1ps

module pumice_dfi_rd_return_checker
    import pumice_pkg::*;
#(
    parameter int DEBUG_EN   = 1,     // 0 => synthesized away
    parameter int DW         = 128,   // DFI/return data width
    parameter int TIMEOUT    = 512,   // cycles before an outstanding read == DROP
    parameter int REF_WINDOW = 64     // cycles a refresh counts as "recent"
) (
    input  logic          clk,
    input  logic          rst_n,
    input  logic          dbg_clear_i,     // runtime: pulse to zero the counters
    // scheduler-issued command stream
    input  logic          cmd_valid_i,
    input  dram_op_e      cmd_op_i,
    // read data returning on the DFI read path (one pulse+last per completed read)
    input  logic          ret_valid_i,
    input  logic          ret_last_i,
    input  logic [DW-1:0] ret_data_i,
    // debug/status outputs (wire to a CSR for on-silicon readback)
    output logic [15:0]   dbg_reads_issued_o,
    output logic [15:0]   dbg_reads_returned_o,
    output logic [15:0]   dbg_drops_o,
    output logic [15:0]   dbg_zero_returns_o,
    output logic [15:0]   dbg_ref_inflight_o,
    output logic          dbg_error_o          // sticky: any DROP or ZERO-in-refresh
);

    generate
    if (DEBUG_EN != 0) begin : g_dbg
        localparam int WDW = (TIMEOUT    < 2) ? 1 : $clog2(TIMEOUT + 1);
        localparam int RWW = (REF_WINDOW < 2) ? 1 : $clog2(REF_WINDOW + 1);

        logic [15:0]     r_issued, r_returned, r_drops, r_zero, r_ref_inflight;
        logic [15:0]     r_outstanding;
        logic [WDW-1:0]  r_watchdog;
        logic [RWW-1:0]  r_ref_win;      // >0 => a refresh was recent
        logic            r_err;

        wire w_issue = cmd_valid_i && is_read_op(cmd_op_i);
        wire w_ret   = ret_valid_i && ret_last_i;               // a read completed
        wire w_ref   = cmd_valid_i && (cmd_op_i == OP_REF);
        wire w_drop  = (r_outstanding != 0) && !w_ret
                        && (r_watchdog == WDW'(TIMEOUT));
        wire w_zerof = w_ret && (ret_data_i == '0) && (r_ref_win != 0);

        always_ff @(posedge clk or negedge rst_n) begin
            if (!rst_n) begin
                r_issued <= '0; r_returned <= '0; r_drops <= '0; r_zero <= '0;
                r_ref_inflight <= '0; r_outstanding <= '0; r_watchdog <= '0;
                r_ref_win <= '0; r_err <= 1'b0;
            end else if (dbg_clear_i) begin
                r_issued <= '0; r_returned <= '0; r_drops <= '0; r_zero <= '0;
                r_ref_inflight <= '0; r_err <= 1'b0;    // counters clear; state stays
            end else begin
                if (w_issue) r_issued   <= r_issued   + 16'd1;
                if (w_ret)   r_returned <= r_returned + 16'd1;

                // outstanding reads
                unique case ({w_issue, w_ret})
                    2'b10:   r_outstanding <= r_outstanding + 16'd1;
                    2'b01:   r_outstanding <= (r_outstanding != 0) ? r_outstanding - 16'd1
                                                                   : 16'd0;
                    default: r_outstanding <= r_outstanding;
                endcase

                // refresh-recent window + in-flight correlation
                if (w_ref) begin
                    r_ref_win <= RWW'(REF_WINDOW);
                    if (r_outstanding != 0) r_ref_inflight <= r_ref_inflight + 16'd1;
                end else if (r_ref_win != 0) begin
                    r_ref_win <= r_ref_win - 1'b1;
                end

                // watchdog on the oldest outstanding read
                if (r_outstanding != 0) begin
                    if (w_ret)                        r_watchdog <= '0;
                    else if (r_watchdog == WDW'(TIMEOUT)) r_watchdog <= '0;
                    else                              r_watchdog <= r_watchdog + 1'b1;
                end else begin
                    r_watchdog <= '0;
                end

                if (w_drop)  r_drops <= r_drops + 16'd1;
                if (w_zerof) r_zero  <= r_zero  + 16'd1;
                if (w_drop || w_zerof) r_err <= 1'b1;
            end
        end

        assign dbg_reads_issued_o   = r_issued;
        assign dbg_reads_returned_o = r_returned;
        assign dbg_drops_o          = r_drops;
        assign dbg_zero_returns_o   = r_zero;
        assign dbg_ref_inflight_o   = r_ref_inflight;
        assign dbg_error_o          = r_err;

`ifndef SYNTHESIS
        always_ff @(posedge clk) begin
            if (rst_n && !dbg_clear_i) begin
                assert (!w_drop)
                  else $error("DFI_RD_RETURN @%0t: read DROP -- %0d read(s) outstanding for %0d cyc with no return (ref_inflight=%0d) -- refresh-drain read loss",
                              $time, r_outstanding, TIMEOUT, r_ref_inflight);
                assert (!w_zerof)
                  else $error("DFI_RD_RETURN @%0t: read returned ALL-ZERO data within %0d cyc of a refresh (zero#%0d, ref_inflight=%0d) -- refresh-drain data drop",
                              $time, REF_WINDOW, r_zero + 16'd1, r_ref_inflight);
            end
        end
`endif
    end else begin : g_nodbg
        assign dbg_reads_issued_o   = '0;
        assign dbg_reads_returned_o = '0;
        assign dbg_drops_o          = '0;
        assign dbg_zero_returns_o   = '0;
        assign dbg_ref_inflight_o   = '0;
        assign dbg_error_o          = 1'b0;
    end
    endgenerate

endmodule : pumice_dfi_rd_return_checker
