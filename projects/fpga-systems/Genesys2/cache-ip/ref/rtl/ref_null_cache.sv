// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: 2026 sean galloway
//
// Module: ref_null_cache
// Purpose:
//   A one-deep GAXI responder standing in for the second cache of the
//   reference rig (cache-ip common-ip TASK-003). The reference L1s are not
//   coherent, so the rig holds ONE cache; the second injector keeps its CSR
//   slot so the jet host stack runs unchanged, and this block answers its
//   requests with zero data one cycle later. The comparison uses ci0; the
//   host sweeps run the second injector with count 0 (--ci1-idle) or ignore
//   its columns.
//
// Author: sean galloway
// Created: 2026-11-11
`timescale 1ns / 1ps

module ref_null_cache #(
    parameter int REQ_W = 32 + 1 + 8 + 64,
    parameter int RSP_W = 64
) (
    input  logic             aclk,
    input  logic             aresetn,
    input  logic             cpu_req_wr_valid,
    output logic             cpu_req_wr_ready,
    input  logic [REQ_W-1:0] cpu_req_wr_data,
    output logic             cpu_rsp_rd_valid,
    input  logic             cpu_rsp_rd_ready,
    output logic [RSP_W-1:0] cpu_rsp_rd_data
);
    /* verilator lint_off UNUSEDSIGNAL */
    logic [REQ_W-1:0] w_unused_req;
    assign w_unused_req = cpu_req_wr_data;
    /* verilator lint_on UNUSEDSIGNAL */

    logic r_pending;
    assign cpu_req_wr_ready = ~r_pending | cpu_rsp_rd_ready;
    assign cpu_rsp_rd_valid = r_pending;
    assign cpu_rsp_rd_data  = '0;

    always_ff @(posedge aclk or negedge aresetn) begin
        if (!aresetn) r_pending <= 1'b0;
        else if (cpu_req_wr_valid & cpu_req_wr_ready) r_pending <= 1'b1;
        else if (cpu_rsp_rd_valid & cpu_rsp_rd_ready) r_pending <= 1'b0;
    end
endmodule : ref_null_cache
