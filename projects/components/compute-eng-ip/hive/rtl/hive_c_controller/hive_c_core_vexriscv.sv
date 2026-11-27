// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: 2026 sean galloway
//
// RTL Design Sherpa - Industry-Standard RTL Design and Verification
// https://github.com/sean-galloway/RTLDesignSherpa
//
// Module: hive_c_core_vexriscv
// Purpose: hive_c_loader's CORE_FLAVOR = "vexriscv" glue: the vendored,
//          generated VexRiscv HIVE-C core (vendor/vexriscv) with its native
//          iBus/dBus simple buses mapped onto the loader's flavor-neutral
//          core ports (one fetch port, one data port).
//
// Documentation: projects/components/compute-eng-ip/hive/docs/hive_mas/ch02_blocks/02_hive_c_controller.md
// Subsystem: hive
//
// Author: sean galloway
// Created: 2026-11-27
//
// Notes:
//   - The core ports' contract (hive_c_loader): a request is accepted in the
//     cycle it is presented (always ready); a read's word arrives exactly one
//     cycle later with its rvalid pulse.  That is the VexRiscv simple-bus
//     contract at latency 1 with cmd.ready tied high: iBus_rsp_valid and
//     dBus_rsp_ready are the loader's rvalids directly, and the cores'
//     pending-fetch / pending-load bookkeeping does the rest.  Writes have
//     no response on either side.
//   - dBus_cmd_payload_mask is already the byte-lane mask of the access
//     (DBusSimplePlugin replicates byte and half data across the word), so
//     it is the data port's byte write enable as-is.  A load returns the
//     whole word; the core extracts the addressed lanes.
//   - Bus errors are tied off: HiveCGen builds the core with
//     catchAccessFault = false, so rsp error inputs are ignored by the core.
//   - Run: VexRiscv's reset (active high, asynchronous) is !run.  run is
//     hive_c_loader's CTRL flop, so the release is synchronous to clk, and
//     the core can touch memory exactly while run is high: core_active = run.
//     rst_n is unused here (run is already 0 under rst_n); peregrine's glue
//     needs it for its clean-before-reset sequencing.
//   - The obs_* outputs are the accepted fetch and data requests, as the
//     core issued them (fetch order, wrong-path fetches included).  They
//     exist for the TB (hive_c_loader core_ibus_* / core_dbus_* nets).

`timescale 1ns / 1ps

module hive_c_core_vexriscv (
    input  logic        clk,
    /* verilator lint_off UNUSEDSIGNAL */
    input  logic        rst_n,
    /* verilator lint_on UNUSEDSIGNAL */
    input  logic        run,
    output logic        core_active,

    input  logic        irq_external,
    input  logic        irq_timer,
    input  logic        irq_software,

    // Fetch port
    output logic        f_req,
    output logic [31:0] f_addr,
    input  logic        f_rvalid,
    input  logic [31:0] f_rdata,

    // Data port
    output logic        d_req,
    output logic        d_wr,
    output logic [3:0]  d_mask,
    output logic [31:0] d_addr,
    output logic [31:0] d_wdata,
    input  logic        d_rvalid,
    input  logic [31:0] d_rdata,

    // Observation (TB)
    output logic        obs_fetch_valid,
    output logic [31:0] obs_fetch_pc,
    output logic        obs_data_valid,
    output logic        obs_data_wr,
    output logic [31:0] obs_data_addr,
    output logic [31:0] obs_data_wdata,
    output logic [3:0]  obs_data_mask
);

    localparam logic CMD_ALWAYS_READY = 1'b1;
    localparam logic BUS_ERROR_NONE   = 1'b0;

    /* verilator lint_off UNUSEDSIGNAL */
    logic [1:0] w_dbus_size;   // the mask already encodes size and lane
    /* verilator lint_on UNUSEDSIGNAL */

    VexRiscv u_vexriscv (
        .iBus_cmd_valid           (f_req),
        .iBus_cmd_ready           (CMD_ALWAYS_READY),
        .iBus_cmd_payload_pc      (f_addr),
        .iBus_rsp_valid           (f_rvalid),
        .iBus_rsp_payload_error   (BUS_ERROR_NONE),
        .iBus_rsp_payload_inst    (f_rdata),
        .timerInterrupt           (irq_timer),
        .externalInterrupt        (irq_external),
        .softwareInterrupt        (irq_software),
        .dBus_cmd_valid           (d_req),
        .dBus_cmd_ready           (CMD_ALWAYS_READY),
        .dBus_cmd_payload_wr      (d_wr),
        .dBus_cmd_payload_mask    (d_mask),
        .dBus_cmd_payload_address (d_addr),
        .dBus_cmd_payload_data    (d_wdata),
        .dBus_cmd_payload_size    (w_dbus_size),
        .dBus_rsp_ready           (d_rvalid),
        .dBus_rsp_error           (BUS_ERROR_NONE),
        .dBus_rsp_data            (d_rdata),
        .clk                      (clk),
        .reset                    (!run)
    );

    assign core_active = run;

    // cmd.ready is tied high, so a valid request is an accepted one
    assign obs_fetch_valid = f_req;
    assign obs_fetch_pc    = f_addr;
    assign obs_data_valid  = d_req;
    assign obs_data_wr     = d_wr;
    assign obs_data_addr   = d_addr;
    assign obs_data_wdata  = d_wdata;
    assign obs_data_mask   = d_mask;

endmodule : hive_c_core_vexriscv
