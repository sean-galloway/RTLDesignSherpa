//      // verilator_coverage annotation
        // SPDX-License-Identifier: MIT
        // SPDX-FileCopyrightText: 2024-2025 sean galloway
        //
        // RTL Design Sherpa - Industry-Standard RTL Design and Verification
        // https://github.com/sean-galloway/RTLDesignSherpa
        //
        // Module: dataint_checksum
        // Purpose: Dataint Checksum module
        //
        // Documentation: rtl/common/PRD.md
        // Subsystem: common
        //
        // Author: sean galloway
        // Created: 2025-10-18
        
        `timescale 1ns / 1ps
        
        // Generic Checksum Module
        
        `include "reset_defs.svh"
        module dataint_checksum #(
            parameter int WIDTH = 8
        ) (
 005350     input  logic             clk,
 000162     rst_n,
 000012     input  logic             reset,
 001076     input  logic             valid,
 000062     input  logic [WIDTH-1:0] data,
 000030     output logic [WIDTH-1:0] chksum
        );
        
 000030     logic [WIDTH-1:0] r_count;
        
            `ALWAYS_FF_RST(clk, rst_n,
                if (!rst_n) r_count <= 'b0;
                else if (reset) r_count <= 'b0;
                else if (valid) r_count <= r_count + data;
%000006     )
        
        
            assign chksum = r_count;
        
        endmodule : dataint_checksum
        
