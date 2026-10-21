// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: 2026 sean galloway
//
// RTL Design Sherpa - Industry-Standard RTL Design and Verification
// https://github.com/sean-galloway/RTLDesignSherpa
//
// Module: kestrel_alu_dsp
// Purpose: Seven of kestrel_alu's ten rows -- ADD, SUB, AND, OR, XOR, SLT,
//          SLTU -- in one 7-series DSP48E1 (kestrel_alu USE_DSP = 1)
//
// Documentation: projects/components/riscv-ip/kestrel-rv32i/docs/kestrel_mas
// Subsystem: riscv-ip/kestrel-rv32i
//
// Author: sean galloway
// Created: 2026-10-20
//
// Notes:
//   - Operands: C = a, A:B = b, each extended from 32 to 48 bits with its
//     sign bit for SLT and a zero otherwise.  The DSP's post-adder / logic
//     unit is steered per op by OPMODE and ALUMODE (the 7-series DSP48E1
//     encodings, checked against Vivado's DSP48E1 simulation model):
//
//       op            OPMODE {Z,Y,X}    ALUMODE   P
//       ADD           011 00 11         0000      C + A:B
//       SUB/SLT/SLTU  011 00 11         0011      C - A:B
//       XOR           011 00 11         0100      A:B ^ C
//       AND           011 00 11         1100      A:B & C
//       OR            011 10 11         1100      A:B | C   (Y = all ones)
//
//     y = P[31:0]; lt = P[47], the sign of the 48-bit a - b, which is
//     a < b signed (SLT) or unsigned (SLTU) given the extension above.
//   - Vivado does not infer the DSP logic unit (measured on xc7a100t: a
//     case mixing add/sub with bitwise ops, or even a lone XOR under
//     use_dsp = "logic", maps to no DSP), so the slice is instantiated.
//     The approach -- one DSP for the add/sub/logic rows -- is the BRISKI
//     barrel core's; the SLT/SLTU fold-in uses the subtract's sign as in
//     the DSP48E user guide's compare application (UG193 p. 96).
//   - Fully combinational (every DSP register off): kestrel is single
//     cycle.  USE_MULT "NONE" (the logic unit excludes the multiplier, and
//     it saves power).
//   - FPGA_FAMILY selects the primitive; both current boards are 7-series
//     (DSP48E1), and the build derives the family from the part.
//   - Simulation and formal (no SYNTHESIS define) use a behavioral model of
//     the slice's adder/logic unit computed from the same OPMODE/ALUMODE,
//     so DV checks the op -> control decode too.  Vivado synthesis defines
//     SYNTHESIS and gets the primitive.

`timescale 1ns / 1ps

module kestrel_alu_dsp #(
    // DSP primitive family, set per board by the build from the part
    // (create_project.tcl: get_property ARCHITECTURE).  "7SERIES" (Artix-7
    // Nexys A7, Kintex-7 Genesys 2): DSP48E1.  Other families (DSP48E2,
    // DSP58) are not mapped yet and stop elaboration.
    parameter string FPGA_FAMILY = "7SERIES"
) (
    input  kestrel_pkg::alu_op_e op,
    input  logic [31:0]          a,
    input  logic [31:0]          b,
    output logic [31:0]          y,     // ADD/SUB/AND/OR/XOR result
    output logic                 lt     // SLT/SLTU result
);

    import kestrel_pkg::*;

    localparam logic [6:0] OPMODE_C_AB      = 7'b011_00_11;   // Z = C, Y = 0,    X = A:B
    localparam logic [6:0] OPMODE_C_ONES_AB = 7'b011_10_11;   // Z = C, Y = ones, X = A:B
    localparam logic [3:0] ALU_ADD          = 4'b0000;        // Z + X + Y
    localparam logic [3:0] ALU_SUB          = 4'b0011;        // Z - (X + Y)
    localparam logic [3:0] ALU_XOR          = 4'b0100;        // X ^ Z      (Y = 0)
    localparam logic [3:0] ALU_AND_OR       = 4'b1100;        // X & Z (Y = 0), X | Z (Y = ones)

    logic [6:0]  opmode;
    logic [3:0]  alumode;
    logic        ext_a, ext_b;
    logic [47:0] c_in, ab_in, p;

    always_comb begin
        opmode  = OPMODE_C_AB;
        alumode = ALU_ADD;
        unique case (op)
            SUB, SLT, SLTU: alumode = ALU_SUB;
            XOR:            alumode = ALU_XOR;
            AND:            alumode = ALU_AND_OR;
            OR:             begin alumode = ALU_AND_OR; opmode = OPMODE_C_ONES_AB; end
            default:        ;                                 // ADD (and rows the DSP does not serve)
        endcase
    end

    assign ext_a = (op == SLT) & a[31];
    assign ext_b = (op == SLT) & b[31];
    assign c_in  = {{16{ext_a}}, a};
    assign ab_in = {{16{ext_b}}, b};

    if (FPGA_FAMILY != "7SERIES") begin : g_family_check
        $error("kestrel_alu_dsp: FPGA_FAMILY \"%s\" has no DSP mapping (supported: 7SERIES)",
               FPGA_FAMILY);
    end

`ifdef SYNTHESIS
    DSP48E1 #(
        .A_INPUT            ("DIRECT"),
        .B_INPUT            ("DIRECT"),
        .USE_DPORT          ("FALSE"),
        .USE_MULT           ("NONE"),
        .USE_SIMD           ("ONE48"),
        .USE_PATTERN_DETECT ("NO_PATDET"),
        .AREG (0), .BREG (0), .CREG (0), .DREG (0), .ADREG (0), .MREG (0), .PREG (0),
        .ACASCREG (0), .BCASCREG (0), .ALUMODEREG (0), .OPMODEREG (0),
        .CARRYINREG (0), .CARRYINSELREG (0), .INMODEREG (0)
    ) u_dsp48 (
        .A            (ab_in[47:18]),
        .B            (ab_in[17:0]),
        .C            (c_in),
        .D            (25'd0),
        .OPMODE       (opmode),
        .ALUMODE      (alumode),
        .INMODE       (5'd0),
        .CARRYIN      (1'b0),
        .CARRYINSEL   (3'b000),
        .ACIN         (30'd0),
        .BCIN         (18'd0),
        .PCIN         (48'd0),
        .CARRYCASCIN  (1'b0),
        .MULTSIGNIN   (1'b0),
        .CLK          (1'b0),
        .CEA1 (1'b0), .CEA2 (1'b0), .CEAD (1'b0), .CEALUMODE (1'b0), .CEB1 (1'b0),
        .CEB2 (1'b0), .CEC (1'b0), .CECARRYIN (1'b0), .CECTRL (1'b0), .CED (1'b0),
        .CEINMODE (1'b0), .CEM (1'b0), .CEP (1'b0),
        .RSTA (1'b0), .RSTALLCARRYIN (1'b0), .RSTALUMODE (1'b0), .RSTB (1'b0),
        .RSTC (1'b0), .RSTCTRL (1'b0), .RSTD (1'b0), .RSTINMODE (1'b0), .RSTM (1'b0),
        .RSTP (1'b0),
        .P            (p),
        .ACOUT (), .BCOUT (), .PCOUT (), .CARRYCASCOUT (), .MULTSIGNOUT (),
        .CARRYOUT (), .OVERFLOW (), .UNDERFLOW (), .PATTERNDETECT (),
        .PATTERNBDETECT ()
    );
`else
    // Behavioral model of the DSP48E1 post-adder / logic unit for the codes
    // above: X = A:B, Y = 0 or all ones (OPMODE[3:2] = 10), Z = C; a sum
    // and carry pair from the three inputs (Z inverted when ALUMODE[0]),
    // ALUMODE[2] drops the carries, ALUMODE[3] takes the carry term as the
    // result, ALUMODE[1] inverts the output.
    logic [47:0] x_mux, y_mux, z_mux, s_term, c_term, c_used, s_used;

    assign x_mux  = ab_in;
    assign y_mux  = (opmode[3:2] == 2'b10) ? '1 : '0;
    assign z_mux  = c_in;
    assign s_term = (alumode[0] ? ~z_mux : z_mux) ^ x_mux ^ y_mux;
    assign c_term = (x_mux & y_mux) | ((alumode[0] ? ~z_mux : z_mux) & y_mux)
                  | (x_mux & (alumode[0] ? ~z_mux : z_mux));
    assign c_used = alumode[2] ? '0 : c_term;
    assign s_used = alumode[3] ? c_term : s_term;
    assign p      = alumode[1] ? ~({c_used[46:0], 1'b0} + s_used)
                               :  ({c_used[46:0], 1'b0} + s_used);
`endif

    assign y  = p[31:0];
    assign lt = p[47];

endmodule : kestrel_alu_dsp
