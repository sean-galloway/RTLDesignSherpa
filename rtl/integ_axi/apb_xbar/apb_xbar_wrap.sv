
`timescale 1ns / 1ps

module apb_xbar_wrap #(
    parameter int M = 2,
    parameter int S = 4,
    parameter int ADDR_WIDTH = 32,
    parameter int DATA_WIDTH = 32,
    parameter int STRB_WIDTH = DATA_WIDTH/8
) (
    input  logic                 aclk,
    input  logic                 aresetn,

    input  logic                 m0_apb_psel,
    input  logic                 m0_apb_penable,
    input  logic                 m0_apb_pwrite,
    input  logic [AW-1:0]        m0_apb_paddr,
    input  logic [DW:0]          m0_apb_pwdata,
    input  logic [SW:0]          m0_apb_pstrb,
    output logic                 m0_apb_pready,
    output logic [DW:0]          m0_apb_prdata,
    output logic                 m0_apb_pslverr,

    input  logic                 m1_apb_psel,
    input  logic                 m1_apb_penable,
    input  logic                 m1_apb_pwrite,
    input  logic [AW-1:0]        m1_apb_paddr,
    input  logic [DW:0]          m1_apb_pwdata,
    input  logic [SW:0]          m1_apb_pstrb,
    output logic                 m1_apb_pready,
    output logic [DW:0]          m1_apb_prdata,
    output logic                 m1_apb_pslverr,

    input  logic                 m2_apb_psel,
    input  logic                 m2_apb_penable,
    input  logic                 m2_apb_pwrite,
    input  logic [AW-1:0]        m2_apb_paddr,
    input  logic [DW:0]          m2_apb_pwdata,
    input  logic [SW:0]          m2_apb_pstrb,
    output logic                 m2_apb_pready,
    output logic [DW:0]          m2_apb_prdata,
    output logic                 m2_apb_pslverr,

    output logic                 s0_apb_psel,
    output logic                 s0_apb_penable,
    output logic                 s0_apb_pwrite,
    output logic [AW-1:0]        s0_apb_paddr,
    output logic [DW-1:0]        s0_apb_pwdata,
    output logic [SW-1:0]        s0_apb_pstrb,
    input  logic                 s0_apb_pready,
    input  logic [DW-1:0]        s0_apb_prdata,
    input  logic                 s0_apb_pslverr,

    output logic                 s1_apb_psel,
    output logic                 s1_apb_penable,
    output logic                 s1_apb_pwrite,
    output logic [AW-1:0]        s1_apb_paddr,
    output logic [DW-1:0]        s1_apb_pwdata,
    output logic [SW-1:0]        s1_apb_pstrb,
    input  logic                 s1_apb_pready,
    input  logic [DW-1:0]        s1_apb_prdata,
    input  logic                 s1_apb_pslverr,

    output logic                 s2_apb_psel,
    output logic                 s2_apb_penable,
    output logic                 s2_apb_pwrite,
    output logic [AW-1:0]        s2_apb_paddr,
    output logic [DW-1:0]        s2_apb_pwdata,
    output logic [SW-1:0]        s2_apb_pstrb,
    input  logic                 s2_apb_pready,
    input  logic [DW-1:0]        s2_apb_prdata,
    input  logic                 s2_apb_pslverr,

    output logic                 s3_apb_psel,
    output logic                 s3_apb_penable,
    output logic                 s3_apb_pwrite,
    output logic [AW-1:0]        s3_apb_paddr,
    output logic [DW-1:0]        s3_apb_pwdata,
    output logic [SW-1:0]        s3_apb_pstrb,
    input  logic                 s3_apb_pready,
    input  logic [DW-1:0]        s3_apb_prdata,
    input  logic                 s3_apb_pslverr,

    output logic                 s4_apb_psel,
    output logic                 s4_apb_penable,
    output logic                 s4_apb_pwrite,
    output logic [AW-1:0]        s4_apb_paddr,
    output logic [DW-1:0]        s4_apb_pwdata,
    output logic [SW-1:0]        s4_apb_pstrb,
    input  logic                 s4_apb_pready,
    input  logic [DW-1:0]        s4_apb_prdata,
    input  logic                 s4_apb_pslverr
);


    localparam int DW  = DATA_WIDTH;
    localparam int AW  = ADDR_WIDTH;
    localparam int SW  = STRB_WIDTH;


    apb_xbar #(
        .M(3),
        .S(5),
        .ADDR_WIDTH(32),
        .DATA_WIDTH(32)
    ) apb_xbar_inst (
        .aclk                (aclk),
        .aresetn             (aresetn),
        .SLAVE_ENABLE        ({1'b1, 1'b1, 1'b1, 1'b1, 1'b1}),
        .SLAVE_ADDR_BASE     ({32'h0, 32'h1000, 32'h2000, 32'h3000, 32'h4000}),
        .SLAVE_ADDR_LIMIT    ({32'hFFF, 32'h1FFF, 32'h2FFF, 32'h3FFF, 32'h4FFF}),
        .THRESHOLDS          (12'h444),

        .m_apb_psel     ({m2_apb_psel, m1_apb_psel, m0_apb_psel}),
        .m_apb_penable  ({m2_apb_penable, m1_apb_penable, m0_apb_penable}),
        .m_apb_pwrite   ({m2_apb_pwrite, m1_apb_pwrite, m0_apb_pwrite}),
        .m_apb_paddr    ({m2_apb_paddr, m1_apb_paddr, m0_apb_paddr}),
        .m_apb_pwdata   ({m2_apb_pwdata, m1_apb_pwdata, m0_apb_pwdata}),
        .m_apb_pstrb    ({m2_apb_pstrb, m1_apb_pstrb, m0_apb_pstrb}),
        .m_apb_pready   ({m2_apb_pready, m1_apb_pready, m0_apb_pready}),
        .m_apb_prdata   ({m2_apb_prdata, m1_apb_prdata, m0_apb_prdata}),
        .m_apb_pslverr  ({m2_apb_pslverr, m1_apb_pslverr, m0_apb_pslverr}),

        .s_apb_psel    ({s4_apb_psel, s3_apb_psel, s2_apb_psel, s1_apb_psel, s0_apb_psel}),
        .s_apb_penable ({s4_apb_penable, s3_apb_penable, s2_apb_penable, s1_apb_penable, s0_apb_penable}),
        .s_apb_pwrite  ({s4_apb_pwrite, s3_apb_pwrite, s2_apb_pwrite, s1_apb_pwrite, s0_apb_pwrite}),
        .s_apb_paddr   ({s4_apb_paddr, s3_apb_paddr, s2_apb_paddr, s1_apb_paddr, s0_apb_paddr}),
        .s_apb_pwdata  ({s4_apb_pwdata, s3_apb_pwdata, s2_apb_pwdata, s1_apb_pwdata, s0_apb_pwdata}),
        .s_apb_pstrb   ({s4_apb_pstrb, s3_apb_pstrb, s2_apb_pstrb, s1_apb_pstrb, s0_apb_pstrb}),
        .s_apb_pready  ({s4_apb_pready, s3_apb_pready, s2_apb_pready, s1_apb_pready, s0_apb_pready}),
        .s_apb_prdata  ({s4_apb_prdata, s3_apb_prdata, s2_apb_prdata, s1_apb_prdata, s0_apb_prdata}),
        .s_apb_pslverr ({s4_apb_pslverr, s3_apb_pslverr, s2_apb_pslverr, s1_apb_pslverr, s0_apb_pslverr})
    );

endmodule : apb_xbar_wrap
