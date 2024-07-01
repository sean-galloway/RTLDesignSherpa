
`timescale 1ns / 1ps

module apb_xbar_wrap_m1_s1_feedthru #(
    parameter int M = 1,
    parameter int S = 1,
    parameter int ADDR_WIDTH = 32,
    parameter int DATA_WIDTH = 32,
    parameter int STRB_WIDTH = 32/8
) (
    input  logic                 aclk,
    input  logic                 aresetn,

    input  logic                 m0_apb_psel,
    input  logic                 m0_apb_penable,
    input  logic                 m0_apb_pwrite,
    input  logic [2:0]           m0_apb_pprot,
    input  logic [AW-1:0]        m0_apb_paddr,
    input  logic [DW-1:0]        m0_apb_pwdata,
    input  logic [SW-1:0]        m0_apb_pstrb,
    output logic                 m0_apb_pready,
    output logic [DW-1:0]        m0_apb_prdata,
    output logic                 m0_apb_pslverr,

    output logic                 s0_apb_psel,
    output logic                 s0_apb_penable,
    output logic                 s0_apb_pwrite,
    output logic [2:0]           s0_apb_pprot,
    output logic [AW-1:0]        s0_apb_paddr,
    output logic [DW-1:0]        s0_apb_pwdata,
    output logic [SW-1:0]        s0_apb_pstrb,
    input  logic                 s0_apb_pready,
    input  logic [DW-1:0]        s0_apb_prdata,
    input  logic                 s0_apb_pslverr
);


    localparam int DW  = DATA_WIDTH;
    localparam int AW  = ADDR_WIDTH;
    localparam int SW  = STRB_WIDTH;


    assign s0_apb_psel    = m0_apb_psel;
    assign s0_apb_penable = m0_apb_penable;
    assign s0_apb_pwrite  = m0_apb_pwrite;
    assign s0_apb_pprot   = m0_apb_pprot;
    assign s0_apb_paddr   = m0_apb_paddr;
    assign s0_apb_pwdata  = m0_apb_pwdata;
    assign s0_apb_pstrb   = m0_apb_pstrb;

    assign m0_apb_pready  = s0_apb_pready;
    assign m0_apb_prdata  = s0_apb_prdata;
    assign m0_apb_pslverr = s0_apb_pslverr;

endmodule : apb_xbar_wrap_m1_s1_feedthru
