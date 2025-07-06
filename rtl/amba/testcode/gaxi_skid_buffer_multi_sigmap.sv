// axi_skid_buffer_multi.sv: Wrapper for multi-signal skid buffer
module gaxi_skid_buffer_multi_sigmap #(
    parameter integer ADDR_WIDTH = 4,
    parameter integer CTRL_WIDTH = 4,
    parameter integer DATA_WIDTH = 8,
    parameter integer DEPTH = 2,
    parameter integer AW = ADDR_WIDTH,
    parameter integer CW = CTRL_WIDTH,
    parameter integer DW = DATA_WIDTH
)(
    input  logic                axi_aclk,
    input  logic                axi_aresetn,
    // Write channel
    input  logic                wr_valid,
    output logic                wr_ready,
    input  logic [AW-1:0]       wr_siga,    // addr
    input  logic [CW-1:0]       wr_sigb,    // ctrl
    input  logic [DW-1:0]       wr_sigc,    // data0
    input  logic [DW-1:0]       wr_sigd,    // data1
    // Read channel
    output logic                rd_valid,
    input  logic                rd_ready,
    output logic [AW-1:0]       rd_sige,    // addr
    output logic [CW-1:0]       rd_sigf,    // ctrl
    output logic [DW-1:0]       rd_sigg,    // data0
    output logic [DW-1:0]       rd_sigh     // data1  
);

    // Instantiate the original skid buffer
    gaxi_skid_buffer #(.DATA_WIDTH(AW+CW+DW+DW), .DEPTH(DEPTH)) u_gaxi_skid_buffer (
        .i_axi_aclk    (axi_aclk),
        .i_axi_aresetn (axi_aresetn),
        .i_wr_valid    (wr_valid),
        .o_wr_ready    (wr_ready),
        .i_wr_data     ({wr_siga, wr_sigb, wr_sigd, wr_sigc}),
        .o_rd_valid    (rd_valid),
        .i_rd_ready    (rd_ready),
        .o_rd_data     ({rd_sige, rd_sigf, rd_sigh, rd_sigg}),
        .ow_count      (),
        .o_rd_count    ()
    );

endmodule : gaxi_skid_buffer_multi_sigmap
