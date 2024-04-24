`timescale 1ns / 1ps
`include "axi_params.svh"

// Generic Slave module to prove out maximal performance
module axi_slave
// #(
//     parameter int AXI_ID_WIDTH      = 4,
//     parameter int AXI_ADDR_WIDTH    = 32,
//     parameter int AXI_DATA_WIDTH    = 32,
//     parameter int AXI_USER_WIDTH    = 1,
//     parameter int AXI_WSTRB_WIDTH   = AXI_DATA_WIDTH / 8
// )
(
    // Global Clock and Reset
    input  logic s_axi_aclk,
    input  logic s_axi_aresetn,

    // Write address channel (AW)
    input  logic [AXI_ID_WIDTH-1:0]    s_axi_awid,
    input  logic [AXI_ADDR_WIDTH-1:0]  s_axi_awaddr,
    input  logic [7:0]                 s_axi_awlen,
    input  logic [2:0]                 s_axi_awsize,
    input  logic [1:0]                 s_axi_awburst,
    input  logic                       s_axi_awlock,
    input  logic [3:0]                 s_axi_awcache,
    input  logic [2:0]                 s_axi_awprot,
    input  logic [3:0]                 s_axi_awqos,
    input  logic [3:0]                 s_axi_awregion,
    input  logic [AXI_USER_WIDTH-1:0]  s_axi_awuser,
    input  logic                       s_axi_awvalid,
    output logic                       s_axi_awready,

    // Write data channel (W)
    input  logic [AXI_ID_WIDTH-1:0]    s_axi_wid,
    input  logic [AXI_DATA_WIDTH-1:0]  s_axi_wdata,
    input  logic [AXI_WSTRB_WIDTH-1:0] s_axi_wstrb,
    input  logic                       s_axi_wlast,
    input  logic [AXI_USER_WIDTH-1:0]  s_axi_wuser,
    input  logic                       s_axi_wvalid,
    output logic                       s_axi_wready,

    // Write response channel (B)
    output logic [AXI_ID_WIDTH-1:0]    s_axi_bid,
    output logic [1:0]                 s_axi_bresp,
    output logic [AXI_USER_WIDTH-1:0]  s_axi_buser,
    output logic                       s_axi_bvalid,
    input  logic                       s_axi_bready,

    // Read address channel (AR)
    input  logic [AXI_ID_WIDTH-1:0]    s_axi_arid,
    input  logic [AXI_ADDR_WIDTH-1:0]  s_axi_araddr,
    input  logic [7:0]                 s_axi_arlen,
    input  logic [2:0]                 s_axi_arsize,
    input  logic [1:0]                 s_axi_arburst,
    input  logic                       s_axi_arlock,
    input  logic [3:0]                 s_axi_arcache,
    input  logic [2:0]                 s_axi_arprot,
    input  logic [3:0]                 s_axi_arqos,
    input  logic [3:0]                 s_axi_arregion,
    input  logic [AXI_USER_WIDTH-1:0]  s_axi_aruser,
    input  logic                       s_axi_arvalid,
    output logic                       s_axi_arready,

    // Read data channel (R)
    output logic [AXI_ID_WIDTH-1:0]    s_axi_rid,
    output logic [AXI_DATA_WIDTH-1:0]  s_axi_rdata,
    output logic [1:0]                 s_axi_rresp,
    output logic                       s_axi_rlast,
    output logic [AXI_USER_WIDTH-1:0]  s_axi_ruser,
    output logic                       s_axi_rvalid,
    input  logic                       s_axi_rready,

    // Write Fifo Channel, out
    output  logic                       o_wr_pkt_valid,
    input   logic                       i_wr_pkt_ready,
    output  logic [AXI_ADDR_WIDTH-1:0]  o_wr_pkt_addr,
    output  logic [AXI_DATA_WIDTH-1:0]  o_wr_pkt_data,
    output  logic [AXI_WSTRB_WIDTH-1:0] o_wr_pkt_strb,

    // Read Fifo Channel, out
    output  logic                       o_rd_pkt_valid,
    input   logic                       i_rd_pkt_ready,
    output  logic [AXI_ADDR_WIDTH-1:0]  o_rd_pkt_addr,

    // Read Fifo Channel, ret
    input   logic                       i_rdret_pkt_valid,
    output  logic                       o_rdret_pkt_ready,
    input   logic [AXI_DATA_WIDTH-1:0]  i_rdret_pkt_data
);

    localparam int AW       = AXI_ADDR_WIDTH;
    localparam int DW       = AXI_DATA_WIDTH;
    localparam int IW       = AXI_USER_WIDTH;
    localparam int SW       = AXI_WSTRB_WIDTH;
    localparam int UW       = AXI_USER_WIDTH;
    localparam int AWSize   = IW+AW+8+3+2+1+4+3+4+4+UW;
    localparam int WSize    = IW+DW+SW+1+UW;
    localparam int BSize    = IW+2+UW;
    localparam int ARSize   = IW+AW+8+3+2+1+4+3+4+4+UW;
    localparam int RSize    = IW+DW+2+1+UW;

    ///////////////////////////////////////////////////////////////////////////////////////////
    // Write address channel (AW)
    logic [AXI_ID_WIDTH-1:0]    r_axi_awid;
    logic [AXI_ADDR_WIDTH-1:0]  r_axi_awaddr;
    logic [7:0]                 r_axi_awlen;
    logic [2:0]                 r_axi_awsize;
    logic [1:0]                 r_axi_awburst;
    logic                       r_axi_awlock;
    logic [3:0]                 r_axi_awcache;
    logic [2:0]                 r_axi_awprot;
    logic [3:0]                 r_axi_awqos;
    logic [3:0]                 r_axi_awregion;
    logic [AXI_USER_WIDTH-1:0]  r_axi_awuser;
    logic                       r_axi_awvalid;
    logic                       r_axi_awready;
    axi_skid_buffer #(.DATA_WIDTH(AWSize)) inst_aw_phase (
        .i_axi_aclk               (s_axi_aclk),
        .i_axi_aresetn            (s_axi_aresetn),
        .i_wr_valid               (s_axi_awvalid),
        .o_wr_ready               (s_axi_awready),
        .i_wr_data                ({s_axi_awid,s_axi_awaddr,s_axi_awlen,s_axi_awsize,s_axi_awburst,
                                    s_axi_awlock,s_axi_awcache,s_axi_awprot,s_axi_awqos,
                                    s_axi_awregion,s_axi_awuser}),
        .o_rd_valid               (r_axi_awvalid),
        .i_rd_ready               (r_axi_awready),
        .o_rd_data                ({r_axi_awid,r_axi_awaddr,r_axi_awlen,r_axi_awsize,r_axi_awburst,
                                    r_axi_awlock,r_axi_awcache,r_axi_awprot,r_axi_awqos,
                                    r_axi_awregion,r_axi_awuser})
    );

    logic           r_write_ip, w_write_xfer;
    logic [AW-1:0]  w_curr_addr, w_next_addr, r_addr;

    // assign interface sigs to the write port
    assign o_wr_pkt_valid = r_axi_awvalid && r_axi_wvalid && r_axi_bready;
    assign o_wr_pkt_addr  = w_curr_addr;
    assign o_wr_pkt_data  = r_axi_wdata;
    assign o_wr_pkt_strb  = r_axi_wstrb;
    assign r_axi_awready  = o_wr_pkt_valid && i_wr_pkt_ready && r_axi_wlast && r_axi_bready;
    assign r_axi_wready   = o_wr_pkt_valid && i_wr_pkt_ready && r_axi_bready;
    assign r_axi_bvalid   = r_axi_awready;
    assign r_axi_bid      = r_axi_awid;
    assign r_axi_bresp    = 2'b00; // add more later if needed
    assign r_axi_buser    = r_axi_awuser;
    assign w_write_xfer = o_wr_pkt_valid && i_wr_pkt_ready;
    assign w_curr_addr = (r_write_ip) ? r_addr : r_axi_awaddr;

    always_ff @(posedge s_axi_aclk or negedge s_axi_aresetn) begin
        if (~s_axi_aresetn) begin
            r_write_ip <= 'b0;
            r_addr <= 'b0;
        end else begin
            if (r_write_ip) // clear when getting the command packet
                if (r_axi_awvalid && r_axi_awready) r_write_ip <= 'b0;
            else if (w_write_xfer)  r_write_ip <= 'b1;
            if (w_write_xfer) r_addr <= w_next_addr;
        end
    end

    // Address Generation
    axi_gen_addr #(.AW(AW),.DW(DW),.LEN(8)) inst_wr_addr_gen (
        .i_curr_addr         (w_curr_addr),
        .i_size              (r_axi_awsize),
        .i_burst             (r_axi_awburst),
        .i_len               (r_axi_awlen),
        .ow_next_addr        (w_next_addr)
    );

    ///////////////////////////////////////////////////////////////////////////////////////////
    // Write data channel (W)
    logic [AXI_ID_WIDTH-1:0]    r_axi_wid;
    logic [AXI_DATA_WIDTH-1:0]  r_axi_wdata;
    logic [AXI_WSTRB_WIDTH-1:0] r_axi_wstrb;
    logic                       r_axi_wlast;
    logic [AXI_USER_WIDTH-1:0]  r_axi_wuser;
    logic                       r_axi_wvalid;
    logic                       r_axi_wready;
    axi_skid_buffer #(.DATA_WIDTH(WSize)) inst_w_phase (
        .i_axi_aclk               (s_axi_aclk),
        .i_axi_aresetn            (s_axi_aresetn),
        .i_wr_valid               (s_axi_wvalid),
        .o_wr_ready               (s_axi_wready),
        .i_wr_data                ({s_axi_wid,s_axi_wdata,s_axi_wstrb,s_axi_wlast,s_axi_wuser}),
        .o_rd_valid               (r_axi_wvalid),
        .i_rd_ready               (r_axi_wready),
        .o_rd_data                ({r_axi_wid,r_axi_wdata,r_axi_wstrb,r_axi_wlast,r_axi_wuser})
    );

    ///////////////////////////////////////////////////////////////////////////////////////////
    // Write response channel (B)
    logic [AXI_ID_WIDTH-1:0]    r_axi_bid;
    logic [1:0]                 r_axi_bresp;
    logic [AXI_USER_WIDTH-1:0]  r_axi_buser;
    logic                       r_axi_bvalid;
    logic                       r_axi_bready;
    axi_skid_buffer #(.DATA_WIDTH(BSize)) inst_b_phase (
        .i_axi_aclk               (s_axi_aclk),
        .i_axi_aresetn            (s_axi_aresetn),
        .i_wr_valid               (r_axi_bvalid),
        .o_wr_ready               (r_axi_bready),
        .i_wr_data                ({r_axi_bid,r_axi_bresp,r_axi_buser}),
        .o_rd_valid               (s_axi_bvalid),
        .i_rd_ready               (s_axi_bready),
        .o_rd_data                ({s_axi_bid,s_axi_bresp,s_axi_buser})
    );

    ///////////////////////////////////////////////////////////////////////////////////////////
    // Read address channel (AR)
    logic [AXI_ID_WIDTH-1:0]    r_axi_arid;
    logic [AXI_ADDR_WIDTH-1:0]  r_axi_araddr;
    logic [7:0]                 r_axi_arlen;
    logic [2:0]                 r_axi_arsize;
    logic [1:0]                 r_axi_arburst;
    logic                       r_axi_arlock;
    logic [3:0]                 r_axi_arcache;
    logic [2:0]                 r_axi_arprot;
    logic [3:0]                 r_axi_arqos;
    logic [3:0]                 r_axi_arregion;
    logic [AXI_USER_WIDTH-1:0]  r_axi_aruser;
    logic                       r_axi_arvalid;
    logic                       r_axi_arready;
    axi_skid_buffer #(.DATA_WIDTH(ARSize)) inst_ar_phase (
        .i_axi_aclk               (s_axi_aclk),
        .i_axi_aresetn            (s_axi_aresetn),
        .i_wr_valid               (s_axi_arvalid),
        .o_wr_ready               (s_axi_arready),
        .i_wr_data                ({s_axi_arid,s_axi_araddr,s_axi_arlen,s_axi_arsize,s_axi_arburst,
                                    s_axi_arlock,s_axi_arcache,s_axi_arprot,s_axi_arqos,
                                    s_axi_arregion,s_axi_aruser}),
        .o_rd_valid               (r_axi_arvalid),
        .i_rd_ready               (r_axi_arready),
        .o_rd_data                ({r_axi_arid,r_axi_araddr,r_axi_arlen,r_axi_arsize,r_axi_arburst,
                                    r_axi_arlock,r_axi_arcache,r_axi_arprot,r_axi_arqos,
                                    r_axi_arregion,r_axi_aruser})
    );

    ///////////////////////////////////////////////////////////////////////////////////////////
    // Read data channel (R)
    logic [AXI_ID_WIDTH-1:0]    r_axi_rid;
    logic [AXI_DATA_WIDTH-1:0]  r_axi_rdata;
    logic [1:0]                 r_axi_rresp;
    logic                       r_axi_rlast;
    logic [AXI_USER_WIDTH-1:0]  r_axi_ruser;
    logic                       r_axi_rvalid;
    logic                       r_axi_rready;
    axi_skid_buffer #(.DATA_WIDTH(RSize)) inst_r_phase (
        .i_axi_aclk               (s_axi_aclk),
        .i_axi_aresetn            (s_axi_aresetn),
        .i_wr_valid               (r_axi_rvalid),
        .o_wr_ready               (r_axi_rready),
        .i_wr_data                ({r_axi_rid,r_axi_rdata,r_axi_rresp,r_axi_rlast,r_axi_ruser}),
        .o_rd_valid               (s_axi_rvalid),
        .i_rd_ready               (s_axi_rready),
        .o_rd_data                ({s_axi_rid,s_axi_rdata,s_axi_rresp,s_axi_rlast,s_axi_ruser})
    );


endmodule : axi_slave
