`timescale 1ns / 1ps

module axil4_master_wr
#(
    // AXI-Lite parameters
    parameter int AXIL_ADDR_WIDTH    = 32,
    parameter int AXIL_DATA_WIDTH    = 32,

    // Skid buffer depths
    parameter int SKID_DEPTH_AW     = 2,
    parameter int SKID_DEPTH_W      = 2,
    parameter int SKID_DEPTH_B      = 2,

    // Derived parameters
    parameter int AW       = AXIL_ADDR_WIDTH,
    parameter int DW       = AXIL_DATA_WIDTH,
    parameter int AWSize   = AW+3,        // addr + prot
    parameter int WSize    = DW+(DW/8),   // data + strb
    parameter int BSize    = 2            // resp only
)
(
    // Global Clock and Reset
    input  logic                       aclk,
    input  logic                       aresetn,

    // Slave AXI-Lite Interface (Input Side)
    // Write address channel (AW)
    input  logic [AW-1:0]              fub_awaddr,
    input  logic [2:0]                 fub_awprot,
    input  logic                       fub_awvalid,
    output logic                       fub_awready,

    // Write data channel (W)
    input  logic [DW-1:0]              fub_wdata,
    input  logic [DW/8-1:0]            fub_wstrb,
    input  logic                       fub_wvalid,
    output logic                       fub_wready,

    // Write response channel (B)
    output logic [1:0]                 fub_bresp,
    output logic                       fub_bvalid,
    input  logic                       fub_bready,

    // Master AXI-Lite Interface (Output Side)
    // Write address channel (AW)
    output logic [AW-1:0]              m_axil_awaddr,
    output logic [2:0]                 m_axil_awprot,
    output logic                       m_axil_awvalid,
    input  logic                       m_axil_awready,

    // Write data channel (W)
    output logic [DW-1:0]              m_axil_wdata,
    output logic [DW/8-1:0]            m_axil_wstrb,
    output logic                       m_axil_wvalid,
    input  logic                       m_axil_wready,

    // Write response channel (B)
    input  logic [1:0]                 m_axil_bresp,
    input  logic                       m_axil_bvalid,
    output logic                       m_axil_bready,

    // Status outputs for clock gating
    output logic                       busy
);

    // SKID buffer connections
    logic [3:0]                 int_aw_count;
    logic [AWSize-1:0]          int_aw_pkt;
    logic                       int_skid_awvalid;
    logic                       int_skid_awready;

    logic [3:0]                 int_w_count;
    logic [WSize-1:0]           int_w_pkt;
    logic                       int_skid_wvalid;
    logic                       int_skid_wready;

    logic [3:0]                 int_b_count;
    logic [BSize-1:0]           int_b_pkt;
    logic                       int_skid_bvalid;
    logic                       int_skid_bready;

    // Busy signal indicates activity in the buffers
    assign busy = (int_aw_count > 0) || (int_w_count > 0) || (int_b_count > 0) ||
                    fub_awvalid || fub_wvalid || m_axil_bvalid;

    // Instantiate AW Skid Buffer
    gaxi_skid_buffer #(
        .DEPTH(SKID_DEPTH_AW),
        .DATA_WIDTH(AWSize),
        .INSTANCE_NAME("AXIL_AW_SKID")
    ) aw_channel (
        .axi_aclk               (aclk),
        .axi_aresetn            (aresetn),
        .wr_valid               (fub_awvalid),
        .wr_ready               (fub_awready),
        .wr_data                ({fub_awaddr, fub_awprot}),
        .rd_valid               (int_skid_awvalid),
        .rd_ready               (int_skid_awready),
        .rd_count               (int_aw_count),
        .rd_data                (int_aw_pkt),
        /* verilator lint_off PINCONNECTEMPTY */
        .count                  ()
        /* verilator lint_on PINCONNECTEMPTY */
    );

    // Unpack AW signals from SKID buffer
    assign {m_axil_awaddr, m_axil_awprot} = int_aw_pkt;
    assign m_axil_awvalid = int_skid_awvalid;
    assign int_skid_awready = m_axil_awready;

    // Instantiate W Skid Buffer
    gaxi_skid_buffer #(
        .DEPTH(SKID_DEPTH_W),
        .DATA_WIDTH(WSize),
        .INSTANCE_NAME("AXIL_W_SKID")
    ) w_channel (
        .axi_aclk               (aclk),
        .axi_aresetn            (aresetn),
        .wr_valid               (fub_wvalid),
        .wr_ready               (fub_wready),
        .wr_data                ({fub_wdata, fub_wstrb}),
        .rd_valid               (int_skid_wvalid),
        .rd_ready               (int_skid_wready),
        .rd_count               (int_w_count),
        .rd_data                (int_w_pkt),
        /* verilator lint_off PINCONNECTEMPTY */
        .count                  ()
        /* verilator lint_on PINCONNECTEMPTY */
    );

    // Unpack W signals from SKID buffer
    assign {m_axil_wdata, m_axil_wstrb} = int_w_pkt;
    assign m_axil_wvalid = int_skid_wvalid;
    assign int_skid_wready = m_axil_wready;

    // Instantiate B channel for write response back
    gaxi_skid_buffer #(
        .DEPTH(SKID_DEPTH_B),
        .DATA_WIDTH(BSize),
        .INSTANCE_NAME("AXIL_B_SKID")
    ) b_channel (
        .axi_aclk               (aclk),
        .axi_aresetn            (aresetn),
        .wr_valid               (m_axil_bvalid),
        .wr_ready               (m_axil_bready),
        .wr_data                (m_axil_bresp),
        .rd_valid               (int_skid_bvalid),
        .rd_ready               (int_skid_bready),
        .rd_count               (int_b_count),
        .rd_data                (fub_bresp),
        /* verilator lint_off PINCONNECTEMPTY */
        .count                  ()
        /* verilator lint_on PINCONNECTEMPTY */
    );

    assign fub_bvalid = int_skid_bvalid;
    assign int_skid_bready = fub_bready;

endmodule : axil4_master_wr
