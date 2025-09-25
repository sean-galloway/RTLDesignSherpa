`timescale 1ns / 1ps

module axis_slave
#(
    parameter int SKID_DEPTH         = 4,
    parameter int AXIS_DATA_WIDTH    = 32,
    parameter int AXIS_ID_WIDTH      = 8,
    parameter int AXIS_DEST_WIDTH    = 4,
    parameter int AXIS_USER_WIDTH    = 1,
    
    // Short and calculated params
    parameter int DW       = AXIS_DATA_WIDTH,
    parameter int IW       = AXIS_ID_WIDTH,
    parameter int DESTW    = AXIS_DEST_WIDTH,
    parameter int UW       = AXIS_USER_WIDTH,
    parameter int SW       = DW / 8,
    parameter int IW_WIDTH = (IW > 0) ? IW : 1,    // Minimum 1 bit for zero-width signals
    parameter int DESTW_WIDTH = (DESTW > 0) ? DESTW : 1,
    parameter int UW_WIDTH = (UW > 0) ? UW : 1,
    parameter int TSize    = DW+SW+1+IW_WIDTH+DESTW_WIDTH+UW_WIDTH  // tdata+tstrb+tlast+tid+tdest+tuser
)
(
    // Global Clock and Reset
    input  logic                       aclk,
    input  logic                       aresetn,

    // Slave AXI4-Stream Interface (Input Side)
    input  logic [DW-1:0]              s_axis_tdata,
    input  logic [SW-1:0]              s_axis_tstrb,
    input  logic                       s_axis_tlast,
    input  logic [IW_WIDTH-1:0]        s_axis_tid,
    input  logic [DESTW_WIDTH-1:0]     s_axis_tdest,
    input  logic [UW_WIDTH-1:0]        s_axis_tuser,
    input  logic                       s_axis_tvalid,
    output logic                       s_axis_tready,

    // Master AXI4-Stream Interface (Output Side to memory or backend)
    output logic [DW-1:0]              fub_axis_tdata,
    output logic [SW-1:0]              fub_axis_tstrb,
    output logic                       fub_axis_tlast,
    output logic [IW_WIDTH-1:0]        fub_axis_tid,
    output logic [DESTW_WIDTH-1:0]      fub_axis_tdest,
    output logic [UW_WIDTH-1:0]        fub_axis_tuser,
    output logic                       fub_axis_tvalid,
    input  logic                       fub_axis_tready,

    // Status outputs for clock gating
    output logic                       busy
);

    // Internal connections for skid buffer
    logic [3:0]                int_t_count;
    logic [TSize-1:0]          int_t_pkt;
    logic                      int_skid_tvalid;
    logic                      int_skid_tready;

    // Busy signal indicates activity in the buffer
    assign busy = (int_t_count > 0) || s_axis_tvalid;

    // Instantiate T Skid Buffer
    gaxi_skid_buffer #(
        .DEPTH(SKID_DEPTH),
        .DATA_WIDTH(TSize),
        .INSTANCE_NAME("AXIS_T_SKID")
    ) i_t_channel (
        .axi_aclk               (aclk),
        .axi_aresetn            (aresetn),
        .wr_valid               (s_axis_tvalid),
        .wr_ready               (s_axis_tready),
        .wr_data                ({s_axis_tdata, s_axis_tstrb, s_axis_tlast,
                                  s_axis_tid, s_axis_tdest, s_axis_tuser}),
        .rd_valid               (int_skid_tvalid),
        .rd_ready               (int_skid_tready),
        .rd_count               (int_t_count),
        .rd_data                (int_t_pkt),
        /* verilator lint_off PINCONNECTEMPTY */
        .count                  ()
        /* verilator lint_on PINCONNECTEMPTY */
    );

    // Unpack T signals from SKID buffer with conditional assignments
    // Handle all combinations of zero-width signals
    generate
        if (IW > 0 && DESTW > 0 && UW > 0) begin : full_signals
            assign {fub_axis_tdata, fub_axis_tstrb, fub_axis_tlast,
                    fub_axis_tid, fub_axis_tdest, fub_axis_tuser} = int_t_pkt;
        end else if (IW > 0 && DESTW > 0 && UW == 0) begin : no_user
            assign {fub_axis_tdata, fub_axis_tstrb, fub_axis_tlast,
                    fub_axis_tid, fub_axis_tdest} = int_t_pkt[TSize-1:1];
            assign fub_axis_tuser = '0;
        end else if (IW > 0 && DESTW == 0 && UW > 0) begin : no_dest
            assign {fub_axis_tdata, fub_axis_tstrb, fub_axis_tlast,
                    fub_axis_tid, fub_axis_tuser} = int_t_pkt[TSize-1:1];
            assign fub_axis_tdest = '0;
        end else if (IW == 0 && DESTW > 0 && UW > 0) begin : no_id
            assign {fub_axis_tdata, fub_axis_tstrb, fub_axis_tlast,
                    fub_axis_tdest, fub_axis_tuser} = int_t_pkt[TSize-1:1];
            assign fub_axis_tid = '0;
        end else if (IW > 0 && DESTW == 0 && UW == 0) begin : no_dest_no_user
            assign {fub_axis_tdata, fub_axis_tstrb, fub_axis_tlast,
                    fub_axis_tid} = int_t_pkt[TSize-1:2];
            assign fub_axis_tdest = '0;
            assign fub_axis_tuser = '0;
        end else if (IW == 0 && DESTW > 0 && UW == 0) begin : no_id_no_user
            assign {fub_axis_tdata, fub_axis_tstrb, fub_axis_tlast,
                    fub_axis_tdest} = int_t_pkt[TSize-1:2];
            assign fub_axis_tid = '0;
            assign fub_axis_tuser = '0;
        end else if (IW == 0 && DESTW == 0 && UW > 0) begin : no_id_no_dest
            assign {fub_axis_tdata, fub_axis_tstrb, fub_axis_tlast,
                    fub_axis_tuser} = int_t_pkt[TSize-1:2];
            assign fub_axis_tid = '0;
            assign fub_axis_tdest = '0;
        end else begin : no_id_no_dest_no_user
            assign {fub_axis_tdata, fub_axis_tstrb, fub_axis_tlast} = int_t_pkt[TSize-1:3];
            assign fub_axis_tid = '0;
            assign fub_axis_tdest = '0;
            assign fub_axis_tuser = '0;
        end
    endgenerate
    assign fub_axis_tvalid = int_skid_tvalid;
    assign int_skid_tready = fub_axis_tready;

endmodule : axis_slave
