`timescale 1ns / 1ps

module axi2apb_convert #(
    parameter int SIDE_DEPTH        = 6,
    parameter int AXI_ID_WIDTH      = 8,
    parameter int AXI_ADDR_WIDTH    = 32,
    parameter int AXI_DATA_WIDTH    = 32,
    parameter int AXI_USER_WIDTH    = 1,
    parameter int APB_ADDR_WIDTH    = 32,
    parameter int APB_DATA_WIDTH    = 32,
    parameter int AXI_WSTRB_WIDTH   = AXI_DATA_WIDTH / 8,
    parameter int APB_WSTRB_WIDTH   = APB_DATA_WIDTH / 8
) (
    // Clock and Reset
    input  logic                    aclk,
    input  logic                    aresetn,

    // Inputs from axi_slave_stub
    input  logic [AWSize-1:0]       r_s_axi_aw_pkt,
    input  logic [1:0]              r_s_axi_aw_count,
    input  logic                    r_s_axi_awvalid,
    output logic                    w_s_axi_awready,

    input  logic [WSize-1:0]        r_s_axi_w_pkt,
    input  logic                    r_s_axi_wvalid,
    output logic                    w_s_axi_wready,

    output logic [BSize-1:0]        r_s_axi_b_pkt,
    output logic                    w_s_axi_bvalid,
    input  logic                    r_s_axi_bready,

    input  logic [ARSize-1:0]       r_s_axi_ar_pkt,
    input  logic [1:0]              r_s_axi_ar_count,
    input  logic                    r_s_axi_arvalid,
    output logic                    w_s_axi_arready,

    output logic [RSize-1:0]        r_s_axi_r_pkt,
    output logic                    w_s_axi_rvalid,
    input  logic                    r_s_axi_rready,

    // APB Master Interface
    output logic                    w_cmd_valid,
    input  logic                    r_cmd_ready,
    output logic [APBCmdWidth-1:0]  r_cmd_data,

    input  logic                    r_rsp_valid,
    output logic                    w_rsp_ready,
    input  logic [APBRspWidth-1:0]  r_rsp_data
);

    localparam int AW                = AXI_ADDR_WIDTH;
    localparam int DW                = AXI_DATA_WIDTH;
    localparam int IW                = AXI_ID_WIDTH;
    localparam int UW                = AXI_USER_WIDTH;
    localparam int SW                = AXI_DATA_WIDTH / 8;
    localparam int APBAW             = APB_ADDR_WIDTH;
    localparam int APBDW             = APB_DATA_WIDTH;
    localparam int APBSW             = APB_DATA_WIDTH / 8;
    localparam int AXI2APBRATIO      = DW / APBDW;
    localparam int AWSize            = IW + AW + 8 + 3 + 2 + 1 + 4 + 3 + 4 + 4 + UW;
    localparam int WSize             = DW + SW + 1 + UW;
    localparam int BSize             = IW + 2 + UW;
    localparam int ARSize            = IW + AW + 8 + 3 + 2 + 1 + 4 + 3 + 4 + 4 + UW;
    localparam int RSize             = IW + DW + 2 + 1 + UW;
    localparam int APBCmdWidth       = APBAW + APBDW + APBSW + 3 + 1 + 1 + 1;
    localparam int APBRspWidth       = APBDW + 1 + 1 + 1;
    localparam int SideSize          = 1 + IW + 1 + UW;

    // Extract signals from AW packet
    logic [IW-1:0]     r_s_axi_awid;
    logic [AW-1:0]     r_s_axi_awaddr;
    logic [7:0]        r_s_axi_awlen;
    logic [2:0]        r_s_axi_awsize;
    logic [1:0]        r_s_axi_awburst;
    logic              r_s_axi_awlock;
    logic [3:0]        r_s_axi_awcache;
    logic [2:0]        r_s_axi_awprot;
    logic [3:0]        r_s_axi_awqos;
    logic [3:0]        r_s_axi_awregion;
    logic [UW-1:0]     r_s_axi_awuser;

    assign {r_s_axi_awid, r_s_axi_awaddr, r_s_axi_awlen, r_s_axi_awsize, r_s_axi_awburst,
            r_s_axi_awlock, r_s_axi_awcache, r_s_axi_awprot, r_s_axi_awqos,
            r_s_axi_awregion, r_s_axi_awuser} = r_s_axi_aw_pkt;

    // Extract signals from W packet
    logic [DW-1:0]     r_s_axi_wdata;
    logic [SW-1:0]     r_s_axi_wstrb;
    logic              r_s_axi_wlast;
    logic [UW-1:0]     r_s_axi_wuser;

    assign {r_s_axi_wdata, r_s_axi_wstrb, r_s_axi_wlast, r_s_axi_wuser} = r_s_axi_w_pkt;

    // Extract signals from AR packet
    logic [IW-1:0]     r_s_axi_arid;
    logic [AW-1:0]     r_s_axi_araddr;
    logic [7:0]        r_s_axi_arlen;
    logic [2:0]        r_s_axi_arsize;
    logic [1:0]        r_s_axi_arburst;
    logic              r_s_axi_arlock;
    logic [3:0]        r_s_axi_arcache;
    logic [2:0]        r_s_axi_arprot;
    logic [3:0]        r_s_axi_arqos;
    logic [3:0]        r_s_axi_arregion;
    logic [UW-1:0]     r_s_axi_aruser;

    assign {r_s_axi_arid, r_s_axi_araddr, r_s_axi_arlen, r_s_axi_arsize, r_s_axi_arburst,
            r_s_axi_arlock, r_s_axi_arcache, r_s_axi_arprot, r_s_axi_arqos,
            r_s_axi_arregion, r_s_axi_aruser} = r_s_axi_ar_pkt;

    // Side Skid Buffer for read and write responses
    logic                w_side_in_valid;
    logic                r_side_in_ready;
    logic [SideSize-1:0] r_side_in_data;
    logic [SideSize-1:0] r_side_in_data_rd;
    logic [SideSize-1:0] r_side_in_data_wr;
    logic                r_side_out_valid;
    logic                w_side_out_ready;
    logic [SideSize-1:0] r_side_out_data;
    logic [DW-1:0]       w_data_zeros;
    logic [DW-1:0]       w_data_read;
    logic                w_pslverr, r_pslverr;
    logic [1:0]          w_resp_rd;
    logic [1:0]          w_resp_wr;

    // Unbundling signals
    logic                r_side_operation;
    logic [IW-1:0]       r_side_id;
    logic [DW-1:0]       r_side_data;
    logic                r_side_last;
    logic [UW-1:0]       r_side_user;

    assign w_data_zeros = 'b0;

    // APB Master Packet signals
    logic                          w_apb_cmd_pkt_last;
    logic                          w_apb_cmd_pkt_first;
    logic                          w_apb_cmd_pkt_pwrite;
    logic [2:0]                    w_apb_cmd_pkt_pprot;
    logic [APB_WSTRB_WIDTH-1:0]    w_apb_cmd_pkt_pstrb;
    logic [APB_ADDR_WIDTH-1:0]     w_apb_cmd_pkt_paddr;
    logic [APB_DATA_WIDTH-1:0]     w_apb_cmd_pkt_pwdata;

    // APB Response Packet signals
    logic [APB_DATA_WIDTH-1:0]     r_apb_rsp_pkt_prdata;
    logic                          r_apb_rsp_pkt_pslverr;
    logic                          r_apb_rsp_pkt_first;
    logic                          r_apb_rsp_pkt_last;

    // Data shift register and pointer
    logic [DW-1:0]                   r_axi_data_shift, w_axi_data_shift;
    logic [$clog2(AXI2APBRATIO)-1:0] r_axi_rd_data_pointer, w_axi_rd_data_pointer;
    logic [$clog2(AXI2APBRATIO)-1:0] r_axi_wr_data_pointer, w_axi_wr_data_pointer;
    logic [$clog2(AXI2APBRATIO)-1:0] r_axi_rsp_data_pointer, w_axi_rsp_data_pointer;
    int                              axi2abpratio = AXI2APBRATIO;

    // axi_gen_addr module
    logic [APBAW-1:0] w_next_addr;
    logic [APBAW-1:0] w_next_addr_gen;
    logic [APBAW-1:0] r_apb_paddr;
    logic [2:0]       r_axi_size;
    logic [1:0]       r_axi_burst;
    logic [7:0]       r_axi_len;
    logic [APBAW-1:0] w_alignment_mask = APBSW - 1;

    // Burst counter
    logic [7:0]       r_burst_count, w_burst_count;

    // APB FSM
    typedef enum logic [2:0] {
        IDLE     = 3'b001,
        READ     = 3'b010,
        WRITE    = 3'b100
    } apb_state_t;
    apb_state_t r_apb_state, r_apb_last_state, w_apb_next_state;

    // Response FSM
    typedef enum logic [1:0] {
        RSP_IDLE    = 2'b01,
        RSP_ACTIVE  = 2'b10
    } rsp_state_t;
    rsp_state_t r_rsp_state, w_rsp_next_state;

    // assign the side queue input packets
    assign r_side_in_data_rd = {1'b0, r_s_axi_arid,
                                w_apb_cmd_pkt_last, r_s_axi_aruser};
    assign r_side_in_data_wr = {1'b1, r_s_axi_awid,
                                w_apb_cmd_pkt_last, r_s_axi_awuser};
    // Assign the side data input
    assign r_side_in_data    = (r_apb_state == READ) ? r_side_in_data_rd : r_side_in_data_wr;

    // Unbundle the data output
    assign {r_side_operation, r_side_id,
            r_side_last, r_side_user} = r_side_out_data;

    // Assign the side outputs to the responses to the AXI slave
    assign w_data_read    = (axi2abpratio == 1) ? r_apb_rsp_pkt_prdata : w_axi_data_shift;
    assign w_resp_rd      = (w_pslverr) ? 2'b10 : 2'b00;
    assign w_resp_wr      = (w_pslverr | r_pslverr) ? 2'b10 : 2'b00;
    assign r_s_axi_r_pkt  = {r_side_id, w_data_read, w_resp_rd, r_side_last, r_side_user};
    assign r_s_axi_b_pkt  = {r_side_id, w_resp_wr, r_side_user};

    // Assign the apb master command packet
    assign r_cmd_data  = {w_apb_cmd_pkt_last, w_apb_cmd_pkt_first, w_apb_cmd_pkt_pwrite,
                            w_apb_cmd_pkt_pprot, w_apb_cmd_pkt_pstrb, w_apb_cmd_pkt_paddr,
                            w_apb_cmd_pkt_pwdata};

    // Assign the apb master response packet
    assign {r_apb_rsp_pkt_last, r_apb_rsp_pkt_first, r_apb_rsp_pkt_pslverr,
                r_apb_rsp_pkt_prdata} = r_rsp_data;

    // select the proper inputs to the gen_addr module
    assign r_axi_size  = (r_apb_state == READ) ? r_s_axi_arsize  : r_s_axi_awsize;
    assign r_axi_burst = (r_apb_state == READ) ? r_s_axi_arburst : r_s_axi_awburst;
    assign r_axi_len   = (r_apb_state == READ) ? r_s_axi_arlen   : r_s_axi_awlen;

    // Instantiate the gen_addr module
    axi_gen_addr #(
        .AW                 (APBAW),
        .DW                 (DW),
        .ODW                (APBDW),
        .LEN                (8)
    ) axi_gen_addr_common (
        .i_curr_addr        (r_apb_paddr),
        .i_size             (r_axi_size),
        .i_burst            (r_axi_burst),
        .i_len              (r_axi_len),
        .ow_next_addr       (w_next_addr_gen)
    );

    always_ff @(posedge aclk or negedge aresetn) begin
        if (~aresetn) begin
            r_apb_state            <= IDLE;
            r_apb_last_state       <= IDLE;
            r_rsp_state            <= RSP_IDLE;
            r_apb_paddr            <= 'b0;
            r_burst_count          <= 'b0;
            r_axi_data_shift       <= 'b0;
            r_axi_rd_data_pointer  <= 'b0;
            r_axi_rsp_data_pointer <= 'b0;
        end else begin
            r_apb_state            <= w_apb_next_state;
            r_apb_last_state       <= r_apb_state;
            r_rsp_state            <= w_rsp_next_state;
            r_axi_rd_data_pointer  <= w_axi_rd_data_pointer;
            r_axi_wr_data_pointer  <= w_axi_wr_data_pointer;
            r_axi_rsp_data_pointer <= w_axi_rsp_data_pointer;

            if (r_rsp_state == RSP_IDLE) begin
                r_pslverr <= 1'b0;
                r_axi_rsp_data_pointer <= 'b0;
            end else
                r_pslverr <= r_pslverr | w_pslverr;  // TODO: only assert w_pslverr when rsp is vld

            if ((r_rsp_state == RSP_ACTIVE) && r_rsp_valid && w_rsp_ready) begin
                if (axi2abpratio == 1) begin
                    r_axi_data_shift <= r_apb_rsp_pkt_prdata;
                end else begin
                    r_axi_data_shift[r_axi_rsp_data_pointer*APBDW +: APBDW] <= r_apb_rsp_pkt_prdata;
                    r_axi_rsp_data_pointer <= r_axi_rsp_data_pointer + 1;
                    if (r_axi_rsp_data_pointer == axi2abpratio-1) begin
                        r_axi_rsp_data_pointer <= 'b0;
                    end
                end
            end

            if ((r_apb_state == IDLE) && (w_apb_next_state == READ)) begin
                r_apb_paddr           <= r_s_axi_araddr & ~w_alignment_mask;
                r_burst_count         <= r_s_axi_arlen;
                r_axi_rd_data_pointer <= 'b0;
                r_axi_data_shift      <= 'b0;
            end else if ((r_apb_state == IDLE) && (w_apb_next_state == WRITE)) begin
                r_apb_paddr           <= r_s_axi_awaddr & ~w_alignment_mask;
                r_burst_count         <= r_s_axi_awlen;
                r_axi_wr_data_pointer <= 'b0;
            end

            if (r_cmd_ready && (r_apb_state != IDLE)) begin
                r_apb_paddr   <= w_next_addr;
                r_burst_count <= w_burst_count;
                if ((r_apb_state == READ) && w_cmd_valid) begin
                    if (axi2abpratio != 1) begin
                        r_axi_rd_data_pointer <= r_axi_rd_data_pointer + 1;
                        if (r_axi_rd_data_pointer == axi2abpratio-1)
                            r_axi_rd_data_pointer <= 'b0;
                    end
                end else if ((r_apb_state == WRITE)) begin
                    if (axi2abpratio != 1 && w_cmd_valid) begin
                        r_axi_wr_data_pointer <= r_axi_wr_data_pointer + 1;
                        if (r_axi_wr_data_pointer == axi2abpratio-1)
                            r_axi_wr_data_pointer <= 'b0;
                    end
                end
            end
        end
    end

    always_comb begin
        w_apb_next_state           = r_apb_state;
        w_rsp_next_state           = r_rsp_state;
        w_next_addr                = r_apb_paddr;
        w_pslverr                  = (r_rsp_valid) ? r_apb_rsp_pkt_pslverr : 1'b0;
        w_cmd_valid                = 1'b0;
        w_side_in_valid            = 1'b0;
        w_apb_cmd_pkt_pwrite       = 1'b0;
        w_apb_cmd_pkt_pwdata       = (axi2abpratio == 1)    ? r_s_axi_wdata  :
                                        r_s_axi_wdata[r_axi_wr_data_pointer*APBDW +: APBDW];
        w_apb_cmd_pkt_pstrb        = (axi2abpratio == 1)    ? r_s_axi_wstrb  :
                                        r_s_axi_wstrb[r_axi_wr_data_pointer*APBSW +: APBSW];
        w_apb_cmd_pkt_pprot        = (r_apb_state  == READ) ? r_s_axi_arprot : r_s_axi_awprot;
        w_apb_cmd_pkt_paddr        = r_apb_paddr & ~w_alignment_mask;
        w_apb_cmd_pkt_first        = 1'b0;
        w_apb_cmd_pkt_last         = 1'b0;
        w_axi_rd_data_pointer      = r_axi_rd_data_pointer;
        w_axi_wr_data_pointer      = r_axi_wr_data_pointer;
        w_axi_rsp_data_pointer     = r_axi_rsp_data_pointer;
        w_axi_data_shift           = r_axi_data_shift;
        w_s_axi_awready            = 1'b0;
        w_s_axi_wready             = 1'b0;
        w_s_axi_bvalid             = 1'b0;
        w_s_axi_arready            = 1'b0;
        w_s_axi_rvalid             = 1'b0;
        w_side_out_ready           = 1'b0;
        w_rsp_ready                = 1'b0;
        w_burst_count              = r_burst_count;

        case (r_rsp_state)
            RSP_IDLE: begin
                if (r_rsp_valid && r_apb_rsp_pkt_first) begin
                    w_rsp_next_state = RSP_ACTIVE;
                end
            end
            RSP_ACTIVE: begin
                if (r_rsp_valid && r_side_out_valid) begin
                    if (~r_side_operation && r_s_axi_rready) begin
                        w_side_out_ready = 1'b1;
                        w_rsp_ready      = 1'b1;
                        w_axi_data_shift[r_axi_rsp_data_pointer*APBDW +: APBDW] =
                                r_apb_rsp_pkt_prdata;
                        if (r_axi_rsp_data_pointer == axi2abpratio-1) begin
                            w_axi_rsp_data_pointer = 'b0;
                            w_s_axi_rvalid         = 1'b1;
                        end
                        if (r_side_last)
                            w_rsp_next_state = RSP_IDLE;
                    end else if (r_side_operation && r_s_axi_bready) begin
                        w_rsp_ready      = 1'b1;
                        w_side_out_ready = 1'b1;
                        if (r_side_last) begin
                            w_s_axi_bvalid   = 1'b1;
                            w_rsp_next_state = RSP_IDLE;
                        end
                    end
                end
            end
            default: w_rsp_next_state = RSP_IDLE;
        endcase

        case (r_apb_state)
            IDLE: begin
                if (~r_side_out_valid) // let the last command sequence clear out before the next
                    if (r_s_axi_awvalid && r_s_axi_wvalid) begin
                        w_apb_next_state     = WRITE;
                        w_apb_cmd_pkt_pwrite = 1'b1;
                        w_apb_cmd_pkt_paddr  = r_s_axi_awaddr & ~w_alignment_mask;
                    end else if (r_s_axi_arvalid) begin
                        w_apb_next_state     = READ;
                        w_apb_cmd_pkt_pwrite = 1'b0;
                        w_apb_cmd_pkt_paddr  = r_s_axi_araddr & ~w_alignment_mask;
                    end
            end

            READ: begin
                if (r_cmd_ready && r_side_in_ready) begin
                    w_cmd_valid     = 'b1;
                    w_next_addr     = w_next_addr_gen;
                    w_side_in_valid = 1'b1;
                    if (r_apb_last_state == IDLE)
                        w_apb_cmd_pkt_first = 1'b1;
                    if (r_axi_rd_data_pointer == axi2abpratio-1) begin
                        w_axi_rd_data_pointer = 'b0;
                        if (r_burst_count == 0) begin
                            w_apb_next_state   = IDLE;
                            w_s_axi_arready    = 1'b1;
                            w_apb_cmd_pkt_last = 1'b1;
                        end else begin
                            w_burst_count    = r_burst_count - 1;
                        end
                    end else begin
                        w_axi_rd_data_pointer = r_axi_rd_data_pointer + 1;
                    end
                end
            end

            WRITE: begin
                w_apb_cmd_pkt_pwrite = 1'b1;
                if (r_cmd_ready && r_side_in_ready && r_s_axi_wvalid) begin
                    w_cmd_valid = 'b1;
                    w_next_addr = w_next_addr_gen;
                    w_side_in_valid = 1'b1;
                    if (r_apb_last_state == IDLE)
                        w_apb_cmd_pkt_first = 1'b1;
                    if (r_axi_wr_data_pointer == axi2abpratio-1) begin
                        if (r_burst_count == 0) begin
                            w_apb_next_state      = IDLE;
                            w_s_axi_awready       = 1'b1;
                            w_s_axi_wready        = 1'b1;
                            w_axi_wr_data_pointer = 'b0;
                            w_apb_cmd_pkt_last    = 1'b1;
                        end else begin
                            w_burst_count      = r_burst_count - 1;
                            w_s_axi_wready     = 1'b1;
                        end
                    end else begin
                        w_axi_wr_data_pointer = r_axi_wr_data_pointer + 1;
                    end
                end
            end

            default: w_apb_next_state = IDLE;
        endcase
    end

    // Instantiate the side queue
    axi_fifo_sync #(.DATA_WIDTH(SideSize), .DEPTH(SIDE_DEPTH)) inst_side_fifo (
        .i_axi_aclk               (aclk),
        .i_axi_aresetn            (aresetn),
        .i_wr_valid               (w_side_in_valid),
        .o_wr_ready               (r_side_in_ready),
        .i_wr_data                (r_side_in_data),
        .o_rd_valid               (r_side_out_valid),
        .i_rd_ready               (w_side_out_ready),
        .ow_rd_data               (r_side_out_data)
    );

endmodule : axi2apb_convert
