`timescale 1ns / 1ps

module axi_wr_upscale
#(
    parameter int SKID_DEPTH_AW          = 2,
    parameter int SKID_DEPTH_W           = 4,
    parameter int SKID_DEPTH_B           = 2,
    parameter int SKID_DEPTH_AR          = 2,
    parameter int SKID_DEPTH_R           = 4,

    parameter int AXI_ID_WIDTH        = 8,
    parameter int AXI_ADDR_WIDTH      = 32,
    parameter int AXI_MST_DATA_WIDTH  = 32,
    parameter int AXI_SLV_DATA_WIDTH  = 32,
    parameter int AXI_USER_WIDTH      = 1,
    parameter int AXI_MST_WSTRB_WIDTH = AXI_MST_DATA_WIDTH / 8,
    parameter int AXI_SLV_WSTRB_WIDTH = AXI_SLV_DATA_WIDTH / 8,
    // Short and aclculated params
    parameter int AW       = AXI_ADDR_WIDTH,
    parameter int MDW      = AXI_MST_DATA_WIDTH,
    parameter int SDW      = AXI_SLV_DATA_WIDTH,
    parameter int IW       = AXI_ID_WIDTH,
    parameter int MSW      = AXI_MST_WSTRB_WIDTH,
    parameter int SSW      = AXI_SLV_WSTRB_WIDTH,
    parameter int UW       = AXI_USER_WIDTH,
    parameter int MAWSize  = IW+AW+8+3+2+1+4+3+4+4+UW,
    parameter int MWSize   = MDW+MSW+1+UW,
    parameter int SAWSize  = IW+AW+8+3+2+1+4+3+4+4+UW,
    parameter int SWSize   = SDW+SSW+1+UW,
    parameter int BSize    = IW+2+UW
) (
    // Global Clock and Reset
    input  logic aclk,
    input  logic aresetn,

    // Write address channel (AW)
    input  logic [AXI_ID_WIDTH-1:0]        s_axi_awid,
    input  logic [AXI_ADDR_WIDTH-1:0]      s_axi_awaddr,
    input  logic [7:0]                     s_axi_awlen,
    input  logic [2:0]                     s_axi_awsize,
    input  logic [1:0]                     s_axi_awburst,
    input  logic                           s_axi_awlock,
    input  logic [3:0]                     s_axi_awcache,
    input  logic [2:0]                     s_axi_awprot,
    input  logic [3:0]                     s_axi_awqos,
    input  logic [3:0]                     s_axi_awregion,
    input  logic [AXI_USER_WIDTH-1:0]      s_axi_awuser,
    input  logic                           s_axi_awvalid,
    output logic                           s_axi_awready,

    // Write data channel (W)
    input  logic [AXI_SLV_DATA_WIDTH-1:0]  s_axi_wdata,
    input  logic [AXI_SLV_WSTRB_WIDTH-1:0] s_axi_wstrb,
    input  logic                           s_axi_wlast,
    input  logic [AXI_USER_WIDTH-1:0]      s_axi_wuser,
    input  logic                           s_axi_wvalid,
    output logic                           s_axi_wready,

    // Write response channel (B)
    output logic [AXI_ID_WIDTH-1:0]        s_axi_bid,
    output logic [1:0]                     s_axi_bresp,
    output logic [AXI_USER_WIDTH-1:0]      s_axi_buser,
    output logic                           s_axi_bvalid,
    input  logic                           s_axi_bready,

    // Write address channel (AW)
    output logic [AXI_ID_WIDTH-1:0]        m_axi_awid,
    output logic [AXI_ADDR_WIDTH-1:0]      m_axi_awaddr,
    output logic [7:0]                     m_axi_awlen,
    output logic [2:0]                     m_axi_awsize,
    output logic [1:0]                     m_axi_awburst,
    output logic                           m_axi_awlock,
    output logic [3:0]                     m_axi_awcache,
    output logic [2:0]                     m_axi_awprot,
    output logic [3:0]                     m_axi_awqos,
    output logic [3:0]                     m_axi_awregion,
    output logic [AXI_USER_WIDTH-1:0]      m_axi_awuser,
    output logic                           m_axi_awvalid,
    input  logic                           m_axi_awready,

    // Write data channel (W)
    output logic [AXI_MST_DATA_WIDTH-1:0]  m_axi_wdata,
    output logic [AXI_MST_WSTRB_WIDTH-1:0] m_axi_wstrb,
    output logic                           m_axi_wlast,
    output logic [AXI_USER_WIDTH-1:0]      m_axi_wuser,
    output logic                           m_axi_wvalid,
    input  logic                           m_axi_wready,

    // Write response channel (B)
    input  logic [AXI_ID_WIDTH-1:0]        m_axi_bid,
    input  logic [1:0]                     m_axi_bresp,
    input  logic [AXI_USER_WIDTH-1:0]      m_axi_buser,
    input  logic                           m_axi_bvalid,
    output logic                           m_axi_bready
);

    // Data and Strobe Size values
    localparam int DataRatio = AXI_SLV_DATA_WIDTH / AXI_MST_DATA_WIDTH;
    localparam int DataDiff  = AXI_SLV_DATA_WIDTH - AXI_MST_DATA_WIDTH;
    localparam int StrbDiff  = AXI_SLV_WSTRB_WIDTH - AXI_MST_WSTRB_WIDTH;

    logic                       r_s_axi_awvalid;
    logic                       r_s_axi_awready;
    logic [3:0]                 r_s_axi_aw_count;
    logic [SAWSize-1:0]         r_s_axi_aw_pkt;

    logic [AXI_ADDR_WIDTH-1:0]  r_s_axi_awaddr;
    logic [7:0]                 r_s_axi_awlen;
    logic [2:0]                 r_s_axi_awsize;
    logic [1:0]                 r_s_axi_awburst;
    logic                       r_s_axi_awlock;
    logic [3:0]                 r_s_axi_awcache;
    logic [2:0]                 r_s_axi_awprot;
    logic [3:0]                 r_s_axi_awqos;
    logic [3:0]                 r_s_axi_awregion;
    logic [AXI_USER_WIDTH-1:0]  r_s_axi_awuser;

    assign {r_s_axi_awid,r_s_axi_awaddr,r_s_axi_awlen,r_s_axi_awsize,r_s_axi_awburst,
                r_s_axi_awlock,r_s_axi_awcache,r_s_axi_awprot,r_s_axi_awqos,
                r_s_axi_awregion,r_s_axi_awuser} = r_s_axi_aw_pkt;

    // W interface
    logic                           r_s_axi_wvalid;
    logic                           r_s_axi_wready;
    logic [SWSize-1:0]              r_s_axi_w_pkt;

    logic [AXI_MST_DATA_WIDTH-1:0]  r_s_axi_wdata;
    logic [AXI_MST_WSTRB_WIDTH-1:0] r_s_axi_wstrb;
    logic                           r_s_axi_wlast;
    logic [AXI_USER_WIDTH-1:0]      r_s_axi_wuser;

    assign {r_s_axi_wdata,r_s_axi_wstrb,r_s_axi_wlast,r_s_axi_wuser} = r_s_axi_w_pkt;

    // B interface
    logic                       r_s_axi_bvalid;
    logic                       r_s_axi_bready;
    logic [BSize-1:0]           r_s_axi_b_pkt;

    // AW interface
    logic                       r_m_axi_awvalid;
    logic                       r_m_axi_awready;
    logic [3:0]                 r_m_axi_aw_count;
    logic [MAWSize-1:0]         r_m_axi_aw_pkt;

    logic [AXI_ID_WIDTH-1:0]    r_m_axi_awid;
    logic [AXI_ADDR_WIDTH-1:0]  r_m_axi_awaddr;
    logic [7:0]                 r_m_axi_awlen;
    logic [2:0]                 r_m_axi_awsize;
    logic [1:0]                 r_m_axi_awburst;
    logic                       r_m_axi_awlock;
    logic [3:0]                 r_m_axi_awcache;
    logic [2:0]                 r_m_axi_awprot;
    logic [3:0]                 r_m_axi_awqos;
    logic [3:0]                 r_m_axi_awregion;
    logic [AXI_USER_WIDTH-1:0]  r_m_axi_awuser;

    assign r_m_axi_aw_pkt = {r_m_axi_awid,r_m_axi_awaddr,r_m_axi_awlen,r_m_axi_awsize,
                r_m_axi_awburst, r_m_axi_awlock,r_m_axi_awcache,r_m_axi_awprot,r_m_axi_awqos,
                r_m_axi_awregion,r_m_axi_awuser};

    // W interface
    logic                           r_m_axi_wvalid;
    logic                           r_m_axi_wready;
    logic [MWSize-1:0]              r_m_axi_w_pkt;

    assign r_m_axi_w_pkt = {r_m_axi_wdata,r_m_axi_wstrb,r_m_axi_wlast,r_m_axi_wuser};

    logic [AXI_MST_DATA_WIDTH-1:0]  r_m_axi_wdata;
    logic [AXI_MST_WSTRB_WIDTH-1:0] r_m_axi_wstrb;
    logic                           r_m_axi_wlast;
    logic [AXI_USER_WIDTH-1:0]      r_m_axi_wuser;

    // B interface
    logic                       r_m_axi_bvalid;
    logic                       r_m_axi_bready;
    logic [BSize-1:0]           r_m_axi_b_pkt;

    // B Interface
    assign r_s_axi_bvalid = r_m_axi_bvalid;
    assign r_m_axi_bready = r_s_axi_bready;
    assign r_s_axi_b_pkt  = r_m_axi_b_pkt;

    axi_slave_wr_stub #(
        .SKID_DEPTH_AW          (SKID_DEPTH_AW),
        .SKID_DEPTH_W           (SKID_DEPTH_W),
        .SKID_DEPTH_B           (SKID_DEPTH_B),
        .AXI_ID_WIDTH           (AXI_ID_WIDTH),
        .AXI_ADDR_WIDTH         (AXI_ADDR_WIDTH),
        .AXI_DATA_WIDTH         (AXI_SLV_DATA_WIDTH),
        .AXI_USER_WIDTH         (AXI_USER_WIDTH),
        .AXI_WSTRB_WIDTH        (AXI_SLV_WSTRB_WIDTH)
    ) axi_slave_wr_stub_inst (
        .aclk                   (aclk),
        .aresetn                (aresetn),
        // Write address channel (AW)
        .s_axi_awid             (s_axi_awid),
        .s_axi_awaddr           (s_axi_awaddr),
        .s_axi_awlen            (s_axi_awlen),
        .s_axi_awsize           (s_axi_awsize),
        .s_axi_awburst          (s_axi_awburst),
        .s_axi_awlock           (s_axi_awlock),
        .s_axi_awcache          (s_axi_awcache),
        .s_axi_awprot           (s_axi_awprot),
        .s_axi_awqos            (s_axi_awqos),
        .s_axi_awregion         (s_axi_awregion),
        .s_axi_awuser           (s_axi_awuser),
        .s_axi_awvalid          (s_axi_awvalid),
        .s_axi_awready          (s_axi_awready),
        // Write data channel (W)
        .s_axi_wdata            (s_axi_wdata),
        .s_axi_wstrb            (s_axi_wstrb),
        .s_axi_wlast            (s_axi_wlast),
        .s_axi_wuser            (s_axi_wuser),
        .s_axi_wvalid           (s_axi_wvalid),
        .s_axi_wready           (s_axi_wready),
        // Write response channel (B)
        .s_axi_bid              (s_axi_bid),
        .s_axi_bresp            (s_axi_bresp),
        .s_axi_buser            (s_axi_buser),
        .s_axi_bvalid           (s_axi_bvalid),
        .s_axi_bready           (s_axi_bready),
        // Stub Outputs/Inputs
        // AW interface
        .r_s_axi_awvalid        (r_s_axi_awvalid),
        .r_s_axi_awready        (r_s_axi_awready),
        .r_s_axi_aw_count       (r_s_axi_aw_count),
        .r_s_axi_aw_pkt         (r_s_axi_aw_pkt),
        // W interface
        .r_s_axi_wvalid         (r_s_axi_wvalid),
        .r_s_axi_wready         (r_s_axi_wready),
        .r_s_axi_w_pkt          (r_s_axi_w_pkt),
        // B interface
        .r_s_axi_bvalid         (r_s_axi_bvalid),
        .r_s_axi_bready         (r_s_axi_bready),
        .r_s_axi_b_pkt          (r_s_axi_b_pkt)
    );

    axi_master_wr_stub #(
        .SKID_DEPTH_AW       (SKID_DEPTH_AW),
        .SKID_DEPTH_W        (SKID_DEPTH_W),
        .SKID_DEPTH_B        (SKID_DEPTH_B),
        .AXI_ID_WIDTH        (AXI_ID_WIDTH),
        .AXI_ADDR_WIDTH      (AXI_ADDR_WIDTH),
        .AXI_DATA_WIDTH      (AXI_MST_DATA_WIDTH),
        .AXI_USER_WIDTH      (AXI_USER_WIDTH),
        .AXI_WSTRB_WIDTH     (AXI_MST_WSTRB_WIDTH)
    ) u_axi_master_wr_stub (
        // Global Clock and Reset
        .aclk                (aclk),
        .aresetn             (aresetn),
        // Write address channel (AW)
        .m_axi_awid          (m_axi_awid),
        .m_axi_awaddr        (m_axi_awaddr),
        .m_axi_awlen         (m_axi_awlen),
        .m_axi_awsize        (m_axi_awsize),
        .m_axi_awburst       (m_axi_awburst),
        .m_axi_awlock        (m_axi_awlock),
        .m_axi_awcache       (m_axi_awcache),
        .m_axi_awprot        (m_axi_awprot),
        .m_axi_awqos         (m_axi_awqos),
        .m_axi_awregion      (m_axi_awregion),
        .m_axi_awuser        (m_axi_awuser),
        .m_axi_awvalid       (m_axi_awvalid),
        .m_axi_awready       (m_axi_awready),
        // Write data channel (W)
        .m_axi_wdata         (m_axi_wdata),
        .m_axi_wstrb         (m_axi_wstrb),
        .m_axi_wlast         (m_axi_wlast),
        .m_axi_wuser         (m_axi_wuser),
        .m_axi_wvalid        (m_axi_wvalid),
        .m_axi_wready        (m_axi_wready),
        // Write response channel (B)
        .m_axi_bid           (m_axi_bid),
        .m_axi_bresp         (m_axi_bresp),
        .m_axi_buser         (m_axi_buser),
        .m_axi_bvalid        (m_axi_bvalid),
        .m_axi_bready        (m_axi_bready),
        // Stub Outputs/Inputs
        // AW interface
        .r_m_axi_awvalid     (r_m_axi_awvalid),
        .r_m_axi_awready     (r_m_axi_awready),
        .r_m_axi_aw_count    (r_m_axi_aw_count),
        .r_m_axi_aw_pkt      (r_m_axi_aw_pkt),
        // W interface
        .r_m_axi_wvalid      (r_m_axi_wvalid),
        .r_m_axi_wready      (r_m_axi_wready),
        .r_m_axi_w_pkt       (r_m_axi_w_pkt),
        // B interface
        .r_m_axi_bvalid      (r_m_axi_bvalid),
        .r_m_axi_bready      (r_m_axi_bready),
        .r_m_axi_b_pkt       (r_m_axi_b_pkt)
    );

    // Transfer FSM
    typedef enum logic [2:0] {
        IDLE    = 3'b001,
        SIMPLE  = 3'b010,
        COMBINE = 3'b100
    } xfer_state_t;
    xfer_state_t r_xfer_state, w_xfer_next_state;

    // length counter
    logic [7:0]       r_length_count, w_length_count;
    logic [9:0]       w_xfer_size_bytes;

    // Data and Strobe accumulator
    logic [MDW-1:0]  r_data_accum, w_data_accum;
    logic [MSW-1:0]  r_strb_accum, w_strb_accum;
    logic [7:0]      r_accum_count_dn, w_accum_count_dn;
    logic [7:0]      r_accum_count_up, w_accum_count_up;
    logic [2:0]      r_awsize, w_awsize;

    // Size calculation
    assign w_xfer_size_bytes = (1 << r_s_axi_awsize);

    always_ff @(posedge aclk or negedge aresetn) begin
        if (~aresetn) begin
            r_xfer_state     <= IDLE;
            r_length_count   <= 'b0;
            r_data_accum     <= 'b0;
            r_strb_accum     <= 'b0;
            r_accum_count_up <= 'b0;
            r_accum_count_dn <= 'b0;
            r_awsize         <= 'b0;
        end else begin
            r_xfer_state      <= w_xfer_next_state;
            r_length_count    <= w_length_count;
            r_strb_accum      <= w_strb_accum;
            r_accum_count_up  <= w_accum_count_up;
            r_accum_count_dn  <= w_accum_count_dn;
            r_awsize          <= w_awsize;

            if (r_xfer_state == IDLE) begin
                r_data_accum     <= 'b0;
                r_strb_accum     <= 'b0;
            end else begin
                r_data_accum[SDW*r_accum_count_up+:SDW] <= r_s_axi_wdata;
                r_strb_accum[SSW*r_accum_count_up+:SSW] <= r_s_axi_wstrb;
            end
        end
    end

    // Take care of the control signals and the FSM
    always_comb begin
        w_xfer_next_state        = r_xfer_state;
        w_accum_count_dn         = r_accum_count_dn;
        w_accum_count_up         = r_accum_count_up;
        w_awsize                 = (w_xfer_next_state != IDLE) ? r_s_axi_awsize : r_awsize;
        w_data_accum             = r_data_accum;
        w_strb_accum             = r_strb_accum;
        r_s_axi_awready          = 1'b0;
        r_s_axi_wready           = 1'b0;
        w_length_count           = r_length_count;
        r_m_axi_awid             = r_s_axi_awid;
        r_m_axi_awaddr           = r_s_axi_awaddr;
        r_m_axi_awlen            = r_s_axi_awlen;
        r_m_axi_awsize           = r_s_axi_awsize;
        r_m_axi_awburst          = r_s_axi_awburst;
        r_m_axi_awlock           = r_s_axi_awlock;
        r_m_axi_awcache          = r_s_axi_awcache;
        r_m_axi_awprot           = r_s_axi_awprot;
        r_m_axi_awqos            = r_s_axi_awqos;
        r_m_axi_awregion         = r_s_axi_awregion;
        r_m_axi_awuser           = r_s_axi_awuser;
        r_m_axi_wdata            = (r_xfer_state == SIMPLE) ? {{DataDiff{1'b0}}, r_s_axi_wdata} :
                                        {r_s_axi_wdata, r_data_accum};
        r_m_axi_wstrb            = (r_xfer_state == SIMPLE) ? {{StrbDiff{1'b0}}, r_s_axi_wstrb} :
                                        {r_s_axi_wstrb, r_strb_accum};
        r_m_axi_wlast            = r_s_axi_wlast;
        r_m_axi_wuser            = r_s_axi_wuser;

        case (r_xfer_state)
            IDLE: begin
                if (r_s_axi_awvalid && r_m_axi_awready) begin
                    r_m_axi_awvalid  = 1'b1;
                    r_s_axi_awready  = 1'b1;
                    w_length_count   = r_s_axi_awlen;
                    w_accum_count_dn = DataRatio;
                    w_accum_count_up = 'b0;
                    w_data_accum     = 'b0;
                    w_strb_accum     = 'b0;
                    if (w_xfer_size_bytes <= AXI_MST_DATA_WIDTH) begin
                        w_xfer_next_state = SIMPLE;
                    end else begin
                        w_xfer_next_state = COMBINE;
                    end
                end
            end
            SIMPLE: begin
                if (r_s_axi_wvalid && r_m_axi_wready) begin
                    r_m_axi_wvalid = 1'b1;
                    r_s_axi_wready = 1'b1;
                    if (r_s_axi_wlast) begin
                        w_xfer_next_state = IDLE;
                    end
                end
            end
            COMBINE: begin
                if (r_s_axi_wvalid && r_m_axi_wready) begin
                    w_length_count = r_length_count-1;
                    w_accum_count_dn = r_accum_count_dn-1;
                    w_accum_count_up = r_accum_count_up+1;
                    if (r_accum_count_dn == 0) begin
                        r_m_axi_wvalid = 1'b1;
                        r_s_axi_wready = 1'b1;
                        if (w_length_count == 0) begin
                            r_m_axi_wlast     = 1'b1;
                            w_xfer_next_state = IDLE;
                            if (r_length_count * (AXI_SLV_DATA_WIDTH/8) < AXI_MST_DATA_WIDTH/8) begin
                                w_accum_count_dn = r_length_count;
                            end else begin
                                w_accum_count_dn = DataRatio;
                            end
                        end
                    end else begin
                        w_accum_count_dn = r_accum_count_dn-1;
                        w_accum_count_up = r_accum_count_up+1;
                        r_s_axi_wready = 1'b1;
                    end
                end
            end
            default: w_xfer_next_state = IDLE;
        endcase
    end

endmodule : axi_wr_upscale
