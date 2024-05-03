`timescale 1ns / 1ps

module axi2apb_shim #(
    parameter int AXI_ADDRESS_WIDTH = 32,
    parameter int AXI_DATA_WIDTH    = 32,
    parameter int AXI_ID_WIDTH      = 8,
    parameter int AXI_USER_WIDTH    = 1,
    parameter int APB_ADDR_WIDTH    = 32
) (
    // Clock and Reset
    input  logic                          aclk,
    input  logic                          aresetn,

    // AXI Slave Interface (Inputs)
    input  logic [AXI_ID_WIDTH-1:0]       s_axi_awid,
    input  logic [AXI_ADDRESS_WIDTH-1:0]  s_axi_awaddr,
    input  logic [7:0]                    s_axi_awlen,
    input  logic [2:0]                    s_axi_awsize,
    input  logic [1:0]                    s_axi_awburst,
    input  logic                          s_axi_awlock,
    input  logic [3:0]                    s_axi_awcache,
    input  logic [2:0]                    s_axi_awprot,
    input  logic [3:0]                    s_axi_awqos,
    input  logic [3:0]                    s_axi_awregion,
    input  logic [AXI_USER_WIDTH-1:0]     s_axi_awuser,
    input  logic                          s_axi_awvalid,
    input  logic [AXI_DATA_WIDTH-1:0]     s_axi_wdata,
    input  logic [AXI_DATA_WIDTH/8-1:0]   s_axi_wstrb,
    input  logic                          s_axi_wlast,
    input  logic [AXI_USER_WIDTH-1:0]     s_axi_wuser,
    input  logic                          s_axi_wvalid,
    input  logic                          s_axi_bready,
    input  logic [AXI_ID_WIDTH-1:0]       s_axi_arid,
    input  logic [AXI_ADDRESS_WIDTH-1:0]  s_axi_araddr,
    input  logic [7:0]                    s_axi_arlen,
    input  logic [2:0]                    s_axi_arsize,
    input  logic [1:0]                    s_axi_arburst,
    input  logic                          s_axi_arlock,
    input  logic [3:0]                    s_axi_arcache,
    input  logic [2:0]                    s_axi_arprot,
    input  logic [3:0]                    s_axi_arqos,
    input  logic [3:0]                    s_axi_arregion,
    input  logic [AXI_USER_WIDTH-1:0]     s_axi_aruser,
    input  logic                          s_axi_arvalid,
    input  logic                          s_axi_rready,

    // AXI Slave Interface (Outputs)
    output logic                          s_axi_awready,
    output logic                          s_axi_wready,
    output logic [AXI_ID_WIDTH-1:0]       s_axi_bid,
    output logic [1:0]                    s_axi_bresp,
    output logic [AXI_USER_WIDTH-1:0]     s_axi_buser,
    output logic                          s_axi_bvalid,
    output logic                          s_axi_arready,
    output logic [AXI_ID_WIDTH-1:0]       s_axi_rid,
    output logic [AXI_DATA_WIDTH-1:0]     s_axi_rdata,
    output logic [1:0]                    s_axi_rresp,
    output logic                          s_axi_rlast,
    output logic [AXI_USER_WIDTH-1:0]     s_axi_ruser,
    output logic                          s_axi_rvalid,

    // APB Master Interface (Outputs)
    output logic                          PSEL,
    output logic [APB_ADDR_WIDTH-1:0]     PADDR,
    output logic                          PENABLE,
    output logic                          PWRITE,
    output logic [AXI_DATA_WIDTH-1:0]     PWDATA,

    // APB Master Interface (Inputs)
    input  logic [AXI_DATA_WIDTH-1:0]     PRDATA,
    input  logic                          PREADY,
    input  logic                          PSLVERR
);

    localparam int unsigned AW    = AXI_ADDRESS_WIDTH;
    localparam int unsigned DW    = AXI_DATA_WIDTH;
    localparam int unsigned APBAW = APB_ADDR_WIDTH;
    localparam int unsigned IW    = AXI_ID_WIDTH;
    localparam int unsigned UW    = AXI_USER_WIDTH;
    localparam int unsigned SW    = AXI_DATA_WIDTH / 8;

    localparam int unsigned AWSize = IW+AW+8+3+2+1+4+3+4+4+UW;
    localparam int unsigned WSize  = DW+SW+1+UW;
    localparam int unsigned BSize  = IW+2+UW;
    localparam int unsigned ARSize = IW+AW+8+3+2+1+4+3+4+4+UW;
    localparam int unsigned RSize  = IW+DW+2+1+UW;

    // Internal signals
    logic [AWSize-1:0]         r_axi_aw_pkt;
    logic                      r_axi_awvalid;
    logic                      r_axi_awready;
    logic [WSize-1:0]          r_axi_w_pkt;
    logic                      r_axi_wvalid;
    logic                      r_axi_wready;
    logic [BSize-1:0]          r_axi_b_pkt;
    logic                      r_axi_bvalid;
    logic                      r_axi_bready;
    logic [ARSize-1:0]         r_axi_ar_pkt;
    logic                      r_axi_arvalid;
    logic                      r_axi_arready;
    logic [RSize-1:0]          r_axi_r_pkt;
    logic                      r_axi_rvalid;
    logic                      r_axi_rready;

    // Instantiate the axi_slave_stub
    axi_slave_stub #(
        .AXI_ID_WIDTH   (AXI_ID_WIDTH),
        .AXI_ADDR_WIDTH (AXI_ADDR_WIDTH),
        .AXI_DATA_WIDTH (AXI_DATA_WIDTH),
        .AXI_USER_WIDTH (AXI_USER_WIDTH)
    ) axi_slave_stub_inst (
        .aclk         (aclk),
        .aresetn      (aresetn),
        // Write address channel (AW)
        .s_axi_awid     (s_axi_awid),
        .s_axi_awaddr   (s_axi_awaddr),
        .s_axi_awlen    (s_axi_awlen),
        .s_axi_awsize   (s_axi_awsize),
        .s_axi_awburst  (s_axi_awburst),
        .s_axi_awlock   (s_axi_awlock),
        .s_axi_awcache  (s_axi_awcache),
        .s_axi_awprot   (s_axi_awprot),
        .s_axi_awqos    (s_axi_awqos),
        .s_axi_awregion (s_axi_awregion),
        .s_axi_awuser   (s_axi_awuser),
        .s_axi_awvalid  (s_axi_awvalid),
        .s_axi_awready  (s_axi_awready),
        // Write data channel (W)
        .s_axi_wdata    (s_axi_wdata),
        .s_axi_wstrb    (s_axi_wstrb),
        .s_axi_wlast    (s_axi_wlast),
        .s_axi_wuser    (s_axi_wuser),
        .s_axi_wvalid   (s_axi_wvalid),
        .s_axi_wready   (s_axi_wready),
        // Write response channel (B)
        .s_axi_bid      (s_axi_bid),
        .s_axi_bresp    (s_axi_bresp),
        .s_axi_buser    (s_axi_buser),
        .s_axi_bvalid   (s_axi_bvalid),
        .s_axi_bready   (s_axi_bready),
        // Read address channel (AR)
        .s_axi_arid     (s_axi_arid),
        .s_axi_araddr   (s_axi_araddr),
        .s_axi_arlen    (s_axi_arlen),
        .s_axi_arsize   (s_axi_arsize),
        .s_axi_arburst  (s_axi_arburst),
        .s_axi_arlock   (s_axi_arlock),
        .s_axi_arcache  (s_axi_arcache),
        .s_axi_arprot   (s_axi_arprot),
        .s_axi_arqos    (s_axi_arqos),
        .s_axi_arregion (s_axi_arregion),
        .s_axi_aruser   (s_axi_aruser),
        .s_axi_arvalid  (s_axi_arvalid),
        .s_axi_arready  (s_axi_arready),
        // Read data channel (R)
        .s_axi_rid      (s_axi_rid),
        .s_axi_rdata    (s_axi_rdata),
        .s_axi_rresp    (s_axi_rresp),
        .s_axi_rlast    (s_axi_rlast),
        .s_axi_ruser    (s_axi_ruser),
        .s_axi_rvalid   (s_axi_rvalid),
        .s_axi_rready   (s_axi_rready),
        // Stub Outputs/Inputs
        // AW interface
        .r_axi_awvalid  (r_axi_awvalid),
        .r_axi_awready  (r_axi_awready),
        .r_axi_aw_pkt   (r_axi_aw_pkt),
        // W interface
        .r_axi_wvalid   (r_axi_wvalid),
        .r_axi_wready   (r_axi_wready),
        .r_axi_w_pkt    (r_axi_w_pkt),
        // B interface
        .r_axi_bvalid   (r_axi_bvalid),
        .r_axi_bready   (r_axi_bready),
        .r_axi_b_pkt    (r_axi_b_pkt),
        // AR interface
        .r_axi_arvalid  (r_axi_arvalid),
        .r_axi_arready  (r_axi_arready),
        .r_axi_ar_pkt   (r_axi_ar_pkt),
        // R interface
        .r_axi_rvalid   (r_axi_rvalid),
        .r_axi_rready   (r_axi_rready),
        .r_axi_r_pkt    (r_axi_r_pkt)
    );


    // Extract signals from AW packet
    logic [IW-1:0]     r_axi_awid;
    logic [AW-1:0]     r_axi_awaddr;
    logic [7:0]        r_axi_awlen;
    logic [2:0]        r_axi_awsize;
    logic [1:0]        r_axi_awburst;
    logic              r_axi_awlock;
    logic [3:0]        r_axi_awcache;
    logic [2:0]        r_axi_awprot;
    logic [3:0]        r_axi_awqos;
    logic [3:0]        r_axi_awregion;
    logic [UW-1:0]     r_axi_awuser;

    assign {r_axi_awid, r_axi_awaddr, r_axi_awlen, r_axi_awsize, r_axi_awburst,
            r_axi_awlock, r_axi_awcache, r_axi_awprot, r_axi_awqos,
            r_axi_awregion, r_axi_awuser} = r_axi_aw_pkt;

    // Extract signals from W packet
    logic [DW-1:0]     r_axi_wdata;
    logic [SW-1:0]     r_axi_wstrb;
    logic              r_axi_wlast;
    logic [UW-1:0]     r_axi_wuser;

    assign {r_axi_wdata, r_axi_wstrb, r_axi_wlast, r_axi_wuser} = r_axi_w_pkt;

    // Extract signals from B packet
    logic [IW-1:0]     r_axi_bid;
    logic [1:0]        r_axi_bresp;
    logic [UW-1:0]     r_axi_buser;

    assign {r_axi_bid, r_axi_bresp, r_axi_buser} = r_axi_b_pkt;

    // Extract signals from AR packet
    logic [IW-1:0]     r_axi_arid;
    logic [AW-1:0]     r_axi_araddr;
    logic [7:0]        r_axi_arlen;
    logic [2:0]        r_axi_arsize;
    logic [1:0]        r_axi_arburst;
    logic              r_axi_arlock;
    logic [3:0]        r_axi_arcache;
    logic [2:0]        r_axi_arprot;
    logic [3:0]        r_axi_arqos;
    logic [3:0]        r_axi_arregion;
    logic [UW-1:0]     r_axi_aruser;

    assign {r_axi_arid, r_axi_araddr, r_axi_arlen, r_axi_arsize, r_axi_arburst,
            r_axi_arlock, r_axi_arcache, r_axi_arprot, r_axi_arqos,
            r_axi_arregion, r_axi_aruser} = r_axi_ar_pkt;

    // Extract signals from R packet
    logic [IW-1:0]     r_axi_rid;
    logic [DW-1:0]     r_axi_rdata;
    logic [1:0]        r_axi_rresp;
    logic              r_axi_rlast;
    logic [UW-1:0]     r_axi_ruser;

    assign {r_axi_rid, r_axi_rdata, r_axi_rresp, r_axi_rlast, r_axi_ruser} = r_axi_r_pkt;

    // Optimized APB FSM
    typedef enum logic [2:0] {
        IDLE  = 3'b001,
        READ  = 3'b010,
        WRITE = 3'b100
    } apb_state_t;

    apb_state_t apb_state, apb_next_state;

    logic [APBAW-1:0] r_paddr;
    logic             sample_RDATA;
    logic [DW-1:0]    RDATA_Q;

    always_ff @(posedge aclk or negedge aresetn) begin
        if (~aresetn) begin
            apb_state <= IDLE;
            RDATA_Q   <= '0;
            r_paddr   <= 'b0;
        end else begin
            apb_state <= apb_next_state;

            if (sample_RDATA)
                RDATA_Q <= PRDATA;

            if (apb_next_state == READ) begin
                r_paddr <= r_axi_araddr;
            end else if (apb_next_state == WRITE) begin
                r_paddr <= r_axi_awaddr;
            end
        end
    end

    always_comb begin
        apb_next_state = apb_state;
        PSEL           = 1'b0;
        PENABLE        = 1'b0;
        PWRITE         = 1'b0;
        PADDR          = r_paddr;
        PWDATA         = r_axi_w_pkt[DW-1:0];
        sample_RDATA   = 1'b0;
        r_axi_awready  = 1'b0;
        r_axi_wready   = 1'b0;
        r_axi_arready  = 1'b0;
        r_axi_rvalid   = 1'b0;
        r_axi_bvalid   = 1'b0;

        case (apb_state)
            IDLE: begin
                if (r_axi_arvalid) begin
                    apb_next_state = READ;
                    PSEL           = 1'b1;
                    r_axi_arready  = 1'b1;
                end else if (r_axi_awvalid && r_axi_wvalid) begin
                    apb_next_state = WRITE;
                    PSEL           = 1'b1;
                    PWRITE         = 1'b1;
                    r_axi_awready  = 1'b1;
                    r_axi_wready   = 1'b1;
                end
            end

            READ: begin
                PSEL         = 1'b1;
                PENABLE      = 1'b1;
                sample_RDATA = 1'b1;

                if (PREADY) begin
                    apb_next_state = IDLE;
                    r_axi_rvalid   = 1'b1;
                end
            end

            WRITE: begin
                PSEL    = 1'b1;
                PENABLE = 1'b1;
                PWRITE  = 1'b1;

                if (PREADY) begin
                    apb_next_state = IDLE;
                    r_axi_bvalid   = 1'b1;
                end
            end

            default: apb_next_state = IDLE;
        endcase
    end

    // Assign output signals
    assign r_axi_r_pkt  = {r_axi_arid, RDATA_Q, PSLVERR ? 2'b10 : 2'b00, 1'b1, {UW{1'b0}}};
    assign r_axi_b_pkt  = {r_axi_awid, PSLVERR ? 2'b10 : 2'b00, {UW{1'b0}}};

endmodule : axi2apb_shim
