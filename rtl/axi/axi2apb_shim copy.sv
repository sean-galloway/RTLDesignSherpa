`timescale 1ns / 1ps

module axi2apb_shim #(
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
    input  logic                       aclk,
    input  logic                       aresetn,

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

    // APB Master Interface (Outputs)
    output logic                          m_apb_PSEL,
    output logic [APB_ADDR_WIDTH-1:0]     m_apb_PADDR,
    output logic                          m_apb_PENABLE,
    output logic                          m_apb_PWRITE,
    output logic [APB_DATA_WIDTH-1:0]     m_apb_PWDATA,
    output logic [APB_WSTRB_WIDTH-1:0]    m_apb_PSTRB,
    output logic [2:0]                    m_apb_PPROT,

    // APB Master Interface (Inputs)
    input  logic [APB_DATA_WIDTH-1:0]     m_apb_PRDATA,
    input  logic                          m_apb_PREADY,
    input  logic                          m_apb_PSLVERR
);

    localparam int AW           = AXI_ADDR_WIDTH;
    localparam int DW           = AXI_DATA_WIDTH;
    localparam int IW           = AXI_ID_WIDTH;
    localparam int UW           = AXI_USER_WIDTH;
    localparam int SW           = AXI_DATA_WIDTH / 8;
    localparam int APBAW        = APB_ADDR_WIDTH;
    localparam int APBDW        = APB_DATA_WIDTH;
    localparam int APBSW        = APB_DATA_WIDTH / 8;
    localparam int AXI2APBRATIO = DW / APBDW;
    localparam int AWSize       = IW+AW+8+3+2+1+4+3+4+4+UW;
    localparam int WSize        = DW+SW+1+UW;
    localparam int BSize        = IW+2+UW;
    localparam int ARSize       = IW+AW+8+3+2+1+4+3+4+4+UW;
    localparam int RSize        = IW+DW+2+1+UW;

    // Internal signals
    logic [AWSize-1:0]         r_s_axi_aw_pkt;
    logic                      r_s_axi_awvalid;
    logic                      r_s_axi_awready;
    logic [WSize-1:0]          r_s_axi_w_pkt;
    logic                      r_s_axi_wvalid;
    logic                      r_s_axi_wready;
    logic [BSize-1:0]          r_s_axi_b_pkt;
    logic                      r_s_axi_bvalid;
    logic                      r_s_axi_bready;
    logic [ARSize-1:0]         r_s_axi_ar_pkt;
    logic                      r_s_axi_arvalid;
    logic                      r_s_axi_arready;
    logic [RSize-1:0]          r_s_axi_r_pkt;
    logic                      r_s_axi_rvalid;
    logic                      r_s_axi_rready;

    // Instantiate the axi_slave_stub
    axi_slave_stub #                   (
        .AXI_ID_WIDTH             (IW),
        .AXI_ADDR_WIDTH           (AW),
        .AXI_DATA_WIDTH           (DW),
        .AXI_USER_WIDTH           (UW)
    ) axi_slave_stub_inst         (
        .aclk                     (aclk),
        .aresetn                  (aresetn),
        // Write address channel  (AW)
        .s_axi_awid               (s_axi_awid),
        .s_axi_awaddr             (s_axi_awaddr),
        .s_axi_awlen              (s_axi_awlen),
        .s_axi_awsize             (s_axi_awsize),
        .s_axi_awburst            (s_axi_awburst),
        .s_axi_awlock             (s_axi_awlock),
        .s_axi_awcache            (s_axi_awcache),
        .s_axi_awprot             (s_axi_awprot),
        .s_axi_awqos              (s_axi_awqos),
        .s_axi_awregion           (s_axi_awregion),
        .s_axi_awuser             (s_axi_awuser),
        .s_axi_awvalid            (s_axi_awvalid),
        .s_axi_awready            (s_axi_awready),
        // Write data channel     (W)
        .s_axi_wdata              (s_axi_wdata),
        .s_axi_wstrb              (s_axi_wstrb),
        .s_axi_wlast              (s_axi_wlast),
        .s_axi_wuser              (s_axi_wuser),
        .s_axi_wvalid             (s_axi_wvalid),
        .s_axi_wready             (s_axi_wready),
        // Write response channel (B)
        .s_axi_bid                (s_axi_bid),
        .s_axi_bresp              (s_axi_bresp),
        .s_axi_buser              (s_axi_buser),
        .s_axi_bvalid             (s_axi_bvalid),
        .s_axi_bready             (s_axi_bready),
        // Read address channel   (AR)
        .s_axi_arid               (s_axi_arid),
        .s_axi_araddr             (s_axi_araddr),
        .s_axi_arlen              (s_axi_arlen),
        .s_axi_arsize             (s_axi_arsize),
        .s_axi_arburst            (s_axi_arburst),
        .s_axi_arlock             (s_axi_arlock),
        .s_axi_arcache            (s_axi_arcache),
        .s_axi_arprot             (s_axi_arprot),
        .s_axi_arqos              (s_axi_arqos),
        .s_axi_arregion           (s_axi_arregion),
        .s_axi_aruser             (s_axi_aruser),
        .s_axi_arvalid            (s_axi_arvalid),
        .s_axi_arready            (s_axi_arready),
        // Read data channel      (R)
        .s_axi_rid                (s_axi_rid),
        .s_axi_rdata              (s_axi_rdata),
        .s_axi_rresp              (s_axi_rresp),
        .s_axi_rlast              (s_axi_rlast),
        .s_axi_ruser              (s_axi_ruser),
        .s_axi_rvalid             (s_axi_rvalid),
        .s_axi_rready             (s_axi_rready),
        // Stub Outputs/Inputs
        // AW interface
        .r_s_axi_awvalid          (r_s_axi_awvalid),
        .r_s_axi_awready          (r_s_axi_awready),
        .r_s_axi_aw_pkt           (r_s_axi_aw_pkt),
        // W interface
        .r_s_axi_wvalid           (r_s_axi_wvalid),
        .r_s_axi_wready           (r_s_axi_wready),
        .r_s_axi_w_pkt            (r_s_axi_w_pkt),
        // B interface
        .r_s_axi_bvalid           (r_s_axi_bvalid),
        .r_s_axi_bready           (r_s_axi_bready),
        .r_s_axi_b_pkt            (r_s_axi_b_pkt),
        // AR interface
        .r_s_axi_arvalid          (r_s_axi_arvalid),
        .r_s_axi_arready          (r_s_axi_arready),
        .r_s_axi_ar_pkt           (r_s_axi_ar_pkt),
        // R interface
        .r_s_axi_rvalid           (r_s_axi_rvalid),
        .r_s_axi_rready           (r_s_axi_rready),
        .r_s_axi_r_pkt            (r_s_axi_r_pkt)
    );

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
    logic [WSize-1:0]  r_r_s_axi_w_pkt;
    logic [DW-1:0]     r_s_axi_wdata;
    logic [SW-1:0]     r_s_axi_wstrb;
    logic              r_s_axi_wlast;
    logic [UW-1:0]     r_s_axi_wuser;

    assign {r_s_axi_wdata, r_s_axi_wstrb, r_s_axi_wlast, r_s_axi_wuser} = r_s_axi_w_pkt;

    // Extract signals from B packet
    logic [BSize-1:0]  r_r_s_axi_b_pkt;

    always_ff @(posedge aclk) begin
        r_s_axi_b_pkt <= r_r_s_axi_b_pkt;
    end

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

    // Extract signals from R packet
    logic [IW-1:0]     r_s_axi_rid;
    logic [DW-1:0]     r_s_axi_rdata;
    logic [1:0]        r_s_axi_rresp;
    logic              r_s_axi_rlast;
    logic [UW-1:0]     r_s_axi_ruser;

    assign {r_s_axi_rid, r_s_axi_rdata, r_s_axi_rresp, r_s_axi_rlast, r_s_axi_ruser} = r_s_axi_r_pkt;

    // Instantiate the axi_gen_addr module
    logic [APBAW-1:0] w_next_addr_read;
    logic [APBAW-1:0] w_next_addr_write;
    logic [APBAW-1:0] w_next_addr;
    logic [APBAW-1:0] r_m_apb_PADDR;

    axi_gen_addr #(
        .AW              (APBAW),
        .DW              (DW),
        .ODW             (APBDW),
        .LEN             (8)
    ) axi_gen_addr_read  (
        .i_curr_addr     (r_m_apb_PADDR),
        .i_size          (r_s_axi_arsize),
        .i_burst         (r_s_axi_arburst),
        .i_len           (r_s_axi_arlen),
        .ow_next_addr    (w_next_addr_read)
    );

    axi_gen_addr #       (
        .AW              (APBAW),
        .DW              (DW),
        .ODW             (APBDW),
        .LEN             (8)
    ) axi_gen_addr_write (
        .i_curr_addr     (r_m_apb_PADDR),
        .i_size          (r_s_axi_awsize),
        .i_burst         (r_s_axi_awburst),
        .i_len           (r_s_axi_awlen),
        .ow_next_addr    (w_next_addr_write)
    );

    // Burst counter
    logic [7:0]                      r_burst_count, w_burst_count;
    // Data shift register and pointer
    logic [DW-1:0] r_axi_data_shift, w_axi_data_shift;
    logic [$clog2(AXI2APBRATIO)-1:0] r_axi_data_pointer, w_axi_data_pointer;
    logic                            w_rlast;
    int                              axi2abpratio = AXI2APBRATIO;

    // Optimized APB FSM
    typedef enum logic [2:0] {
        IDLE   = 3'b001,
        READ   = 3'b010,
        WRITE  = 3'b100
    } apb_state_t;

    apb_state_t r_apb_state, w_apb_next_state;

    always_ff @(posedge aclk or negedge aresetn) begin
        if (~aresetn) begin
            r_apb_state        <= IDLE;
            r_m_apb_PADDR      <= 'b0;
            r_burst_count      <= 'b0;
            r_axi_data_shift   <= 'b0;
            r_axi_data_pointer <= 'b0;
        end else begin
            r_apb_state        <= w_apb_next_state;
            r_axi_data_pointer <= w_axi_data_pointer;

            if ((r_apb_state == IDLE) && (w_apb_next_state == READ)) begin
                r_m_apb_PADDR      <= r_s_axi_araddr;
                r_burst_count      <= r_s_axi_arlen;
                r_axi_data_pointer <= 'b0;
                r_axi_data_shift   <= 'b0;
            end else if ((r_apb_state == IDLE) && (w_apb_next_state == WRITE)) begin
                r_m_apb_PADDR      <= r_s_axi_awaddr;
                r_burst_count      <= r_s_axi_awlen;
                r_axi_data_pointer <= 'b0;
            end

            if (m_apb_PENABLE) begin
                r_m_apb_PADDR <= w_next_addr;
                r_burst_count <= w_burst_count;

                if ((r_apb_state == READ) && m_apb_PREADY) begin
                    if (axi2abpratio == 1) begin
                        r_axi_data_shift <= m_apb_PRDATA;
                    end else begin
                        r_axi_data_shift[r_axi_data_pointer*APBDW +: APBDW] <= m_apb_PRDATA;
                        r_axi_data_pointer <= r_axi_data_pointer + 1;
                        if (r_axi_data_pointer == axi2abpratio-1) begin
                            r_axi_data_pointer <= 'b0;
                        end
                    end
                end else if ((r_apb_state == WRITE) && m_apb_PREADY) begin
                    if (axi2abpratio != 1) begin
                        r_axi_data_pointer <= r_axi_data_pointer + 1;
                        if (r_axi_data_pointer == axi2abpratio-1) begin
                            r_axi_data_pointer <= 'b0;
                        end
                    end
                end
            end
        end
    end

    always_comb begin
        w_apb_next_state   = r_apb_state;
        w_next_addr        = r_m_apb_PADDR;
        m_apb_PSEL         = 1'b0;
        m_apb_PENABLE      = 1'b0;
        m_apb_PWRITE       = 1'b0;
        m_apb_PWDATA       = (axi2abpratio == 1) ? r_s_axi_wdata : r_s_axi_wdata[r_axi_data_pointer*APBDW +: APBDW];
        m_apb_PSTRB        = (axi2abpratio == 1) ? r_s_axi_wstrb : r_s_axi_wstrb[r_axi_data_pointer*APBSW +: APBSW];
        m_apb_PPROT        = (r_apb_state == READ) ? r_s_axi_arprot : r_s_axi_awprot;
        r_s_axi_awready    = 1'b0;
        r_s_axi_wready     = 1'b0;
        r_s_axi_arready    = 1'b0;
        r_s_axi_rvalid     = 1'b0;
        r_s_axi_bvalid     = 1'b0;
        w_burst_count      = r_burst_count;
        m_apb_PADDR        = r_m_apb_PADDR;
        w_axi_data_pointer = r_axi_data_pointer;
        w_axi_data_shift   = r_axi_data_shift;
        w_rlast            = 'b0;

        case (r_apb_state)
            IDLE: begin
                if (r_s_axi_arvalid) begin
                    w_apb_next_state = READ;
                    m_apb_PSEL       = 1'b1;
                    m_apb_PADDR      = r_s_axi_araddr;
                end else if (r_s_axi_awvalid && r_s_axi_wvalid) begin
                    w_apb_next_state = WRITE;
                    m_apb_PSEL       = 1'b1;
                    m_apb_PWRITE     = 1'b1;
                    m_apb_PADDR      = r_s_axi_awaddr;
                end
            end

            READ: begin
                m_apb_PSEL = 1'b1;
                if (r_s_axi_rready) begin
                    m_apb_PENABLE = 1'b1;
                    if (m_apb_PREADY) begin
                        if (axi2abpratio == 1) begin
                            if (r_burst_count == 0) begin
                                w_apb_next_state = IDLE;
                                r_s_axi_arready  = 1'b1;
                                w_rlast          = 1'b1;
                            end else begin
                                w_burst_count    = r_burst_count - 1;
                            end
                            r_s_axi_rvalid = 1'b1;
                        end else begin
                            w_axi_data_pointer = r_axi_data_pointer + 1;
                            w_axi_data_shift[r_axi_data_pointer*APBDW +: APBDW] = m_apb_PRDATA;
                            if (r_axi_data_pointer == axi2abpratio-1) begin
                                w_axi_data_pointer = 'b0;
                                if (r_burst_count == 0) begin
                                    w_apb_next_state = IDLE;
                                    r_s_axi_arready  = 1'b1;
                                    w_rlast          = 1'b1;
                                end else begin
                                    w_burst_count    = r_burst_count - 1;
                                end
                                r_s_axi_rvalid = 1'b1;
                            end
                        end
                        w_next_addr = w_next_addr_read;
                    end
                end
            end

            WRITE: begin
                m_apb_PSEL   = 1'b1;
                m_apb_PWRITE = 1'b1;
                if (r_s_axi_wvalid) begin
                    if (r_s_axi_bready) begin
                        m_apb_PENABLE = 1'b1;
                        if (m_apb_PREADY) begin
                            if (axi2abpratio == 1) begin
                                if (r_burst_count == 0) begin
                                    w_apb_next_state = IDLE;
                                    r_s_axi_bvalid   = 1'b1;
                                    r_s_axi_awready  = 1'b1;
                                    r_s_axi_wready   = 1'b1;
                                end else begin
                                    w_burst_count    = r_burst_count - 1;
                                    r_s_axi_wready   = 1'b1;
                                end
                            end else begin
                                if (r_axi_data_pointer == axi2abpratio-1) begin
                                    if (r_burst_count == 0) begin
                                        w_apb_next_state   = IDLE;
                                        r_s_axi_bvalid     = 1'b1;
                                        r_s_axi_awready    = 1'b1;
                                        r_s_axi_wready     = 1'b1;
                                        w_axi_data_pointer = 'b0;
                                    end else begin
                                        w_burst_count    = r_burst_count - 1;
                                        r_s_axi_wready = 1'b1;
                                    end
                                end else begin
                                    w_axi_data_pointer = r_axi_data_pointer + 1;
                                end
                            end
                            w_next_addr = w_next_addr_write;
                        end
                    end
                end
            end

            default: w_apb_next_state = IDLE;
        endcase
    end

    // Assign output signals
    assign r_s_axi_r_pkt    = {r_s_axi_arid, (axi2abpratio == 1) ? m_apb_PRDATA : w_axi_data_shift,
                                m_apb_PSLVERR ? 2'b10 : 2'b00, w_rlast,
                                r_s_axi_aruser};
    assign r_r_s_axi_b_pkt  = {r_s_axi_awid, m_apb_PSLVERR ? 2'b10 : 2'b00, r_s_axi_awuser};

endmodule : axi2apb_shim
