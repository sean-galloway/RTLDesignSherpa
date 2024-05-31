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

    // Internal signals
    logic [IW-1:0]   axi_id;
    logic [AW-1:0]   axi_addr;
    logic [7:0]      axi_len;
    logic [2:0]      axi_size;
    logic [1:0]      axi_burst;
    logic [UW-1:0]   axi_user;
    logic [DW-1:0]   data_buffer;
    logic            data_valid, data_ready;
    logic [$clog2(AXI2APBRATIO)-1:0] data_pointer;
    logic [APB_ADDR_WIDTH-1:0] next_addr;
    logic [APB_ADDR_WIDTH+APB_DATA_WIDTH+APB_WSTRB_WIDTH+4-1:0] cmd_packet;
    logic [APB_DATA_WIDTH+2-1:0] resp_packet;
    logic cmd_valid, cmd_ready, rsp_valid, rsp_ready;
    logic read_in_progress, write_in_progress;
    logic [DW-1:0] rdata_buffer;
    logic [$clog2(AXI2APBRATIO)-1:0] rdata_pointer;
    logic rdata_valid, rdata_ready, rlast;
    logic [7:0] rlen_counter;

    // Instantiate the axi_slave_stub
    axi_slave_stub #(
        .AXI_ID_WIDTH (AXI_ID_WIDTH),
        .AXI_ADDR_WIDTH (AXI_ADDR_WIDTH),
        .AXI_DATA_WIDTH (AXI_DATA_WIDTH),
        .AXI_USER_WIDTH (AXI_USER_WIDTH)
    ) axi_slave_stub_inst (
        .aclk (aclk),
        .aresetn (aresetn),
        // Write address channel (AW)
        .s_axi_awid (s_axi_awid),
        .s_axi_awaddr (s_axi_awaddr),
        .s_axi_awlen (s_axi_awlen),
        .s_axi_awsize (s_axi_awsize),
        .s_axi_awburst (s_axi_awburst),
        .s_axi_awlock (s_axi_awlock),
        .s_axi_awcache (s_axi_awcache),
        .s_axi_awprot (s_axi_awprot),
        .s_axi_awqos (s_axi_awqos),
        .s_axi_awregion (s_axi_awregion),
        .s_axi_awuser (s_axi_awuser),
        .s_axi_awvalid (s_axi_awvalid),
        .s_axi_awready (s_axi_awready),
        // Write data channel (W)
        .s_axi_wdata (s_axi_wdata),
        .s_axi_wstrb (s_axi_wstrb),
        .s_axi_wlast (s_axi_wlast),
        .s_axi_wuser (s_axi_wuser),
        .s_axi_wvalid (s_axi_wvalid),
        .s_axi_wready (s_axi_wready),
        // Write response channel (B)
        .s_axi_bid (s_axi_bid),
        .s_axi_bresp (s_axi_bresp),
        .s_axi_buser (s_axi_buser),
        .s_axi_bvalid (s_axi_bvalid),
        .s_axi_bready (s_axi_bready),
        // Read address channel (AR)
        .s_axi_arid (s_axi_arid),
        .s_axi_araddr (s_axi_araddr),
        .s_axi_arlen (s_axi_arlen),
        .s_axi_arsize (s_axi_arsize),
        .s_axi_arburst (s_axi_arburst),
        .s_axi_arlock (s_axi_arlock),
        .s_axi_arcache (s_axi_arcache),
        .s_axi_arprot (s_axi_arprot),
        .s_axi_arqos (s_axi_arqos),
        .s_axi_arregion (s_axi_arregion),
        .s_axi_aruser (s_axi_aruser),
        .s_axi_arvalid (s_axi_arvalid),
        .s_axi_arready (s_axi_arready),
        // Read data channel (R)
        .s_axi_rid (s_axi_rid),
        .s_axi_rdata (s_axi_rdata),
        .s_axi_rresp (s_axi_rresp),
        .s_axi_rlast (s_axi_rlast),
        .s_axi_ruser (s_axi_ruser),
        .s_axi_rvalid (s_axi_rvalid),
        .s_axi_rready (s_axi_rready)
    );

    // Instantiate the axi_gen_addr for address generation
    axi_gen_addr #(
        .AW (AW),
        .DW (DW),
        .ODW (APBDW),
        .LEN (8)
    ) axi_gen_addr_inst (
        .i_curr_addr (axi_addr),
        .i_size (axi_size),
        .i_burst (axi_burst),
        .i_len (axi_len),
        .ow_next_addr (next_addr)
    );

    // Instantiate the apb_master_stub
    apb_master_stub #(
        .DATA_WIDTH (APB_DATA_WIDTH),
        .ADDR_WIDTH (APB_ADDR_WIDTH),
        .STRB_WIDTH (APB_WSTRB_WIDTH)
    ) apb_master_inst (
        .aclk (aclk),
        .aresetn (aresetn),
        .m_apb_PSEL (m_apb_PSEL),
        .m_apb_PENABLE (m_apb_PENABLE),
        .m_apb_PADDR (m_apb_PADDR),
        .m_apb_PWRITE (m_apb_PWRITE),
        .m_apb_PWDATA (m_apb_PWDATA),
        .m_apb_PSTRB (m_apb_PSTRB),
        .m_apb_PPROT (m_apb_PPROT),
        .m_apb_PRDATA (m_apb_PRDATA),
        .m_apb_PSLVERR (m_apb_PSLVERR),
        .m_apb_PREADY (m_apb_PREADY),
        .i_cmd_valid (cmd_valid),
        .o_cmd_ready (cmd_ready),
        .i_cmd_data (cmd_packet),
        .o_rsp_valid (rsp_valid),
        .i_rsp_ready (rsp_ready),
        .o_rsp_data (resp_packet)
    );

    // FSM for AXI to APB transactions
    typedef enum logic [1:0] {
        IDLE = 2'b00,
        WRITE_CMD = 2'b01,
        READ_CMD = 2'b10
    } fsm_state_t;

    fsm_state_t current_state, next_state;

    always_ff @(posedge aclk or negedge aresetn) begin
        if (!aresetn) begin
            current_state <= IDLE;
            axi_id <= '0;
            axi_len <= '0;
            data_pointer <= '0;
            data_valid <= '0;
            data_buffer <= '0;
            read_in_progress <= 1'b0;
            write_in_progress <= 1'b0;
            axi_user <= '0;
            rdata_buffer <= '0;
            rdata_pointer <= '0;
            rdata_valid <= '0;
            rlast <= '0;
            rlen_counter <= '0;
        end else begin
            current_state <= next_state;
            if (current_state == WRITE_CMD || current_state == READ_CMD) begin
                if (cmd_ready) begin
                    axi_addr <= next_addr;
                    axi_len <= axi_len - 1;
                    if (axi_len == 0) begin
                        current_state <= IDLE;
                    end
                end
            end
            if (s_axi_wvalid && s_axi_wready) begin
                data_buffer <= s_axi_wdata;
                data_valid <= 1'b1;
            end
            if (rsp_valid) begin
                rdata_buffer[(rdata_pointer*APBDW) +: APBDW] <= m_apb_PRDATA;
                rdata_pointer <= rdata_pointer + 1;
                if (rdata_pointer == AXI2APBRATIO-1) begin
                    rdata_valid <= 1'b1;
                    rdata_pointer <= '0;
                    if (rlen_counter == 1) begin
                        rlast <= 1'b1;
                    end
                    rlen_counter <= rlen_counter - 1;
                end
            end
            if (current_state == WRITE_CMD) begin
                axi_id <= s_axi_awid;
                axi_len <= s_axi_awlen;
                axi_addr <= s_axi_awaddr;
                axi_size <= s_axi_awsize;
                axi_burst <= s_axi_awburst;
                axi_user <= s_axi_awuser;
                write_in_progress <= 1'b1;
                read_in_progress <= 1'b0;
            end else if (current_state == READ_CMD) begin
                axi_id <= s_axi_arid;
                axi_len <= s_axi_arlen;
                axi_addr <= s_axi_araddr;
                axi_size <= s_axi_arsize;
                axi_burst <= s_axi_arburst;
                axi_user <= s_axi_aruser;
                rlen_counter <= s_axi_arlen + 1;
                write_in_progress <= 1'b0;
                read_in_progress <= 1'b1;
            end
        end
    end

    always_comb begin
        next_state = current_state;
        cmd_valid = 1'b0;
        rsp_ready = 1'b0;
        s_axi_awready = 1'b0;
        s_axi_wready = 1'b0;
        s_axi_arready = 1'b0;
        s_axi_rvalid = 1'b0;
        s_axi_bvalid = 1'b0;
        next_addr = axi_addr;

        case (current_state)
            IDLE: begin
                if (s_axi_awvalid && s_axi_wvalid) begin
                    next_state = WRITE_CMD;
                    cmd_valid = 1'b1;
                    s_axi_awready = 1'b1;
                    s_axi_wready = 1'b1;
                end else if (s_axi_arvalid) begin
                    next_state = READ_CMD;
                    cmd_valid = 1'b1;
                    s_axi_arready = 1'b1;
                end
            end

            WRITE_CMD: begin
                if (cmd_ready) begin
                    cmd_valid = 1'b1;
                    next_addr = next_addr;
                    if (axi_len == 0) begin
                        s_axi_bvalid = 1'b1;
                        next_state = IDLE;
                    end
                end
            end

            READ_CMD: begin
                if (cmd_ready) begin
                    cmd_valid = 1'b1;
                    next_addr = next_addr;
                    if (axi_len == 0) begin
                        s_axi_rvalid = 1'b1;
                        s_axi_rlast = rlast;
                        next_state = IDLE;
                    end
                end
                if (rdata_valid) begin
                    s_axi_rvalid = 1'b1;
                    rdata_valid = 1'b0;
                end
            end

            default: next_state = IDLE;
        endcase
    end

    // AXI read and write response signals
    assign s_axi_bid = axi_id;
    assign s_axi_bresp = resp_packet[1:0];
    assign s_axi_buser = axi_user;
    assign s_axi_rid = axi_id;
    assign s_axi_rdata = rdata_buffer;
    assign s_axi_rresp = resp_packet[APB_DATA_WIDTH+1:APB_DATA_WIDTH];
    assign s_axi_rlast = (axi_len == 0) ? 1'b1 : 1'b0;
    assign s_axi_ruser = axi_user;

    // Command packet construction
    assign cmd_packet = (write_in_progress) ? {1'b1, s_axi_awprot, s_axi_wstrb, axi_addr, data_buffer} :
                        {1'b0, s_axi_arprot, 4'b0, axi_addr, 32'b0};

endmodule : axi2apb_shim
