`timescale 1ns / 1ps

// 2-to-4 APB crossbar with address decoding and arbitration
// 2 masters to 4 slaves using apb_slave and apb_master modules
//
// Address Map (same for all masters):
//   Slave 0: [0x10000000, 0x1000FFFF]
//   Slave 1: [0x10010000, 0x1001FFFF]
//   Slave 2: [0x10020000, 0x1002FFFF]
//   Slave 3: [0x10030000, 0x1003FFFF]

module apb_xbar_2to4 #(
    parameter int ADDR_WIDTH = 32,
    parameter int DATA_WIDTH = 32,
    parameter int STRB_WIDTH = DATA_WIDTH / 8,
    parameter logic [ADDR_WIDTH-1:0] BASE_ADDR = 32'h10000000
) (
    // Clock and Reset
    input  logic                  pclk,
    input  logic                  presetn,

    // Master 0 APB interface (from external master 0)
    input  logic                  m0_apb_PSEL,
    input  logic                  m0_apb_PENABLE,
    input  logic [ADDR_WIDTH-1:0] m0_apb_PADDR,
    input  logic                  m0_apb_PWRITE,
    input  logic [DATA_WIDTH-1:0] m0_apb_PWDATA,
    input  logic [STRB_WIDTH-1:0] m0_apb_PSTRB,
    input  logic [2:0]            m0_apb_PPROT,
    output logic [DATA_WIDTH-1:0] m0_apb_PRDATA,
    output logic                  m0_apb_PSLVERR,
    output logic                  m0_apb_PREADY,

    // Master 1 APB interface (from external master 1)
    input  logic                  m1_apb_PSEL,
    input  logic                  m1_apb_PENABLE,
    input  logic [ADDR_WIDTH-1:0] m1_apb_PADDR,
    input  logic                  m1_apb_PWRITE,
    input  logic [DATA_WIDTH-1:0] m1_apb_PWDATA,
    input  logic [STRB_WIDTH-1:0] m1_apb_PSTRB,
    input  logic [2:0]            m1_apb_PPROT,
    output logic [DATA_WIDTH-1:0] m1_apb_PRDATA,
    output logic                  m1_apb_PSLVERR,
    output logic                  m1_apb_PREADY,

    // Slave 0 APB interface (to external slave 0)
    output logic                  s0_apb_PSEL,
    output logic                  s0_apb_PENABLE,
    output logic [ADDR_WIDTH-1:0] s0_apb_PADDR,
    output logic                  s0_apb_PWRITE,
    output logic [DATA_WIDTH-1:0] s0_apb_PWDATA,
    output logic [STRB_WIDTH-1:0] s0_apb_PSTRB,
    output logic [2:0]            s0_apb_PPROT,
    input  logic [DATA_WIDTH-1:0] s0_apb_PRDATA,
    input  logic                  s0_apb_PSLVERR,
    input  logic                  s0_apb_PREADY,

    // Slave 1 APB interface (to external slave 1)
    output logic                  s1_apb_PSEL,
    output logic                  s1_apb_PENABLE,
    output logic [ADDR_WIDTH-1:0] s1_apb_PADDR,
    output logic                  s1_apb_PWRITE,
    output logic [DATA_WIDTH-1:0] s1_apb_PWDATA,
    output logic [STRB_WIDTH-1:0] s1_apb_PSTRB,
    output logic [2:0]            s1_apb_PPROT,
    input  logic [DATA_WIDTH-1:0] s1_apb_PRDATA,
    input  logic                  s1_apb_PSLVERR,
    input  logic                  s1_apb_PREADY,

    // Slave 2 APB interface (to external slave 2)
    output logic                  s2_apb_PSEL,
    output logic                  s2_apb_PENABLE,
    output logic [ADDR_WIDTH-1:0] s2_apb_PADDR,
    output logic                  s2_apb_PWRITE,
    output logic [DATA_WIDTH-1:0] s2_apb_PWDATA,
    output logic [STRB_WIDTH-1:0] s2_apb_PSTRB,
    output logic [2:0]            s2_apb_PPROT,
    input  logic [DATA_WIDTH-1:0] s2_apb_PRDATA,
    input  logic                  s2_apb_PSLVERR,
    input  logic                  s2_apb_PREADY,

    // Slave 3 APB interface (to external slave 3)
    output logic                  s3_apb_PSEL,
    output logic                  s3_apb_PENABLE,
    output logic [ADDR_WIDTH-1:0] s3_apb_PADDR,
    output logic                  s3_apb_PWRITE,
    output logic [DATA_WIDTH-1:0] s3_apb_PWDATA,
    output logic [STRB_WIDTH-1:0] s3_apb_PSTRB,
    output logic [2:0]            s3_apb_PPROT,
    input  logic [DATA_WIDTH-1:0] s3_apb_PRDATA,
    input  logic                  s3_apb_PSLVERR,
    input  logic                  s3_apb_PREADY
);

    // Command/Response interfaces for master 0 apb_slave
    logic                  m0_cmd_valid;
    logic                  m0_cmd_ready;
    logic                  m0_cmd_pwrite;
    logic [ADDR_WIDTH-1:0] m0_cmd_paddr;
    logic [DATA_WIDTH-1:0] m0_cmd_pwdata;
    logic [STRB_WIDTH-1:0] m0_cmd_pstrb;
    logic [2:0]            m0_cmd_pprot;
    logic                  m0_rsp_valid;
    logic                  m0_rsp_ready;
    logic [DATA_WIDTH-1:0] m0_rsp_prdata;
    logic                  m0_rsp_pslverr;

    // Command/Response interfaces for master 1 apb_slave
    logic                  m1_cmd_valid;
    logic                  m1_cmd_ready;
    logic                  m1_cmd_pwrite;
    logic [ADDR_WIDTH-1:0] m1_cmd_paddr;
    logic [DATA_WIDTH-1:0] m1_cmd_pwdata;
    logic [STRB_WIDTH-1:0] m1_cmd_pstrb;
    logic [2:0]            m1_cmd_pprot;
    logic                  m1_rsp_valid;
    logic                  m1_rsp_ready;
    logic [DATA_WIDTH-1:0] m1_rsp_prdata;
    logic                  m1_rsp_pslverr;

    // Command/Response interfaces for slave apb_masters
    logic                  s0_cmd_valid, s1_cmd_valid, s2_cmd_valid, s3_cmd_valid;
    logic                  s0_cmd_ready, s1_cmd_ready, s2_cmd_ready, s3_cmd_ready;
    logic                  s0_cmd_pwrite, s1_cmd_pwrite, s2_cmd_pwrite, s3_cmd_pwrite;
    logic [ADDR_WIDTH-1:0] s0_cmd_paddr, s1_cmd_paddr, s2_cmd_paddr, s3_cmd_paddr;
    logic [DATA_WIDTH-1:0] s0_cmd_pwdata, s1_cmd_pwdata, s2_cmd_pwdata, s3_cmd_pwdata;
    logic [STRB_WIDTH-1:0] s0_cmd_pstrb, s1_cmd_pstrb, s2_cmd_pstrb, s3_cmd_pstrb;
    logic [2:0]            s0_cmd_pprot, s1_cmd_pprot, s2_cmd_pprot, s3_cmd_pprot;
    logic                  s0_rsp_valid, s1_rsp_valid, s2_rsp_valid, s3_rsp_valid;
    logic                  s0_rsp_ready, s1_rsp_ready, s2_rsp_ready, s3_rsp_ready;
    logic [DATA_WIDTH-1:0] s0_rsp_prdata, s1_rsp_prdata, s2_rsp_prdata, s3_rsp_prdata;
    logic                  s0_rsp_pslverr, s1_rsp_pslverr, s2_rsp_pslverr, s3_rsp_pslverr;

    // APB Slave 0 - converts master 0 APB to cmd/rsp
    apb_slave #(
        .ADDR_WIDTH (ADDR_WIDTH),
        .DATA_WIDTH (DATA_WIDTH),
        .STRB_WIDTH (STRB_WIDTH),
        .PROT_WIDTH (3)
    ) u_apb_slave_m0 (
        .pclk           (pclk),
        .presetn        (presetn),
        .s_apb_PSEL     (m0_apb_PSEL),
        .s_apb_PENABLE  (m0_apb_PENABLE),
        .s_apb_PREADY   (m0_apb_PREADY),
        .s_apb_PADDR    (m0_apb_PADDR),
        .s_apb_PWRITE   (m0_apb_PWRITE),
        .s_apb_PWDATA   (m0_apb_PWDATA),
        .s_apb_PSTRB    (m0_apb_PSTRB),
        .s_apb_PPROT    (m0_apb_PPROT),
        .s_apb_PRDATA   (m0_apb_PRDATA),
        .s_apb_PSLVERR  (m0_apb_PSLVERR),
        .cmd_valid      (m0_cmd_valid),
        .cmd_ready      (m0_cmd_ready),
        .cmd_pwrite     (m0_cmd_pwrite),
        .cmd_paddr      (m0_cmd_paddr),
        .cmd_pwdata     (m0_cmd_pwdata),
        .cmd_pstrb      (m0_cmd_pstrb),
        .cmd_pprot      (m0_cmd_pprot),
        .rsp_valid      (m0_rsp_valid),
        .rsp_ready      (m0_rsp_ready),
        .rsp_prdata     (m0_rsp_prdata),
        .rsp_pslverr    (m0_rsp_pslverr)
    );

    // APB Slave 1 - converts master 1 APB to cmd/rsp
    apb_slave #(
        .ADDR_WIDTH (ADDR_WIDTH),
        .DATA_WIDTH (DATA_WIDTH),
        .STRB_WIDTH (STRB_WIDTH),
        .PROT_WIDTH (3)
    ) u_apb_slave_m1 (
        .pclk           (pclk),
        .presetn        (presetn),
        .s_apb_PSEL     (m1_apb_PSEL),
        .s_apb_PENABLE  (m1_apb_PENABLE),
        .s_apb_PREADY   (m1_apb_PREADY),
        .s_apb_PADDR    (m1_apb_PADDR),
        .s_apb_PWRITE   (m1_apb_PWRITE),
        .s_apb_PWDATA   (m1_apb_PWDATA),
        .s_apb_PSTRB    (m1_apb_PSTRB),
        .s_apb_PPROT    (m1_apb_PPROT),
        .s_apb_PRDATA   (m1_apb_PRDATA),
        .s_apb_PSLVERR  (m1_apb_PSLVERR),
        .cmd_valid      (m1_cmd_valid),
        .cmd_ready      (m1_cmd_ready),
        .cmd_pwrite     (m1_cmd_pwrite),
        .cmd_paddr      (m1_cmd_paddr),
        .cmd_pwdata     (m1_cmd_pwdata),
        .cmd_pstrb      (m1_cmd_pstrb),
        .cmd_pprot      (m1_cmd_pprot),
        .rsp_valid      (m1_rsp_valid),
        .rsp_ready      (m1_rsp_ready),
        .rsp_prdata     (m1_rsp_prdata),
        .rsp_pslverr    (m1_rsp_pslverr)
    );

    // Address decode for each master
    logic [1:0] m0_slave_sel;
    logic m0_addr_in_range;
    logic [1:0] r_m0_slave_sel;  // Registered for response routing
    logic [1:0] m1_slave_sel;
    logic m1_addr_in_range;
    logic [1:0] r_m1_slave_sel;  // Registered for response routing

    always_comb begin
        m0_addr_in_range = (m0_cmd_paddr >= BASE_ADDR) &&
                          (m0_cmd_paddr < (BASE_ADDR + 32'h00040000));
        m0_slave_sel = m0_cmd_paddr[17:16];

        m1_addr_in_range = (m1_cmd_paddr >= BASE_ADDR) &&
                          (m1_cmd_paddr < (BASE_ADDR + 32'h00040000));
        m1_slave_sel = m1_cmd_paddr[17:16];

    end

    // Register slave selection for each master when command accepted
    always_ff @(posedge pclk or negedge presetn) begin
        if (!presetn) begin
            r_m0_slave_sel <= 2'd0;
            r_m1_slave_sel <= 2'd0;
        end else begin
            if (m0_cmd_valid && m0_cmd_ready) begin
                r_m0_slave_sel <= m0_slave_sel;
            end
            if (m1_cmd_valid && m1_cmd_ready) begin
                r_m1_slave_sel <= m1_slave_sel;
            end
        end
    end

    // Arbitration and command routing for each slave
    // Each slave has independent round-robin arbitration between the masters
    // Uses proven arbiter_round_robin module from rtl/common/

    // Slave 0 arbitration signals
    logic [1:0] s0_arb_request;
    logic [1:0] s0_arb_grant;
    logic [1:0] s0_arb_grant_ack;

    // Build request vector for slave 0
    always_comb begin
        s0_arb_request[0] = m0_cmd_valid && m0_addr_in_range && m0_slave_sel == 2'd0;
        s0_arb_request[1] = m1_cmd_valid && m1_addr_in_range && m1_slave_sel == 2'd0;
    end

    // Build grant_ack vector for slave 0 (transaction complete)
    always_comb begin
        s0_arb_grant_ack[0] = s0_arb_grant[0] && s0_rsp_valid && s0_rsp_ready;
        s0_arb_grant_ack[1] = s0_arb_grant[1] && s0_rsp_valid && s0_rsp_ready;
    end

    // Round-robin arbiter for slave 0
    arbiter_round_robin #(
        .CLIENTS(2),
        .WAIT_GNT_ACK(1)  // Lock grant until transaction completes
    ) u_s0_arbiter (
        .clk        (pclk),
        .rst_n      (presetn),
        .block_arb  (1'b0),
        .request    (s0_arb_request),
        .grant_ack  (s0_arb_grant_ack),
        .grant_valid(),  // Not used
        .grant      (s0_arb_grant),
        .grant_id   (),  // Not used
        .last_grant ()   // Not used
    );

    // Command routing to slave 0
    always_comb begin
        s0_cmd_valid = 1'b0;
        s0_cmd_pwrite = 1'b0;
        s0_cmd_paddr = '0;
        s0_cmd_pwdata = '0;
        s0_cmd_pstrb = '0;
        s0_cmd_pprot = '0;
        case (1'b1)
            s0_arb_grant[0]: begin
                s0_cmd_valid = m0_cmd_valid && m0_addr_in_range && (m0_slave_sel == 2'd0);
                s0_cmd_pwrite = m0_cmd_pwrite;
                s0_cmd_paddr = m0_cmd_paddr;
                s0_cmd_pwdata = m0_cmd_pwdata;
                s0_cmd_pstrb = m0_cmd_pstrb;
                s0_cmd_pprot = m0_cmd_pprot;
            end
            s0_arb_grant[1]: begin
                s0_cmd_valid = m1_cmd_valid && m1_addr_in_range && (m1_slave_sel == 2'd0);
                s0_cmd_pwrite = m1_cmd_pwrite;
                s0_cmd_paddr = m1_cmd_paddr;
                s0_cmd_pwdata = m1_cmd_pwdata;
                s0_cmd_pstrb = m1_cmd_pstrb;
                s0_cmd_pprot = m1_cmd_pprot;
            end
        endcase
    end

    // Slave 1 arbitration signals
    logic [1:0] s1_arb_request;
    logic [1:0] s1_arb_grant;
    logic [1:0] s1_arb_grant_ack;

    // Build request vector for slave 1
    always_comb begin
        s1_arb_request[0] = m0_cmd_valid && m0_addr_in_range && m0_slave_sel == 2'd1;
        s1_arb_request[1] = m1_cmd_valid && m1_addr_in_range && m1_slave_sel == 2'd1;
    end

    // Build grant_ack vector for slave 1 (transaction complete)
    always_comb begin
        s1_arb_grant_ack[0] = s1_arb_grant[0] && s1_rsp_valid && s1_rsp_ready;
        s1_arb_grant_ack[1] = s1_arb_grant[1] && s1_rsp_valid && s1_rsp_ready;
    end

    // Round-robin arbiter for slave 1
    arbiter_round_robin #(
        .CLIENTS(2),
        .WAIT_GNT_ACK(1)  // Lock grant until transaction completes
    ) u_s1_arbiter (
        .clk        (pclk),
        .rst_n      (presetn),
        .block_arb  (1'b0),
        .request    (s1_arb_request),
        .grant_ack  (s1_arb_grant_ack),
        .grant_valid(),  // Not used
        .grant      (s1_arb_grant),
        .grant_id   (),  // Not used
        .last_grant ()   // Not used
    );

    // Command routing to slave 1
    always_comb begin
        s1_cmd_valid = 1'b0;
        s1_cmd_pwrite = 1'b0;
        s1_cmd_paddr = '0;
        s1_cmd_pwdata = '0;
        s1_cmd_pstrb = '0;
        s1_cmd_pprot = '0;
        case (1'b1)
            s1_arb_grant[0]: begin
                s1_cmd_valid = m0_cmd_valid && m0_addr_in_range && (m0_slave_sel == 2'd1);
                s1_cmd_pwrite = m0_cmd_pwrite;
                s1_cmd_paddr = m0_cmd_paddr;
                s1_cmd_pwdata = m0_cmd_pwdata;
                s1_cmd_pstrb = m0_cmd_pstrb;
                s1_cmd_pprot = m0_cmd_pprot;
            end
            s1_arb_grant[1]: begin
                s1_cmd_valid = m1_cmd_valid && m1_addr_in_range && (m1_slave_sel == 2'd1);
                s1_cmd_pwrite = m1_cmd_pwrite;
                s1_cmd_paddr = m1_cmd_paddr;
                s1_cmd_pwdata = m1_cmd_pwdata;
                s1_cmd_pstrb = m1_cmd_pstrb;
                s1_cmd_pprot = m1_cmd_pprot;
            end
        endcase
    end

    // Slave 2 arbitration signals
    logic [1:0] s2_arb_request;
    logic [1:0] s2_arb_grant;
    logic [1:0] s2_arb_grant_ack;

    // Build request vector for slave 2
    always_comb begin
        s2_arb_request[0] = m0_cmd_valid && m0_addr_in_range && m0_slave_sel == 2'd2;
        s2_arb_request[1] = m1_cmd_valid && m1_addr_in_range && m1_slave_sel == 2'd2;
    end

    // Build grant_ack vector for slave 2 (transaction complete)
    always_comb begin
        s2_arb_grant_ack[0] = s2_arb_grant[0] && s2_rsp_valid && s2_rsp_ready;
        s2_arb_grant_ack[1] = s2_arb_grant[1] && s2_rsp_valid && s2_rsp_ready;
    end

    // Round-robin arbiter for slave 2
    arbiter_round_robin #(
        .CLIENTS(2),
        .WAIT_GNT_ACK(1)  // Lock grant until transaction completes
    ) u_s2_arbiter (
        .clk        (pclk),
        .rst_n      (presetn),
        .block_arb  (1'b0),
        .request    (s2_arb_request),
        .grant_ack  (s2_arb_grant_ack),
        .grant_valid(),  // Not used
        .grant      (s2_arb_grant),
        .grant_id   (),  // Not used
        .last_grant ()   // Not used
    );

    // Command routing to slave 2
    always_comb begin
        s2_cmd_valid = 1'b0;
        s2_cmd_pwrite = 1'b0;
        s2_cmd_paddr = '0;
        s2_cmd_pwdata = '0;
        s2_cmd_pstrb = '0;
        s2_cmd_pprot = '0;
        case (1'b1)
            s2_arb_grant[0]: begin
                s2_cmd_valid = m0_cmd_valid && m0_addr_in_range && (m0_slave_sel == 2'd2);
                s2_cmd_pwrite = m0_cmd_pwrite;
                s2_cmd_paddr = m0_cmd_paddr;
                s2_cmd_pwdata = m0_cmd_pwdata;
                s2_cmd_pstrb = m0_cmd_pstrb;
                s2_cmd_pprot = m0_cmd_pprot;
            end
            s2_arb_grant[1]: begin
                s2_cmd_valid = m1_cmd_valid && m1_addr_in_range && (m1_slave_sel == 2'd2);
                s2_cmd_pwrite = m1_cmd_pwrite;
                s2_cmd_paddr = m1_cmd_paddr;
                s2_cmd_pwdata = m1_cmd_pwdata;
                s2_cmd_pstrb = m1_cmd_pstrb;
                s2_cmd_pprot = m1_cmd_pprot;
            end
        endcase
    end

    // Slave 3 arbitration signals
    logic [1:0] s3_arb_request;
    logic [1:0] s3_arb_grant;
    logic [1:0] s3_arb_grant_ack;

    // Build request vector for slave 3
    always_comb begin
        s3_arb_request[0] = m0_cmd_valid && m0_addr_in_range && m0_slave_sel == 2'd3;
        s3_arb_request[1] = m1_cmd_valid && m1_addr_in_range && m1_slave_sel == 2'd3;
    end

    // Build grant_ack vector for slave 3 (transaction complete)
    always_comb begin
        s3_arb_grant_ack[0] = s3_arb_grant[0] && s3_rsp_valid && s3_rsp_ready;
        s3_arb_grant_ack[1] = s3_arb_grant[1] && s3_rsp_valid && s3_rsp_ready;
    end

    // Round-robin arbiter for slave 3
    arbiter_round_robin #(
        .CLIENTS(2),
        .WAIT_GNT_ACK(1)  // Lock grant until transaction completes
    ) u_s3_arbiter (
        .clk        (pclk),
        .rst_n      (presetn),
        .block_arb  (1'b0),
        .request    (s3_arb_request),
        .grant_ack  (s3_arb_grant_ack),
        .grant_valid(),  // Not used
        .grant      (s3_arb_grant),
        .grant_id   (),  // Not used
        .last_grant ()   // Not used
    );

    // Command routing to slave 3
    always_comb begin
        s3_cmd_valid = 1'b0;
        s3_cmd_pwrite = 1'b0;
        s3_cmd_paddr = '0;
        s3_cmd_pwdata = '0;
        s3_cmd_pstrb = '0;
        s3_cmd_pprot = '0;
        case (1'b1)
            s3_arb_grant[0]: begin
                s3_cmd_valid = m0_cmd_valid && m0_addr_in_range && (m0_slave_sel == 2'd3);
                s3_cmd_pwrite = m0_cmd_pwrite;
                s3_cmd_paddr = m0_cmd_paddr;
                s3_cmd_pwdata = m0_cmd_pwdata;
                s3_cmd_pstrb = m0_cmd_pstrb;
                s3_cmd_pprot = m0_cmd_pprot;
            end
            s3_arb_grant[1]: begin
                s3_cmd_valid = m1_cmd_valid && m1_addr_in_range && (m1_slave_sel == 2'd3);
                s3_cmd_pwrite = m1_cmd_pwrite;
                s3_cmd_paddr = m1_cmd_paddr;
                s3_cmd_pwdata = m1_cmd_pwdata;
                s3_cmd_pstrb = m1_cmd_pstrb;
                s3_cmd_pprot = m1_cmd_pprot;
            end
        endcase
    end

    // Master cmd_ready signals
    always_comb begin
        m0_cmd_ready = 1'b0;
        if (m0_cmd_valid && m0_addr_in_range) begin
            case (m0_slave_sel)
                2'd0: m0_cmd_ready = s0_arb_grant[0] && s0_cmd_ready;
                2'd1: m0_cmd_ready = s1_arb_grant[0] && s1_cmd_ready;
                2'd2: m0_cmd_ready = s2_arb_grant[0] && s2_cmd_ready;
                2'd3: m0_cmd_ready = s3_arb_grant[0] && s3_cmd_ready;
            endcase
        end
    end

    always_comb begin
        m1_cmd_ready = 1'b0;
        if (m1_cmd_valid && m1_addr_in_range) begin
            case (m1_slave_sel)
                2'd0: m1_cmd_ready = s0_arb_grant[1] && s0_cmd_ready;
                2'd1: m1_cmd_ready = s1_arb_grant[1] && s1_cmd_ready;
                2'd2: m1_cmd_ready = s2_arb_grant[1] && s2_cmd_ready;
                2'd3: m1_cmd_ready = s3_arb_grant[1] && s3_cmd_ready;
            endcase
        end
    end

    // Response routing from slaves to masters
    always_comb begin
        m0_rsp_valid = 1'b0;
        m0_rsp_prdata = '0;
        m0_rsp_pslverr = 1'b0;
        case (r_m0_slave_sel)
            2'd0: begin
                if (s0_arb_grant[0]) begin
                    m0_rsp_valid = s0_rsp_valid;
                    m0_rsp_prdata = s0_rsp_prdata;
                    m0_rsp_pslverr = s0_rsp_pslverr;
                end
            end
            2'd1: begin
                if (s1_arb_grant[0]) begin
                    m0_rsp_valid = s1_rsp_valid;
                    m0_rsp_prdata = s1_rsp_prdata;
                    m0_rsp_pslverr = s1_rsp_pslverr;
                end
            end
            2'd2: begin
                if (s2_arb_grant[0]) begin
                    m0_rsp_valid = s2_rsp_valid;
                    m0_rsp_prdata = s2_rsp_prdata;
                    m0_rsp_pslverr = s2_rsp_pslverr;
                end
            end
            2'd3: begin
                if (s3_arb_grant[0]) begin
                    m0_rsp_valid = s3_rsp_valid;
                    m0_rsp_prdata = s3_rsp_prdata;
                    m0_rsp_pslverr = s3_rsp_pslverr;
                end
            end
        endcase
    end

    always_comb begin
        m1_rsp_valid = 1'b0;
        m1_rsp_prdata = '0;
        m1_rsp_pslverr = 1'b0;
        case (r_m1_slave_sel)
            2'd0: begin
                if (s0_arb_grant[1]) begin
                    m1_rsp_valid = s0_rsp_valid;
                    m1_rsp_prdata = s0_rsp_prdata;
                    m1_rsp_pslverr = s0_rsp_pslverr;
                end
            end
            2'd1: begin
                if (s1_arb_grant[1]) begin
                    m1_rsp_valid = s1_rsp_valid;
                    m1_rsp_prdata = s1_rsp_prdata;
                    m1_rsp_pslverr = s1_rsp_pslverr;
                end
            end
            2'd2: begin
                if (s2_arb_grant[1]) begin
                    m1_rsp_valid = s2_rsp_valid;
                    m1_rsp_prdata = s2_rsp_prdata;
                    m1_rsp_pslverr = s2_rsp_pslverr;
                end
            end
            2'd3: begin
                if (s3_arb_grant[1]) begin
                    m1_rsp_valid = s3_rsp_valid;
                    m1_rsp_prdata = s3_rsp_prdata;
                    m1_rsp_pslverr = s3_rsp_pslverr;
                end
            end
        endcase
    end

    // Slave 0 rsp_ready
    always_comb begin
        s0_rsp_ready = 1'b0;
        if (s0_arb_grant[0] && r_m0_slave_sel == 2'd0) s0_rsp_ready = m0_rsp_ready;
        if (s0_arb_grant[1] && r_m1_slave_sel == 2'd0) s0_rsp_ready = m1_rsp_ready;
    end

    // Slave 1 rsp_ready
    always_comb begin
        s1_rsp_ready = 1'b0;
        if (s1_arb_grant[0] && r_m0_slave_sel == 2'd1) s1_rsp_ready = m0_rsp_ready;
        if (s1_arb_grant[1] && r_m1_slave_sel == 2'd1) s1_rsp_ready = m1_rsp_ready;
    end

    // Slave 2 rsp_ready
    always_comb begin
        s2_rsp_ready = 1'b0;
        if (s2_arb_grant[0] && r_m0_slave_sel == 2'd2) s2_rsp_ready = m0_rsp_ready;
        if (s2_arb_grant[1] && r_m1_slave_sel == 2'd2) s2_rsp_ready = m1_rsp_ready;
    end

    // Slave 3 rsp_ready
    always_comb begin
        s3_rsp_ready = 1'b0;
        if (s3_arb_grant[0] && r_m0_slave_sel == 2'd3) s3_rsp_ready = m0_rsp_ready;
        if (s3_arb_grant[1] && r_m1_slave_sel == 2'd3) s3_rsp_ready = m1_rsp_ready;
    end

    // APB Master 0 - converts cmd/rsp to slave 0 APB
    apb_master #(
        .ADDR_WIDTH (ADDR_WIDTH),
        .DATA_WIDTH (DATA_WIDTH),
        .STRB_WIDTH (STRB_WIDTH),
        .PROT_WIDTH (3)
    ) u_apb_master_s0 (
        .pclk           (pclk),
        .presetn        (presetn),
        .m_apb_PSEL     (s0_apb_PSEL),
        .m_apb_PENABLE  (s0_apb_PENABLE),
        .m_apb_PREADY   (s0_apb_PREADY),
        .m_apb_PADDR    (s0_apb_PADDR),
        .m_apb_PWRITE   (s0_apb_PWRITE),
        .m_apb_PWDATA   (s0_apb_PWDATA),
        .m_apb_PSTRB    (s0_apb_PSTRB),
        .m_apb_PPROT    (s0_apb_PPROT),
        .m_apb_PRDATA   (s0_apb_PRDATA),
        .m_apb_PSLVERR  (s0_apb_PSLVERR),
        .cmd_valid      (s0_cmd_valid),
        .cmd_ready      (s0_cmd_ready),
        .cmd_pwrite     (s0_cmd_pwrite),
        .cmd_paddr      (s0_cmd_paddr),
        .cmd_pwdata     (s0_cmd_pwdata),
        .cmd_pstrb      (s0_cmd_pstrb),
        .cmd_pprot      (s0_cmd_pprot),
        .rsp_valid      (s0_rsp_valid),
        .rsp_ready      (s0_rsp_ready),
        .rsp_prdata     (s0_rsp_prdata),
        .rsp_pslverr    (s0_rsp_pslverr)
    );

    // APB Master 1 - converts cmd/rsp to slave 1 APB
    apb_master #(
        .ADDR_WIDTH (ADDR_WIDTH),
        .DATA_WIDTH (DATA_WIDTH),
        .STRB_WIDTH (STRB_WIDTH),
        .PROT_WIDTH (3)
    ) u_apb_master_s1 (
        .pclk           (pclk),
        .presetn        (presetn),
        .m_apb_PSEL     (s1_apb_PSEL),
        .m_apb_PENABLE  (s1_apb_PENABLE),
        .m_apb_PREADY   (s1_apb_PREADY),
        .m_apb_PADDR    (s1_apb_PADDR),
        .m_apb_PWRITE   (s1_apb_PWRITE),
        .m_apb_PWDATA   (s1_apb_PWDATA),
        .m_apb_PSTRB    (s1_apb_PSTRB),
        .m_apb_PPROT    (s1_apb_PPROT),
        .m_apb_PRDATA   (s1_apb_PRDATA),
        .m_apb_PSLVERR  (s1_apb_PSLVERR),
        .cmd_valid      (s1_cmd_valid),
        .cmd_ready      (s1_cmd_ready),
        .cmd_pwrite     (s1_cmd_pwrite),
        .cmd_paddr      (s1_cmd_paddr),
        .cmd_pwdata     (s1_cmd_pwdata),
        .cmd_pstrb      (s1_cmd_pstrb),
        .cmd_pprot      (s1_cmd_pprot),
        .rsp_valid      (s1_rsp_valid),
        .rsp_ready      (s1_rsp_ready),
        .rsp_prdata     (s1_rsp_prdata),
        .rsp_pslverr    (s1_rsp_pslverr)
    );

    // APB Master 2 - converts cmd/rsp to slave 2 APB
    apb_master #(
        .ADDR_WIDTH (ADDR_WIDTH),
        .DATA_WIDTH (DATA_WIDTH),
        .STRB_WIDTH (STRB_WIDTH),
        .PROT_WIDTH (3)
    ) u_apb_master_s2 (
        .pclk           (pclk),
        .presetn        (presetn),
        .m_apb_PSEL     (s2_apb_PSEL),
        .m_apb_PENABLE  (s2_apb_PENABLE),
        .m_apb_PREADY   (s2_apb_PREADY),
        .m_apb_PADDR    (s2_apb_PADDR),
        .m_apb_PWRITE   (s2_apb_PWRITE),
        .m_apb_PWDATA   (s2_apb_PWDATA),
        .m_apb_PSTRB    (s2_apb_PSTRB),
        .m_apb_PPROT    (s2_apb_PPROT),
        .m_apb_PRDATA   (s2_apb_PRDATA),
        .m_apb_PSLVERR  (s2_apb_PSLVERR),
        .cmd_valid      (s2_cmd_valid),
        .cmd_ready      (s2_cmd_ready),
        .cmd_pwrite     (s2_cmd_pwrite),
        .cmd_paddr      (s2_cmd_paddr),
        .cmd_pwdata     (s2_cmd_pwdata),
        .cmd_pstrb      (s2_cmd_pstrb),
        .cmd_pprot      (s2_cmd_pprot),
        .rsp_valid      (s2_rsp_valid),
        .rsp_ready      (s2_rsp_ready),
        .rsp_prdata     (s2_rsp_prdata),
        .rsp_pslverr    (s2_rsp_pslverr)
    );

    // APB Master 3 - converts cmd/rsp to slave 3 APB
    apb_master #(
        .ADDR_WIDTH (ADDR_WIDTH),
        .DATA_WIDTH (DATA_WIDTH),
        .STRB_WIDTH (STRB_WIDTH),
        .PROT_WIDTH (3)
    ) u_apb_master_s3 (
        .pclk           (pclk),
        .presetn        (presetn),
        .m_apb_PSEL     (s3_apb_PSEL),
        .m_apb_PENABLE  (s3_apb_PENABLE),
        .m_apb_PREADY   (s3_apb_PREADY),
        .m_apb_PADDR    (s3_apb_PADDR),
        .m_apb_PWRITE   (s3_apb_PWRITE),
        .m_apb_PWDATA   (s3_apb_PWDATA),
        .m_apb_PSTRB    (s3_apb_PSTRB),
        .m_apb_PPROT    (s3_apb_PPROT),
        .m_apb_PRDATA   (s3_apb_PRDATA),
        .m_apb_PSLVERR  (s3_apb_PSLVERR),
        .cmd_valid      (s3_cmd_valid),
        .cmd_ready      (s3_cmd_ready),
        .cmd_pwrite     (s3_cmd_pwrite),
        .cmd_paddr      (s3_cmd_paddr),
        .cmd_pwdata     (s3_cmd_pwdata),
        .cmd_pstrb      (s3_cmd_pstrb),
        .cmd_pprot      (s3_cmd_pprot),
        .rsp_valid      (s3_rsp_valid),
        .rsp_ready      (s3_rsp_ready),
        .rsp_prdata     (s3_rsp_prdata),
        .rsp_pslverr    (s3_rsp_pslverr)
    );

endmodule : apb_xbar_2to4
