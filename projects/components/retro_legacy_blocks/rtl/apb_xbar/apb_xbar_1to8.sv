`timescale 1ns / 1ps

// 1-to-8 APB crossbar with address decoding and arbitration
// 1 master to 8 slaves using apb_slave and apb_master modules
//
// Address Map (same for all masters):
//   Slave 0: [0xFEC00000, 0xFEC00FFF] (4KB)
//   Slave 1: [0xFEC01000, 0xFEC01FFF] (4KB)
//   Slave 2: [0xFEC02000, 0xFEC02FFF] (4KB)
//   Slave 3: [0xFEC03000, 0xFEC03FFF] (4KB)
//   Slave 4: [0xFEC04000, 0xFEC04FFF] (4KB)
//   Slave 5: [0xFEC05000, 0xFEC05FFF] (4KB)
//   Slave 6: [0xFEC06000, 0xFEC06FFF] (4KB)
//   Slave 7: [0xFEC07000, 0xFEC07FFF] (4KB)

module apb_xbar_1to8 #(
    parameter int ADDR_WIDTH = 32,
    parameter int DATA_WIDTH = 32,
    parameter int STRB_WIDTH = DATA_WIDTH / 8,
    parameter logic [ADDR_WIDTH-1:0] BASE_ADDR = 32'hFEC00000
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
    input  logic                  s3_apb_PREADY,

    // Slave 4 APB interface (to external slave 4)
    output logic                  s4_apb_PSEL,
    output logic                  s4_apb_PENABLE,
    output logic [ADDR_WIDTH-1:0] s4_apb_PADDR,
    output logic                  s4_apb_PWRITE,
    output logic [DATA_WIDTH-1:0] s4_apb_PWDATA,
    output logic [STRB_WIDTH-1:0] s4_apb_PSTRB,
    output logic [2:0]            s4_apb_PPROT,
    input  logic [DATA_WIDTH-1:0] s4_apb_PRDATA,
    input  logic                  s4_apb_PSLVERR,
    input  logic                  s4_apb_PREADY,

    // Slave 5 APB interface (to external slave 5)
    output logic                  s5_apb_PSEL,
    output logic                  s5_apb_PENABLE,
    output logic [ADDR_WIDTH-1:0] s5_apb_PADDR,
    output logic                  s5_apb_PWRITE,
    output logic [DATA_WIDTH-1:0] s5_apb_PWDATA,
    output logic [STRB_WIDTH-1:0] s5_apb_PSTRB,
    output logic [2:0]            s5_apb_PPROT,
    input  logic [DATA_WIDTH-1:0] s5_apb_PRDATA,
    input  logic                  s5_apb_PSLVERR,
    input  logic                  s5_apb_PREADY,

    // Slave 6 APB interface (to external slave 6)
    output logic                  s6_apb_PSEL,
    output logic                  s6_apb_PENABLE,
    output logic [ADDR_WIDTH-1:0] s6_apb_PADDR,
    output logic                  s6_apb_PWRITE,
    output logic [DATA_WIDTH-1:0] s6_apb_PWDATA,
    output logic [STRB_WIDTH-1:0] s6_apb_PSTRB,
    output logic [2:0]            s6_apb_PPROT,
    input  logic [DATA_WIDTH-1:0] s6_apb_PRDATA,
    input  logic                  s6_apb_PSLVERR,
    input  logic                  s6_apb_PREADY,

    // Slave 7 APB interface (to external slave 7)
    output logic                  s7_apb_PSEL,
    output logic                  s7_apb_PENABLE,
    output logic [ADDR_WIDTH-1:0] s7_apb_PADDR,
    output logic                  s7_apb_PWRITE,
    output logic [DATA_WIDTH-1:0] s7_apb_PWDATA,
    output logic [STRB_WIDTH-1:0] s7_apb_PSTRB,
    output logic [2:0]            s7_apb_PPROT,
    input  logic [DATA_WIDTH-1:0] s7_apb_PRDATA,
    input  logic                  s7_apb_PSLVERR,
    input  logic                  s7_apb_PREADY
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

    // Command/Response interfaces for slave apb_masters
    logic                  s0_cmd_valid, s1_cmd_valid, s2_cmd_valid, s3_cmd_valid, s4_cmd_valid, s5_cmd_valid, s6_cmd_valid, s7_cmd_valid;
    logic                  s0_cmd_ready, s1_cmd_ready, s2_cmd_ready, s3_cmd_ready, s4_cmd_ready, s5_cmd_ready, s6_cmd_ready, s7_cmd_ready;
    logic                  s0_cmd_pwrite, s1_cmd_pwrite, s2_cmd_pwrite, s3_cmd_pwrite, s4_cmd_pwrite, s5_cmd_pwrite, s6_cmd_pwrite, s7_cmd_pwrite;
    logic [ADDR_WIDTH-1:0] s0_cmd_paddr, s1_cmd_paddr, s2_cmd_paddr, s3_cmd_paddr, s4_cmd_paddr, s5_cmd_paddr, s6_cmd_paddr, s7_cmd_paddr;
    logic [DATA_WIDTH-1:0] s0_cmd_pwdata, s1_cmd_pwdata, s2_cmd_pwdata, s3_cmd_pwdata, s4_cmd_pwdata, s5_cmd_pwdata, s6_cmd_pwdata, s7_cmd_pwdata;
    logic [STRB_WIDTH-1:0] s0_cmd_pstrb, s1_cmd_pstrb, s2_cmd_pstrb, s3_cmd_pstrb, s4_cmd_pstrb, s5_cmd_pstrb, s6_cmd_pstrb, s7_cmd_pstrb;
    logic [2:0]            s0_cmd_pprot, s1_cmd_pprot, s2_cmd_pprot, s3_cmd_pprot, s4_cmd_pprot, s5_cmd_pprot, s6_cmd_pprot, s7_cmd_pprot;
    logic                  s0_rsp_valid, s1_rsp_valid, s2_rsp_valid, s3_rsp_valid, s4_rsp_valid, s5_rsp_valid, s6_rsp_valid, s7_rsp_valid;
    logic                  s0_rsp_ready, s1_rsp_ready, s2_rsp_ready, s3_rsp_ready, s4_rsp_ready, s5_rsp_ready, s6_rsp_ready, s7_rsp_ready;
    logic [DATA_WIDTH-1:0] s0_rsp_prdata, s1_rsp_prdata, s2_rsp_prdata, s3_rsp_prdata, s4_rsp_prdata, s5_rsp_prdata, s6_rsp_prdata, s7_rsp_prdata;
    logic                  s0_rsp_pslverr, s1_rsp_pslverr, s2_rsp_pslverr, s3_rsp_pslverr, s4_rsp_pslverr, s5_rsp_pslverr, s6_rsp_pslverr, s7_rsp_pslverr;

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

    // Address decode for each master
    logic [2:0] m0_slave_sel;
    logic m0_addr_in_range;
    logic [2:0] r_m0_slave_sel;  // Registered for response routing

    always_comb begin
        m0_addr_in_range = (m0_cmd_paddr >= BASE_ADDR) &&
                          (m0_cmd_paddr < (BASE_ADDR + 32'h00008000));
        m0_slave_sel = m0_cmd_paddr[14:12];

    end

    // Register slave selection for each master when command accepted
    always_ff @(posedge pclk or negedge presetn) begin
        if (!presetn) begin
            r_m0_slave_sel <= 3'd0;
        end else begin
            if (m0_cmd_valid && m0_cmd_ready) begin
                r_m0_slave_sel <= m0_slave_sel;
            end
        end
    end

    // Single master - command routing based on address decode
    assign s0_cmd_valid = m0_cmd_valid && m0_addr_in_range && (m0_slave_sel == 3'd0);
    assign s0_cmd_pwrite = m0_cmd_pwrite;
    assign s0_cmd_paddr = m0_cmd_paddr;
    assign s0_cmd_pwdata = m0_cmd_pwdata;
    assign s0_cmd_pstrb = m0_cmd_pstrb;
    assign s0_cmd_pprot = m0_cmd_pprot;

    assign s1_cmd_valid = m0_cmd_valid && m0_addr_in_range && (m0_slave_sel == 3'd1);
    assign s1_cmd_pwrite = m0_cmd_pwrite;
    assign s1_cmd_paddr = m0_cmd_paddr;
    assign s1_cmd_pwdata = m0_cmd_pwdata;
    assign s1_cmd_pstrb = m0_cmd_pstrb;
    assign s1_cmd_pprot = m0_cmd_pprot;

    assign s2_cmd_valid = m0_cmd_valid && m0_addr_in_range && (m0_slave_sel == 3'd2);
    assign s2_cmd_pwrite = m0_cmd_pwrite;
    assign s2_cmd_paddr = m0_cmd_paddr;
    assign s2_cmd_pwdata = m0_cmd_pwdata;
    assign s2_cmd_pstrb = m0_cmd_pstrb;
    assign s2_cmd_pprot = m0_cmd_pprot;

    assign s3_cmd_valid = m0_cmd_valid && m0_addr_in_range && (m0_slave_sel == 3'd3);
    assign s3_cmd_pwrite = m0_cmd_pwrite;
    assign s3_cmd_paddr = m0_cmd_paddr;
    assign s3_cmd_pwdata = m0_cmd_pwdata;
    assign s3_cmd_pstrb = m0_cmd_pstrb;
    assign s3_cmd_pprot = m0_cmd_pprot;

    assign s4_cmd_valid = m0_cmd_valid && m0_addr_in_range && (m0_slave_sel == 3'd4);
    assign s4_cmd_pwrite = m0_cmd_pwrite;
    assign s4_cmd_paddr = m0_cmd_paddr;
    assign s4_cmd_pwdata = m0_cmd_pwdata;
    assign s4_cmd_pstrb = m0_cmd_pstrb;
    assign s4_cmd_pprot = m0_cmd_pprot;

    assign s5_cmd_valid = m0_cmd_valid && m0_addr_in_range && (m0_slave_sel == 3'd5);
    assign s5_cmd_pwrite = m0_cmd_pwrite;
    assign s5_cmd_paddr = m0_cmd_paddr;
    assign s5_cmd_pwdata = m0_cmd_pwdata;
    assign s5_cmd_pstrb = m0_cmd_pstrb;
    assign s5_cmd_pprot = m0_cmd_pprot;

    assign s6_cmd_valid = m0_cmd_valid && m0_addr_in_range && (m0_slave_sel == 3'd6);
    assign s6_cmd_pwrite = m0_cmd_pwrite;
    assign s6_cmd_paddr = m0_cmd_paddr;
    assign s6_cmd_pwdata = m0_cmd_pwdata;
    assign s6_cmd_pstrb = m0_cmd_pstrb;
    assign s6_cmd_pprot = m0_cmd_pprot;

    assign s7_cmd_valid = m0_cmd_valid && m0_addr_in_range && (m0_slave_sel == 3'd7);
    assign s7_cmd_pwrite = m0_cmd_pwrite;
    assign s7_cmd_paddr = m0_cmd_paddr;
    assign s7_cmd_pwdata = m0_cmd_pwdata;
    assign s7_cmd_pstrb = m0_cmd_pstrb;
    assign s7_cmd_pprot = m0_cmd_pprot;

    // Master ready when selected slave is ready
    always_comb begin
        m0_cmd_ready = 1'b0;
        if (m0_cmd_valid && m0_addr_in_range) begin
            case (m0_slave_sel)
                3'd0: m0_cmd_ready = s0_cmd_ready;
                3'd1: m0_cmd_ready = s1_cmd_ready;
                3'd2: m0_cmd_ready = s2_cmd_ready;
                3'd3: m0_cmd_ready = s3_cmd_ready;
                3'd4: m0_cmd_ready = s4_cmd_ready;
                3'd5: m0_cmd_ready = s5_cmd_ready;
                3'd6: m0_cmd_ready = s6_cmd_ready;
                3'd7: m0_cmd_ready = s7_cmd_ready;
            endcase
        end
    end

    // Response routing based on registered slave selection
    always_comb begin
        m0_rsp_valid = 1'b0;
        m0_rsp_prdata = '0;
        m0_rsp_pslverr = 1'b0;
        case (r_m0_slave_sel)
            3'd0: begin
                m0_rsp_valid = s0_rsp_valid;
                m0_rsp_prdata = s0_rsp_prdata;
                m0_rsp_pslverr = s0_rsp_pslverr;
            end
            3'd1: begin
                m0_rsp_valid = s1_rsp_valid;
                m0_rsp_prdata = s1_rsp_prdata;
                m0_rsp_pslverr = s1_rsp_pslverr;
            end
            3'd2: begin
                m0_rsp_valid = s2_rsp_valid;
                m0_rsp_prdata = s2_rsp_prdata;
                m0_rsp_pslverr = s2_rsp_pslverr;
            end
            3'd3: begin
                m0_rsp_valid = s3_rsp_valid;
                m0_rsp_prdata = s3_rsp_prdata;
                m0_rsp_pslverr = s3_rsp_pslverr;
            end
            3'd4: begin
                m0_rsp_valid = s4_rsp_valid;
                m0_rsp_prdata = s4_rsp_prdata;
                m0_rsp_pslverr = s4_rsp_pslverr;
            end
            3'd5: begin
                m0_rsp_valid = s5_rsp_valid;
                m0_rsp_prdata = s5_rsp_prdata;
                m0_rsp_pslverr = s5_rsp_pslverr;
            end
            3'd6: begin
                m0_rsp_valid = s6_rsp_valid;
                m0_rsp_prdata = s6_rsp_prdata;
                m0_rsp_pslverr = s6_rsp_pslverr;
            end
            3'd7: begin
                m0_rsp_valid = s7_rsp_valid;
                m0_rsp_prdata = s7_rsp_prdata;
                m0_rsp_pslverr = s7_rsp_pslverr;
            end
        endcase
    end

    assign s0_rsp_ready = (r_m0_slave_sel == 3'd0) ? m0_rsp_ready : 1'b0;
    assign s1_rsp_ready = (r_m0_slave_sel == 3'd1) ? m0_rsp_ready : 1'b0;
    assign s2_rsp_ready = (r_m0_slave_sel == 3'd2) ? m0_rsp_ready : 1'b0;
    assign s3_rsp_ready = (r_m0_slave_sel == 3'd3) ? m0_rsp_ready : 1'b0;
    assign s4_rsp_ready = (r_m0_slave_sel == 3'd4) ? m0_rsp_ready : 1'b0;
    assign s5_rsp_ready = (r_m0_slave_sel == 3'd5) ? m0_rsp_ready : 1'b0;
    assign s6_rsp_ready = (r_m0_slave_sel == 3'd6) ? m0_rsp_ready : 1'b0;
    assign s7_rsp_ready = (r_m0_slave_sel == 3'd7) ? m0_rsp_ready : 1'b0;
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

    // APB Master 4 - converts cmd/rsp to slave 4 APB
    apb_master #(
        .ADDR_WIDTH (ADDR_WIDTH),
        .DATA_WIDTH (DATA_WIDTH),
        .STRB_WIDTH (STRB_WIDTH),
        .PROT_WIDTH (3)
    ) u_apb_master_s4 (
        .pclk           (pclk),
        .presetn        (presetn),
        .m_apb_PSEL     (s4_apb_PSEL),
        .m_apb_PENABLE  (s4_apb_PENABLE),
        .m_apb_PREADY   (s4_apb_PREADY),
        .m_apb_PADDR    (s4_apb_PADDR),
        .m_apb_PWRITE   (s4_apb_PWRITE),
        .m_apb_PWDATA   (s4_apb_PWDATA),
        .m_apb_PSTRB    (s4_apb_PSTRB),
        .m_apb_PPROT    (s4_apb_PPROT),
        .m_apb_PRDATA   (s4_apb_PRDATA),
        .m_apb_PSLVERR  (s4_apb_PSLVERR),
        .cmd_valid      (s4_cmd_valid),
        .cmd_ready      (s4_cmd_ready),
        .cmd_pwrite     (s4_cmd_pwrite),
        .cmd_paddr      (s4_cmd_paddr),
        .cmd_pwdata     (s4_cmd_pwdata),
        .cmd_pstrb      (s4_cmd_pstrb),
        .cmd_pprot      (s4_cmd_pprot),
        .rsp_valid      (s4_rsp_valid),
        .rsp_ready      (s4_rsp_ready),
        .rsp_prdata     (s4_rsp_prdata),
        .rsp_pslverr    (s4_rsp_pslverr)
    );

    // APB Master 5 - converts cmd/rsp to slave 5 APB
    apb_master #(
        .ADDR_WIDTH (ADDR_WIDTH),
        .DATA_WIDTH (DATA_WIDTH),
        .STRB_WIDTH (STRB_WIDTH),
        .PROT_WIDTH (3)
    ) u_apb_master_s5 (
        .pclk           (pclk),
        .presetn        (presetn),
        .m_apb_PSEL     (s5_apb_PSEL),
        .m_apb_PENABLE  (s5_apb_PENABLE),
        .m_apb_PREADY   (s5_apb_PREADY),
        .m_apb_PADDR    (s5_apb_PADDR),
        .m_apb_PWRITE   (s5_apb_PWRITE),
        .m_apb_PWDATA   (s5_apb_PWDATA),
        .m_apb_PSTRB    (s5_apb_PSTRB),
        .m_apb_PPROT    (s5_apb_PPROT),
        .m_apb_PRDATA   (s5_apb_PRDATA),
        .m_apb_PSLVERR  (s5_apb_PSLVERR),
        .cmd_valid      (s5_cmd_valid),
        .cmd_ready      (s5_cmd_ready),
        .cmd_pwrite     (s5_cmd_pwrite),
        .cmd_paddr      (s5_cmd_paddr),
        .cmd_pwdata     (s5_cmd_pwdata),
        .cmd_pstrb      (s5_cmd_pstrb),
        .cmd_pprot      (s5_cmd_pprot),
        .rsp_valid      (s5_rsp_valid),
        .rsp_ready      (s5_rsp_ready),
        .rsp_prdata     (s5_rsp_prdata),
        .rsp_pslverr    (s5_rsp_pslverr)
    );

    // APB Master 6 - converts cmd/rsp to slave 6 APB
    apb_master #(
        .ADDR_WIDTH (ADDR_WIDTH),
        .DATA_WIDTH (DATA_WIDTH),
        .STRB_WIDTH (STRB_WIDTH),
        .PROT_WIDTH (3)
    ) u_apb_master_s6 (
        .pclk           (pclk),
        .presetn        (presetn),
        .m_apb_PSEL     (s6_apb_PSEL),
        .m_apb_PENABLE  (s6_apb_PENABLE),
        .m_apb_PREADY   (s6_apb_PREADY),
        .m_apb_PADDR    (s6_apb_PADDR),
        .m_apb_PWRITE   (s6_apb_PWRITE),
        .m_apb_PWDATA   (s6_apb_PWDATA),
        .m_apb_PSTRB    (s6_apb_PSTRB),
        .m_apb_PPROT    (s6_apb_PPROT),
        .m_apb_PRDATA   (s6_apb_PRDATA),
        .m_apb_PSLVERR  (s6_apb_PSLVERR),
        .cmd_valid      (s6_cmd_valid),
        .cmd_ready      (s6_cmd_ready),
        .cmd_pwrite     (s6_cmd_pwrite),
        .cmd_paddr      (s6_cmd_paddr),
        .cmd_pwdata     (s6_cmd_pwdata),
        .cmd_pstrb      (s6_cmd_pstrb),
        .cmd_pprot      (s6_cmd_pprot),
        .rsp_valid      (s6_rsp_valid),
        .rsp_ready      (s6_rsp_ready),
        .rsp_prdata     (s6_rsp_prdata),
        .rsp_pslverr    (s6_rsp_pslverr)
    );

    // APB Master 7 - converts cmd/rsp to slave 7 APB
    apb_master #(
        .ADDR_WIDTH (ADDR_WIDTH),
        .DATA_WIDTH (DATA_WIDTH),
        .STRB_WIDTH (STRB_WIDTH),
        .PROT_WIDTH (3)
    ) u_apb_master_s7 (
        .pclk           (pclk),
        .presetn        (presetn),
        .m_apb_PSEL     (s7_apb_PSEL),
        .m_apb_PENABLE  (s7_apb_PENABLE),
        .m_apb_PREADY   (s7_apb_PREADY),
        .m_apb_PADDR    (s7_apb_PADDR),
        .m_apb_PWRITE   (s7_apb_PWRITE),
        .m_apb_PWDATA   (s7_apb_PWDATA),
        .m_apb_PSTRB    (s7_apb_PSTRB),
        .m_apb_PPROT    (s7_apb_PPROT),
        .m_apb_PRDATA   (s7_apb_PRDATA),
        .m_apb_PSLVERR  (s7_apb_PSLVERR),
        .cmd_valid      (s7_cmd_valid),
        .cmd_ready      (s7_cmd_ready),
        .cmd_pwrite     (s7_cmd_pwrite),
        .cmd_paddr      (s7_cmd_paddr),
        .cmd_pwdata     (s7_cmd_pwdata),
        .cmd_pstrb      (s7_cmd_pstrb),
        .cmd_pprot      (s7_cmd_pprot),
        .rsp_valid      (s7_rsp_valid),
        .rsp_ready      (s7_rsp_ready),
        .rsp_prdata     (s7_rsp_prdata),
        .rsp_pslverr    (s7_rsp_pslverr)
    );

endmodule : apb_xbar_1to8
