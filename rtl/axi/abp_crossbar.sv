`timescale 1ns / 1ps

module apb_crossbar #(
    parameter int          M = 2,                      // Number of APB masters
    parameter int          S = 4,                      // Number of APB slaves
    parameter int          ADDR_WIDTH           = 32,  // Address width
    parameter int          DATA_WIDTH           = 32,  // Data width
    parameter int          STRB_WIDTH           = DATA_WIDTH/8,  // Strobe width
    parameter bit [S-1:0]  SLAVE_ENABLE         = {S{1'b1}},     // Slave enable for address decoding
    parameter int unsigned SLAVE_ADDR_BASE [S]  = '{0, 'h1000, 'h2000, 'h3000},  // Slave address base
    parameter int unsigned SLAVE_ADDR_LIMIT [S] = '{'h0FFF, 'h1FFF, 'h2FFF, 'h3FFF}  // Slave address limit
) (
    input  logic                    clk,
    input  logic                    rst_n,

    // Master interfaces
    input  logic [M-1:0]                 m_apb_psel,
    input  logic [M-1:0]                 m_apb_penable,
    input  logic [M-1:0]                 m_apb_pwrite,
    input  logic [M-1:0][ADDR_WIDTH-1:0] m_apb_paddr,
    input  logic [M-1:0][DATA_WIDTH-1:0] m_apb_pwdata,
    input  logic [M-1:0][STRB_WIDTH-1:0] m_apb_pstrb,
    output logic [M-1:0]                 m_apb_pready,
    output logic [M-1:0][DATA_WIDTH-1:0] m_apb_prdata,
    output logic [M-1:0]                 m_apb_pslverr,

    // Slave interfaces
    output logic [S-1:0]                 s_apb_psel,
    output logic [S-1:0]                 s_apb_penable,
    output logic [S-1:0]                 s_apb_pwrite,
    output logic [S-1:0][ADDR_WIDTH-1:0] s_apb_paddr,
    output logic [S-1:0][DATA_WIDTH-1:0] s_apb_pwdata,
    output logic [S-1:0][STRB_WIDTH-1:0] s_apb_pstrb,
    input  logic [S-1:0]                 s_apb_pready,
    input  logic [S-1:0][DATA_WIDTH-1:0] s_apb_prdata,
    input  logic [S-1:0]                 s_apb_pslverr
);

    // Address decoding logic
    logic [S-1:0] slave_sel;

    always_comb begin
        slave_sel = '0;
        for (int i = 0; i < M; i++) begin
        if (m_apb_psel[i]) begin
            for (int j = 0; j < S; j++) begin
                if (SLAVE_ENABLE[j] && (m_apb_paddr[i] >= SLAVE_ADDR_BASE[j]) && (m_apb_paddr[i] <= SLAVE_ADDR_LIMIT[j])) begin
                    slave_sel[j] = 1'b1;
                    break;
                end
            end
        end
        end
    end

    // Slave interface multiplexing
    always_comb begin
        for (int i = 0; i < S; i++) begin
            s_apb_psel[i]    = (slave_sel[i]) ? |m_apb_psel : 1'b0;
            s_apb_penable[i] = (slave_sel[i]) ? |m_apb_penable : 1'b0;
            s_apb_pwrite[i]  = (slave_sel[i]) ? |m_apb_pwrite : 1'b0;
            s_apb_paddr[i]   = (slave_sel[i]) ? m_apb_paddr[slave_sel[i]] : '0;
            s_apb_pwdata[i]  = (slave_sel[i]) ? m_apb_pwdata[slave_sel[i]] : '0;
            s_apb_pstrb[i]   = (slave_sel[i]) ? m_apb_pstrb[slave_sel[i]] : '0;
        end
    end

    // Master interface multiplexing
    always_comb begin
        for (int i = 0; i < M; i++) begin
            m_apb_pready[i]  = (slave_sel != '0) ? s_apb_pready[slave_sel] : 1'b0;
            m_apb_prdata[i]  = (slave_sel != '0) ? s_apb_prdata[slave_sel] : '0;
            m_apb_pslverr[i] = (slave_sel != '0) ? s_apb_pslverr[slave_sel] : 1'b0;
        end
    end

endmodule