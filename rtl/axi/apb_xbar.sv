`timescale 1ns / 1ps

module apb_xbar #(
    parameter int          M = 2,                      // Number of APB masters (from the master))
    parameter int          S = 4,                      // Number of APB slaves (to the dest)
    parameter int          ADDR_WIDTH           = 32,  // Address width
    parameter int          DATA_WIDTH           = 32,  // Data width
    parameter int          STRB_WIDTH           = DATA_WIDTH/8,  // Strobe width
    parameter bit [S-1:0]  SLAVE_ENABLE         = {S{1'b1}},     // Slave enable for addr decoding
    parameter int unsigned SLAVE_ADDR_BASE [S]  = {0, 'h1000, 'h2000, 'h3000},  // Slave addr base
    parameter int unsigned SLAVE_ADDR_LIMIT [S] = {'h0FFF, 'h1FFF, 'h2FFF, 'h3FFF},  //  addr limit
    parameter int unsigned THRESHOLDS [S]       = {S{4'h4}}
) (
    input  logic                         clk,
    input  logic                         rst_n,

    // Configuration inputs
    input  bit [S-1:0]                   SLAVE_ENABLE,    // Slave enable for addr decoding
    input  int unsigned [S-1:0][AW-1:0] SLAVE_ADDR_BASE,  // Slave addr base
    input  int unsigned [S-1:0][AW-1:0] SLAVE_ADDR_LIMIT, // addr limit
    input  int unsigned [S-1:0]          THRESHOLDS,      // Thresholds for weighted round-robin

    // Master interfaces - These are from the APB master
    input  logic [M-1:0]         m_apb_psel,
    input  logic [M-1:0]         m_apb_penable,
    input  logic [M-1:0]         m_apb_pwrite,
    input  logic [M-1:0][AW-1:0] m_apb_paddr,
    input  logic [M-1:0][DW-1:0] m_apb_pwdata,
    input  logic [M-1:0][SW-1:0] m_apb_pstrb,
    output logic [M-1:0]         m_apb_pready,
    output logic [M-1:0][DW-1:0] m_apb_prdata,
    output logic [M-1:0]         m_apb_pslverr,

    // Slave interfaces - these are to the APB destinations
    output logic [S-1:0]         s_apb_psel,
    output logic [S-1:0]         s_apb_penable,
    output logic [S-1:0]         s_apb_pwrite,
    output logic [S-1:0][AW-1:0] s_apb_paddr,
    output logic [S-1:0][DW-1:0] s_apb_pwdata,
    output logic [S-1:0][SW-1:0] s_apb_pstrb,
    input  logic [S-1:0]         s_apb_pready,
    input  logic [S-1:0][DW-1:0] s_apb_prdata,
    input  logic [S-1:0]         s_apb_pslverr
);
    // local abbreviations
    localparam int DW  = DATA_WIDTH;
    localparam int AW  = ADDR_WIDTH;
    localparam int SW  = STRB_WIDTH;

    // Address decoding logic
    logic [S-1:0][M-1:0] slave_sel;

    always_comb begin
        for (int j = 0; j < S; j++) begin
            for (int i = 0; i < M; i++) begin
                slave_sel[j][i] = 1'b0;
                if (m_apb_psel[i] && SLAVE_ENABLE[j] &&
                    (m_apb_paddr[i] >= SLAVE_ADDR_BASE[j]) &&
                    (m_apb_paddr[i] <= SLAVE_ADDR_LIMIT[j])) begin
                    slave_sel[j][i] = 1'b1;
                end
            end
        end
    end

    // Instantiate arbiters for each slave
    logic [S-1:0][M-1:0]         arb_req;
    logic [S-1:0]                arb_gnt_valid;
    logic [S-1:0][M-1:0]         arb_gnt;
    logic [S-1:0][$clog2(M)-1:0] arb_gnt_id;

    generate
        for (genvar j = 0; j < S; j++) begin : gen_arbiters
            arbiter_weighted_round_robin #(
                .MAX_THRESH  (16),
                .CLIENTS     (M),
                .WAIT_GNT_ACK(1)
            ) arbiter_inst   (
                .i_clk       (clk),
                .i_rst_n     (rst_n),
                .i_block_arb (1'b0),
                .i_max_thresh(THRESHOLDS),
                .i_req       (slave_sel[j]),
                .ow_gnt_valid(arb_gnt_valid[j]),
                .ow_gnt      (arb_gnt[j]),
                .ow_gnt_id   (arb_gnt_id[j]),
                .i_gnt_ack   (m_apb_pready)
            );
        end
    endgenerate

    // Slave interface multiplexing
    always_comb begin
        for (int i = 0; i < S; i++) begin
            int gnt_id = arb_gnt_id[i];
            s_apb_psel[i]    = arb_gnt_valid[i] ? arb_gnt[i][gnt_id] : 1'b0;
            s_apb_penable[i] = arb_gnt_valid[i] ? m_apb_penable[gnt_id] : 1'b0;
            s_apb_pwrite[i]  = arb_gnt_valid[i] ? m_apb_pwrite[gnt_id] : 1'b0;
            s_apb_paddr[i]   = arb_gnt_valid[i] ? m_apb_paddr[gnt_id] : '0;
            s_apb_pwdata[i]  = arb_gnt_valid[i] ? m_apb_pwdata[gnt_id] : '0;
            s_apb_pstrb[i]   = arb_gnt_valid[i] ? m_apb_pstrb[gnt_id] : '0;
        end
    end

    // Master interface multiplexing
    always_comb begin
        for (int i = 0; i < M; i++) begin
            m_apb_pready[i]  = 1'b0;
            m_apb_prdata[i]  = '0;
            m_apb_pslverr[i] = 1'b0;
            for (int j = 0; j < S; j++) begin
                if (arb_gnt[j][i]) begin
                    m_apb_pready[i]  = s_apb_pready[j];
                    m_apb_prdata[i]  = s_apb_prdata[j];
                    m_apb_pslverr[i] = s_apb_pslverr[j];
                end
            end
        end
    end

endmodule : apb_xbar
