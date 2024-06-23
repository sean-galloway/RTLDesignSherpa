`timescale 1ns / 1ps

module apb_xbar #(
    // Number of APB masters (from the master))
    parameter int          M = 2,
    // Number of APB slaves (to the dest)
    parameter int          S = 4,
    // Address width
    parameter int          ADDR_WIDTH = 32,
    // Data widthMAX_THRESH_WIDTH
    parameter int          DATA_WIDTH = 32,
    // Strobe width
    parameter int          STRB_WIDTH = DATA_WIDTH/8,
    parameter int          MAX_THRESH = 16
) (
    input  logic                 aclk,
    input  logic                 aresetn,

    // Slave enable for addr decoding
    input  logic [S-1:0]         SLAVE_ENABLE,
    // Slave address base
    input  logic [S][AW-1:0]     SLAVE_ADDR_BASE,
    // Slave address limit
    input  logic [S][AW-1:0]     SLAVE_ADDR_LIMIT,
    // Thresholds for the Weighted Round Robin Arbiter
    input  logic [MXMTW-1:0]     THRESHOLDS,

    // Master interfaces - These are from the APB master
    input  logic [M]             m_apb_psel,
    input  logic [M]             m_apb_penable,
    input  logic [M]             m_apb_pwrite,
    input  logic [M][AW-1:0]     m_apb_paddr,
    input  logic [M][DW-1:0]     m_apb_pwdata,
    input  logic [M][SW-1:0]     m_apb_pstrb,
    output logic [M]             m_apb_pready,
    output logic [M][DW-1:0]     m_apb_prdata,
    output logic [M]             m_apb_pslverr,

    // Slave interfaces - these are to the APB destinations
    output logic [S]             s_apb_psel,
    output logic [S]             s_apb_penable,
    output logic [S]             s_apb_pwrite,
    output logic [S][AW-1:0]     s_apb_paddr,
    output logic [S][DW-1:0]     s_apb_pwdata,
    output logic [S][SW-1:0]     s_apb_pstrb,
    input  logic [S]             s_apb_pready,
    input  logic [S][DW-1:0]     s_apb_prdata,
    input  logic [S]             s_apb_pslverr
);
    // local abbreviations
    localparam int DW    = DATA_WIDTH;
    localparam int AW    = ADDR_WIDTH;
    localparam int SW    = STRB_WIDTH;
    localparam int MTW   = $clog2(MAX_THRESH);
    localparam int MXMTW = M*MTW;

    // Address decoding logic
    logic [S-1:0][M-1:0] slave_sel;

    generate
        for (genvar j_dec = 0; j_dec < S; j_dec++) begin : gen_decoder
            always_comb begin
                for (int i_dec = 0; i_dec < M; i_dec++) begin
                    slave_sel[j_dec][i_dec] = 1'b0;
                    if (m_apb_psel[i_dec] && SLAVE_ENABLE[j_dec] &&
                            (m_apb_paddr[i_dec] >= SLAVE_ADDR_BASE[j_dec]) &&
                            (m_apb_paddr[i_dec] <= SLAVE_ADDR_LIMIT[j_dec])) begin
                        slave_sel[j_dec][i_dec] = 1'b1;
                    end
                end
            end
        end
    endgenerate

    // Instantiate arbiters for each slave
    // need to choose betweeen all of the masters assuming
    // they are all doing a cycle to the same slave at once
    logic [S-1:0][M-1:0]         arb_req;
    logic [S-1:0]                arb_gnt_valid;
    logic [S-1:0][M-1:0]         arb_gnt;
    logic [S-1:0][$clog2(M):0]   arb_gnt_id;

    generate
        for (genvar i_arb = 0; i_arb < S; i_arb++) begin : gen_arbiters
            arbiter_weighted_round_robin #(
                .MAX_THRESH  (16),
                .CLIENTS     (M),
                .WAIT_GNT_ACK(1)
            ) arbiter_inst   (
                .i_clk       (aclk),
                .i_rst_n     (aresetn),
                .i_block_arb (1'b0),
                .i_max_thresh(THRESHOLDS),
                .i_req       (slave_sel[i_arb]),
                .ow_gnt_valid(arb_gnt_valid[i_arb]),
                .ow_gnt      (arb_gnt[i_arb]),
                .ow_gnt_id   (arb_gnt_id[i_arb]),
                .i_gnt_ack   (m_apb_pready)
            );
        end
    endgenerate

    // Slave interface multiplexing
    generate
        for (genvar j_msel = 0; j_msel < S; j_msel++) begin : gen_master_sel
            always_comb begin
                int gnt_id = arb_gnt_id[j_msel];
                s_apb_psel[j_msel]    = arb_gnt_valid[j_msel] ? arb_gnt[j_msel][gnt_id] : 1'b0;
                s_apb_penable[j_msel] = arb_gnt_valid[j_msel] ? m_apb_penable[gnt_id] : 1'b0;
                s_apb_pwrite[j_msel]  = arb_gnt_valid[j_msel] ? m_apb_pwrite[gnt_id] : 1'b0;
                s_apb_paddr[j_msel]   = arb_gnt_valid[j_msel] ? m_apb_paddr[gnt_id] : '0;
                s_apb_pwdata[j_msel]  = arb_gnt_valid[j_msel] ? m_apb_pwdata[gnt_id] : '0;
                s_apb_pstrb[j_msel]   = arb_gnt_valid[j_msel] ? m_apb_pstrb[gnt_id] : '0;
            end
        end
    endgenerate

    // Master interface multiplexing
    generate
        for (genvar i_ssel = 0; i_ssel < M; i_ssel++) begin : gen_slave_sel
            for (genvar j_ssel = 0; j_ssel < S; j_ssel++) begin : gen_slave_sel_inner
                always_comb begin
                    m_apb_pready[i_ssel]  = 1'b0;
                    m_apb_prdata[i_ssel]  = '0;
                    m_apb_pslverr[i_ssel] = 1'b0;
                    if (arb_gnt[j_ssel][i_ssel]) begin
                        m_apb_pready[i_ssel]  = s_apb_pready[j_ssel];
                        m_apb_prdata[i_ssel]  = s_apb_prdata[j_ssel];
                        m_apb_pslverr[i_ssel] = s_apb_pslverr[j_ssel];
                    end
                end
            end
        end
    endgenerate

endmodule : apb_xbar
