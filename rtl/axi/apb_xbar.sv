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
    input  logic [M][2:0]        m_apb_pprot,
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
    output logic [S][2:0]        s_apb_pprot,
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

    integer file;

    initial begin
        // Open the file
        file = $fopen("debug_log.txt", "w");

        // Check if the file was opened successfully
        if (file == 0) begin
            $display("Error: Could not open file.");
            $finish;
        end
    end

    // flop the ready coming back
    logic [M]            r_m_apb_pready;

    always_ff @(posedge aclk or negedge aresetn) begin
        if (~aresetn)
            r_m_apb_pready <= '0;
        else
            r_m_apb_pready <= m_apb_pready & m_apb_penable;
    end

    // Address decoding logic
    logic [S-1:0][M-1:0] slave_sel;

    generate
        for (genvar s_dec = 0; s_dec < S; s_dec++) begin : gen_decoder
            always_comb begin
                for (int m_dec = 0; m_dec < M; m_dec++) begin
                    slave_sel[s_dec][m_dec] = 1'b0;
                    if (m_apb_psel[m_dec] && SLAVE_ENABLE[s_dec] &&
                            (m_apb_paddr[m_dec] >= SLAVE_ADDR_BASE[s_dec]) &&
                            (m_apb_paddr[m_dec] <= SLAVE_ADDR_LIMIT[s_dec])) begin
                        slave_sel[s_dec][m_dec] = 1'b1;
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
    logic [$clog2(M):0]          arb_slv_id [0:$clog2(S)-1];

    generate
        for (genvar s_arb = 0; s_arb < S; s_arb++) begin : gen_arbiters
            arbiter_weighted_round_robin #(
                .MAX_THRESH  (16),
                .CLIENTS     (M),
                .WAIT_GNT_ACK(1)
            ) arbiter_inst   (
                .i_clk       (aclk),
                .i_rst_n     (aresetn),
                .i_block_arb (1'b0),
                .i_max_thresh(THRESHOLDS),
                .i_req       (slave_sel[s_arb]),
                .ow_gnt_valid(arb_gnt_valid[s_arb]),
                .ow_gnt      (arb_gnt[s_arb]),
                .ow_gnt_id   (arb_gnt_id[s_arb]),
                .i_gnt_ack   (r_m_apb_pready)
            );
        end
    endgenerate

    // Slave interface multiplexing
    generate
        for (genvar s_msel = 0; s_msel < S; s_msel++) begin : gen_master_sel
            always_comb begin
                int gnt_id = arb_gnt_id[s_msel];
                s_apb_psel[s_msel]    = arb_gnt_valid[s_msel] ? arb_gnt[s_msel][gnt_id] : 1'b0;
                s_apb_penable[s_msel] = arb_gnt_valid[s_msel] ? m_apb_penable[gnt_id] : 1'b0;
                s_apb_pwrite[s_msel]  = arb_gnt_valid[s_msel] ? m_apb_pwrite[gnt_id] : 1'b0;
                s_apb_pprot[s_msel]   = arb_gnt_valid[s_msel] ? m_apb_pprot[gnt_id] : '0;
                s_apb_paddr[s_msel]   = arb_gnt_valid[s_msel] ? m_apb_paddr[gnt_id] : '0;
                s_apb_pwdata[s_msel]  = arb_gnt_valid[s_msel] ? m_apb_pwdata[gnt_id] : '0;
                s_apb_pstrb[s_msel]   = arb_gnt_valid[s_msel] ? m_apb_pstrb[gnt_id] : '0;
                $fdisplay(file, "Master Sel: gnt_id=%0d s_msel=%0d @%0t ns",
                                gnt_id, s_msel, $realtime / 1e3);
            end
        end
    endgenerate

    // Master interface multiplexing
    generate
        for (genvar m_ssel = 0; m_ssel < M; m_ssel++) begin : gen_slave_id
            for (genvar s_ssel = 0; s_ssel < S; s_ssel++) begin : gen_slave_id_inner
                always_comb begin
                    if (s_ssel == 0)
                        arb_slv_id[m_ssel] = '0;
                    if (arb_gnt[s_ssel][m_ssel]) begin
                        arb_slv_id[m_ssel] = s_ssel;
                    end
                end
            end
        end
    endgenerate

    generate
        for (genvar m_demux = 0; m_demux < M; m_demux++) begin : gen_demux
            always_comb begin
                int slv_id = arb_slv_id[m_demux];
                m_apb_pready[m_demux]  = s_apb_pready[slv_id];
                m_apb_prdata[m_demux]  = s_apb_prdata[slv_id];
                m_apb_pslverr[m_demux] = s_apb_pslverr[slv_id];
            end
        end
    endgenerate

endmodule : apb_xbar
