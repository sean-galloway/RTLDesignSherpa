`timescale 1ns / 1ps

module apb_xbar_thin #(
    // Number of APB masters (from the master))
    parameter int M = 2,
    // Number of APB slaves (to the dest)
    parameter int S = 4,
    // Address width
    parameter int ADDR_WIDTH = 32,
    // Data widthMAX_THRESH_WIDTH
    parameter int DATA_WIDTH = 32,
    // Strobe width
    parameter int STRB_WIDTH = DATA_WIDTH/8,
    parameter int MAX_THRESH = 16,
    // local abbreviations
    parameter int DW    = DATA_WIDTH,
    parameter int AW    = ADDR_WIDTH,
    parameter int SW    = STRB_WIDTH,
    parameter int MTW   = $clog2(MAX_THRESH),
    parameter int MXMTW = M * MTW
) (
    input  logic                         aclk,
    input  logic                         aresetn,

    // Slave enable for addr decoding
    input  logic [S-1:0]                 SLAVE_ENABLE,
    // Slave address base
    input  logic [S-1:0][ADDR_WIDTH-1:0] SLAVE_ADDR_BASE,
    // Slave address limit
    input  logic [S-1:0][ADDR_WIDTH-1:0] SLAVE_ADDR_LIMIT,
    // Thresholds for the Weighted Round Robin Arbiter
    input  logic [MXMTW-1:0]             THRESHOLDS,

    // Master interfaces - These are from the APB master
    input  logic [M-1:0]                 m_apb_psel,
    input  logic [M-1:0]                 m_apb_penable,
    input  logic [M-1:0]                 m_apb_pwrite,
    input  logic [M-1:0][2:0]            m_apb_pprot,
    input  logic [M-1:0][ADDR_WIDTH-1:0] m_apb_paddr,
    input  logic [M-1:0][DATA_WIDTH-1:0] m_apb_pwdata,
    input  logic [M-1:0][STRB_WIDTH-1:0] m_apb_pstrb,
    output logic [M-1:0]                 m_apb_pready,
    output logic [M-1:0][DATA_WIDTH-1:0] m_apb_prdata,
    output logic [M-1:0]                 m_apb_pslverr,

    // Slave interfaces - these are to the APB destinations
    output logic [S-1:0]                 s_apb_psel,
    output logic [S-1:0]                 s_apb_penable,
    output logic [S-1:0]                 s_apb_pwrite,
    output logic [S-1:0][2:0]            s_apb_pprot,
    output logic [S-1:0][ADDR_WIDTH-1:0] s_apb_paddr,
    output logic [S-1:0][DATA_WIDTH-1:0] s_apb_pwdata,
    output logic [S-1:0][STRB_WIDTH-1:0] s_apb_pstrb,
    input  logic [S-1:0]                 s_apb_pready,
    input  logic [S-1:0][DATA_WIDTH-1:0] s_apb_prdata,
    input  logic [S-1:0]                 s_apb_pslverr
);

    integer file;

    initial begin
        file = $fopen("debug_log.txt", "w");
        if (file == 0) begin
            $display("Error: could not open file.");
            $finish;
        end
    end

    ////////////////////////////////////////////////////////////////////////////////////////////////
    // Address decoding logic
    logic [S-1:0][M-1:0]             master_sel;

    generate
        for (genvar s_dec = 0; s_dec < S; s_dec++) begin : gen_decoder
            always_comb begin
                for (int m_dec = 0; m_dec < M; m_dec++) begin
                    master_sel[s_dec][m_dec] = 1'b0;
                    if (m_apb_psel[m_dec] && SLAVE_ENABLE[s_dec] &&
                            (m_apb_paddr[m_dec] >= SLAVE_ADDR_BASE[s_dec]) &&
                            (m_apb_paddr[m_dec] <= SLAVE_ADDR_LIMIT[s_dec])) begin
                        master_sel[s_dec][m_dec] = 1'b1;
                        $fdisplay(file, "Decode: Time=%0t s_dec=%0h m_dec=%0h", $realtime/1e3, s_dec, m_dec);
                    end
                end
            end
        end
    endgenerate

    ////////////////////////////////////////////////////////////////////////////////////////////////
    // Instantiate arbiters for each slave
    logic [S-1:0]                arb_gnt_valid;
    logic [S-1:0][M-1:0]         arb_gnt;
    logic [S-1:0][$clog2(M):0]   arb_gnt_id;
    logic [M-1:0]                arb_gnt_ack;

    // assert the gnt_ack
    always_ff @(posedge aclk or negedge aresetn) begin
        if (~aresetn)
            arb_gnt_ack <= '0;
        else
            arb_gnt_ack <= m_apb_pready & m_apb_penable & m_apb_penable;
    end

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
                .i_req       (master_sel[s_arb]),
                .ow_gnt_valid(arb_gnt_valid[s_arb]),
                .ow_gnt      (arb_gnt[s_arb]),
                .ow_gnt_id   (arb_gnt_id[s_arb]),
                .i_gnt_ack   (arb_gnt_ack)
            );
        end
    endgenerate

    always_comb begin
        for (int s_loop=0; s_loop<S; s_loop++) begin
            $fdisplay(file, "Arbiter outputs @ %0t", $realtime/1e3);
            $fdisplay(file, "s_loop=%0d arb_gnt_valid=%0b", s_loop, arb_gnt_valid[s_loop]);
            $fdisplay(file, "s_loop=%0d arb_gnt=%0b", s_loop, arb_gnt[s_loop]);
            $fdisplay(file, "s_loop=%0d arb_gnt_id=%0d", s_loop, arb_gnt_id[s_loop]);
        end
    end

    always_comb begin
        for (int m_loop=0; m_loop<M; m_loop++) begin
            $fdisplay(file, "Time=%0t m_loop=%0d: psel=%0b penable=%0b pready=%0b pwrite=%0b pprot=%0h paddr=%0h pwdata=%0h pstrb=%0h",
                    $realtime/1e3, m_loop,
                    m_apb_psel[m_loop], m_apb_pready[m_loop], m_apb_penable[m_loop], m_apb_pwrite[m_loop],
                    m_apb_pprot[m_loop], m_apb_paddr[m_loop], m_apb_pwdata[m_loop],
                    m_apb_pstrb[m_loop]);

        end
    end

    ////////////////////////////////////////////////////////////////////////////////////////////////
    // Slave interface multiplexing
    generate
        for (genvar s_mux = 0; s_mux < S; s_mux++) begin : gen_slave_mux
            always_comb begin
                logic [$clog2(M):0] mst_id;
                mst_id = arb_gnt_id[s_mux];
                s_apb_psel[s_mux]    = arb_gnt_valid[s_mux] ? m_apb_psel[mst_id] : 1'b0;
                s_apb_penable[s_mux] = arb_gnt_valid[s_mux] ? m_apb_penable[mst_id] : 1'b0;
                s_apb_pwrite[s_mux]  = arb_gnt_valid[s_mux] ? m_apb_pwrite[mst_id] : 1'b0;
                s_apb_pprot[s_mux]   = arb_gnt_valid[s_mux] ? m_apb_pprot[mst_id] : '0;
                s_apb_paddr[s_mux]   = arb_gnt_valid[s_mux] ? m_apb_paddr[mst_id] : '0;
                s_apb_pwdata[s_mux]  = arb_gnt_valid[s_mux] ? m_apb_pwdata[mst_id] : '0;
                s_apb_pstrb[s_mux]   = arb_gnt_valid[s_mux] ? m_apb_pstrb[mst_id] : '0;
                $fdisplay(file, "Master Sel: mst_id=%0d s_mux=%0d arb_gnt_valid=%0b @ %0t ns",
                    mst_id, s_mux, arb_gnt_valid, $realtime / 1e3);
//                $fdisplay(file, "m_apb_psel=%0b m_apb_penable=%0b m_apb_pwrite=%0b m_apb_pprot=%0h m_apb_paddr=%0h m_apb_pwdata=%0h m_apb_pstrb=%0h",
//                    m_apb_psel[mst_id], m_apb_penable[mst_id], m_apb_pwrite[mst_id], m_apb_pprot[mst_id], m_apb_paddr[mst_id], m_apb_pwdata[mst_id], m_apb_pstrb[mst_id]);
            end
        end
    endgenerate

    ////////////////////////////////////////////////////////////////////////////////////////////////
    // Master interface
    // Declare the new array with swapped dimensions
    logic [M-1:0][S-1:0] arb_gnt_mst;

    // Generate block to swap indices
    generate
        for (genvar m = 0; m < M; m++) begin : gen_arb_gnt_mst_m
            for (genvar s = 0; s < S; s++) begin : gen_arb_gnt_mst_s
                always_comb begin
                    arb_gnt_mst[m][s] = arb_gnt[s][m];
                end
            end
        end
    endgenerate

    generate
        for (genvar m_demux = 0; m_demux < M; m_demux++) begin : gen_demux
            always_comb begin
                m_apb_pready[m_demux]  = 1'b0;  // default value
                m_apb_prdata[m_demux]  = '0;    // default value
                m_apb_pslverr[m_demux] = 1'b0;  // default value
                for (int s_demux = 0; s_demux < S; s_demux++) begin
                    if (arb_gnt_mst[m_demux][s_demux]) begin
                        m_apb_pready[m_demux]  = s_apb_pready[s_demux];
                        m_apb_prdata[m_demux]  = s_apb_prdata[s_demux];
                        m_apb_pslverr[m_demux] = s_apb_pslverr[s_demux];
                        $fdisplay(file, "DeMux Sel: m_demux=%0d s_demux=%0d @ %0t ns",
                            m_demux, s_demux, $realtime / 1e3);
                    end
                end
            end
        end
    endgenerate

endmodule : apb_xbar_thin
