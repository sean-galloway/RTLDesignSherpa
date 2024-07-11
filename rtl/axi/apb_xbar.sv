`timescale 1ns / 1ps

module apb_xbar #(
    // Number of APB masters (from the master))
    parameter int M = 3,
    // Number of APB slaves (to the dest)
    parameter int S = 6,
    // Address width
    parameter int ADDR_WIDTH = 32,
    // Data widthMAX_THRESH_WIDTH
    parameter int DATA_WIDTH = 32,
    // Strobe width
    parameter int STRB_WIDTH = DATA_WIDTH/8,
    parameter int MAX_THRESH = 16,
    parameter int SKID4      = 1
) (
    input  logic                         aclk,
    input  logic                         aresetn,

    // Slave enable for addr decoding
    input  logic [S-1:0]                 SLAVE_ENABLE,
    // Slave address base
    input  logic [S-1:0][ADDR_WIDTH-1:0] SLAVE_ADDR_BASE,
    // Slave address limit
    input  logic [S-1:0][ADDR_WIDTH-1:0] SLAVE_ADDR_LIMIT,
    // Thresholds for the Weighted Round Robin Arbiters
    input  logic [MXMTW-1:0]             MST_THRESHOLDS,
    input  logic [SXMTW-1:0]             SLV_THRESHOLDS,

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

    // local abbreviations
    localparam int DW     = DATA_WIDTH;
    localparam int AW     = ADDR_WIDTH;
    localparam int SW     = STRB_WIDTH;
    localparam int MID    = $clog2(M);
    localparam int SID    = $clog2(S);
    localparam int MTW    = $clog2(MAX_THRESH);
    localparam int MXMTW  = M * MTW;
    localparam int SXMTW  = S * MTW;
    localparam int SLVCPW = AW + DW + SW + 4;
    localparam int SLVRPW = DW + 1;
    localparam int MSTCPW = AW + DW + SW + 6;
    localparam int MSTRPW = DW + 3;

    integer file;

    initial begin
        file = $fopen("debug_log.txt", "w");
        if (file == 0) begin
            $display("Error: could not open file.");
            $finish;
        end
    end

    ////////////////////////////////////////////////////////////////////////////////////////////////
    // Internal signals for Slave command and response packets
    logic [M-1:0]                     r_slv_cmd_valid;
    logic [M-1:0]                     r_slv_cmd_ready;
    logic [M-1:0][SLVCPW-1:0]         r_slv_cmd_data;
    logic [M-1:0]                     r_slv_cmd_pwrite;
    logic [M-1:0][2:0]                r_slv_cmd_pprot;
    logic [M-1:0][STRB_WIDTH-1:0]     r_slv_cmd_pstrb;
    logic [M-1:0][ADDR_WIDTH-1:0]     r_slv_cmd_paddr;
    logic [M-1:0][DATA_WIDTH-1:0]     r_slv_cmd_pwdata;

    logic [M-1:0]                     r_slv_rsp_valid;
    logic [M-1:0]                     r_slv_rsp_ready;
    logic [M-1:0][SLVRPW-1:0]         r_slv_rsp_data;
    logic [M-1:0][DATA_WIDTH-1:0]     r_slv_rsp_prdata;
    logic [M-1:0]                     r_slv_rsp_pslverr;

    logic [M-1:0][S-1:0]              slave_sel;
    logic [M-1:0]                     slv_arb_gnt_valid;
    logic [M-1:0][S-1:0]              slv_arb_gnt;
    logic [M-1:0][SID-1:0]            slv_arb_gnt_id;
    logic [S-1:0]                     slv_arb_gnt_ack;
    logic [S-1:0][M-1:0]              slv_arb_gnt_swap;

    // Generate block to swap indices
    generate
        for (genvar s_slv_swap = 0; s_slv_swap < S; s_slv_swap++) begin : gen_slv_arb_gnt_swap
            for (genvar m_slv_swap = 0; m_slv_swap < M; m_slv_swap++) begin : gen_slv_arb_gnt_swap
                always_comb begin
                    slv_arb_gnt_swap[s_slv_swap][m_slv_swap] = slv_arb_gnt[m_slv_swap][s_slv_swap];
                end
            end
        end
    endgenerate

    generate
        for (genvar m_port = 0; m_port < M; m_port++) begin : gen_apb_slave_stubs

            assign {r_slv_cmd_pwrite[m_port], r_slv_cmd_pprot[m_port], r_slv_cmd_pstrb[m_port],
                        r_slv_cmd_paddr[m_port], r_slv_cmd_pwdata[m_port]} = r_slv_cmd_data[m_port];

            apb_slave_stub #(
                .SKID4            (SKID4),
                .DATA_WIDTH       (DATA_WIDTH),
                .ADDR_WIDTH       (ADDR_WIDTH),
                .STRB_WIDTH       (STRB_WIDTH)
            ) u_apb_slave_stub    (
                .aclk             (aclk),
                .aresetn          (aresetn),
                .s_apb_PSEL       (m_apb_psel[m_port]),
                .s_apb_PENABLE    (m_apb_penable[m_port]),
                .s_apb_PADDR      (m_apb_paddr[m_port]),
                .s_apb_PWRITE     (m_apb_pwrite[m_port]),
                .s_apb_PWDATA     (m_apb_pwdata[m_port]),
                .s_apb_PSTRB      (m_apb_pstrb[m_port]),
                .s_apb_PPROT      (m_apb_pprot[m_port]),
                .s_apb_PRDATA     (m_apb_prdata[m_port]),
                .s_apb_PSLVERR    (m_apb_pslverr[m_port]),
                .s_apb_PREADY     (m_apb_pready[m_port]),
                .o_cmd_valid      (r_slv_cmd_valid[m_port]), // used
                .i_cmd_ready      (r_slv_cmd_ready[m_port]), // used
                .o_cmd_data       (r_slv_cmd_data[m_port]),  // used
                .i_rsp_valid      (r_slv_rsp_valid[m_port]), // used
                .o_rsp_ready      (r_slv_rsp_ready[m_port]), // used
                .i_rsp_data       (r_slv_rsp_data[m_port])   // used
            );

            arbiter_weighted_round_robin #(
                .MAX_THRESH  (16),
                .CLIENTS     (S),
                .WAIT_GNT_ACK(1)
            ) master_arbiter_inst (
                .i_clk       (aclk),
                .i_rst_n     (aresetn),
                .i_block_arb (1'b0),
                .i_max_thresh(SLV_THRESHOLDS),
                .i_req       (slave_sel[m_port]),          // used
                .ow_gnt_valid(slv_arb_gnt_valid[m_port]),  // used
                .ow_gnt      (slv_arb_gnt[m_port]),        // used
                .ow_gnt_id   (slv_arb_gnt_id[m_port]),     // not needed for now
                .i_gnt_ack   (slv_arb_gnt_ack)             // used
            );

        end
    endgenerate

    ////////////////////////////////////////////////////////////////////////////////////////////////
    // Instantiate Master stubs and axi_fifo_sync
    logic [S-1:0]                r_mst_cmd_valid;
    logic [S-1:0]                r_mst_cmd_ready;
    logic [S-1:0][MSTCPW-1:0]    r_mst_cmd_data;
    logic [S-1:0]                r_mst_rsp_valid;
    logic [S-1:0]                r_mst_rsp_ready;
    logic [S-1:0][MSTRPW-1:0]    r_mst_rsp_data;

    logic [S-1:0]                r_mst_rsp_last;
    logic [S-1:0]                r_mst_rsp_first;
    logic [S-1:0]                r_mst_rsp_pslverr;
    logic [S-1:0][DW-1:0]        r_mst_rsp_prdata;

    logic [S-1:0]                r_mst_side_wr_valid;
    logic [S-1:0]                r_mst_side_wr_ready;
    logic [S-1:0][MID-1:0]       r_mst_side_wr_data;
    logic [S-1:0]                r_mst_side_rd_ready;
    logic [S-1:0]                r_mst_side_rd_valid;
    logic [S-1:0][MID-1:0]       r_mst_side_rd_data;

    logic [S-1:0][M-1:0]         master_sel;
    logic [S-1:0]                mst_arb_gnt_valid;
    logic [S-1:0][M-1:0]         mst_arb_gnt;
    logic [S-1:0][MID-1:0]       mst_arb_gnt_id;
    logic [M-1:0]                mst_arb_gnt_ack;

    logic [M-1:0][S-1:0]         mst_arb_gnt_swap;

    // Generate block to swap indices
    generate
        for (genvar m_mst_swap = 0; m_mst_swap < M; m_mst_swap++) begin : gen_arb_gnt_mst_m
            for (genvar s_mst_swap = 0; s_mst_swap < S; s_mst_swap++) begin : gen_arb_gnt_mst_s
                always_comb begin
                    mst_arb_gnt_swap[m_mst_swap][s_mst_swap] = mst_arb_gnt[s_mst_swap][m_mst_swap];
                end
            end
        end
    endgenerate

    generate
        for (genvar s_port = 0; s_port < S; s_port++) begin : gen_apb_master_stubs

            assign {r_mst_rsp_last[s_port], r_mst_rsp_first[s_port],
                    r_mst_rsp_pslverr[s_port], r_mst_rsp_prdata[s_port]} = r_mst_rsp_data[s_port];

            apb_master_stub #(
                .DATA_WIDTH     (DATA_WIDTH),
                .ADDR_WIDTH     (ADDR_WIDTH),
                .STRB_WIDTH     (STRB_WIDTH)
            ) u_apb_master_stub (
                .aclk           (aclk),
                .aresetn        (aresetn),
                .m_apb_PSEL     (s_apb_psel[s_port]),
                .m_apb_PENABLE  (s_apb_penable[s_port]),
                .m_apb_PADDR    (s_apb_paddr[s_port]),
                .m_apb_PWRITE   (s_apb_pwrite[s_port]),
                .m_apb_PWDATA   (s_apb_pwdata[s_port]),
                .m_apb_PSTRB    (s_apb_pstrb[s_port]),
                .m_apb_PPROT    (s_apb_pprot[s_port]),
                .m_apb_PRDATA   (s_apb_prdata[s_port]),
                .m_apb_PSLVERR  (s_apb_pslverr[s_port]),
                .m_apb_PREADY   (s_apb_pready[s_port]),
                .i_cmd_valid    (r_mst_cmd_valid[s_port]), // used
                .o_cmd_ready    (r_mst_cmd_ready[s_port]), // used
                .i_cmd_data     (r_mst_cmd_data[s_port]),  // used
                .o_rsp_valid    (r_mst_rsp_valid[s_port]), // used
                .i_rsp_ready    (r_mst_rsp_ready[s_port]), // used
                .o_rsp_data     (r_mst_rsp_data[s_port])   // used
            );

            // Instantiate axi_fifo_sync
            axi_skid_buffer #(
                .SKID4        (1),
                .DATA_WIDTH   (MID)
            ) side_queue_inst (
                .i_axi_aclk   (aclk),
                .i_axi_aresetn(aresetn),
                .i_wr_valid   (r_mst_side_wr_valid[s_port]), // used
                .o_wr_ready   (r_mst_side_wr_ready[s_port]), // used
                .i_wr_data    (r_mst_side_wr_data[s_port]),  // used
                .o_rd_valid   (r_mst_side_rd_valid[s_port]), // used
                .i_rd_ready   (r_mst_side_rd_ready[s_port]), // used
                .o_rd_data    (r_mst_side_rd_data[s_port])   // used
            );

            arbiter_weighted_round_robin #(
                .MAX_THRESH  (16),
                .CLIENTS     (M),
                .WAIT_GNT_ACK(1)
            ) master_arbiter_inst (
                .i_clk       (aclk),
                .i_rst_n     (aresetn),
                .i_block_arb (1'b0),
                .i_max_thresh(SLV_THRESHOLDS),
                .i_req       (master_sel[s_port]),        // used
                .ow_gnt_valid(mst_arb_gnt_valid[s_port]), // used
                .ow_gnt      (mst_arb_gnt[s_port]),       // used
                .ow_gnt_id   (mst_arb_gnt_id[s_port]),    // used
                .i_gnt_ack   (mst_arb_gnt_ack)            // used
            );

        end
    endgenerate

    ////////////////////////////////////////////////////////////////////////////////////////////////
    // assert the gnt_acks
    always_ff @(posedge aclk or negedge aresetn) begin
        if (~aresetn) begin
            mst_arb_gnt_ack   <= '0;
            slv_arb_gnt_ack   <= '0;
        end else begin
            mst_arb_gnt_ack <= r_mst_cmd_valid & r_mst_cmd_ready;
            slv_arb_gnt_ack <= r_slv_rsp_valid & r_slv_rsp_ready;
        end
    end

    ////////////////////////////////////////////////////////////////////////////////////////////////
    // Address decoding logic
    generate
        for (genvar s_dec = 0; s_dec < S; s_dec++) begin : gen_decoder
            always_comb begin
                for (int m_dec = 0; m_dec < M; m_dec++) begin
                    master_sel[s_dec][m_dec] = 1'b0;
                    if (r_slv_cmd_valid[m_dec] && SLAVE_ENABLE[s_dec] &&
                            (r_slv_cmd_paddr[m_dec] >= SLAVE_ADDR_BASE[s_dec]) &&
                            (r_slv_cmd_paddr[m_dec] <= SLAVE_ADDR_LIMIT[s_dec])) begin
                        master_sel[s_dec][m_dec] = 1'b1;
                    end
                end
            end
        end
    endgenerate

    ////////////////////////////////////////////////////////////////////////////////////////////////
    // Generate the select signals for the slave arbiter
    // This sends response information back to the slave stubs
    generate
        for (genvar m_slv_arb = 0; m_slv_arb < M; m_slv_arb++) begin : gen_slv_arb
            always_comb begin
                for (int s_slv_arb = 0; s_slv_arb < S; s_slv_arb++) begin : gen_slv_arb_inner
                    slave_sel[m_slv_arb][s_slv_arb] = 'b0;
                    if (r_mst_side_rd_valid[s_slv_arb] &&
                            r_mst_side_rd_data[s_slv_arb] == m_slv_arb &&
                            r_slv_rsp_ready[m_slv_arb] &&
                            r_mst_rsp_valid[s_slv_arb]) begin
                        slave_sel[m_slv_arb][s_slv_arb] = 1'b1;
                    end
                end
            end
        end
    endgenerate


    ////////////////////////////////////////////////////////////////////////////////////////////////
    // Master interface multiplexing
    generate
        for (genvar s_mux = 0; s_mux < S; s_mux++) begin : gen_slave_mux
            always_comb begin
                r_mst_side_rd_ready[s_mux] = 'b0;
                r_mst_rsp_ready[s_mux]     = 'b0;
                r_mst_cmd_valid[s_mux]     = 'b0;
                r_mst_cmd_data[s_mux]      = 'b0;
                r_mst_side_wr_valid[s_mux] = 'b0;
                r_mst_side_wr_data[s_mux]  = 'b0;
                for (int m_mux = 0; m_mux < M; m_mux++) begin
                    if (r_mst_cmd_ready[s_mux] && r_mst_side_wr_ready[s_mux] &&
                            mst_arb_gnt[s_mux][m_mux] && mst_arb_gnt_valid[s_mux]) begin

                        r_mst_cmd_valid[s_mux] = 'b1;
                        r_mst_cmd_data[s_mux]  = {1'b0, 1'b0, r_slv_cmd_pwrite[m_mux],
                            r_slv_cmd_pprot[m_mux], r_slv_cmd_pstrb[m_mux],
                            r_slv_cmd_paddr[m_mux], r_slv_cmd_pwdata[m_mux]};
                        r_mst_side_wr_valid[s_mux] = 1'b1;
                        r_mst_side_wr_data[s_mux] = mst_arb_gnt_id[s_mux];
                    end

                    if (slv_arb_gnt_valid[m_mux] && slv_arb_gnt_swap[s_mux][m_mux]) begin
                        r_mst_side_rd_ready[s_mux] = 1'b1;
                        r_mst_rsp_ready[s_mux]     = 1'b1;
                    end
                end
            end
        end
    endgenerate

    ////////////////////////////////////////////////////////////////////////////////////////////////
    // Slave interface de-muxing
    generate
        for (genvar m_slv_demux = 0; m_slv_demux < M; m_slv_demux++) begin : gen_slv_demux
            always_comb begin
                r_slv_cmd_ready[m_slv_demux] = 'b0;
                for (int s_slv_demux = 0; s_slv_demux < S; s_slv_demux++) begin : gen_slv_demux_inner
                    if (mst_arb_gnt_swap[m_slv_demux][s_slv_demux])
                        r_slv_cmd_ready[m_slv_demux] = 'b1;
                end
            end
        end
    endgenerate

    // de-mux the master interface's respnses back to the apb_slaves
    generate
        for (genvar m_demux = 0; m_demux < M; m_demux++) begin : gen_demux
            always_comb begin
                r_slv_rsp_valid[m_demux]  = 1'b0;
                r_slv_rsp_data[m_demux]  = '0;
                for (int s_demux = 0; s_demux < S; s_demux++) begin
                    if (slv_arb_gnt[m_demux][s_demux] && slv_arb_gnt_valid[m_demux]) begin
                        r_slv_rsp_valid[m_demux] = 1'b1;
                        r_slv_rsp_data[m_demux]  = {r_mst_rsp_pslverr[s_demux],
                                                        r_mst_rsp_prdata[s_demux]};
                    end
                end
            end
        end
    endgenerate


    ////////////////////////////////////////////////////////////////////////////////////////////////
    // signal dumps
    initial begin
        forever begin
            @(negedge aclk);
            $fdisplay(file, "==================================================================================================");
            for (int m_loop=0; m_loop<3; m_loop++) begin
                $fdisplay(file, "Slave Interface @ %0t m_loop=%0d m_apb_penable=%0b m_apb_pready=%0b m_apb_paddr=%0h m_apb_psel=%0b",
                    $realtime/1e3, m_loop, m_apb_penable[m_loop], m_apb_pready[m_loop], m_apb_paddr[m_loop], m_apb_psel[m_loop]);
            end
            for (int m_loop=0; m_loop<3; m_loop++) begin
                $fdisplay(file, "Slave Queues @ %0t: m_loop=%0d r_slv_cmd_valid=%0b r_slv_cmd_ready=%0b r_slv_cmd_paddr=%0h r_slv_rsp_valid=%0b r_slv_rsp_ready=%0b",
                    $realtime/1e3, m_loop, r_slv_cmd_valid[m_loop], r_slv_cmd_ready[m_loop], r_slv_cmd_paddr[m_loop], r_slv_rsp_valid[m_loop], r_slv_rsp_ready[m_loop]);
            end
            for (int m_loop=0; m_loop<3; m_loop++) begin
                $fdisplay(file, "Slave Arb @ %0t: m_loop=%0d slv_arb_gnt_valid=%0b slv_arb_gnt=%0b slv_arb_gnt_ack=%0b slv_arb_gnt_id=%0d",
                    $realtime/1e3, m_loop, slv_arb_gnt_valid[m_loop], slv_arb_gnt[m_loop], slv_arb_gnt_ack[m_loop], slv_arb_gnt_id[m_loop]);
            end
            for (int m_loop=0; m_loop<3; m_loop++) begin
                $fdisplay(file, "Slave Decode @ %0t: m_loop=%0d slave_sel=%0b",
                    $realtime/1e3, m_loop, slave_sel[m_loop]);
            end

            $fdisplay(file, "--------------------------------------------------------------------------------------------------");
            for (int s_loop=0; s_loop<6; s_loop++) begin
                $fdisplay(file, "Master Interface @ %0t s_loop=%0d s_apb_penable=%0b s_apb_pready=%0b s_apb_paddr=%0h s_apb_psel=%0b",
                    $realtime/1e3, s_loop, s_apb_penable[s_loop], s_apb_pready[s_loop], s_apb_paddr[s_loop], s_apb_psel[s_loop]);
            end
            for (int s_loop=0; s_loop<6; s_loop++) begin
                $fdisplay(file, "Master Arb @ %0t: s_loop=%0d mst_arb_gnt_valid=%0b mst_arb_gnt=%0b mst_arb_gnt_ack=%0b mst_arb_gnt_id=%0d",
                    $realtime/1e3, s_loop, mst_arb_gnt_valid[s_loop], mst_arb_gnt[s_loop], mst_arb_gnt_ack[s_loop], mst_arb_gnt_id[s_loop]);
            end
            for (int s_loop=0; s_loop<6; s_loop++) begin
                $fdisplay(file, "Master Decode @ %0t: s_loop=%0d master_sel=%0b",
                    $realtime/1e3, s_loop, master_sel[s_loop]);
            end
            for (int s_loop=0; s_loop<6; s_loop++) begin
                $fdisplay(file, "Master Queues @ %0t: s_loop=%0d r_mst_cmd_valid=%0b r_mst_cmd_ready=%0b r_mst_rsp_valid=%0b r_mst_rsp_ready=%0b r_mst_side_wr_valid=%b r_mst_side_wr_ready=%0b r_mst_side_rd_valid=%b r_mst_side_rd_ready=%0b ",
                    $realtime/1e3, s_loop, r_mst_cmd_valid[s_loop], r_mst_cmd_ready[s_loop], r_mst_rsp_valid[s_loop], r_mst_rsp_ready[s_loop],
                    r_mst_side_wr_valid[s_loop], r_mst_side_wr_ready[s_loop], r_mst_side_rd_valid[s_loop], r_mst_side_rd_ready[s_loop]);
            end

        end
    end

    // initial begin
    //     #28149 $finish;
    // end

endmodule : apb_xbar
