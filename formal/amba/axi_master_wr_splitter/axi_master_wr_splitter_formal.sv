// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: 2024-2025 sean galloway
//
// Yosys-compatible copy of axi_master_wr_splitter.sv
// Removed: initial assert, $error/$fatal, verilator pragmas

`timescale 1ns / 1ps

`include "reset_defs.svh"

module axi_master_wr_splitter
#(
    parameter int AXI_ID_WIDTH      = 8,
    parameter int AXI_ADDR_WIDTH    = 32,
    parameter int AXI_DATA_WIDTH    = 32,
    parameter int AXI_USER_WIDTH    = 1,
    parameter int SPLIT_FIFO_DEPTH  = 4,
    parameter int IW = AXI_ID_WIDTH,
    parameter int AW = AXI_ADDR_WIDTH,
    parameter int DW = AXI_DATA_WIDTH,
    parameter int UW = AXI_USER_WIDTH
)
(
    input  logic aclk,
    input  logic aresetn,
    input  logic [11:0] alignment_mask,

    output logic [IW-1:0]              m_axi_awid,
    output logic [AW-1:0]              m_axi_awaddr,
    output logic [7:0]                 m_axi_awlen,
    output logic [2:0]                 m_axi_awsize,
    output logic [1:0]                 m_axi_awburst,
    output logic                       m_axi_awlock,
    output logic [3:0]                 m_axi_awcache,
    output logic [2:0]                 m_axi_awprot,
    output logic [3:0]                 m_axi_awqos,
    output logic [3:0]                 m_axi_awregion,
    output logic [UW-1:0]              m_axi_awuser,
    output logic                       m_axi_awvalid,
    input  logic                       m_axi_awready,

    output logic [DW-1:0]              m_axi_wdata,
    output logic [DW/8-1:0]            m_axi_wstrb,
    output logic                       m_axi_wlast,
    output logic [UW-1:0]              m_axi_wuser,
    output logic                       m_axi_wvalid,
    input  logic                       m_axi_wready,

    input  logic [IW-1:0]              m_axi_bid,
    input  logic [1:0]                 m_axi_bresp,
    input  logic [UW-1:0]              m_axi_buser,
    input  logic                       m_axi_bvalid,
    output logic                       m_axi_bready,

    input  logic                       block_ready,

    input  logic [IW-1:0]              fub_awid,
    input  logic [AW-1:0]              fub_awaddr,
    input  logic [7:0]                 fub_awlen,
    input  logic [2:0]                 fub_awsize,
    input  logic [1:0]                 fub_awburst,
    input  logic                       fub_awlock,
    input  logic [3:0]                 fub_awcache,
    input  logic [2:0]                 fub_awprot,
    input  logic [3:0]                 fub_awqos,
    input  logic [3:0]                 fub_awregion,
    input  logic [UW-1:0]              fub_awuser,
    input  logic                       fub_awvalid,
    output logic                       fub_awready,

    input  logic [DW-1:0]              fub_wdata,
    input  logic [DW/8-1:0]            fub_wstrb,
    input  logic                       fub_wlast,
    input  logic [UW-1:0]              fub_wuser,
    input  logic                       fub_wvalid,
    output logic                       fub_wready,

    output logic [IW-1:0]              fub_bid,
    output logic [1:0]                 fub_bresp,
    output logic [UW-1:0]              fub_buser,
    output logic                       fub_bvalid,
    input  logic                       fub_bready,

    output logic [AW-1:0]              fub_split_addr,
    output logic [IW-1:0]              fub_split_id,
    output logic [7:0]                 fub_split_cnt,
    output logic                       fub_split_valid,
    input  logic                       fub_split_ready
);

    // State definitions
    typedef enum logic [1:0] {
        IDLE      = 2'b01,
        SPLITTING = 2'b10
    } split_state_t;

    split_state_t r_split_state;

    // Buffered original transaction
    logic [IW-1:0]  r_orig_awid;
    logic [AW-1:0]  r_orig_awaddr;
    logic [7:0]     r_orig_awlen;
    logic [2:0]     r_orig_awsize;
    logic [1:0]     r_orig_awburst;
    logic           r_orig_awlock;
    logic [3:0]     r_orig_awcache;
    logic [2:0]     r_orig_awprot;
    logic [3:0]     r_orig_awqos;
    logic [3:0]     r_orig_awregion;
    logic [UW-1:0]  r_orig_awuser;

    logic [AW-1:0]  r_current_addr;
    logic [7:0]     r_current_len;
    logic [7:0]     r_split_count;

    // Data channel tracking
    logic [7:0]     r_expected_beats;
    logic [7:0]     r_beat_counter;
    logic           r_data_splitting;

    // Response consolidation
    logic [7:0]     r_expected_response_count;
    logic [7:0]     r_received_response_count;
    logic           r_waiting_for_responses;
    logic [IW-1:0]  r_original_txn_id;
    logic [1:0]     r_consolidated_resp_status;
    logic [UW-1:0]  r_consolidated_buser;

    // Current transaction selection
    logic [AW-1:0]  w_current_addr;
    logic [7:0]     w_current_len;
    logic [2:0]     w_current_size;

    always_comb begin
        if (r_split_state == IDLE) begin
            w_current_addr = fub_awaddr;
            w_current_len = fub_awlen;
            w_current_size = fub_awsize;
        end else begin
            w_current_addr = r_current_addr;
            w_current_len = r_current_len;
            w_current_size = r_orig_awsize;
        end
    end

    // Split combinational logic
    logic           w_split_required;
    logic [7:0]     w_split_len;
    logic [AW-1:0]  w_next_boundary_addr;
    logic [7:0]     w_remaining_len_after_split;
    logic           w_new_split_needed;

    axi_split_combi #(
        .AW(AW),
        .DW(DW)
    ) inst_axi_split_combi (
        .aclk                      (aclk),
        .aresetn                   (aresetn),
        .current_addr              (w_current_addr),
        .current_len               (w_current_len),
        .ax_size                   (w_current_size),
        .alignment_mask            (alignment_mask),
        .is_idle_state             (r_split_state == IDLE),
        .transaction_valid         (fub_awvalid),
        .split_required            (w_split_required),
        .split_len                 (w_split_len),
        .next_boundary_addr        (w_next_boundary_addr),
        .remaining_len_after_split (w_remaining_len_after_split),
        .new_split_needed          (w_new_split_needed)
    );

    logic w_is_final_split;
    assign w_is_final_split = (r_split_state == SPLITTING) && !w_split_required;

    logic w_split_boundary_reached;
    logic w_generate_wlast;
    assign w_split_boundary_reached = (r_beat_counter + 1 >= r_expected_beats);

    // State machine with response consolidation
    `ALWAYS_FF_RST(aclk, aresetn,
        if (`RST_ASSERTED(aresetn)) begin
            r_split_state <= IDLE;
            r_current_addr <= '0;
            r_current_len <= '0;
            r_split_count <= 8'd0;
            r_orig_awid <= '0;
            r_orig_awaddr <= '0;
            r_orig_awlen <= '0;
            r_orig_awsize <= '0;
            r_orig_awburst <= '0;
            r_orig_awlock <= '0;
            r_orig_awcache <= '0;
            r_orig_awprot <= '0;
            r_orig_awqos <= '0;
            r_orig_awregion <= '0;
            r_orig_awuser <= '0;
            r_expected_beats <= '0;
            r_beat_counter <= '0;
            r_data_splitting <= 1'b0;
            r_expected_response_count <= '0;
            r_received_response_count <= '0;
            r_waiting_for_responses <= 1'b0;
            r_original_txn_id <= '0;
            r_consolidated_resp_status <= 2'b00;
            r_consolidated_buser <= '0;
        end else begin
            case (r_split_state)
                IDLE: begin
                    if (fub_awvalid && m_axi_awready && !block_ready) begin
                        r_orig_awid <= fub_awid;
                        r_orig_awaddr <= fub_awaddr;
                        r_orig_awlen <= fub_awlen;
                        r_orig_awsize <= fub_awsize;
                        r_orig_awburst <= fub_awburst;
                        r_orig_awlock <= fub_awlock;
                        r_orig_awcache <= fub_awcache;
                        r_orig_awprot <= fub_awprot;
                        r_orig_awqos <= fub_awqos;
                        r_orig_awregion <= fub_awregion;
                        r_orig_awuser <= fub_awuser;
                        r_original_txn_id <= fub_awid;
                        r_consolidated_resp_status <= 2'b00;
                        r_consolidated_buser <= fub_awuser;

                        if (w_new_split_needed) begin
                            r_split_state <= SPLITTING;
                            r_current_addr <= w_next_boundary_addr;
                            r_current_len <= w_remaining_len_after_split;
                            r_split_count <= 8'd2;
                            r_expected_beats <= w_split_len + 1;
                            r_beat_counter <= '0;
                            r_data_splitting <= 1'b1;
                            r_expected_response_count <= 8'd2;
                            r_received_response_count <= '0;
                            r_waiting_for_responses <= 1'b1;
                        end else begin
                            r_expected_beats <= fub_awlen + 1;
                            r_beat_counter <= '0;
                            r_data_splitting <= 1'b0;
                            r_expected_response_count <= 8'd1;
                            r_received_response_count <= '0;
                            r_waiting_for_responses <= 1'b0;
                        end
                    end
                end

                SPLITTING: begin
                    if (m_axi_awvalid && m_axi_awready) begin
                        if (w_split_required) begin
                            r_current_addr <= w_next_boundary_addr;
                            r_current_len <= w_remaining_len_after_split;
                            r_split_count <= r_split_count + 8'd1;
                            r_expected_response_count <= r_expected_response_count + 8'd1;
                        end else begin
                            r_split_state <= IDLE;
                            r_split_count <= 8'd0;
                        end
                    end
                end

                default: r_split_state <= IDLE;
            endcase

            // Data beat counter
            if (m_axi_wvalid && m_axi_wready) begin
                r_beat_counter <= r_beat_counter + 1;
                if (w_split_boundary_reached) begin
                    r_beat_counter <= '0;
                    if (r_split_state == SPLITTING) begin
                        if (w_split_required)
                            r_expected_beats <= w_split_len + 1;
                        else
                            r_expected_beats <= w_current_len + 1;
                    end else begin
                        r_data_splitting <= 1'b0;
                    end
                end
            end

            // Response consolidation
            if (m_axi_bvalid && m_axi_bready) begin
                r_received_response_count <= r_received_response_count + 8'd1;
                if (m_axi_bresp > r_consolidated_resp_status)
                    r_consolidated_resp_status <= m_axi_bresp;
                if (r_received_response_count + 8'd1 >= r_expected_response_count) begin
                    r_waiting_for_responses <= 1'b0;
                    r_received_response_count <= '0;
                    r_expected_response_count <= '0;
                end
            end
        end
    )

    // AW channel - master side
    always_comb begin
        m_axi_awaddr = w_current_addr;
        m_axi_awlen = w_split_required ? w_split_len : w_current_len;

        if (r_split_state == IDLE) begin
            m_axi_awid = fub_awid;
            m_axi_awsize = fub_awsize;
            m_axi_awburst = fub_awburst;
            m_axi_awlock = fub_awlock;
            m_axi_awcache = fub_awcache;
            m_axi_awprot = fub_awprot;
            m_axi_awqos = fub_awqos;
            m_axi_awregion = fub_awregion;
            m_axi_awuser = fub_awuser;
        end else begin
            m_axi_awid = r_orig_awid;
            m_axi_awsize = r_orig_awsize;
            m_axi_awburst = r_orig_awburst;
            m_axi_awlock = r_orig_awlock;
            m_axi_awcache = r_orig_awcache;
            m_axi_awprot = r_orig_awprot;
            m_axi_awqos = r_orig_awqos;
            m_axi_awregion = r_orig_awregion;
            m_axi_awuser = r_orig_awuser;
        end

        case (r_split_state)
            IDLE: m_axi_awvalid = fub_awvalid;
            SPLITTING: m_axi_awvalid = 1'b1;
            default: m_axi_awvalid = 1'b0;
        endcase
    end

    // AW channel - slave side ready
    always_comb begin
        case (r_split_state)
            IDLE: begin
                if (w_new_split_needed)
                    fub_awready = 1'b0;
                else
                    fub_awready = m_axi_awready && !block_ready;
            end
            SPLITTING: begin
                fub_awready = w_is_final_split && m_axi_awready && !block_ready;
            end
            default: begin
                fub_awready = 1'b0;
            end
        endcase
    end

    // WLAST generation
    always_comb begin
        if (r_data_splitting)
            w_generate_wlast = fub_wvalid && w_split_boundary_reached;
        else
            w_generate_wlast = fub_wlast;
    end

    // W channel
    assign m_axi_wdata = fub_wdata;
    assign m_axi_wstrb = fub_wstrb;
    assign m_axi_wuser = fub_wuser;
    assign m_axi_wlast = w_generate_wlast;
    assign m_axi_wvalid = fub_wvalid;
    assign fub_wready = m_axi_wready;

    // B channel - response consolidation
    logic w_is_final_response;
    logic w_should_send_consolidated_response;

    assign w_is_final_response = (r_received_response_count + 8'd1 >= r_expected_response_count);
    assign w_should_send_consolidated_response = !r_waiting_for_responses || w_is_final_response;

    always_comb begin
        if (r_waiting_for_responses) begin
            fub_bid = r_original_txn_id;
            fub_bresp = w_is_final_response ? r_consolidated_resp_status : 2'b00;
            fub_buser = r_consolidated_buser;
            fub_bvalid = m_axi_bvalid && w_is_final_response;
            m_axi_bready = fub_bready || !w_is_final_response;
        end else begin
            fub_bid = m_axi_bid;
            fub_bresp = m_axi_bresp;
            fub_buser = m_axi_buser;
            fub_bvalid = m_axi_bvalid;
            m_axi_bready = fub_bready;
        end
    end

    // Split info FIFO
    logic [AW+IW+8-1:0] split_fifo_din;
    logic w_split_fifo_valid;

    assign w_split_fifo_valid = fub_awvalid && fub_awready;

    always_comb begin
        if (r_split_state == IDLE)
            split_fifo_din = {fub_awaddr, fub_awid,
                              w_new_split_needed ? 8'd2 : 8'd1};
        else
            split_fifo_din = {r_orig_awaddr, r_orig_awid, r_split_count};
    end

    gaxi_fifo_sync #(
        .REGISTERED (0),
        .DATA_WIDTH (AW + IW + 8),
        .DEPTH      (SPLIT_FIFO_DEPTH)
    ) inst_split_info_fifo (
        .axi_aclk    (aclk),
        .axi_aresetn (aresetn),
        .wr_valid    (w_split_fifo_valid),
        .wr_data     (split_fifo_din),
        .rd_ready    (fub_split_ready),
        .rd_valid    (fub_split_valid),
        .rd_data     ({fub_split_addr, fub_split_id, fub_split_cnt}),
        .wr_ready    (),
        .count       ()
    );

endmodule : axi_master_wr_splitter
