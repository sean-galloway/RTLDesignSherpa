// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: 2026 sean galloway

module formal_monitor_trans_cam_equiv (
    input logic clk,
    input logic rst_n
);
    localparam int DEPTH = 4;
    localparam int ID_WIDTH = 4;
    localparam int PAYLOAD_WIDTH = 16;

    (* anyseq *) reg clear;
    (* anyseq *) reg [ID_WIDTH-1:0] lookup_addr_id;
    (* anyseq *) reg [ID_WIDTH-1:0] lookup_data_id;
    (* anyseq *) reg [ID_WIDTH-1:0] lookup_resp_id;
    (* anyseq *) reg addr_wants_alloc;
    (* anyseq *) reg data_wants_alloc;
    (* anyseq *) reg resp_wants_alloc;
    (* anyseq *) reg [DEPTH-1:0] addr_alloc_mask;
    (* anyseq *) reg [DEPTH-1:0] data_alloc_mask;
    (* anyseq *) reg [DEPTH-1:0] resp_alloc_mask;
    (* anyseq *) reg [DEPTH-1:0] entry_we;
    (* anyseq *) reg [DEPTH-1:0] entry_valid_next;
    (* anyseq *) reg [DEPTH*ID_WIDTH-1:0] entry_id_flat;
    (* anyseq *) reg [DEPTH*PAYLOAD_WIDTH-1:0] entry_payload_flat;

    wire [DEPTH-1:0] d_addr_match, d_data_match, d_resp_match, d_data_first;
    wire [DEPTH-1:0] g_addr_match, g_data_match, g_resp_match, g_data_first;
    wire [DEPTH-1:0] d_free, g_free;
    wire [DEPTH-1:0] d_addr_alloc, d_data_alloc, d_resp_alloc;
    wire [DEPTH-1:0] g_addr_alloc, g_data_alloc, g_resp_alloc;
    wire [DEPTH-1:0] d_entry_valid, g_entry_valid;
    wire [DEPTH*ID_WIDTH-1:0] d_entry_id_flat, g_entry_id_flat;
    wire [DEPTH*PAYLOAD_WIDTH-1:0] d_entry_payload_flat, g_entry_payload_flat;

    monitor_trans_cam #(
        .DEPTH(DEPTH), .ID_WIDTH(ID_WIDTH), .PAYLOAD_WIDTH(PAYLOAD_WIDTH)
    ) dut (
        .clk(clk), .rst_n(rst_n), .clear(clear),
        .lookup_addr_id(lookup_addr_id), .lookup_data_id(lookup_data_id),
        .lookup_resp_id(lookup_resp_id),
        .addr_match_oh(d_addr_match), .data_match_oh(d_data_match),
        .resp_match_oh(d_resp_match), .data_match_first_oh(d_data_first),
        .free_oh(d_free),
        .addr_wants_alloc(addr_wants_alloc), .data_wants_alloc(data_wants_alloc),
        .resp_wants_alloc(resp_wants_alloc),
        .addr_alloc_mask(addr_alloc_mask), .data_alloc_mask(data_alloc_mask),
        .resp_alloc_mask(resp_alloc_mask),
        .addr_alloc_oh(d_addr_alloc), .data_alloc_oh(d_data_alloc),
        .resp_alloc_oh(d_resp_alloc), .entry_we(entry_we),
        .entry_valid_next(entry_valid_next), .entry_id_next(entry_id_flat),
        .entry_payload_next(entry_payload_flat), .entry_valid(d_entry_valid),
        .entry_id(d_entry_id_flat), .entry_payload(d_entry_payload_flat)
    );

    monitor_trans_cam_gold #(
        .DEPTH(DEPTH), .ID_WIDTH(ID_WIDTH), .PAYLOAD_WIDTH(PAYLOAD_WIDTH)
    ) gold (
        .clk(clk), .rst_n(rst_n), .clear(clear),
        .lookup_addr_id(lookup_addr_id), .lookup_data_id(lookup_data_id),
        .lookup_resp_id(lookup_resp_id),
        .addr_match_oh(g_addr_match), .data_match_oh(g_data_match),
        .resp_match_oh(g_resp_match), .data_match_first_oh(g_data_first),
        .free_oh(g_free),
        .addr_wants_alloc(addr_wants_alloc), .data_wants_alloc(data_wants_alloc),
        .resp_wants_alloc(resp_wants_alloc),
        .addr_alloc_mask(addr_alloc_mask), .data_alloc_mask(data_alloc_mask),
        .resp_alloc_mask(resp_alloc_mask),
        .addr_alloc_oh(g_addr_alloc), .data_alloc_oh(g_data_alloc),
        .resp_alloc_oh(g_resp_alloc), .entry_we(entry_we),
        .entry_valid_next(entry_valid_next), .entry_id_next(entry_id_flat),
        .entry_payload_next(entry_payload_flat), .entry_valid(g_entry_valid),
        .entry_id(g_entry_id_flat), .entry_payload(g_entry_payload_flat)
    );

    reg [7:0] f_past_valid = 0;
    always @(posedge clk)
        f_past_valid <= f_past_valid + (f_past_valid < 8'hFF);
    initial assume (!rst_n);
    always @(posedge clk) if (f_past_valid >= 2) assume (rst_n);

    always @(posedge clk) begin
        if (rst_n) begin
            ap_addr_match: assert (d_addr_match == g_addr_match);
            ap_data_match: assert (d_data_match == g_data_match);
            ap_resp_match: assert (d_resp_match == g_resp_match);
            ap_data_first: assert (d_data_first == g_data_first);
            ap_free: assert (d_free == g_free);
            ap_addr_alloc: assert (d_addr_alloc == g_addr_alloc);
            ap_data_alloc: assert (d_data_alloc == g_data_alloc);
            ap_resp_alloc: assert (d_resp_alloc == g_resp_alloc);
            ap_entry_valid: assert (d_entry_valid == g_entry_valid);
            ap_entry_id: assert (d_entry_id_flat == g_entry_id_flat);
            ap_entry_payload: assert (d_entry_payload_flat == g_entry_payload_flat);
        end
    end
endmodule
