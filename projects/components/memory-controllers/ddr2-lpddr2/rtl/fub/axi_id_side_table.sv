// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: 2024-2026 sean galloway
//
// Module: axi_id_side_table
// Purpose: Per-AXI-ID metadata side-table. Captures the AXI4 attribute
//          fields (user/cache/prot/qos/region/size/burst) at the host
//          AW / AR handshake and replays them at completion time on
//          the B / R channels (BUSER mirrors AWUSER, RUSER mirrors
//          ARUSER per the AXI4 contract), and exposes QoS for downstream
//          scheduling.
//
//          Originally lived inline in axi_intake (F2). Extracted into
//          its own FUB (F4) so the QoS lookups consumed by the
//          scheduler are visible at the macro boundary.
//
//          Storage: 2 * 2**IW rows of axi_meta_t (UW + 23 bits each).
//          For IW=4 / UW=1, that's 32 rows of 24 bits ≈ 96 distributed
//          flops — small enough to leave in distributed RAM.
//
//          Reads are combinational; the scheduler / B-FIFO snoop the
//          table directly by ID. Writes happen on the AW/AR accept
//          handshake.

`timescale 1ns / 1ps

`include "reset_defs.svh"

module axi_id_side_table
    import ddr2_lpddr2_pkg::*;
#(
    parameter int AXI_ID_WIDTH   = 4,
    parameter int AXI_USER_WIDTH = 1,
    // aliases
    parameter int IW = AXI_ID_WIDTH,
    parameter int UW = AXI_USER_WIDTH
) (
    input  logic            aclk,
    input  logic            aresetn,

    //=========================================================================
    // Write ports — captured at host-side AW / AR accept handshake.
    //=========================================================================
    input  logic            aw_we_i,
    input  logic [IW-1:0]   aw_id_i,
    input  logic [UW-1:0]   aw_user_i,
    input  logic [3:0]      aw_cache_i,
    input  logic [2:0]      aw_prot_i,
    input  logic [3:0]      aw_qos_i,
    input  logic [3:0]      aw_region_i,
    input  logic [2:0]      aw_size_i,
    input  logic [1:0]      aw_burst_i,

    input  logic            ar_we_i,
    input  logic [IW-1:0]   ar_id_i,
    input  logic [UW-1:0]   ar_user_i,
    input  logic [3:0]      ar_cache_i,
    input  logic [2:0]      ar_prot_i,
    input  logic [3:0]      ar_qos_i,
    input  logic [3:0]      ar_region_i,
    input  logic [2:0]      ar_size_i,
    input  logic [1:0]      ar_burst_i,

    //=========================================================================
    // Lookup ports — combinational reads.
    //   *_push_* — used at aw_push / ar_push handshake to forward QoS
    //              into the downstream CAM (for QoS-aware scheduling).
    //   *_compl_* — used at B FIFO push / R-emit to echo USER back per
    //               the AXI4 contract.
    // Two read ports per side because the two consumers fire on
    // independent handshakes and can collide same-cycle.
    //=========================================================================
    input  logic [IW-1:0]   aw_push_id_i,
    output logic [3:0]      aw_push_qos_o,

    input  logic [IW-1:0]   aw_compl_id_i,
    output logic [UW-1:0]   aw_compl_user_o,

    input  logic [IW-1:0]   ar_push_id_i,
    output logic [3:0]      ar_push_qos_o,

    input  logic [IW-1:0]   ar_compl_id_i,
    output logic [UW-1:0]   ar_compl_user_o,

    //=========================================================================
    // obs_* (future CSR readout)
    //=========================================================================
    output logic [15:0]     obs_aw_writes_o,
    output logic [15:0]     obs_ar_writes_o
);

    localparam int ID_TAB_DEPTH = 1 << IW;

    typedef struct packed {
        logic [UW-1:0] user;
        logic [3:0]    cache;
        logic [2:0]    prot;
        logic [3:0]    qos;
        logic [3:0]    region;
        logic [2:0]    size;
        logic [1:0]    burst;
    } axi_meta_t;

    axi_meta_t r_aw_tab [0:ID_TAB_DEPTH-1];
    axi_meta_t r_ar_tab [0:ID_TAB_DEPTH-1];

    logic [15:0] r_aw_writes;
    logic [15:0] r_ar_writes;

    `ALWAYS_FF_RST(aclk, aresetn, begin
        if (`RST_ASSERTED(aresetn)) begin
            r_aw_writes <= 16'd0;
            r_ar_writes <= 16'd0;
        end else begin
            if (aw_we_i) begin
                r_aw_tab[aw_id_i].user   <= aw_user_i;
                r_aw_tab[aw_id_i].cache  <= aw_cache_i;
                r_aw_tab[aw_id_i].prot   <= aw_prot_i;
                r_aw_tab[aw_id_i].qos    <= aw_qos_i;
                r_aw_tab[aw_id_i].region <= aw_region_i;
                r_aw_tab[aw_id_i].size   <= aw_size_i;
                r_aw_tab[aw_id_i].burst  <= aw_burst_i;
                r_aw_writes <= r_aw_writes + 16'd1;
            end
            if (ar_we_i) begin
                r_ar_tab[ar_id_i].user   <= ar_user_i;
                r_ar_tab[ar_id_i].cache  <= ar_cache_i;
                r_ar_tab[ar_id_i].prot   <= ar_prot_i;
                r_ar_tab[ar_id_i].qos    <= ar_qos_i;
                r_ar_tab[ar_id_i].region <= ar_region_i;
                r_ar_tab[ar_id_i].size   <= ar_size_i;
                r_ar_tab[ar_id_i].burst  <= ar_burst_i;
                r_ar_writes <= r_ar_writes + 16'd1;
            end
        end
    end)

    assign aw_push_qos_o   = r_aw_tab[aw_push_id_i].qos;
    assign aw_compl_user_o = r_aw_tab[aw_compl_id_i].user;
    assign ar_push_qos_o   = r_ar_tab[ar_push_id_i].qos;
    assign ar_compl_user_o = r_ar_tab[ar_compl_id_i].user;

    assign obs_aw_writes_o = r_aw_writes;
    assign obs_ar_writes_o = r_ar_writes;

endmodule : axi_id_side_table
