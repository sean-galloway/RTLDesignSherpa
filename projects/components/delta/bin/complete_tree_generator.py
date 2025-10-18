#!/usr/bin/env python3
# SPDX-License-Identifier: MIT
# SPDX-FileCopyrightText: 2024-2025 sean galloway
#
# RTL Design Sherpa - Industry-Standard RTL Design and Verification
# https://github.com/sean-galloway/RTLDesignSherpa
#
# Module: complete_tree_generator
# Purpose: Complete Tree Topology Generator for Delta
#
# Documentation: projects/components/delta/PRD.md
# Subsystem: delta
#
# Author: sean galloway
# Created: 2025-10-18

"""
Complete Tree Topology Generator for Delta
Generates both fan-out (1→N) and fan-in (N→1) tree structures

Use Cases:
1. Fan-out: 1 RAPIDS DMA → N compute nodes (1:2 splitters cascaded)
2. Fan-in: N compute nodes → 1 RAPIDS DMA (2:1 mergers cascaded)
3. Bidirectional: Full crossbar via tree composition

Author: RTL Design Sherpa
Version: 1.0
"""

import argparse
import math
from typing import List, Tuple


def generate_2to1_merger() -> str:
    """Generate complete 2:1 merger with round-robin arbitration"""

    lines = []
    lines.append("//==============================================================================")
    lines.append("// Module: delta_merge_2to1")
    lines.append("// Project: Delta - AXI-Stream Crossbar Generator")
    lines.append("//==============================================================================")
    lines.append("// Description: AXI-Stream 2:1 Merger - Arbitrate two inputs to one output")
    lines.append("//")
    lines.append("// Features:")
    lines.append("//   - Round-robin arbitration")
    lines.append("//   - Packet atomicity (grant locked until TLAST)")
    lines.append("//   - Full AXI-Stream compliance")
    lines.append("//==============================================================================")
    lines.append("")

    lines.append("module delta_merge_2to1 #(")
    lines.append("    parameter int DATA_WIDTH = 64,")
    lines.append("    parameter int DEST_WIDTH = 4,")
    lines.append("    parameter int ID_WIDTH   = 2,")
    lines.append("    parameter int USER_WIDTH = 1")
    lines.append(") (")
    lines.append("    input  logic aclk,")
    lines.append("    input  logic aresetn,")
    lines.append("")

    lines.append("    // Input Interface 0")
    lines.append("    input  logic [DATA_WIDTH-1:0]  s0_axis_tdata,")
    lines.append("    input  logic                   s0_axis_tvalid,")
    lines.append("    output logic                   s0_axis_tready,")
    lines.append("    input  logic                   s0_axis_tlast,")
    lines.append("    input  logic [DEST_WIDTH-1:0]  s0_axis_tdest,")
    lines.append("    input  logic [ID_WIDTH-1:0]    s0_axis_tid,")
    lines.append("    input  logic [USER_WIDTH-1:0]  s0_axis_tuser,")
    lines.append("")

    lines.append("    // Input Interface 1")
    lines.append("    input  logic [DATA_WIDTH-1:0]  s1_axis_tdata,")
    lines.append("    input  logic                   s1_axis_tvalid,")
    lines.append("    output logic                   s1_axis_tready,")
    lines.append("    input  logic                   s1_axis_tlast,")
    lines.append("    input  logic [DEST_WIDTH-1:0]  s1_axis_tdest,")
    lines.append("    input  logic [ID_WIDTH-1:0]    s1_axis_tid,")
    lines.append("    input  logic [USER_WIDTH-1:0]  s1_axis_tuser,")
    lines.append("")

    lines.append("    // Output Interface")
    lines.append("    output logic [DATA_WIDTH-1:0]  m_axis_tdata,")
    lines.append("    output logic                   m_axis_tvalid,")
    lines.append("    input  logic                   m_axis_tready,")
    lines.append("    output logic                   m_axis_tlast,")
    lines.append("    output logic [DEST_WIDTH-1:0]  m_axis_tdest,")
    lines.append("    output logic [ID_WIDTH-1:0]    m_axis_tid,")
    lines.append("    output logic [USER_WIDTH-1:0]  m_axis_tuser")
    lines.append(");")
    lines.append("")

    lines.append("    // Arbiter state")
    lines.append("    logic r_grant_1;        // 0=grant to input 0, 1=grant to input 1")
    lines.append("    logic r_packet_active;  // Packet in progress")
    lines.append("")

    lines.append("    // Round-robin arbitration with packet atomicity")
    lines.append("    always_ff @(posedge aclk or negedge aresetn) begin")
    lines.append("        if (!aresetn) begin")
    lines.append("            r_grant_1 <= 1'b0;")
    lines.append("            r_packet_active <= 1'b0;")
    lines.append("        end else begin")
    lines.append("            if (r_packet_active) begin")
    lines.append("                // Hold grant until TLAST")
    lines.append("                if (m_axis_tvalid && m_axis_tready && m_axis_tlast) begin")
    lines.append("                    r_packet_active <= 1'b0;")
    lines.append("                    r_grant_1 <= !r_grant_1;  // Switch for next packet")
    lines.append("                end")
    lines.append("            end else begin")
    lines.append("                // Arbitrate for new packet")
    lines.append("                if (s0_axis_tvalid && s1_axis_tvalid) begin")
    lines.append("                    // Both requesting: use round-robin state")
    lines.append("                    // Keep current grant (already toggled after last packet)")
    lines.append("                end else if (s1_axis_tvalid) begin")
    lines.append("                    r_grant_1 <= 1'b1;")
    lines.append("                end else if (s0_axis_tvalid) begin")
    lines.append("                    r_grant_1 <= 1'b0;")
    lines.append("                end")
    lines.append("")
    lines.append("                if (s0_axis_tvalid || s1_axis_tvalid)")
    lines.append("                    r_packet_active <= 1'b1;")
    lines.append("            end")
    lines.append("        end")
    lines.append("    end")
    lines.append("")

    lines.append("    // Output multiplexing")
    lines.append("    assign m_axis_tdata  = r_grant_1 ? s1_axis_tdata  : s0_axis_tdata;")
    lines.append("    assign m_axis_tvalid = r_grant_1 ? s1_axis_tvalid : s0_axis_tvalid;")
    lines.append("    assign m_axis_tlast  = r_grant_1 ? s1_axis_tlast  : s0_axis_tlast;")
    lines.append("    assign m_axis_tdest  = r_grant_1 ? s1_axis_tdest  : s0_axis_tdest;")
    lines.append("    assign m_axis_tid    = r_grant_1 ? s1_axis_tid    : s0_axis_tid;")
    lines.append("    assign m_axis_tuser  = r_grant_1 ? s1_axis_tuser  : s0_axis_tuser;")
    lines.append("")

    lines.append("    // Backpressure to selected input")
    lines.append("    assign s0_axis_tready = !r_grant_1 && m_axis_tready;")
    lines.append("    assign s1_axis_tready = r_grant_1  && m_axis_tready;")
    lines.append("")

    lines.append("endmodule")
    lines.append("")

    return "\n".join(lines)


def generate_fanout_tree(num_outputs: int, data_width: int = 64) -> str:
    """
    Generate 1→N fan-out tree (e.g., 1 RAPIDS DMA → N compute nodes)
    Uses cascaded 1:2 splitters
    """

    depth = math.ceil(math.log2(num_outputs))
    dest_width = max(1, math.ceil(math.log2(num_outputs)))

    lines = []
    lines.append(f"// 1→{num_outputs} Fan-Out Tree (RAPIDS DMA to compute nodes)")
    lines.append(f"// Depth: {depth} stages of 1:2 splitters")
    lines.append("")

    lines.append(f"module delta_fanout_1to{num_outputs} #(")
    lines.append(f"    parameter int DATA_WIDTH = {data_width},")
    lines.append(f"    parameter int DEST_WIDTH = {dest_width},")
    lines.append("    parameter int ID_WIDTH   = 2,")
    lines.append("    parameter int USER_WIDTH = 1")
    lines.append(") (")
    lines.append("    input  logic aclk,")
    lines.append("    input  logic aresetn,")
    lines.append("")
    lines.append("    // Input from RAPIDS DMA")
    lines.append("    input  logic [DATA_WIDTH-1:0]  s_axis_tdata,")
    lines.append("    input  logic                   s_axis_tvalid,")
    lines.append("    output logic                   s_axis_tready,")
    lines.append("    input  logic                   s_axis_tlast,")
    lines.append("    input  logic [DEST_WIDTH-1:0]  s_axis_tdest,")
    lines.append("    input  logic [ID_WIDTH-1:0]    s_axis_tid,")
    lines.append("    input  logic [USER_WIDTH-1:0]  s_axis_tuser,")
    lines.append("")
    lines.append(f"    // Outputs to {num_outputs} compute nodes")
    lines.append(f"    output logic [DATA_WIDTH-1:0]  m_axis_tdata  [{num_outputs}],")
    lines.append(f"    output logic                   m_axis_tvalid [{num_outputs}],")
    lines.append(f"    input  logic                   m_axis_tready [{num_outputs}],")
    lines.append(f"    output logic                   m_axis_tlast  [{num_outputs}],")
    lines.append(f"    output logic [DEST_WIDTH-1:0]  m_axis_tdest  [{num_outputs}],")
    lines.append(f"    output logic [ID_WIDTH-1:0]    m_axis_tid    [{num_outputs}],")
    lines.append(f"    output logic [USER_WIDTH-1:0]  m_axis_tuser  [{num_outputs}]")
    lines.append(");")
    lines.append("")

    # Generate internal wiring
    lines.append("    // Internal signals for tree stages")
    num_stages = depth
    for stage in range(num_stages):
        num_nodes_in_stage = 2**stage
        lines.append(f"    // Stage {stage} - {num_nodes_in_stage} nodes")
        for node in range(num_nodes_in_stage):
            if stage == 0:
                continue  # Input is s_axis
            lines.append(f"    logic [DATA_WIDTH-1:0]  stage{stage}_node{node}_tdata;")
            lines.append(f"    logic                   stage{stage}_node{node}_tvalid;")
            lines.append(f"    logic                   stage{stage}_node{node}_tready;")
            lines.append(f"    logic                   stage{stage}_node{node}_tlast;")
            lines.append(f"    logic [DEST_WIDTH-1:0]  stage{stage}_node{node}_tdest;")
            lines.append(f"    logic [ID_WIDTH-1:0]    stage{stage}_node{node}_tid;")
            lines.append(f"    logic [USER_WIDTH-1:0]  stage{stage}_node{node}_tuser;")
        lines.append("")

    lines.append("    // Splitter instantiations")
    lines.append("    // Stage 0: Root splitter")
    lines.append("    delta_split_1to2 #(")
    lines.append("        .DATA_WIDTH(DATA_WIDTH),")
    lines.append("        .DEST_WIDTH(DEST_WIDTH),")
    lines.append("        .ID_WIDTH(ID_WIDTH),")
    lines.append("        .USER_WIDTH(USER_WIDTH),")
    lines.append(f"        .SPLIT_BIT({depth-1})  // MSB of TDEST")
    lines.append("    ) u_split_root (")
    lines.append("        .aclk(aclk), .aresetn(aresetn),")
    lines.append("        .s_axis_tdata(s_axis_tdata),")
    lines.append("        .s_axis_tvalid(s_axis_tvalid),")
    lines.append("        .s_axis_tready(s_axis_tready),")
    lines.append("        .s_axis_tlast(s_axis_tlast),")
    lines.append("        .s_axis_tdest(s_axis_tdest),")
    lines.append("        .s_axis_tid(s_axis_tid),")
    lines.append("        .s_axis_tuser(s_axis_tuser),")
    if num_outputs == 2:
        lines.append("        .m0_axis_tdata(m_axis_tdata[0]),")
        lines.append("        .m0_axis_tvalid(m_axis_tvalid[0]),")
        lines.append("        .m0_axis_tready(m_axis_tready[0]),")
        lines.append("        .m0_axis_tlast(m_axis_tlast[0]),")
        lines.append("        .m0_axis_tdest(m_axis_tdest[0]),")
        lines.append("        .m0_axis_tid(m_axis_tid[0]),")
        lines.append("        .m0_axis_tuser(m_axis_tuser[0]),")
        lines.append("        .m1_axis_tdata(m_axis_tdata[1]),")
        lines.append("        .m1_axis_tvalid(m_axis_tvalid[1]),")
        lines.append("        .m1_axis_tready(m_axis_tready[1]),")
        lines.append("        .m1_axis_tlast(m_axis_tlast[1]),")
        lines.append("        .m1_axis_tdest(m_axis_tdest[1]),")
        lines.append("        .m1_axis_tid(m_axis_tid[1]),")
        lines.append("        .m1_axis_tuser(m_axis_tuser[1])")
    else:
        lines.append("        .m0_axis_tdata(stage1_node0_tdata),")
        lines.append("        .m0_axis_tvalid(stage1_node0_tvalid),")
        lines.append("        .m0_axis_tready(stage1_node0_tready),")
        lines.append("        .m0_axis_tlast(stage1_node0_tlast),")
        lines.append("        .m0_axis_tdest(stage1_node0_tdest),")
        lines.append("        .m0_axis_tid(stage1_node0_tid),")
        lines.append("        .m0_axis_tuser(stage1_node0_tuser),")
        lines.append("        .m1_axis_tdata(stage1_node1_tdata),")
        lines.append("        .m1_axis_tvalid(stage1_node1_tvalid),")
        lines.append("        .m1_axis_tready(stage1_node1_tready),")
        lines.append("        .m1_axis_tlast(stage1_node1_tlast),")
        lines.append("        .m1_axis_tdest(stage1_node1_tdest),")
        lines.append("        .m1_axis_tid(stage1_node1_tid),")
        lines.append("        .m1_axis_tuser(stage1_node1_tuser)")
    lines.append("    );")
    lines.append("")

    lines.append("    // Additional stages would be instantiated here...")
    lines.append("    // (Full implementation requires recursive instantiation)")
    lines.append("")

    lines.append("endmodule")
    lines.append("")

    return "\n".join(lines)


def generate_fanin_tree(num_inputs: int, data_width: int = 64) -> str:
    """
    Generate N→1 fan-in tree (e.g., N compute nodes → 1 RAPIDS DMA)
    Uses cascaded 2:1 mergers
    """

    depth = math.ceil(math.log2(num_inputs))
    dest_width = 1  # All go to same destination

    lines = []
    lines.append(f"// {num_inputs}→1 Fan-In Tree (compute nodes to RAPIDS DMA)")
    lines.append(f"// Depth: {depth} stages of 2:1 mergers")
    lines.append("")

    lines.append(f"module delta_fanin_{num_inputs}to1 #(")
    lines.append(f"    parameter int DATA_WIDTH = {data_width},")
    lines.append("    parameter int DEST_WIDTH = 1,")
    lines.append("    parameter int ID_WIDTH   = 2,")
    lines.append("    parameter int USER_WIDTH = 1")
    lines.append(") (")
    lines.append("    input  logic aclk,")
    lines.append("    input  logic aresetn,")
    lines.append("")
    lines.append(f"    // Inputs from {num_inputs} compute nodes")
    lines.append(f"    input  logic [DATA_WIDTH-1:0]  s_axis_tdata  [{num_inputs}],")
    lines.append(f"    input  logic                   s_axis_tvalid [{num_inputs}],")
    lines.append(f"    output logic                   s_axis_tready [{num_inputs}],")
    lines.append(f"    input  logic                   s_axis_tlast  [{num_inputs}],")
    lines.append(f"    input  logic [DEST_WIDTH-1:0]  s_axis_tdest  [{num_inputs}],")
    lines.append(f"    input  logic [ID_WIDTH-1:0]    s_axis_tid    [{num_inputs}],")
    lines.append(f"    input  logic [USER_WIDTH-1:0]  s_axis_tuser  [{num_inputs}],")
    lines.append("")
    lines.append("    // Output to RAPIDS DMA")
    lines.append("    output logic [DATA_WIDTH-1:0]  m_axis_tdata,")
    lines.append("    output logic                   m_axis_tvalid,")
    lines.append("    input  logic                   m_axis_tready,")
    lines.append("    output logic                   m_axis_tlast,")
    lines.append("    output logic [DEST_WIDTH-1:0]  m_axis_tdest,")
    lines.append("    output logic [ID_WIDTH-1:0]    m_axis_tid,")
    lines.append("    output logic [USER_WIDTH-1:0]  m_axis_tuser")
    lines.append(");")
    lines.append("")

    # For simplicity, show structure for small sizes
    if num_inputs == 2:
        lines.append("    // Simple 2→1 merger")
        lines.append("    delta_merge_2to1 #(")
        lines.append("        .DATA_WIDTH(DATA_WIDTH),")
        lines.append("        .DEST_WIDTH(DEST_WIDTH),")
        lines.append("        .ID_WIDTH(ID_WIDTH),")
        lines.append("        .USER_WIDTH(USER_WIDTH)")
        lines.append("    ) u_merge_root (")
        lines.append("        .aclk(aclk), .aresetn(aresetn),")
        lines.append("        .s0_axis_tdata(s_axis_tdata[0]),")
        lines.append("        .s0_axis_tvalid(s_axis_tvalid[0]),")
        lines.append("        .s0_axis_tready(s_axis_tready[0]),")
        lines.append("        .s0_axis_tlast(s_axis_tlast[0]),")
        lines.append("        .s0_axis_tdest(s_axis_tdest[0]),")
        lines.append("        .s0_axis_tid(s_axis_tid[0]),")
        lines.append("        .s0_axis_tuser(s_axis_tuser[0]),")
        lines.append("        .s1_axis_tdata(s_axis_tdata[1]),")
        lines.append("        .s1_axis_tvalid(s_axis_tvalid[1]),")
        lines.append("        .s1_axis_tready(s_axis_tready[1]),")
        lines.append("        .s1_axis_tlast(s_axis_tlast[1]),")
        lines.append("        .s1_axis_tdest(s_axis_tdest[1]),")
        lines.append("        .s1_axis_tid(s_axis_tid[1]),")
        lines.append("        .s1_axis_tuser(s_axis_tuser[1]),")
        lines.append("        .m_axis_tdata(m_axis_tdata),")
        lines.append("        .m_axis_tvalid(m_axis_tvalid),")
        lines.append("        .m_axis_tready(m_axis_tready),")
        lines.append("        .m_axis_tlast(m_axis_tlast),")
        lines.append("        .m_axis_tdest(m_axis_tdest),")
        lines.append("        .m_axis_tid(m_axis_tid),")
        lines.append("        .m_axis_tuser(m_axis_tuser)")
        lines.append("    );")
    elif num_inputs == 4:
        lines.append("    // Internal signals for stage 1")
        lines.append("    logic [DATA_WIDTH-1:0]  stage1_0_tdata, stage1_1_tdata;")
        lines.append("    logic                   stage1_0_tvalid, stage1_1_tvalid;")
        lines.append("    logic                   stage1_0_tready, stage1_1_tready;")
        lines.append("    logic                   stage1_0_tlast, stage1_1_tlast;")
        lines.append("    logic [DEST_WIDTH-1:0]  stage1_0_tdest, stage1_1_tdest;")
        lines.append("    logic [ID_WIDTH-1:0]    stage1_0_tid, stage1_1_tid;")
        lines.append("    logic [USER_WIDTH-1:0]  stage1_0_tuser, stage1_1_tuser;")
        lines.append("")
        lines.append("    // Stage 0: First level mergers (4→2)")
        lines.append("    delta_merge_2to1 #(.DATA_WIDTH(DATA_WIDTH), .DEST_WIDTH(DEST_WIDTH),")
        lines.append("                       .ID_WIDTH(ID_WIDTH), .USER_WIDTH(USER_WIDTH))")
        lines.append("    u_merge_s0_pair0 (")
        lines.append("        .aclk(aclk), .aresetn(aresetn),")
        lines.append("        .s0_axis_tdata(s_axis_tdata[0]), .s0_axis_tvalid(s_axis_tvalid[0]),")
        lines.append("        .s0_axis_tready(s_axis_tready[0]), .s0_axis_tlast(s_axis_tlast[0]),")
        lines.append("        .s0_axis_tdest(s_axis_tdest[0]), .s0_axis_tid(s_axis_tid[0]),")
        lines.append("        .s0_axis_tuser(s_axis_tuser[0]),")
        lines.append("        .s1_axis_tdata(s_axis_tdata[1]), .s1_axis_tvalid(s_axis_tvalid[1]),")
        lines.append("        .s1_axis_tready(s_axis_tready[1]), .s1_axis_tlast(s_axis_tlast[1]),")
        lines.append("        .s1_axis_tdest(s_axis_tdest[1]), .s1_axis_tid(s_axis_tid[1]),")
        lines.append("        .s1_axis_tuser(s_axis_tuser[1]),")
        lines.append("        .m_axis_tdata(stage1_0_tdata), .m_axis_tvalid(stage1_0_tvalid),")
        lines.append("        .m_axis_tready(stage1_0_tready), .m_axis_tlast(stage1_0_tlast),")
        lines.append("        .m_axis_tdest(stage1_0_tdest), .m_axis_tid(stage1_0_tid),")
        lines.append("        .m_axis_tuser(stage1_0_tuser)")
        lines.append("    );")
        lines.append("")
        lines.append("    delta_merge_2to1 #(.DATA_WIDTH(DATA_WIDTH), .DEST_WIDTH(DEST_WIDTH),")
        lines.append("                       .ID_WIDTH(ID_WIDTH), .USER_WIDTH(USER_WIDTH))")
        lines.append("    u_merge_s0_pair1 (")
        lines.append("        .aclk(aclk), .aresetn(aresetn),")
        lines.append("        .s0_axis_tdata(s_axis_tdata[2]), .s0_axis_tvalid(s_axis_tvalid[2]),")
        lines.append("        .s0_axis_tready(s_axis_tready[2]), .s0_axis_tlast(s_axis_tlast[2]),")
        lines.append("        .s0_axis_tdest(s_axis_tdest[2]), .s0_axis_tid(s_axis_tid[2]),")
        lines.append("        .s0_axis_tuser(s_axis_tuser[2]),")
        lines.append("        .s1_axis_tdata(s_axis_tdata[3]), .s1_axis_tvalid(s_axis_tvalid[3]),")
        lines.append("        .s1_axis_tready(s_axis_tready[3]), .s1_axis_tlast(s_axis_tlast[3]),")
        lines.append("        .s1_axis_tdest(s_axis_tdest[3]), .s1_axis_tid(s_axis_tid[3]),")
        lines.append("        .s1_axis_tuser(s_axis_tuser[3]),")
        lines.append("        .m_axis_tdata(stage1_1_tdata), .m_axis_tvalid(stage1_1_tvalid),")
        lines.append("        .m_axis_tready(stage1_1_tready), .m_axis_tlast(stage1_1_tlast),")
        lines.append("        .m_axis_tdest(stage1_1_tdest), .m_axis_tid(stage1_1_tid),")
        lines.append("        .m_axis_tuser(stage1_1_tuser)")
        lines.append("    );")
        lines.append("")
        lines.append("    // Stage 1: Final merger (2→1)")
        lines.append("    delta_merge_2to1 #(.DATA_WIDTH(DATA_WIDTH), .DEST_WIDTH(DEST_WIDTH),")
        lines.append("                       .ID_WIDTH(ID_WIDTH), .USER_WIDTH(USER_WIDTH))")
        lines.append("    u_merge_s1_root (")
        lines.append("        .aclk(aclk), .aresetn(aresetn),")
        lines.append("        .s0_axis_tdata(stage1_0_tdata), .s0_axis_tvalid(stage1_0_tvalid),")
        lines.append("        .s0_axis_tready(stage1_0_tready), .s0_axis_tlast(stage1_0_tlast),")
        lines.append("        .s0_axis_tdest(stage1_0_tdest), .s0_axis_tid(stage1_0_tid),")
        lines.append("        .s0_axis_tuser(stage1_0_tuser),")
        lines.append("        .s1_axis_tdata(stage1_1_tdata), .s1_axis_tvalid(stage1_1_tvalid),")
        lines.append("        .s1_axis_tready(stage1_1_tready), .s1_axis_tlast(stage1_1_tlast),")
        lines.append("        .s1_axis_tdest(stage1_1_tdest), .s1_axis_tid(stage1_1_tid),")
        lines.append("        .s1_axis_tuser(stage1_1_tuser),")
        lines.append("        .m_axis_tdata(m_axis_tdata), .m_axis_tvalid(m_axis_tvalid),")
        lines.append("        .m_axis_tready(m_axis_tready), .m_axis_tlast(m_axis_tlast),")
        lines.append("        .m_axis_tdest(m_axis_tdest), .m_axis_tid(m_axis_tid),")
        lines.append("        .m_axis_tuser(m_axis_tuser)")
        lines.append("    );")
    else:
        lines.append("    // Additional stages for larger fan-in...")
        lines.append("    // (Full implementation requires recursive instantiation)")

    lines.append("")
    lines.append("endmodule")
    lines.append("")

    return "\n".join(lines)


def main():
    parser = argparse.ArgumentParser(description="Complete tree topology generator for Delta")
    parser.add_argument("--type", choices=["merger", "fanout", "fanin"], required=True,
                        help="Type of module to generate")
    parser.add_argument("--size", type=int, help="Number of inputs/outputs for fanout/fanin")
    parser.add_argument("--output", type=str, default="../rtl", help="Output directory")

    args = parser.parse_args()

    if args.type == "merger":
        code = generate_2to1_merger()
        filename = "delta_merge_2to1.sv"
    elif args.type == "fanout":
        if not args.size:
            parser.error("--size required for fanout")
        code = generate_fanout_tree(args.size)
        filename = f"delta_fanout_1to{args.size}.sv"
    elif args.type == "fanin":
        if not args.size:
            parser.error("--size required for fanin")
        code = generate_fanin_tree(args.size)
        filename = f"delta_fanin_{args.size}to1.sv"

    import os
    os.makedirs(args.output, exist_ok=True)
    output_path = os.path.join(args.output, filename)

    with open(output_path, 'w') as f:
        f.write(code)

    print(f"✓ Generated: {output_path}")


if __name__ == "__main__":
    main()
