#!/usr/bin/env python3
# SPDX-License-Identifier: MIT
# SPDX-FileCopyrightText: 2024-2025 sean galloway
#
# RTL Design Sherpa - Industry-Standard RTL Design and Verification
# https://github.com/sean-galloway/RTLDesignSherpa
#
# Module: BridgeResponseRouter
# Purpose: Response routing and ID tracking for B and R channels
#
# Author: sean galloway
# Created: 2025-10-26

"""
Response Routing for Bridge Generator

Handles:
- Transaction ID tables (write and read)
- B channel demuxing (write response)
- R channel demuxing (read data/response)

Current Implementation: Distributed RAM ID tables
Future Enhancement: CAM-based tracking for better out-of-order performance
"""

import sys
import math
from pathlib import Path

# Import the framework
sys.path.insert(0, str(Path(__file__).resolve().parents[4] / 'bin'))
from rtl_generators.verilog.module import Module


class BridgeResponseRouter:
    """
    Response Routing for Bridge Crossbar

    Routes responses back to originating masters using ID tracking:
    - ID tables map {slave, transaction_id} → master_index
    - B channel: Single-beat write response
    - R channel: Burst-aware read response (multiple beats per transaction)

    NOTE: Current implementation uses distributed RAM for ID tracking.
    For high-performance out-of-order scenarios, consider CAM-based tracking:
    - See cam_tag.sv or cam_tag_perf.sv for CAM implementation
    - CAM provides: transaction counting, ID reuse detection, performance monitoring
    """

    def __init__(self, module: Module, config):
        """
        Initialize response router

        Args:
            module: Module instance for RTL generation
            config: BridgeConfig with topology and ID width
        """
        self.module = module
        self.cfg = config

    def generate_id_tables(self):
        """
        Generate transaction ID tracking tables

        Purpose: Map {slave_index, transaction_id} → master_index for response routing

        Implementation: Distributed RAM (simple, suitable for small ID_WIDTH)
        - write_id_table: Maps AW transactions to master for B response routing
        - read_id_table: Maps AR transactions to master for R response routing

        Table updates:
        - Written on AW/AR handshake completion
        - Read on B/R response arrival
        - Cleared implicitly on overwrite (ID reuse)

        NOTE: For advanced out-of-order tracking, consider CAM-based approach:
        - CAM tracks outstanding transaction count per master/slave pair
        - Detects ID exhaustion and provides backpressure
        - Enables performance monitoring (latency, throughput)
        - See cam_tag.sv or cam_tag_perf.sv for reference
        """
        self.module.comment("==========================================================================")
        self.module.comment("Transaction ID Tracking Tables")
        self.module.comment("==========================================================================")
        self.module.comment("Purpose: Enable ID-based response routing (out-of-order support)")
        self.module.comment("")
        self.module.comment("Structure: Distributed RAM")
        self.module.comment(f"  - {self.cfg.num_slaves} slaves × 2 tables (write, read)")
        self.module.comment(f"  - 2^{self.cfg.id_width} = {2**self.cfg.id_width} entries per table")
        self.module.comment(f"  - Each entry: $clog2({self.cfg.num_masters}) = {math.ceil(math.log2(self.cfg.num_masters))} bits (master index)")
        self.module.comment("")
        self.module.comment("Write ID Table: Stores master index for AW transactions → B routing")
        self.module.comment("Read ID Table:  Stores master index for AR transactions → R routing")
        self.module.comment("")
        self.module.comment("ENHANCEMENT OPPORTUNITY: Replace with CAM for better out-of-order performance:")
        self.module.comment("  - Track outstanding transaction counts")
        self.module.comment("  - Detect ID exhaustion and provide backpressure")
        self.module.comment("  - Enable performance monitoring (latency, throughput)")
        self.module.comment("  - See cam_tag.sv or cam_tag_perf.sv for CAM implementation")
        self.module.comment("==========================================================================")
        self.module.instruction("")

        # Declare ID tables
        master_bits = f"$clog2(NUM_MASTERS)" if self.cfg.num_masters > 1 else "0"
        self.module.instruction(f"// Transaction ID tables: [slave][transaction_id] → master_index")
        self.module.instruction(f"logic [{master_bits}:0] write_id_table [NUM_SLAVES][2**ID_WIDTH];")
        self.module.instruction(f"logic [{master_bits}:0] read_id_table [NUM_SLAVES][2**ID_WIDTH];")
        self.module.instruction("")

        # Generate table write logic
        self.module.comment("ID Table Write Logic")
        self.module.comment("Store master index when AW/AR handshakes complete")
        self.module.instruction("generate")
        self.module.instruction("    for (genvar s = 0; s < NUM_SLAVES; s++) begin : gen_id_table_write")
        self.module.instruction("        always_ff @(posedge aclk or negedge aresetn) begin")
        self.module.instruction("            if (!aresetn) begin")
        self.module.instruction("                // Tables don't need explicit reset (overwritten on use)")
        self.module.instruction("            end else begin")
        self.module.instruction("                // Write ID table: Record master for completed AW transactions")
        self.module.instruction("                if (xbar_m_axi_awvalid[s] && xbar_m_axi_awready[s]) begin")
        self.module.instruction("                    for (int m = 0; m < NUM_MASTERS; m++) begin")
        self.module.instruction("                        if (aw_grant_matrix[s][m]) begin")
        if self.cfg.num_masters > 1:
            self.module.instruction(f"                            write_id_table[s][xbar_m_axi_awid[s]] <= m[{master_bits}:0];")
        else:
            self.module.instruction("                            write_id_table[s][xbar_m_axi_awid[s]] <= 1'b0;  // Only 1 master")
        self.module.instruction("                        end")
        self.module.instruction("                    end")
        self.module.instruction("                end")
        self.module.instruction("")
        self.module.instruction("                // Read ID table: Record master for completed AR transactions")
        self.module.instruction("                if (xbar_m_axi_arvalid[s] && xbar_m_axi_arready[s]) begin")
        self.module.instruction("                    for (int m = 0; m < NUM_MASTERS; m++) begin")
        self.module.instruction("                        if (ar_grant_matrix[s][m]) begin")
        if self.cfg.num_masters > 1:
            self.module.instruction(f"                            read_id_table[s][xbar_m_axi_arid[s]] <= m[{master_bits}:0];")
        else:
            self.module.instruction("                            read_id_table[s][xbar_m_axi_arid[s]] <= 1'b0;  // Only 1 master")
        self.module.instruction("                        end")
        self.module.instruction("                    end")
        self.module.instruction("                end")
        self.module.instruction("            end")
        self.module.instruction("        end")
        self.module.instruction("    end")
        self.module.instruction("endgenerate")
        self.module.instruction("")

    def generate_b_channel_demux(self):
        """
        Generate B channel demux (Write Response)

        B response routing:
        - Lookup master ID from write_id_table using {slave, BID}
        - Route B response to correct master
        - Single-beat response (no burst handling)
        """
        self.module.comment("==========================================================================")
        self.module.comment("B Channel Demux (Write Response)")
        self.module.comment("==========================================================================")
        self.module.comment("ID-based routing: Lookup master from write_id_table[slave][bid]")
        self.module.comment("Single-beat response (no burst, unlike R channel)")
        self.module.comment("==========================================================================")
        self.module.instruction("")

        # B channel signals to masters (combinational routing)
        self.module.instruction("// B channel response routing to masters")
        self.module.instruction("logic [ID_WIDTH-1:0]     b_routed_id    [NUM_MASTERS];")
        self.module.instruction("logic [1:0]              b_routed_resp  [NUM_MASTERS];")
        self.module.instruction("logic                    b_routed_valid [NUM_MASTERS];")
        self.module.instruction("")

        self.module.instruction("always_comb begin")
        self.module.instruction("    // Initialize all master B channels to idle")
        self.module.instruction("    for (int m = 0; m < NUM_MASTERS; m++) begin")
        self.module.instruction("        b_routed_id[m]    = '0;")
        self.module.instruction("        b_routed_resp[m]  = 2'b00;")
        self.module.instruction("        b_routed_valid[m] = 1'b0;")
        self.module.instruction("    end")
        self.module.instruction("")
        self.module.instruction("    // Route B responses from each slave to target master")
        self.module.instruction("    for (int s = 0; s < NUM_SLAVES; s++) begin")
        self.module.instruction(f"        int target_master;  // Master index for this B response")
        self.module.instruction("        if (xbar_m_axi_bvalid[s]) begin")
        self.module.instruction("            // Lookup which master this transaction belongs to")
        self.module.instruction(f"            target_master = int'(write_id_table[s][xbar_m_axi_bid[s]]);")
        self.module.instruction("")
        self.module.instruction("            // Route to target master (ID-based)")
        self.module.instruction("            b_routed_id[target_master]    = xbar_m_axi_bid[s];")
        self.module.instruction("            b_routed_resp[target_master]  = xbar_m_axi_bresp[s];")
        self.module.instruction("            b_routed_valid[target_master] = 1'b1;")
        self.module.instruction("        end else begin")
        self.module.instruction("            target_master = 0;  // Default when no valid")
        self.module.instruction("        end")
        self.module.instruction("    end")
        self.module.instruction("end")
        self.module.instruction("")

        # Assign to output ports
        self.module.instruction("// Assign routed B signals to master output ports")
        self.module.instruction("generate")
        self.module.instruction("    for (genvar m = 0; m < NUM_MASTERS; m++) begin : gen_b_output")
        self.module.instruction("        assign xbar_s_axi_bid[m]    = b_routed_id[m];")
        self.module.instruction("        assign xbar_s_axi_bresp[m]  = b_routed_resp[m];")
        self.module.instruction("        assign xbar_s_axi_bvalid[m] = b_routed_valid[m];")
        self.module.instruction("    end")
        self.module.instruction("endgenerate")
        self.module.instruction("")

        # B channel backpressure routing (BREADY)
        self.module.comment("B channel backpressure: Route master's BREADY to slave")
        self.module.instruction("generate")
        self.module.instruction("    for (genvar s = 0; s < NUM_SLAVES; s++) begin : gen_b_ready")
        self.module.instruction("        always_comb begin")
        self.module.instruction("            int target_master;")
        self.module.instruction("            xbar_m_axi_bready[s] = 1'b0;")
        self.module.instruction("            if (xbar_m_axi_bvalid[s]) begin")
        self.module.instruction("                // Find which master this B response goes to")
        self.module.instruction(f"                target_master = int'(write_id_table[s][xbar_m_axi_bid[s]]);")
        self.module.instruction("                xbar_m_axi_bready[s] = xbar_s_axi_bready[target_master];")
        self.module.instruction("            end else begin")
        self.module.instruction("                target_master = 0;  // Default when no valid")
        self.module.instruction("            end")
        self.module.instruction("        end")
        self.module.instruction("    end")
        self.module.instruction("endgenerate")
        self.module.instruction("")

    def generate_r_channel_demux(self):
        """
        Generate R channel demux (Read Data/Response)

        R response routing:
        - Lookup master ID from read_id_table using {slave, RID}
        - Route R data/response to correct master
        - Handle RLAST (last beat of read burst)
        - Multiple R beats per transaction, all routed to same master
        """
        self.module.comment("==========================================================================")
        self.module.comment("R Channel Demux (Read Data/Response)")
        self.module.comment("==========================================================================")
        self.module.comment("ID-based routing: Lookup master from read_id_table[slave][rid]")
        self.module.comment("Burst support: Multiple R beats (RLAST indicates last beat)")
        self.module.comment("Similar to B channel but with DATA_WIDTH data payload")
        self.module.comment("==========================================================================")
        self.module.instruction("")

        # R channel signals to masters (combinational routing)
        self.module.instruction("// R channel response routing to masters")
        self.module.instruction("logic [DATA_WIDTH-1:0]   r_routed_data  [NUM_MASTERS];")
        self.module.instruction("logic [ID_WIDTH-1:0]     r_routed_id    [NUM_MASTERS];")
        self.module.instruction("logic [1:0]              r_routed_resp  [NUM_MASTERS];")
        self.module.instruction("logic                    r_routed_last  [NUM_MASTERS];")
        self.module.instruction("logic                    r_routed_valid [NUM_MASTERS];")
        self.module.instruction("")

        self.module.instruction("always_comb begin")
        self.module.instruction("    // Initialize all master R channels to idle")
        self.module.instruction("    for (int m = 0; m < NUM_MASTERS; m++) begin")
        self.module.instruction("        r_routed_data[m]  = '0;")
        self.module.instruction("        r_routed_id[m]    = '0;")
        self.module.instruction("        r_routed_resp[m]  = 2'b00;")
        self.module.instruction("        r_routed_last[m]  = 1'b0;")
        self.module.instruction("        r_routed_valid[m] = 1'b0;")
        self.module.instruction("    end")
        self.module.instruction("")
        self.module.instruction("    // Route R responses from each slave to target master")
        self.module.instruction("    for (int s = 0; s < NUM_SLAVES; s++) begin")
        self.module.instruction(f"        int target_master;  // Master index for this R response")
        self.module.instruction("        if (xbar_m_axi_rvalid[s]) begin")
        self.module.instruction("            // Lookup which master this transaction belongs to")
        self.module.instruction(f"            target_master = int'(read_id_table[s][xbar_m_axi_rid[s]]);")
        self.module.instruction("")
        self.module.instruction("            // Route to target master (ID-based, burst-aware)")
        self.module.instruction("            r_routed_data[target_master]  = xbar_m_axi_rdata[s];")
        self.module.instruction("            r_routed_id[target_master]    = xbar_m_axi_rid[s];")
        self.module.instruction("            r_routed_resp[target_master]  = xbar_m_axi_rresp[s];")
        self.module.instruction("            r_routed_last[target_master]  = xbar_m_axi_rlast[s];")
        self.module.instruction("            r_routed_valid[target_master] = 1'b1;")
        self.module.instruction("        end else begin")
        self.module.instruction("            target_master = 0;  // Default when no valid")
        self.module.instruction("        end")
        self.module.instruction("    end")
        self.module.instruction("end")
        self.module.instruction("")

        # Assign to output ports
        self.module.instruction("// Assign routed R signals to master output ports")
        self.module.instruction("generate")
        self.module.instruction("    for (genvar m = 0; m < NUM_MASTERS; m++) begin : gen_r_output")
        self.module.instruction("        assign xbar_s_axi_rdata[m]  = r_routed_data[m];")
        self.module.instruction("        assign xbar_s_axi_rid[m]    = r_routed_id[m];")
        self.module.instruction("        assign xbar_s_axi_rresp[m]  = r_routed_resp[m];")
        self.module.instruction("        assign xbar_s_axi_rlast[m]  = r_routed_last[m];")
        self.module.instruction("        assign xbar_s_axi_rvalid[m] = r_routed_valid[m];")
        self.module.instruction("    end")
        self.module.instruction("endgenerate")
        self.module.instruction("")

        # R channel backpressure routing (RREADY)
        self.module.comment("R channel backpressure: Route master's RREADY to slave")
        self.module.instruction("generate")
        self.module.instruction("    for (genvar s = 0; s < NUM_SLAVES; s++) begin : gen_r_ready")
        self.module.instruction("        always_comb begin")
        self.module.instruction("            int target_master;")
        self.module.instruction("            xbar_m_axi_rready[s] = 1'b0;")
        self.module.instruction("            if (xbar_m_axi_rvalid[s]) begin")
        self.module.instruction("                // Find which master this R response goes to")
        self.module.instruction(f"                target_master = int'(read_id_table[s][xbar_m_axi_rid[s]]);")
        self.module.instruction("                xbar_m_axi_rready[s] = xbar_s_axi_rready[target_master];")
        self.module.instruction("            end else begin")
        self.module.instruction("                target_master = 0;  // Default when no valid")
        self.module.instruction("            end")
        self.module.instruction("        end")
        self.module.instruction("    end")
        self.module.instruction("endgenerate")
        self.module.instruction("")
