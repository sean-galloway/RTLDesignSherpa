#!/usr/bin/env python3
# SPDX-License-Identifier: MIT
# SPDX-FileCopyrightText: 2024-2025 sean galloway
#
# RTL Design Sherpa - Industry-Standard RTL Design and Verification
# https://github.com/sean-galloway/RTLDesignSherpa
#
# Module: BridgeAddressArbiter
# Purpose: Address decode and arbitration logic for bridge crossbars
#
# Author: sean galloway
# Created: 2025-10-26

"""
Address Decode and Arbitration for Bridge Generator

Handles:
- Address decode (AW and AR channels)
- Per-slave round-robin arbitration
- Grant locking until burst complete
"""

import sys
from pathlib import Path

# Import the framework
sys.path.insert(0, str(Path(__file__).resolve().parents[4] / 'bin'))
from rtl_generators.verilog.module import Module


class BridgeAddressArbiter:
    """
    Address Decode and Arbitration for Bridge Crossbar

    Generates address decode logic and arbiter instances:
    - Decodes addresses to determine target slave
    - Arbitrates between masters for each slave
    - Uses standard arbiter_round_robin component with WAIT_GNT_ACK=1
    """

    def __init__(self, module: Module, config):
        """
        Initialize address arbiter

        Args:
            module: Module instance for RTL generation
            config: BridgeConfig with address map and topology
        """
        self.module = module
        self.cfg = config

    def generate_address_decode(self):
        """
        Generate address decode logic for AW and AR channels

        Determines which slave(s) a master is targeting based on address.
        Creates request matrices for arbitration.
        """
        self.module.comment("==========================================================================")
        self.module.comment("Address Decode (AW and AR channels)")
        self.module.comment("==========================================================================")
        self.module.comment("Decode master addresses to determine target slave(s)")
        self.module.comment("Generates request signals for per-slave arbitration")
        self.module.comment("==========================================================================")
        self.module.instruction("")

        # AW request matrix (write address)
        self.module.instruction("// AW channel requests: array of packed vectors per slave")
        self.module.instruction("logic [NUM_MASTERS-1:0] aw_request_matrix [NUM_SLAVES-1:0];")
        self.module.instruction("")

        # AR request matrix (read address)
        self.module.instruction("// AR channel requests: array of packed vectors per slave")
        self.module.instruction("logic [NUM_MASTERS-1:0] ar_request_matrix [NUM_SLAVES-1:0];")
        self.module.instruction("")

        # Generate decode logic for each master
        self.module.instruction("generate")
        self.module.instruction("    for (genvar m = 0; m < NUM_MASTERS; m++) begin : gen_addr_decode")
        self.module.instruction("        always_comb begin")
        self.module.instruction("            // Initialize all requests to 0")
        self.module.instruction("            for (int s = 0; s < NUM_SLAVES; s++) begin")
        self.module.instruction("                aw_request_matrix[s][m] = 1'b0;")
        self.module.instruction("                ar_request_matrix[s][m] = 1'b0;")
        self.module.instruction("            end")
        self.module.instruction("")
        # Generate address decode based on address map if provided, otherwise use simple mapping
        self.module.instruction("            // Decode AW address to slave")
        self.module.instruction("            if (xbar_s_axi_awvalid[m]) begin")

        # Check if address map is configured
        if hasattr(self.cfg, 'address_map') and self.cfg.address_map:
            # Use configured address map - proper address range decode
            self.module.instruction("                // Address decode using configured ranges")
            self.module.instruction("                case (xbar_s_axi_awaddr[m][ADDR_WIDTH-1:ADDR_WIDTH-4])")

            for slave_idx, addr_info in sorted(self.cfg.address_map.items()):
                base_addr = addr_info['base']
                # Extract upper 4 bits - use bit_length to find actual address size
                # For 32-bit addresses like 0x80000000, shift by 28 not 60
                sig_bits = max(32, base_addr.bit_length()) if base_addr > 0 else 32
                upper_nibble = (base_addr >> (sig_bits - 4)) & 0xF
                addr_hex = hex(upper_nibble)[2:].upper()
                self.module.instruction(f"                    4'h{addr_hex}: aw_request_matrix[{slave_idx}][m] = 1'b1;")

            self.module.instruction("                    default: aw_request_matrix[0][m] = 1'b1;  // Unmapped -> slave 0")
            self.module.instruction("                endcase")
        else:
            # Fallback: sequential decode (for backward compatibility or simple bridges)
            self.module.instruction("                // Sequential address decode (legacy)")
            self.module.instruction("                case (xbar_s_axi_awaddr[m][ADDR_WIDTH-1:ADDR_WIDTH-4])")
            for slave_idx in range(self.cfg.num_slaves):
                addr_bits = hex(slave_idx)[2:].upper()
                self.module.instruction(f"                    4'h{addr_bits}: aw_request_matrix[{slave_idx}][m] = 1'b1;")
            self.module.instruction("                    default: aw_request_matrix[0][m] = 1'b1;")
            self.module.instruction("                endcase")

        self.module.instruction("            end")
        self.module.instruction("")

        # Same logic for AR channel
        self.module.instruction("            // Decode AR address to slave")
        self.module.instruction("            if (xbar_s_axi_arvalid[m]) begin")

        if hasattr(self.cfg, 'address_map') and self.cfg.address_map:
            self.module.instruction("                // Address decode using configured ranges")
            self.module.instruction("                case (xbar_s_axi_araddr[m][ADDR_WIDTH-1:ADDR_WIDTH-4])")

            for slave_idx, addr_info in sorted(self.cfg.address_map.items()):
                base_addr = addr_info['base']
                # Extract upper 4 bits - use bit_length to find actual address size
                sig_bits = max(32, base_addr.bit_length()) if base_addr > 0 else 32
                upper_nibble = (base_addr >> (sig_bits - 4)) & 0xF
                addr_hex = hex(upper_nibble)[2:].upper()
                self.module.instruction(f"                    4'h{addr_hex}: ar_request_matrix[{slave_idx}][m] = 1'b1;")

            self.module.instruction("                    default: ar_request_matrix[0][m] = 1'b1;  // Unmapped -> slave 0")
            self.module.instruction("                endcase")
        else:
            self.module.instruction("                // Sequential address decode (legacy)")
            self.module.instruction("                case (xbar_s_axi_araddr[m][ADDR_WIDTH-1:ADDR_WIDTH-4])")
            for slave_idx in range(self.cfg.num_slaves):
                addr_bits = hex(slave_idx)[2:].upper()
                self.module.instruction(f"                    4'h{addr_bits}: ar_request_matrix[{slave_idx}][m] = 1'b1;")
            self.module.instruction("                    default: ar_request_matrix[0][m] = 1'b1;")
            self.module.instruction("                endcase")

        self.module.instruction("            end")
        self.module.instruction("        end")
        self.module.instruction("    end")
        self.module.instruction("endgenerate")
        self.module.instruction("")

    def generate_aw_arbiter(self):
        """
        Generate AW channel arbitration using arbiter_round_robin

        One arbiter per slave to select among requesting masters.
        Grant held until AWVALID && AWREADY handshake completes.
        """
        self.module.comment("==========================================================================")
        self.module.comment("AW Channel Arbitration - Using Standard arbiter_round_robin")
        self.module.comment("==========================================================================")
        self.module.comment("Per-slave round-robin arbitration with grant locking (WAIT_GNT_ACK=1)")
        self.module.comment("Grant persists until AW handshake completes")
        self.module.comment("==========================================================================")
        self.module.instruction("")

        # AW grant matrix and grant active signals
        self.module.instruction("// AW grant matrix: array of packed vectors per slave")
        self.module.instruction("logic [NUM_MASTERS-1:0] aw_grant_matrix [NUM_SLAVES-1:0];")
        self.module.instruction("logic aw_grant_active [NUM_SLAVES-1:0];  // Valid grant exists")
        self.module.instruction("")

        # Generate grant_ack signals from handshake completion
        self.module.instruction("// Grant acknowledgment: AW handshake completion")
        self.module.instruction("logic [NUM_MASTERS-1:0] aw_grant_ack [NUM_SLAVES-1:0];")
        self.module.instruction("")
        self.module.instruction("generate")
        self.module.instruction("    for (genvar s = 0; s < NUM_SLAVES; s++) begin : gen_aw_grant_ack")
        self.module.instruction("        always_comb begin")
        self.module.instruction("            aw_grant_ack[s] = '0;")
        self.module.instruction("            for (int m = 0; m < NUM_MASTERS; m++) begin")
        self.module.instruction("                if (aw_grant_matrix[s][m] && xbar_m_axi_awvalid[s] && xbar_m_axi_awready[s]) begin")
        self.module.instruction("                    aw_grant_ack[s][m] = 1'b1;")
        self.module.instruction("                end")
        self.module.instruction("            end")
        self.module.instruction("        end")
        self.module.instruction("    end")
        self.module.instruction("endgenerate")
        self.module.instruction("")

        # Instantiate arbiters
        self.module.instruction("// Arbiter instances per slave")
        self.module.instruction("generate")
        self.module.instruction("    for (genvar s = 0; s < NUM_SLAVES; s++) begin : gen_aw_arbiter")
        self.module.instruction("")
        self.module.instruction("        arbiter_round_robin #(")
        self.module.instruction("            .CLIENTS(NUM_MASTERS),")
        self.module.instruction("            .WAIT_GNT_ACK(1)  // Hold grant until handshake")
        self.module.instruction("        ) u_aw_arbiter (")
        self.module.instruction("            .clk         (aclk),")
        self.module.instruction("            .rst_n       (aresetn),")
        self.module.instruction("            .block_arb   (1'b0),")
        self.module.instruction("            .request     (aw_request_matrix[s]),")
        self.module.instruction("            .grant_ack   (aw_grant_ack[s]),")
        self.module.instruction("            .grant_valid (aw_grant_active[s]),")
        self.module.instruction("            .grant       (aw_grant_matrix[s]),")
        self.module.instruction("            .grant_id    (),  // Optional: can use for debug")
        self.module.instruction("            .last_grant  ()   // Optional: debug visibility")
        self.module.instruction("        );")
        self.module.instruction("")
        self.module.instruction("    end")
        self.module.instruction("endgenerate")
        self.module.instruction("")

    def generate_ar_arbiter(self):
        """
        Generate AR channel arbitration using arbiter_round_robin

        Similar to AW arbitration but for read address channel.
        Independent arbitration from write path.
        """
        self.module.comment("==========================================================================")
        self.module.comment("AR Channel Arbitration - Using Standard arbiter_round_robin")
        self.module.comment("==========================================================================")
        self.module.comment("Per-slave round-robin arbitration with grant locking (WAIT_GNT_ACK=1)")
        self.module.comment("Grant persists until AR handshake completes")
        self.module.comment("Independent from AW arbitration (separate read/write paths)")
        self.module.comment("==========================================================================")
        self.module.instruction("")

        # AR grant matrix and grant active signals
        self.module.instruction("// AR grant matrix: array of packed vectors per slave")
        self.module.instruction("logic [NUM_MASTERS-1:0] ar_grant_matrix [NUM_SLAVES-1:0];")
        self.module.instruction("logic ar_grant_active [NUM_SLAVES-1:0];  // Valid grant exists")
        self.module.instruction("")

        # Generate grant_ack signals from handshake completion
        self.module.instruction("// Grant acknowledgment: AR handshake completion")
        self.module.instruction("logic [NUM_MASTERS-1:0] ar_grant_ack [NUM_SLAVES-1:0];")
        self.module.instruction("")
        self.module.instruction("generate")
        self.module.instruction("    for (genvar s = 0; s < NUM_SLAVES; s++) begin : gen_ar_grant_ack")
        self.module.instruction("        always_comb begin")
        self.module.instruction("            ar_grant_ack[s] = '0;")
        self.module.instruction("            for (int m = 0; m < NUM_MASTERS; m++) begin")
        self.module.instruction("                if (ar_grant_matrix[s][m] && xbar_m_axi_arvalid[s] && xbar_m_axi_arready[s]) begin")
        self.module.instruction("                    ar_grant_ack[s][m] = 1'b1;")
        self.module.instruction("                end")
        self.module.instruction("            end")
        self.module.instruction("        end")
        self.module.instruction("    end")
        self.module.instruction("endgenerate")
        self.module.instruction("")

        # Instantiate arbiters
        self.module.instruction("// Arbiter instances per slave")
        self.module.instruction("generate")
        self.module.instruction("    for (genvar s = 0; s < NUM_SLAVES; s++) begin : gen_ar_arbiter")
        self.module.instruction("")
        self.module.instruction("        arbiter_round_robin #(")
        self.module.instruction("            .CLIENTS(NUM_MASTERS),")
        self.module.instruction("            .WAIT_GNT_ACK(1)  // Hold grant until handshake")
        self.module.instruction("        ) u_ar_arbiter (")
        self.module.instruction("            .clk         (aclk),")
        self.module.instruction("            .rst_n       (aresetn),")
        self.module.instruction("            .block_arb   (1'b0),")
        self.module.instruction("            .request     (ar_request_matrix[s]),")
        self.module.instruction("            .grant_ack   (ar_grant_ack[s]),")
        self.module.instruction("            .grant_valid (ar_grant_active[s]),")
        self.module.instruction("            .grant       (ar_grant_matrix[s]),")
        self.module.instruction("            .grant_id    (),  // Optional: can use for debug")
        self.module.instruction("            .last_grant  ()   // Optional: debug visibility")
        self.module.instruction("        );")
        self.module.instruction("")
        self.module.instruction("    end")
        self.module.instruction("endgenerate")
        self.module.instruction("")
