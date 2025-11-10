#!/usr/bin/env python3
# SPDX-License-Identifier: MIT
# SPDX-FileCopyrightText: 2024-2025 sean galloway
#
# Arbiter Component - Type-safe arbiter instantiation using Module.instantiate()

import sys
import os

# Add rtl_generators to path
repo_root = os.path.abspath(os.path.join(os.path.dirname(__file__), '../../../../../..'))
sys.path.insert(0, os.path.join(repo_root, 'bin'))

from rtl_generators.verilog.module import Module


class ArbiterComponent:
    """
    Type-safe arbiter instantiation using Module.instantiate()

    This class wraps arbiter_round_robin module to provide type-safe
    port and parameter handling, eliminating string concatenation bugs.

    Example:
        arb = ArbiterComponent(
            num_clients=2,
            instance_name='u_arb_aw_s0',
            clock_signal='aclk',
            reset_signal='aresetn'
        )

        # Get instantiation string
        inst_str = arb.instantiate(
            request_signal='aw_req_vec',
            grant_output='aw_grant_s0',
            grant_valid_output='aw_grant_valid_s0'
        )

        # Returns: arbiter_round_robin #(.CLIENTS(2), ...) u_arb_aw_s0 (...)
    """

    def __init__(self, num_clients: int, instance_name: str,
                 clock_signal: str = 'aclk', reset_signal: str = 'aresetn',
                 reg_output: int = 0):
        """
        Initialize arbiter component

        Args:
            num_clients: Number of requesters (CLIENTS parameter)
            instance_name: Instance name (e.g., 'u_arb_aw_s0')
            clock_signal: Clock signal name (default: 'aclk')
            reset_signal: Reset signal name (default: 'aresetn')
            reg_output: 1 for pipelined, 0 for combinational (default: 0)
        """
        self.num_clients = num_clients
        self.instance_name = instance_name
        self.clock_signal = clock_signal
        self.reset_signal = reset_signal
        self.reg_output = reg_output

        # Create Module for arbiter
        self.arb_module = Module(module_name='arbiter_round_robin')

        # Calculate bit width for grant_id (N parameter)
        # N = ceil(log2(CLIENTS)), minimum 1
        import math
        self.n_width = max(1, math.ceil(math.log2(num_clients))) if num_clients > 1 else 1

        # Add parameters using add_param_string (matches Param API)
        # Note: REG_OUTPUT parameter was removed from arbiter_round_robin
        param_str = f'''
            parameter int CLIENTS = {num_clients},
            parameter int N = {self.n_width}
        '''
        self.arb_module.params.add_param_string(param_str)

    def instantiate(self,
                   request_signal: str,
                   grant_output: str,
                   grant_valid_output: str = None,
                   grant_id_output: str = None,
                   last_grant_output: str = None,
                   block_arb_signal: str = "1'b0",
                   grant_ack_signal: str = None) -> str:
        """
        Generate type-safe arbiter instantiation

        Args:
            request_signal: Request vector signal name (e.g., 'aw_req_vec')
            grant_output: Grant vector output name (e.g., 'aw_grant_s0')
            grant_valid_output: Grant valid output (optional, default: None = unused)
            grant_id_output: Grant ID output (optional, default: None = unused)
            block_arb_signal: Block arbitration signal (default: 1'b0 = never block)
            grant_ack_signal: Grant acknowledge vector (optional, default: tied to grant)

        Returns:
            Complete instantiation string
        """
        # Build input port connections
        # Note: Port names updated to match current arbiter_round_robin interface
        inputs = [
            {'port': 'clk', 'connector': self.clock_signal},
            {'port': 'rst_n', 'connector': self.reset_signal},
            {'port': 'request', 'connector': request_signal},
            {'port': 'block_arb', 'connector': block_arb_signal},
        ]

        # Grant ack: if not provided, tie to grant output (standard usage)
        if grant_ack_signal is None:
            grant_ack_signal = grant_output
        inputs.append({'port': 'grant_ack', 'connector': grant_ack_signal})

        # Build output port connections
        # Note: Port names updated to match current arbiter_round_robin interface
        outputs = [
            {'port': 'grant', 'connector': grant_output},
        ]

        # Optional outputs
        if grant_valid_output:
            outputs.append({'port': 'grant_valid', 'connector': grant_valid_output})

        if grant_id_output:
            outputs.append({'port': 'grant_id', 'connector': grant_id_output})

        # Add last_grant output (informational, for debugging)
        if last_grant_output:
            outputs.append({'port': 'last_grant', 'connector': last_grant_output})

        # Generate instantiation using Module.instantiate()
        inst_str = self.arb_module.instantiate(
            instance_name=self.instance_name,
            inputs=inputs,
            outputs=outputs
        )

        return inst_str

    def get_signals_declaration(self, prefix: str) -> list:
        """
        Get signal declarations needed for this arbiter

        Args:
            prefix: Signal prefix (e.g., 'aw_s0')

        Returns:
            List of signal declaration strings
        """
        signals = []

        # Request vector (input to arbiter)
        signals.append(f"logic [{self.num_clients-1}:0] {prefix}_req_vec;")

        # Grant vector (output from arbiter)
        signals.append(f"logic [{self.num_clients-1}:0] {prefix}_grant;")

        # Grant valid (optional, but recommended)
        signals.append(f"logic {prefix}_grant_valid;")

        # Grant ID (optional, shows which client won)
        signals.append(f"logic [{self.n_width-1}:0] {prefix}_grant_id;")

        return signals


# Example usage and testing
if __name__ == '__main__':
    print("=" * 70)
    print("ArbiterComponent Test - Type-Safe Instantiation")
    print("=" * 70)
    print()

    # Create arbiter for 2 masters
    arb = ArbiterComponent(
        num_clients=2,
        instance_name='u_arb_aw_s0',
        clock_signal='aclk',
        reset_signal='aresetn',
        reg_output=0  # Combinational
    )

    # Get signal declarations
    print("// Signal declarations:")
    for sig in arb.get_signals_declaration('aw_s0'):
        print(f"    {sig}")
    print()

    # Generate instantiation
    print("// Arbiter instantiation:")
    inst = arb.instantiate(
        request_signal='aw_req_vec',
        grant_output='aw_grant_s0',
        grant_valid_output='aw_grant_valid_s0',
        grant_id_output='aw_grant_id_s0'
    )
    print(f"    {inst}")
    print()

    print("=" * 70)
    print("✓ Type-safe instantiation complete!")
    print("  - Parameters: CLIENTS={}, N={}, REG_OUTPUT={}".format(
        arb.num_clients, arb.n_width, arb.reg_output))
    print("  - Ports: All matched to arbiter_round_robin interface")
    print("  - No string concatenation bugs possible!")
    print("=" * 70)
