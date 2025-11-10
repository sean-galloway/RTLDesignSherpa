#!/usr/bin/env python3
# SPDX-License-Identifier: MIT
# SPDX-FileCopyrightText: 2024-2025 sean galloway
#
# Address Decode Component - Generates combinational address decode logic

from typing import List, Dict


class AddressDecodeComponent:
    """
    Generate address decode logic for bridge routing

    This component generates combinational logic that:
    1. Decodes each master's address to determine target slave
    2. Generates arbiter request signals (aw_req/ar_req)
    3. Handles partial connectivity (not all masters to all slaves)

    Example Output:
        // Address decode for master 0: cpu_master
        logic [1:0] addr_decode_aw_m0;  // One-hot decode

        always_comb begin
            addr_decode_aw_m0 = 2'b00;
            if (xbar_m_awaddr[0] >= 32'h80000000 && xbar_m_awaddr[0] < 32'hFFFFFFFF)
                addr_decode_aw_m0[0] = 1'b1;  // Slave 0
            else if (xbar_m_awaddr[0] >= 32'h40000000 && xbar_m_awaddr[0] < 32'h80000000)
                addr_decode_aw_m0[1] = 1'b1;  // Slave 1
        end

        // Generate arbiter requests
        assign aw_req_s0[0] = xbar_m_awvalid[0] && addr_decode_aw_m0[0];
        assign aw_req_s1[0] = xbar_m_awvalid[0] && addr_decode_aw_m0[1];
    """

    def __init__(self, masters: List, slaves: List, connectivity: Dict[str, List[str]],
                 addr_width: int = 32):
        """
        Initialize address decode component

        Args:
            masters: List of PortSpec objects for masters
            slaves: List of PortSpec objects for slaves
            connectivity: Dict mapping master_name -> [connected_slave_names]
            addr_width: Address bus width (default: 32)
        """
        self.masters = masters
        self.slaves = slaves
        self.connectivity = connectivity
        self.addr_width = addr_width

    def generate_decode_signals(self) -> List[str]:
        """
        Generate signal declarations for address decode

        Returns:
            List of signal declaration strings
        """
        signals = []
        num_slaves = len(self.slaves)

        for master_idx, master in enumerate(self.masters):
            # AW channel decode (write address)
            if master.has_write_channels():
                signals.append(f"logic [{num_slaves-1}:0] addr_decode_aw_m{master_idx};  "
                              f"// {master.port_name} write decode")

            # AR channel decode (read address)
            if master.has_read_channels():
                signals.append(f"logic [{num_slaves-1}:0] addr_decode_ar_m{master_idx};  "
                              f"// {master.port_name} read decode")

        return signals

    def generate_decode_logic(self, channel: str) -> List[str]:
        """
        Generate address decode combinational logic

        Args:
            channel: 'aw' for write address or 'ar' for read address

        Returns:
            List of RTL instruction strings
        """
        instructions = []

        instructions.append(f"// {channel.upper()} Channel Address Decode")
        instructions.append("")

        for master_idx, master in enumerate(self.masters):
            # Skip if master doesn't have this channel
            if channel == 'aw' and not master.has_write_channels():
                continue
            if channel == 'ar' and not master.has_read_channels():
                continue

            # Get connected slaves for this master
            connected_slaves = self.connectivity.get(master.port_name, [])

            instructions.append(f"// Address decode for master {master_idx}: {master.port_name}")
            instructions.append(f"always_comb begin")
            instructions.append(f"    addr_decode_{channel}_m{master_idx} = {len(self.slaves)}'b0;")

            # Generate decode for each connected slave
            for slave in self.slaves:
                if slave.port_name not in connected_slaves:
                    continue  # Not connected

                slave_idx = self.slaves.index(slave)
                base_addr = slave.base_addr
                end_addr = base_addr + slave.addr_range - 1

                # Generate address range check
                addr_signal = f"xbar_m_{channel}addr[{master_idx}]"

                if self.addr_width <= 32:
                    base_str = f"{self.addr_width}'h{base_addr:08X}"
                    end_str = f"{self.addr_width}'h{end_addr:08X}"
                else:
                    base_str = f"{self.addr_width}'h{base_addr:016X}"
                    end_str = f"{self.addr_width}'h{end_addr:016X}"

                # Calculate maximum address for this width
                max_addr = (1 << self.addr_width) - 1

                # Optimize address range checks:
                # - Skip >= 0 check for unsigned values (always true)
                # - Skip <= MAX check when end_addr == max address (always true)
                if base_addr == 0 and end_addr == max_addr:
                    # Entire address space - no check needed, always match
                    instructions.append(f"    // Entire address space")
                    instructions.append(f"    addr_decode_{channel}_m{master_idx}[{slave_idx}] = 1'b1;")
                    continue  # Skip the normal assignment below
                elif base_addr == 0:
                    # Starts at 0, only need upper bound
                    instructions.append(f"    if ({addr_signal} <= {end_str})")
                elif end_addr == max_addr:
                    # Ends at max address, only need lower bound
                    instructions.append(f"    if ({addr_signal} >= {base_str})")
                else:
                    # Middle range, need both bounds
                    instructions.append(
                        f"    if ({addr_signal} >= {base_str} && "
                        f"{addr_signal} <= {end_str})"
                    )
                instructions.append(f"        addr_decode_{channel}_m{master_idx}[{slave_idx}] = 1'b1;")

            instructions.append(f"end")
            instructions.append("")

        return instructions

    def generate_arbiter_requests(self, channel: str) -> List[str]:
        """
        Generate arbiter request signal assignments

        Args:
            channel: 'aw' for write address or 'ar' for read address

        Returns:
            List of RTL instruction strings
        """
        instructions = []

        instructions.append(f"// Generate {channel.upper()} arbiter request signals")
        instructions.append("")

        # For each slave, collect requests from all masters
        for slave_idx, slave in enumerate(self.slaves):
            # Skip if slave doesn't support this channel
            if channel == 'aw' and not slave.has_write_channels():
                continue
            if channel == 'ar' and not slave.has_read_channels():
                continue

            instructions.append(f"// Arbiter requests for slave {slave_idx}: {slave.port_name}")

            for master_idx, master in enumerate(self.masters):
                # Skip if master doesn't have this channel
                if channel == 'aw' and not master.has_write_channels():
                    continue
                if channel == 'ar' and not master.has_read_channels():
                    continue

                # Check if master connects to this slave
                connected_slaves = self.connectivity.get(master.port_name, [])
                if slave.port_name not in connected_slaves:
                    # Not connected - tie off
                    instructions.append(
                        f"assign {channel}_req_s{slave_idx}[{master_idx}] = 1'b0;  "
                        f"// {master.port_name} not connected"
                    )
                else:
                    # Connected - generate request
                    instructions.append(
                        f"assign {channel}_req_s{slave_idx}[{master_idx}] = "
                        f"xbar_m_{channel}valid[{master_idx}] && "
                        f"addr_decode_{channel}_m{master_idx}[{slave_idx}];"
                    )

            instructions.append("")

        return instructions

    def generate_all(self) -> Dict[str, List[str]]:
        """
        Generate all address decode logic

        Returns:
            Dictionary with keys:
                'signals' - Signal declarations
                'aw_decode' - AW channel decode logic
                'ar_decode' - AR channel decode logic
                'aw_requests' - AW arbiter request assignments
                'ar_requests' - AR arbiter request assignments
        """
        return {
            'signals': self.generate_decode_signals(),
            'aw_decode': self.generate_decode_logic('aw'),
            'ar_decode': self.generate_decode_logic('ar'),
            'aw_requests': self.generate_arbiter_requests('aw'),
            'ar_requests': self.generate_arbiter_requests('ar'),
        }


# Example usage and testing
if __name__ == '__main__':
    import sys
    import os
    sys.path.insert(0, os.path.join(os.path.dirname(__file__), '../..'))
    from bridge_pkg.config import PortSpec

    print("=" * 70)
    print("AddressDecodeComponent Test")
    print("=" * 70)
    print()

    # Create test configuration
    masters = [
        PortSpec(
            port_name='cpu_master',
            direction='master',
            protocol='axi4',
            channels='wr',
            prefix='cpu_m_axi_',
            data_width=64,
            addr_width=32,
            id_width=4
        )
    ]

    slaves = [
        PortSpec(
            port_name='ddr_ooo',
            direction='slave',
            protocol='axi4',
            channels='rw',
            prefix='ddr_s_axi_',
            data_width=64,
            addr_width=32,
            id_width=4,
            base_addr=0x80000000,
            addr_range=0x80000000,
            enable_ooo=True
        ),
        PortSpec(
            port_name='sram_fifo',
            direction='slave',
            protocol='axi4',
            channels='rw',
            prefix='sram_s_axi_',
            data_width=64,
            addr_width=32,
            id_width=4,
            base_addr=0x40000000,
            addr_range=0x40000000,
            enable_ooo=False
        )
    ]

    connectivity = {
        'cpu_master': ['ddr_ooo', 'sram_fifo']
    }

    # Create component
    addr_decode = AddressDecodeComponent(masters, slaves, connectivity, addr_width=32)

    # Generate all logic
    output = addr_decode.generate_all()

    # Display signals
    print("Signal Declarations:")
    for sig in output['signals']:
        print(f"    {sig}")
    print()

    # Display AW decode logic
    print("AW Channel Decode Logic:")
    for inst in output['aw_decode']:
        print(f"    {inst}")
    print()

    # Display AW requests
    print("AW Arbiter Requests:")
    for inst in output['aw_requests']:
        print(f"    {inst}")
    print()

    print("=" * 70)
    print("✓ AddressDecodeComponent test complete!")
    print("=" * 70)
