# SPDX-License-Identifier: MIT
# SPDX-FileCopyrightText: 2024-2025 sean galloway
#
# RTL Design Sherpa - Industry-Standard RTL Design and Verification
# https://github.com/sean-galloway/RTLDesignSherpa
#
# Module: network_factories
# Purpose: Network Factory Functions - Following AXIL4 Pattern
#
# Documentation: bin/CocoTBFramework/README.md
# Subsystem: framework
#
# Author: sean galloway
# Created: 2025-10-18

"""
Network Factory Functions - Following AXIL4 Pattern

Creates Network Master and Slave interfaces with consistent API patterns
that follow the same structure as AXIL4 factories.

Features:
- Consistent API structure matching AXIL4 factories
- Enhanced Network v2.0 support with chunk_enables
- Integrated compliance checking
- Complete system creation with memory models
- Transaction-level convenience methods

Usage:
    # Create Network Master
    master = create_network_master(dut, clock, prefix="m_network_", log=log)
    await master['interface'].send_packet(channel=5, data=[0x1234], packet_type=NETWORK_PKT_TYPES.TS_PKT)

    # Create Network Slave
    slave = create_network_slave(dut, clock, prefix="s_network_", log=log)
    packet = await slave['interface'].receive_packet()

    # Create complete system
    system = create_network_system(dut, clock, prefix="network_", log=log)
"""

from typing import Dict, Any, List, Optional, Tuple
from contextlib import redirect_stdout
import io
import os

from .network_interfaces import MNOCMaster, MNOCSlave, NETWORK_PKT_TYPES, NETWORK_ACK_TYPES


def create_network_master(dut, clock, prefix="", log=None, **kwargs) -> Dict[str, Any]:
    """
    Create Network Master interface - API consistency with AXIL4.

    Args:
        dut: Device under test
        clock: Clock signal
        prefix: Signal prefix for Network interface
        log: Logger instance
        **kwargs: Additional configuration parameters
            - data_width: Data width (default: 512)
            - addr_width: Address width (default: 8)
            - num_channels: Number of channels (default: 32)
            - initial_credits: Initial credits per channel (default: 4)
            - timeout_cycles: Transaction timeout (default: 1000)
            - multi_sig: Multi-signal mode (default: False)

    Returns:
        Dictionary containing master interface and components
    """
    master = MNOCMaster(dut, clock, prefix, log=log, **kwargs)

    # API consistency with AXIL4 - return structured dictionary
    return {
        'PKT': master.packet_channel,        # Packet channel (GAXI Master)
        'ACK': master.ack_channel,           # ACK channel (GAXI Slave)
        'interface': master,                 # High-level interface
        'compliance_checker': master.compliance_checker,  # Compliance checker

        # Transaction methods for convenience
        'send_packet': master.send_packet,
        'send_config': master.send_config_packet,
        'send_ts': master.send_ts_packet,
        'send_rda': master.send_rda_packet,
        'send_raw': master.send_raw_packet,

        # Credit management
        'get_credits': master.get_credit_status,
        'has_credits': master._has_credits,
    }


def create_network_slave(dut, clock, prefix="", log=None, **kwargs) -> Dict[str, Any]:
    """
    Create Network Slave interface - API consistency with AXIL4.

    Args:
        dut: Device under test
        clock: Clock signal
        prefix: Signal prefix for Network interface
        log: Logger instance
        **kwargs: Additional configuration parameters
            - data_width: Data width (default: 512)
            - addr_width: Address width (default: 8)
            - num_channels: Number of channels (default: 32)
            - timeout_cycles: Transaction timeout (default: 1000)
            - auto_ack: Automatic ACK generation (default: True)
            - multi_sig: Multi-signal mode (default: False)

    Returns:
        Dictionary containing slave interface and components
    """
    slave = MNOCSlave(dut, clock, prefix, log=log, **kwargs)

    # API consistency with AXIL4 - return structured dictionary
    return {
        'PKT': slave.packet_channel,         # Packet channel (GAXI Slave)
        'ACK': slave.ack_channel,            # ACK channel (GAXI Master)
        'interface': slave,                  # High-level interface
        'compliance_checker': slave.compliance_checker,  # Compliance checker

        # Transaction methods for convenience
        'receive_packet': slave.receive_packet,
        'wait_for_packet': slave.wait_for_packet,
        'send_ack': slave.send_ack,
        'get_packets': slave.get_received_packets,
        'get_stats': slave.get_packet_statistics,
        'clear_packets': slave.clear_received_packets,
    }


def create_network_master_slave(dut, clock, prefix="", log=None, **kwargs) -> Tuple[MNOCMaster, MNOCSlave]:
    """
    Create both master and slave interfaces - API consistency with AXIL4.

    Args:
        dut: Device under test
        clock: Clock signal
        prefix: Signal prefix for Network interfaces
        log: Logger instance
        **kwargs: Configuration parameters passed to both interfaces

    Returns:
        Tuple of (MNOCMaster, MNOCSlave) instances
    """
    master = MNOCMaster(dut, clock, prefix + "m_", log=log, **kwargs)
    slave = MNOCSlave(dut, clock, prefix + "s_", log=log, **kwargs)

    return master, slave


def create_network_interface(dut, clock, prefix="", log=None, **kwargs) -> Dict[str, Any]:
    """
    Create complete Network interface (both master and slave) - API consistency with AXIL4.

    Args:
        dut: Device under test
        clock: Clock signal
        prefix: Signal prefix for Network interfaces
        log: Logger instance
        **kwargs: Configuration parameters

    Returns:
        Dictionary containing both master and slave interfaces
    """
    master = create_network_master(dut, clock, prefix + "m_", log=log, **kwargs)
    slave = create_network_slave(dut, clock, prefix + "s_", log=log, **kwargs)

    return {
        'master': master,
        'slave': slave,
        'master_interface': master['interface'],      # Alias for compatibility
        'slave_interface': slave['interface'],        # Alias for compatibility

        # Individual components for direct access
        'master_pkt': master['PKT'],
        'master_ack': master['ACK'],
        'slave_pkt': slave['PKT'],
        'slave_ack': slave['ACK'],

        # Compliance checkers
        'master_compliance_checker': master['compliance_checker'],
        'slave_compliance_checker': slave['compliance_checker'],

        # Convenience transaction methods
        'send_packet': master['send_packet'],
        'receive_packet': slave['receive_packet'],
    }


def create_network_system(dut, clock, prefix="", log=None, memory_model=None, **kwargs) -> Dict[str, Any]:
    """
    Create complete Network system with shared resources - API consistency with AXIL4.

    Args:
        dut: Device under test
        clock: Clock signal
        prefix: Signal prefix for Network system
        log: Logger instance
        memory_model: Optional shared memory model for testing
        **kwargs: Configuration parameters

    Returns:
        Dictionary containing complete Network system
    """
    from ..shared.memory_model import MemoryModel

    # Create shared memory model if not provided
    if memory_model is None:
        memory_model = MemoryModel(
            num_lines=1024,
            bytes_per_line=64,  # 512-bit Network packets
            log=log
        )

    # Add memory model to kwargs
    kwargs_with_memory = {**kwargs, 'memory_model': memory_model}

    # Create master and slave with shared memory
    master = create_network_master(dut, clock, prefix + "m_", log=log, **kwargs_with_memory)
    slave = create_network_slave(dut, clock, prefix + "s_", log=log, **kwargs_with_memory)

    return {
        'master': master,
        'slave': slave,
        'memory_model': memory_model,

        # Convenience transaction methods (similar to AXIL4)
        'send_config': master['send_config'],
        'send_ts': master['send_ts'],
        'send_rda': master['send_rda'],
        'send_raw': master['send_raw'],
        'receive_packet': slave['receive_packet'],

        # System-level utilities
        'get_master_credits': master['get_credits'],
        'get_slave_stats': slave['get_stats'],

        # All compliance checkers
        'master_compliance_checker': master['compliance_checker'],
        'slave_compliance_checker': slave['compliance_checker'],
    }


def create_network_test_environment(dut, clock, **kwargs) -> Dict[str, Any]:
    """
    Create complete Network test environment ready for immediate use.

    This convenience function creates a full system with sensible defaults
    and commonly needed configurations for testing.

    Args:
        dut: Device under test
        clock: Clock signal
        **kwargs: Configuration overrides

    Returns:
        Dictionary containing test environment with utilities
    """
    # Set test-friendly defaults
    test_defaults = {
        'data_width': 512,
        'addr_width': 8,
        'num_channels': 32,
        'initial_credits': 4,
        'timeout_cycles': 1000,
        'auto_ack': True,
        'multi_sig': False,
    }

    # Merge with user overrides
    config = {**test_defaults, **kwargs}
    log = kwargs.get('log')

    # Create system
    system = create_network_system(dut, clock, prefix="network_", log=log, **config)

    # Add test utilities
    system.update({
        'config': config,

        # Quick test methods
        'quick_send': lambda ch, data, pkt_type=NETWORK_PKT_TYPES.TS_PKT:
                    system['send_ts'](ch, data) if pkt_type == NETWORK_PKT_TYPES.TS_PKT else
                    system['master']['send_packet'](ch, data, pkt_type),

        'wait_for_any_packet': lambda timeout=None:
                            system['slave']['receive_packet'](timeout),

        'reset_system': lambda: system['slave']['clear_packets'](),

        # Status methods
        'system_status': lambda: {
            'master_credits': system['get_master_credits'](),
            'slave_stats': system['get_slave_stats'](),
            'compliance_master': system['master_compliance_checker'].get_compliance_report()
                            if system['master_compliance_checker'] else None,
            'compliance_slave': system['slave_compliance_checker'].get_compliance_report()
                            if system['slave_compliance_checker'] else None,
        }
    })

    return system


# ==============================================================================
# UNIFIED COMPLIANCE REPORTING (works for both Network and other protocols)
# ==============================================================================

def get_unified_compliance_reports(components: Dict[str, Any]) -> Dict[str, Any]:
    """
    Unified compliance report collection - works for Network, AXI4, AXIL4.

    Args:
        components: Dictionary of components (from create_*_system functions)

    Returns:
        Dictionary containing all compliance reports
    """
    reports = {}

    # Check for various compliance checker patterns
    checker_keys = [
        'master_compliance_checker', 'slave_compliance_checker',
        'master_write_compliance_checker', 'master_read_compliance_checker',
        'slave_write_compliance_checker', 'slave_read_compliance_checker',
        'compliance_checker'
    ]

    for key in checker_keys:
        if key in components and components[key]:
            try:
                report = components[key].get_compliance_report()
                if report:
                    reports[key] = report
            except AttributeError:
                # Skip if component doesn't have compliance reporting
                pass

    return reports


def print_unified_compliance_reports(components: Dict[str, Any], log=None):
    """
    Print all compliance reports in a unified format.

    Args:
        components: Dictionary of components
        log: Optional logger for output
    """
    reports = get_unified_compliance_reports(components)

    if not reports:
        message = "No compliance violations detected across all components."
        if log:
            log.info(message)
        else:
            print(message)
        return

    for checker_name, report in reports.items():
        header = f"=== {checker_name.upper()} COMPLIANCE REPORT ==="
        if log:
            log.info(header)
            log.info(f"Violations: {report.get('total_violations', 0)}")
            for violation in report.get('violations', []):
                log.warning(f"  {violation}")
        else:
            print(header)
            print(f"Violations: {report.get('total_violations', 0)}")
            for violation in report.get('violations', []):
                print(f"  {violation}")


def check_system_compliance(components: Dict[str, Any]) -> bool:
    """
    Check if system is compliant (no violations across all components).

    Args:
        components: Dictionary of components

    Returns:
        True if no violations found, False otherwise
    """
    reports = get_unified_compliance_reports(components)

    for report in reports.values():
        if report.get('total_violations', 0) > 0:
            return False

    return True


# ==============================================================================
# UTILITY FUNCTIONS FOR Network TESTING
# ==============================================================================

def create_network_packet_sequence(packet_configs: List[Dict[str, Any]]) -> List[Dict[str, Any]]:
    """
    Create a sequence of Network packets for testing.

    Args:
        packet_configs: List of packet configuration dictionaries

    Returns:
        List of prepared packet configurations
    """
    packets = []

    for i, config in enumerate(packet_configs):
        packet = {
            'channel': config.get('channel', 0),
            'data': config.get('data', [i]),
            'packet_type': config.get('packet_type', NETWORK_PKT_TYPES.TS_PKT),
            'chunk_enables': config.get('chunk_enables', 0xFFFF),
            'eos': config.get('eos', False),
            **config.get('extra_fields', {})
        }
        packets.append(packet)

    return packets


async def send_packet_sequence(master_interface, packet_sequence: List[Dict[str, Any]],
                            inter_packet_delay: int = 1):
    """
    Send a sequence of packets with optional delays.

    Args:
        master_interface: Network master interface
        packet_sequence: List of packet configurations
        inter_packet_delay: Delay between packets in cycles
    """
    import cocotb
    from cocotb.triggers import RisingEdge

    for packet in packet_sequence:
        await master_interface.send_packet(**packet)

        # Optional delay between packets
        if inter_packet_delay > 0:
            for _ in range(inter_packet_delay):
                await RisingEdge(master_interface.clock)


def validate_network_packet(packet, expected_config: Dict[str, Any]) -> bool:
    """
    Validate received Network packet matches expected configuration.

    Args:
        packet: Received Network packet
        expected_config: Expected packet configuration

    Returns:
        True if packet matches expectations
    """
    # Check basic fields
    if hasattr(packet, 'addr') and expected_config.get('channel') is not None:
        if packet.addr != expected_config['channel']:
            return False

    if hasattr(packet, 'payload_type') and expected_config.get('packet_type') is not None:
        if packet.payload_type != expected_config['packet_type'].value:
            return False

    if hasattr(packet, 'eos') and expected_config.get('eos') is not None:
        if packet.eos != expected_config['eos']:
            return False

    # Check chunk enables for v2.0 packets
    if hasattr(packet, 'chunk_enables') and expected_config.get('chunk_enables') is not None:
        if packet.chunk_enables != expected_config['chunk_enables']:
            return False

    return True
