#!/usr/bin/env python3
# SPDX-License-Identifier: MIT
# SPDX-FileCopyrightText: 2024-2025 sean galloway
#
# RTL Design Sherpa - Industry-Standard RTL Design and Verification
# https://github.com/sean-galloway/RTLDesignSherpa
#
# Module: TBAXIMonitorConfig
# Purpose: AXI Monitor Configuration Testbench
#
# Documentation: bin/CocoTBFramework/README.md
# Subsystem: framework
#
# Author: sean galloway
# Created: 2025-10-18

"""
AXI Monitor Configuration Testbench

This TB manages AXI monitor filtering configurations and packet monitoring.
Designed to work with existing TBBase infrastructure and MonbusSlave components.

Features:
- Static randomized filtering configurations
- Multi-level filtering: none, medium, high, error-interrupt-only
- Reset/reprogram test patterns
- Packet monitoring and validation
- Configuration conflict detection
- Integration with existing TB state sharing
"""

import asyncio
import random
from typing import Dict, List, Optional, Any
from collections import defaultdict, deque

import cocotb
from cocotb.triggers import RisingEdge, Timer
from cocotb.utils import get_sim_time

from CocoTBFramework.tbclasses.shared.tbbase import TBBase
from CocoTBFramework.tbclasses.monbus.monbus_slave import MonbusSlave
from CocoTBFramework.tbclasses.monbus.monbus_packet import MonbusPacket
from CocoTBFramework.tbclasses.monbus.monbus_types import ProtocolType, PktType


class TBAXIMonitorConfig(TBBase):
    """AXI Monitor Configuration and Packet Monitoring Testbench"""

    # Filter level configurations
    FILTER_CONFIGS = {
        "none": {
            "cfg_axi_pkt_mask": 0x0000,      # Drop nothing
            "cfg_axi_err_select": 0x0000,    # Route nothing to error FIFO
            "cfg_axi_error_mask": 0x0000,    # Show all error events
            "cfg_axi_timeout_mask": 0x0000,  # Show all timeout events
            "cfg_axi_compl_mask": 0x0000,    # Show all completion events
            "cfg_axi_thresh_mask": 0x0000,   # Show all threshold events
            "cfg_axi_perf_mask": 0x0000,     # Show all performance events
            "cfg_axi_addr_mask": 0x0000,     # Show all address match events
            "cfg_axi_debug_mask": 0x0000,    # Show all debug events
        },

        "medium": {
            "cfg_axi_pkt_mask": 0x0080,      # Drop debug packets (bit 7)
            "cfg_axi_err_select": 0x0003,    # Route error+timeout to error FIFO
            "cfg_axi_error_mask": 0x0000,    # Keep all errors
            "cfg_axi_timeout_mask": 0x0000,  # Keep all timeouts
            "cfg_axi_compl_mask": 0xFFF0,    # Drop routine completion events (bits 4-15)
            "cfg_axi_thresh_mask": 0xFF00,   # Drop high-frequency threshold events
            "cfg_axi_perf_mask": 0xFFC0,     # Drop most performance events
            "cfg_axi_addr_mask": 0xFF00,     # Drop most address match events
            "cfg_axi_debug_mask": 0xFFFF,    # Drop all debug events
        },

        "high": {
            "cfg_axi_pkt_mask": 0x00F8,      # Drop debug + perf + some others
            "cfg_axi_err_select": 0x0003,    # Route error+timeout to error FIFO
            "cfg_axi_error_mask": 0x0000,    # Keep all errors
            "cfg_axi_timeout_mask": 0x0000,  # Keep all timeouts
            "cfg_axi_compl_mask": 0xFFFE,    # Only show critical completions
            "cfg_axi_thresh_mask": 0xFFFC,   # Only show severe threshold violations
            "cfg_axi_perf_mask": 0xFFFE,     # Only show critical performance events
            "cfg_axi_addr_mask": 0xFFFF,     # Drop all address match events
            "cfg_axi_debug_mask": 0xFFFF,    # Drop all debug events
        },

        "error-interrupt-only": {
            "cfg_axi_pkt_mask": 0x00FC,      # Drop everything except error/timeout
            "cfg_axi_err_select": 0x0003,    # Route error+timeout to error FIFO
            "cfg_axi_error_mask": 0x0000,    # Always show errors
            "cfg_axi_timeout_mask": 0x0000,  # Always show timeouts
            "cfg_axi_compl_mask": 0xFFFF,    # Drop all completion events
            "cfg_axi_thresh_mask": 0xFFFE,   # Only critical threshold violations
            "cfg_axi_perf_mask": 0xFFFF,     # Drop all performance events
            "cfg_axi_addr_mask": 0xFFFF,     # Drop all address match events
            "cfg_axi_debug_mask": 0xFFFF,    # Drop all debug events
        }
    }

    def __init__(self, dut,
                 filter_level: str = "none",
                 randomize_configs: bool = False,
                 enable_packet_monitoring: bool = True,
                 expected_unit_id: Optional[int] = None,
                 expected_agent_id: Optional[int] = None,
                 **kwargs):
        """Initialize AXI Monitor Configuration TB

        Args:
            dut: Device under test
            filter_level: Initial filter level ("none", "medium", "high", "error-interrupt-only")
            randomize_configs: Whether to randomize filter configurations
            enable_packet_monitoring: Whether to enable monbus packet monitoring
            expected_unit_id: Expected unit ID for packet validation
            expected_agent_id: Expected agent ID for packet validation
        """
        super().__init__(dut, **kwargs)

        # Initialize clock
        self.clock = None
        self.clock_period_ns = 10  # Default 10ns period
        if hasattr(dut, 'aclk'):
            self.clock = dut.aclk
        elif hasattr(dut, 'clk'):
            self.clock = dut.clk

        self.filter_level = filter_level
        self.randomize_configs = randomize_configs
        self.enable_packet_monitoring = enable_packet_monitoring
        self.expected_unit_id = expected_unit_id
        self.expected_agent_id = expected_agent_id

        # Current configuration
        self.current_config = {}
        self.config_applied = False

        # Packet monitoring
        self.monbus_slave = None
        self.packet_stats = defaultdict(int)
        self.packet_history = deque(maxlen=1000)
        self.filter_violations = []

        # State sharing with other TBs
        self.shared_state = {
            'filter_level': filter_level,
            'packets_received': 0,
            'packets_filtered': 0,
            'config_errors': []
        }

        self.log.info(f"AXI Monitor Config TB initialized with filter_level='{filter_level}'")

    async def configure_monitor(self, filter_level: str = None, apply_immediately: bool = True):
        """Configure monitor filtering settings

        Args:
            filter_level: Filter level to apply (None = use current)
            apply_immediately: Whether to apply configuration immediately
        """
        if filter_level:
            self.filter_level = filter_level

        # Get base configuration
        if self.filter_level not in self.FILTER_CONFIGS:
            raise ValueError(f"Unknown filter level: {self.filter_level}")

        self.current_config = self.FILTER_CONFIGS[self.filter_level].copy()

        # Apply randomization if enabled
        if self.randomize_configs:
            self._randomize_config()

        # Apply configuration to DUT
        if apply_immediately:
            await self._apply_config_to_dut()

        # Update shared state
        self.shared_state['filter_level'] = self.filter_level

        self.log.info(f"Monitor configured for filter level '{self.filter_level}'")

    def _randomize_config(self):
        """Apply controlled randomization to filter configurations"""
        for key, base_value in self.current_config.items():
            if "mask" in key:
                # Randomize mask values while preserving filter level intent
                if self.filter_level == "none":
                    # Occasionally set a few random bits for testing
                    self.current_config[key] = random.choice([0x0000, 0x0001, 0x0002, 0x0004])
                elif self.filter_level == "medium":
                    # Vary medium-level filtering slightly
                    self.current_config[key] = base_value ^ random.randint(0, 0x000F)
                elif self.filter_level == "high":
                    # High filtering with some random variation
                    self.current_config[key] = base_value ^ random.randint(0, 0x0003)
                else:  # error-interrupt-only
                    # Very little randomization for production mode
                    self.current_config[key] = base_value ^ random.choice([0, 0, 0, 1])

        self.log.debug(f"Applied randomization to config: {self.current_config}")

    async def _apply_config_to_dut(self):
        """Apply current configuration to DUT signals"""
        # Check if DUT has the configuration signals
        config_signals = [
            'cfg_axi_pkt_mask', 'cfg_axi_err_select', 'cfg_axi_error_mask',
            'cfg_axi_timeout_mask', 'cfg_axi_compl_mask', 'cfg_axi_thresh_mask',
            'cfg_axi_perf_mask', 'cfg_axi_addr_mask', 'cfg_axi_debug_mask'
        ]

        for signal_name in config_signals:
            if hasattr(self.dut, signal_name):
                signal = getattr(self.dut, signal_name)
                value = self.current_config.get(signal_name, 0)
                signal.value = value
                self.log.debug(f"Set {signal_name} = 0x{value:04X}")
            else:
                self.log.warning(f"DUT missing signal: {signal_name}")

        # Wait a few cycles for configuration to propagate
        await self._wait_cycles(3)

        # Check for configuration conflicts
        await self._check_config_conflicts()

        self.config_applied = True
        self.log.info(f"Configuration applied to DUT for level '{self.filter_level}'")

    async def _check_config_conflicts(self):
        """Check for configuration conflicts and log warnings"""
        if hasattr(self.dut, 'cfg_conflict_error'):
            await self._wait_cycles(1)  # Allow conflict detection to settle
            if self.dut.cfg_conflict_error.value:
                conflict_msg = f"Configuration conflict detected for level '{self.filter_level}'"
                self.log.warning(conflict_msg)
                self.shared_state['config_errors'].append(conflict_msg)
                self.filter_violations.append({
                    'type': 'config_conflict',
                    'level': self.filter_level,
                    'time': get_sim_time(),
                    'config': self.current_config.copy()
                })

    async def setup_packet_monitoring(self):
        """Setup MonbusSlave for packet monitoring"""
        if not self.enable_packet_monitoring:
            return

        # Check if DUT has monbus signals
        if not (hasattr(self.dut, 'monbus_valid') and
                hasattr(self.dut, 'monbus_ready') and
                hasattr(self.dut, 'monbus_packet')):
            self.log.warning("DUT missing monbus signals - packet monitoring disabled")
            self.enable_packet_monitoring = False
            return

        # Initialize MonbusSlave
        self.monbus_slave = MonbusSlave(
            dut=self.dut,
            title="AXI Monitor Packet Monitor",
            prefix="",
            clock=self.clock,
            bus_name='monbus',
            expected_unit_id=self.expected_unit_id,
            expected_agent_id=self.expected_agent_id,
            expected_protocol=ProtocolType.PROTOCOL_AXI,  # AXI protocol = 0
            timeout_cycles=1000,
            ready_probability=0.9,  # High ready probability for monitoring
            log=self.log
        )

        # Start packet monitoring task
        cocotb.start_soon(self._monitor_packets_task())

        self.log.info("Packet monitoring setup complete")

    async def _monitor_packets_task(self):
        """Background task to monitor and validate packets"""
        if not self.monbus_slave:
            return

        while True:
            try:
                # Get packet with timeout
                packet = await asyncio.wait_for(
                    self.monbus_slave.get_packet_async(),
                    timeout=1.0
                )

                if packet:
                    await self._process_received_packet(packet)

            except asyncio.TimeoutError:
                # No packets received - this is normal
                continue
            except Exception as e:
                self.log.error(f"Error in packet monitoring: {e}")
                break

    async def _process_received_packet(self, packet):
        """Process a received packet and check filtering"""
        # Update statistics
        self.packet_stats['total_received'] += 1
        self.packet_stats[f'pkt_type_{packet.pkt_type}'] += 1
        self.packet_history.append({
            'packet': packet,
            'time': get_sim_time(),
            'filter_level': self.filter_level
        })

        # Update shared state
        self.shared_state['packets_received'] = self.packet_stats['total_received']

        # Validate packet should have been filtered
        should_be_filtered = self._should_packet_be_filtered(packet)
        if should_be_filtered:
            violation = {
                'type': 'unexpected_packet',
                'packet': packet,
                'filter_level': self.filter_level,
                'time': get_sim_time(),
                'reason': 'packet should have been filtered'
            }
            self.filter_violations.append(violation)
            self.log.warning(f"Filter violation: Unexpected packet type {packet.pkt_type} "
                           f"at filter level '{self.filter_level}'")

        self.log.debug(f"Received packet: type={packet.pkt_type}, protocol={packet.protocol}, "
                      f"event_code={packet.event_code}")

    def _should_packet_be_filtered(self, packet) -> bool:
        """Check if a packet should have been filtered based on current config"""
        if not self.current_config:
            return False

        pkt_type = packet.pkt_type
        event_code = packet.event_code

        # Check packet type mask
        if self.current_config.get('cfg_axi_pkt_mask', 0) & (1 << pkt_type):
            return True

        # Check individual event masks based on packet type
        mask_map = {
            PktType.ERROR: 'cfg_axi_error_mask',
            PktType.TIMEOUT: 'cfg_axi_timeout_mask',
            PktType.COMPLETION: 'cfg_axi_compl_mask',
            PktType.THRESHOLD: 'cfg_axi_thresh_mask',
            PktType.PERF: 'cfg_axi_perf_mask',
            PktType.ADDR_MATCH: 'cfg_axi_addr_mask',
            PktType.DEBUG: 'cfg_axi_debug_mask'
        }

        if pkt_type in mask_map:
            mask_key = mask_map[pkt_type]
            event_mask = self.current_config.get(mask_key, 0)
            if event_mask & (1 << event_code):
                return True

        return False

    async def run_multi_level_test(self, levels: List[str] = None,
                                 cycles_per_level: int = 1000):
        """Run test with multiple filter levels and reset/reprogram pattern

        Args:
            levels: List of filter levels to test (None = all levels)
            cycles_per_level: Simulation cycles to run at each level
        """
        if levels is None:
            levels = ["none", "medium", "high", "error-interrupt-only"]

        self.log.info(f"Starting multi-level test with levels: {levels}")

        for level in levels:
            self.log.info(f"Testing filter level: {level}")

            # Reset statistics for this level
            level_start_stats = self.packet_stats.copy()

            # Configure and apply new level
            await self.configure_monitor(level)

            # Run for specified cycles
            await self._wait_cycles(cycles_per_level)

            # Analyze results for this level
            await self._analyze_level_results(level, level_start_stats)

        self.log.info("Multi-level test completed")

    async def _analyze_level_results(self, level: str, start_stats: Dict):
        """Analyze packet results for a specific filter level"""
        packets_this_level = (self.packet_stats['total_received'] -
                            start_stats.get('total_received', 0))

        self.log.info(f"Level '{level}' results: {packets_this_level} packets received")

        # Check expected packet reduction
        if level != "none" and packets_this_level > 0:
            # Validate that filtering is working
            recent_packets = [p for p in self.packet_history
                            if p['filter_level'] == level][-packets_this_level:]

            unexpected_count = len([p for p in recent_packets
                                  if self._should_packet_be_filtered(p['packet'])])

            if unexpected_count > 0:
                self.log.warning(f"Level '{level}': {unexpected_count} unexpected packets")

    def get_statistics(self) -> Dict[str, Any]:
        """Get current monitoring statistics"""
        return {
            'filter_level': self.filter_level,
            'config_applied': self.config_applied,
            'current_config': self.current_config.copy(),
            'packet_stats': dict(self.packet_stats),
            'filter_violations': len(self.filter_violations),
            'shared_state': self.shared_state.copy()
        }

    def get_shared_state(self) -> Dict[str, Any]:
        """Get shared state for inter-TB communication"""
        return self.shared_state

    async def wait_for_packets(self, min_packets: int = 1, timeout_cycles: int = 10000):
        """Wait for minimum number of packets to be received"""
        start_count = self.packet_stats['total_received']
        start_time = get_sim_time()

        while (self.packet_stats['total_received'] - start_count) < min_packets:
            await self._wait_cycles(10)

            if get_sim_time() - start_time > timeout_cycles * self.clock_period_ns:
                self.log.warning(f"Timeout waiting for {min_packets} packets")
                break

        packets_received = self.packet_stats['total_received'] - start_count
        self.log.info(f"Received {packets_received} packets")
        return packets_received

    async def _wait_cycles(self, count: int = 1):
        """Wait for specified number of clock cycles"""
        if hasattr(self.dut, 'aclk'):
            clk = self.dut.aclk
        elif hasattr(self.dut, 'clk'):
            clk = self.dut.clk
        else:
            # Fallback to timer if no clock found
            await Timer(count * 10, units='ns')
            return

        for _ in range(count):
            await RisingEdge(clk)