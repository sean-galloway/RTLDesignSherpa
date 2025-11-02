# SPDX-License-Identifier: MIT
# SPDX-FileCopyrightText: 2024-2025 sean galloway
#
# RTL Design Sherpa - Industry-Standard RTL Design and Verification
# https://github.com/sean-galloway/RTLDesignSherpa
#
# Module: APBMonitorConfiguration
# Purpose: APB Monitor Core Testbench
#
# Documentation: bin/CocoTBFramework/README.md
# Subsystem: framework
#
# Author: sean galloway
# Created: 2025-10-18

"""
APB Monitor Core Testbench

Handles basic setup, configuration, and ready signal timing.
Individual test classes will inherit from this and provide specific configurations.
"""

import os
import random
import asyncio
from typing import Dict, List, Optional, Tuple, Any

import cocotb
from cocotb.triggers import RisingEdge, Timer, FallingEdge
from cocotb.utils import get_sim_time

from CocoTBFramework.tbclasses.shared.tbbase import TBBase
from CocoTBFramework.components.gaxi.gaxi_master import GAXIMaster
from CocoTBFramework.components.gaxi.gaxi_packet import GAXIPacket
from CocoTBFramework.components.shared.flex_randomizer import FlexRandomizer
from CocoTBFramework.tbclasses.amba.amba_random_configs import AXI_RANDOMIZER_CONFIGS

from CocoTBFramework.tbclasses.monbus.monbus_slave import MonbusSlave
from .apb_monitor_packets import (
    APBCommandPacket, APBResponsePacket, create_apb_write_cmd, create_apb_read_cmd,
    create_apb_ok_rsp, create_apb_error_rsp, format_packet_summary
)
from .apb_monitor_scoreboard import APBMonitorScoreboard, APBScoreboardConfig
from CocoTBFramework.tbclasses.apb.apbgaxiconfig import APBGAXIConfig


class APBMonitorConfiguration:
    """Configuration class for APB monitor settings"""

    def __init__(self):
        # Error detection configuration
        self.error_enable = False
        self.timeout_enable = False
        self.protocol_enable = False
        self.slverr_enable = False

        # Performance monitoring configuration
        self.perf_enable = False
        self.latency_enable = False
        self.throughput_enable = False

        # Debug configuration
        self.debug_enable = False
        self.trans_debug_enable = False
        self.debug_level = 0x0

        # Threshold and timeout values
        self.cmd_timeout_cnt = 100
        self.rsp_timeout_cnt = 200
        self.latency_threshold = 1000
        self.throughput_threshold = 10

    def enable_error_detection(self, enable_protocol=True, enable_slverr=True,
                              enable_timeout=True):
        """Enable error detection features"""
        self.error_enable = True
        self.protocol_enable = enable_protocol
        self.slverr_enable = enable_slverr
        self.timeout_enable = enable_timeout
        return self

    def enable_performance_monitoring(self, enable_latency=True, enable_throughput=True):
        """Enable performance monitoring features"""
        self.perf_enable = True
        self.latency_enable = enable_latency
        self.throughput_enable = enable_throughput
        return self

    def enable_debug_monitoring(self, trans_debug=True, debug_level=0xF):
        """Enable debug monitoring features"""
        self.debug_enable = True
        self.trans_debug_enable = trans_debug
        self.debug_level = debug_level
        return self

    def set_timeouts(self, cmd_timeout=100, rsp_timeout=200):
        """Set timeout values"""
        self.cmd_timeout_cnt = cmd_timeout
        self.rsp_timeout_cnt = rsp_timeout
        return self

    def set_thresholds(self, latency_threshold=1000, throughput_threshold=10):
        """Set performance thresholds"""
        self.latency_threshold = latency_threshold
        self.throughput_threshold = throughput_threshold
        return self


class ReadySignalPattern:
    """Configuration for ready signal patterns"""

    def __init__(self):
        self.cmd_pattern = 'immediate'  # 'immediate', 'delayed', 'random'
        self.rsp_pattern = 'immediate'
        self.cmd_delay_cycles = 0
        self.rsp_delay_cycles = 0

    @classmethod
    def immediate(cls):
        """Both cmd and rsp ready immediately"""
        config = cls()
        config.cmd_pattern = 'immediate'
        config.rsp_pattern = 'immediate'
        return config

    @classmethod
    def delayed(cls, cmd_delay=5, rsp_delay=5):
        """Both cmd and rsp ready after specified delays"""
        config = cls()
        config.cmd_pattern = 'delayed'
        config.rsp_pattern = 'delayed'
        config.cmd_delay_cycles = cmd_delay
        config.rsp_delay_cycles = rsp_delay
        return config

    @classmethod
    def random_backpressure(cls):
        """Random ready patterns for stress testing"""
        config = cls()
        config.cmd_pattern = 'random'
        config.rsp_pattern = 'random'
        return config


class APBMonitorCoreTB(TBBase):
    """
    Core APB Monitor testbench - handles setup, configuration, and basic operations.
    Individual test classes inherit from this and provide specific test configurations.
    """

    def __init__(self, dut):
        """Initialize core APB monitor testbench"""
        super().__init__(dut)

        # Get test parameters from environment
        self.SEED = self.convert_to_int(os.environ.get('SEED', '42'))
        self.AW = self.convert_to_int(os.environ.get('TEST_AW', '32'))
        self.DW = self.convert_to_int(os.environ.get('TEST_DW', '32'))
        self.UNIT_ID = self.convert_to_int(os.environ.get('TEST_UNIT_ID', '1'))
        self.AGENT_ID = self.convert_to_int(os.environ.get('TEST_AGENT_ID', '10'))
        self.MAX_TRANSACTIONS = self.convert_to_int(os.environ.get('TEST_MAX_TRANSACTIONS', '4'))

        self.super_debug = True
        self.TIMEOUT_CYCLES = 1000

        # Calculate derived parameters
        self.SW = self.DW // 8

        # Initialize random generator
        random.seed(self.SEED)

        # Create APB GAXI configuration for consistent field definitions
        self.apb_config = APBGAXIConfig(addr_width=self.AW, data_width=self.DW)
        self.cmd_field_config = self.apb_config.create_cmd_field_config()
        self.rsp_field_config = self.apb_config.create_rsp_field_config()

        # GAXI components (will be initialized in setup)
        self.cmd_master = None
        self.rsp_master = None
        self.monbus_slave = None

        # Randomizers
        self.cmd_randomizer = FlexRandomizer(AXI_RANDOMIZER_CONFIGS['fast']['master'])
        self.rsp_randomizer = FlexRandomizer(AXI_RANDOMIZER_CONFIGS['fast']['master'])
        self.monbus_randomizer = FlexRandomizer(AXI_RANDOMIZER_CONFIGS['fast']['slave'])

        # Ready signal control
        self.ready_pattern = ReadySignalPattern.immediate()

        # Scoreboard
        self.scoreboard = None

        # Test state
        self.test_stats = {
            'cmd_packets_sent': 0,
            'rsp_packets_sent': 0,
            'monitor_packets_received': 0,
        }

        self.log.info(f"APB Monitor Core TB initialized")
        self.log.info(f"  Parameters: AW={self.AW}, DW={self.DW}, SW={self.SW}")
        self.log.info(f"  IDs: UNIT={self.UNIT_ID}, AGENT={self.AGENT_ID}")
        self.log.info(f"  Max transactions: {self.MAX_TRANSACTIONS}")

    async def setup_clocks_and_reset(self, monitor_config: APBMonitorConfiguration = None,
                                   ready_config: ReadySignalPattern = None):
        """Setup clocks, reset, and initialize components with specific configuration"""

        if monitor_config is None:
            monitor_config = APBMonitorConfiguration()
        if ready_config is None:
            ready_config = ReadySignalPattern.immediate()

        self.ready_pattern = ready_config

        # Start clock
        await self.start_clock('aclk', 10, 'ns')

        self.log.info("Creating APB monitor testbench components...")

        # 1. Create CMD Master (drives cmd_* interface)
        self.cmd_master = GAXIMaster(
            dut=self.dut,
            title="CMD_Master",
            prefix="",
            bus_name="",
            pkt_prefix="cmd",
            multi_sig=True,
            clock=self.dut.aclk,
            field_config=self.cmd_field_config,
            timeout_cycles=self.TIMEOUT_CYCLES,
            mode='skid',
            randomizer=self.cmd_randomizer,
            log=self.log,
            super_debug=self.super_debug
        )

        # 2. Create RSP Master (drives rsp_* interface)
        self.rsp_master = GAXIMaster(
            dut=self.dut,
            title="RSP_Master",
            prefix="",
            bus_name="",
            pkt_prefix="rsp",
            multi_sig=True,
            clock=self.dut.aclk,
            field_config=self.rsp_field_config,
            timeout_cycles=self.TIMEOUT_CYCLES,
            mode='skid',
            randomizer=self.rsp_randomizer,
            log=self.log,
            super_debug=self.super_debug
        )

        # 3. Create Monitor Bus Slave (receives monbus packets)
        self.monbus_slave = MonbusSlave(
            dut=self.dut,
            title="MonBus_Slave",
            prefix="",
            clock=self.dut.aclk,
            bus_name="monbus",
            pkt_prefix="",
            expected_unit_id=self.UNIT_ID,
            expected_agent_id=self.AGENT_ID,
            expected_protocol=MonbusProtocol.APB,
            randomizer=self.monbus_randomizer,
            timeout_cycles=self.TIMEOUT_CYCLES,
            log=self.log,
            super_debug=self.super_debug
        )

        # 4. Create scoreboard
        scoreboard_config = APBScoreboardConfig(
            max_transactions=self.MAX_TRANSACTIONS,
            verbose_logging=self.super_debug,
            log_all_packets=self.super_debug,
            enable_strobe_validation=True,
            enable_protection_validation=True,
            enable_phase_timing_validation=True
        )

        self.scoreboard = APBMonitorScoreboard(
            log=self.log,
            component_name="APB_MONITOR_SB",
            config=scoreboard_config
        )

        # 5. Setup monitor bus packet handling
        self._setup_monbus_callbacks()

        # 6. Apply reset and configure monitor
        self.dut.aresetn.value = 0
        await self._apply_monitor_configuration(monitor_config)
        await self.wait_clocks('aclk', 10)

        # 7. Release reset
        self.dut.aresetn.value = 1
        await self.wait_clocks('aclk', 5)

        # 8. Setup ready signal control
        await self._setup_ready_control()

        self.log.info("APB Monitor testbench setup complete")

    def _setup_monbus_callbacks(self):
        """Setup callbacks for MonbusSlave packet handling"""
        def monbus_packet_callback(packet):
            """Handle monitor bus packets from DUT"""
            self.test_stats['monitor_packets_received'] += 1

            # Record in scoreboard
            self.scoreboard.record_monitor_packet(packet)

            time_str = self.get_time_ns_str()
            self.log.info(f"📦 Monitor packet{time_str}: {packet.get_packet_type_name()}.{packet.get_event_code_name()}")

        # Add callback to MonbusSlave
        self.monbus_slave.add_packet_callback(monbus_packet_callback)

    async def _apply_monitor_configuration(self, config: APBMonitorConfiguration):
        """Apply the specified monitor configuration to DUT"""
        self.log.info(f"Applying monitor configuration:")
        self.log.info(f"  Error: {config.error_enable}, Debug: {config.debug_enable}, Perf: {config.perf_enable}")

        # Error detection enables
        self.dut.cfg_error_enable.value = int(config.error_enable)
        self.dut.cfg_timeout_enable.value = int(config.timeout_enable)
        self.dut.cfg_protocol_enable.value = int(config.protocol_enable)
        self.dut.cfg_slverr_enable.value = int(config.slverr_enable)

        # Performance monitoring
        self.dut.cfg_perf_enable.value = int(config.perf_enable)
        self.dut.cfg_latency_enable.value = int(config.latency_enable)
        self.dut.cfg_throughput_enable.value = int(config.throughput_enable)

        # Debug enables
        self.dut.cfg_debug_enable.value = int(config.debug_enable)
        self.dut.cfg_trans_debug_enable.value = int(config.trans_debug_enable)
        self.dut.cfg_debug_level.value = config.debug_level

        # Timeout thresholds
        self.dut.cfg_cmd_timeout_cnt.value = config.cmd_timeout_cnt
        self.dut.cfg_rsp_timeout_cnt.value = config.rsp_timeout_cnt
        self.dut.cfg_latency_threshold.value = config.latency_threshold
        self.dut.cfg_throughput_threshold.value = config.throughput_threshold

    async def _setup_ready_control(self):
        """Setup ready signal control based on pattern"""
        if self.ready_pattern.cmd_pattern == 'immediate':
            self.dut.cmd_ready.value = 1
        else:
            self.dut.cmd_ready.value = 0

        if self.ready_pattern.rsp_pattern == 'immediate':
            self.dut.rsp_ready.value = 1
        else:
            self.dut.rsp_ready.value = 0

        self.log.info(f"Ready patterns: CMD={self.ready_pattern.cmd_pattern}, RSP={self.ready_pattern.rsp_pattern}")

    async def send_apb_command(self, cmd_packet: APBCommandPacket) -> int:
        """Send APB command packet"""
        # Convert to GAXI packet
        gaxi_cmd = GAXIPacket(self.cmd_field_config)
        gaxi_cmd.pwrite = cmd_packet.pwrite
        gaxi_cmd.paddr = cmd_packet.paddr
        gaxi_cmd.pwdata = cmd_packet.pwdata
        gaxi_cmd.pstrb = cmd_packet.pstrb
        gaxi_cmd.pprot = cmd_packet.pprot

        # Send command
        await self.cmd_master.send(gaxi_cmd)

        # Record in scoreboard
        txn_id = self.scoreboard.record_command(cmd_packet, get_sim_time('ns'))

        self.test_stats['cmd_packets_sent'] += 1

        self.log.debug(f"📤 CMD sent: ID={txn_id:02X} {format_packet_summary(cmd_packet)}")
        return txn_id

    async def send_apb_response(self, rsp_packet: APBResponsePacket, transaction_id: Optional[int] = None):
        """Send APB response packet"""
        # Convert to GAXI packet
        gaxi_rsp = GAXIPacket(self.rsp_field_config)
        gaxi_rsp.prdata = rsp_packet.prdata
        gaxi_rsp.pslverr = rsp_packet.pslverr

        # Send response
        await self.rsp_master.send(gaxi_rsp)

        # Record in scoreboard
        matched = self.scoreboard.record_response(rsp_packet, get_sim_time('ns'), transaction_id)

        self.test_stats['rsp_packets_sent'] += 1

        status = "✅" if matched else "❌"
        self.log.debug(f"📤 RSP sent {status}: {format_packet_summary(rsp_packet)}")

    async def send_write_transaction(self, addr: int, data: int, strb: int = None,
                                   expect_error: bool = False, response_delay: int = 5) -> int:
        """Send complete write transaction (command + response)"""
        if strb is None:
            strb = (1 << self.SW) - 1

        # Send command
        cmd = create_apb_write_cmd(addr, data, strb, 0, self.AW, self.DW)
        txn_id = await self.send_apb_command(cmd)

        # Wait before sending response
        await self.wait_clocks('aclk', response_delay)

        # Send response
        if expect_error:
            rsp = create_apb_error_rsp(0, self.DW)
        else:
            rsp = create_apb_ok_rsp(0, self.DW)

        await self.send_apb_response(rsp, txn_id)

        return txn_id

    async def send_read_transaction(self, addr: int, read_data: int = None,
                                  expect_error: bool = False, response_delay: int = 5) -> int:
        """Send complete read transaction (command + response)"""
        if read_data is None:
            read_data = random.randint(0, (1 << self.DW) - 1)

        # Send command
        cmd = create_apb_read_cmd(addr, 0, self.AW, self.DW)
        txn_id = await self.send_apb_command(cmd)

        # Wait before sending response
        await self.wait_clocks('aclk', response_delay)

        # Send response
        if expect_error:
            rsp = create_apb_error_rsp(read_data, self.DW)
        else:
            rsp = create_apb_ok_rsp(read_data, self.DW)

        await self.send_apb_response(rsp, txn_id)

        return txn_id

    async def wait_for_monitor_packets(self, expected_count: int, timeout_cycles: int = 100):
        """Wait for expected number of monitor packets"""
        for cycle in range(timeout_cycles):
            if self.test_stats['monitor_packets_received'] >= expected_count:
                return True
            await self.wait_clocks('aclk', 1)

        self.log.warning(f"Timeout waiting for {expected_count} monitor packets, got {self.test_stats['monitor_packets_received']}")
        return False

    def get_monitor_packets_by_type(self, packet_type):
        """Get monitor packets of specific type"""
        if hasattr(self.monbus_slave, 'get_received_packets'):
            return self.monbus_slave.get_received_packets(packet_type)
        return []

    def get_test_statistics(self) -> Dict[str, Any]:
        """Get comprehensive test statistics"""
        stats = self.test_stats.copy()

        if self.scoreboard:
            stats.update(self.scoreboard.get_statistics())

        if self.monbus_slave:
            monbus_stats = self.monbus_slave.get_statistics()
            stats['monbus_stats'] = monbus_stats

        return stats

    async def shutdown(self):
        """Properly shutdown all components"""
        self.log.info("Shutting down APB Monitor Core testbench...")

        # Final wait for any pending transactions
        await self.wait_clocks('aclk', 10)

        # Log final statistics
        final_stats = self.get_test_statistics()
        self.log.info(f"Final test statistics: {final_stats}")
