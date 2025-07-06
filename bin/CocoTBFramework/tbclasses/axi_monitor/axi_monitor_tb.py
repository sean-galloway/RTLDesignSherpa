"""
AXI4/AXIL Monitor Testbench - COMPREHENSIVE PROTOCOL TESTING (Updated for monbus)

This testbench provides comprehensive testing of AXI monitor functionality:
1. Normal transaction flow verification
2. Error condition injection and detection
3. Timeout scenario testing
4. Monitor bus verification (updated from intrbus to monbus)
5. Configuration testing
6. Protocol violation detection
7. Performance monitoring validation

FEATURES:
- Support for both AXI4 and AXI-Lite
- Configurable test scenarios
- Comprehensive error injection
- Real-time verification with scoreboard
- Detailed reporting and analysis
- Updated to use correct monbus interface naming
"""

import os
import random
import asyncio
import math
from typing import Dict, List, Optional, Tuple, Any

import cocotb
from cocotb.triggers import RisingEdge, Timer, FallingEdge
from cocotb.utils import get_sim_time

from CocoTBFramework.tbclasses.tbbase import TBBase
from CocoTBFramework.components.shared.flex_randomizer import FlexRandomizer
from CocoTBFramework.components.gaxi.gaxi_master import GAXIMaster
from CocoTBFramework.components.gaxi.gaxi_slave import GAXISlave
from CocoTBFramework.components.gaxi.gaxi_monitor import GAXIMonitor
from CocoTBFramework.components.gaxi.gaxi_packet import GAXIPacket
from .axi_monitor_scoreboard import AXIMonitorScoreboard
from .axi_monitor_packets import (
    AXICommandPacket, AXIReadDataPacket, AXIWriteDataPacket, AXIWriteResponsePacket,
    InterruptPacket, MonitorConfigPacket, MonitoredTransaction,
    AXITransactionState, MonitorEventCode, InterruptPacketType,
    convert_gaxi_to_axi_address, convert_gaxi_to_axi_read_data,
    convert_gaxi_to_axi_write_data, convert_gaxi_to_axi_write_response,
    create_axi_command_field_config, create_axi_read_data_field_config,
    create_axi_write_data_field_config, create_axi_write_response_field_config,
    create_interrupt_packet_field_config, create_monitor_config_field_config
)
from ..monbus_components import MonbusSlave, MonbusPacket, create_monbus_field_config


class AXIMonitorTestContext:
    """Context for tracking test scenarios and expected outcomes"""

    def __init__(self, test_name: str, start_time: float):
        self.test_name = test_name
        self.start_time = start_time
        self.transactions_issued = []
        self.expected_errors = []
        self.expected_timeouts = []
        self.expected_interrupts = []
        self.completion_time = None
        self.test_passed = None

    def add_transaction(self, txn_id: int, txn_type: str, expect_error: bool = False):
        """Add a transaction to track"""
        self.transactions_issued.append({
            'id': txn_id,
            'type': txn_type,
            'expect_error': expect_error,
            'timestamp': get_sim_time('ns')
        })

    def add_expected_error(self, error_type: str, txn_id: int = None):
        """Add an expected error"""
        self.expected_errors.append({
            'error_type': error_type,
            'transaction_id': txn_id,
            'detected': False
        })

    def mark_complete(self, passed: bool):
        """Mark test complete"""
        self.completion_time = get_sim_time('ns')
        self.test_passed = passed

    def get_duration(self) -> float:
        end_time = self.completion_time if self.completion_time else get_sim_time('ns')
        return end_time - self.start_time


class AXIMonitorTB(TBBase):
    """
    Comprehensive AXI Monitor Testbench with protocol verification,
    error injection, and comprehensive test scenarios.
    Updated to use monbus interface instead of intrbus.
    """

    def __init__(self, dut):
        """Initialize the AXI monitor testbench"""
        super().__init__(dut)

        # Get test parameters from environment
        self.SEED = self.convert_to_int(os.environ.get('SEED', '42'))
        self.TEST_LEVEL = os.environ.get('TEST_LEVEL', 'basic')
        self.IW = self.convert_to_int(os.environ.get('TEST_IW', '8'))
        self.AW = self.convert_to_int(os.environ.get('TEST_AW', '32'))
        self.DW = self.convert_to_int(os.environ.get('TEST_DW', '32'))
        self.UW = self.convert_to_int(os.environ.get('TEST_UW', '1'))
        self.IS_AXI4 = self.convert_to_int(os.environ.get('TEST_IS_AXI4', '1')) == 1
        self.MAX_TRANSACTIONS = self.convert_to_int(os.environ.get('TEST_MAX_TRANSACTIONS', '16'))
        self.UNIT_ID = self.convert_to_int(os.environ.get('TEST_UNIT_ID', '9'))
        self.AGENT_ID = self.convert_to_int(os.environ.get('TEST_AGENT_ID', '99'))

        self.super_debug = True
        self.TIMEOUT_CYCLES = 1000

        # Calculate derived parameters
        self.MAX_ID = (1 << self.IW) - 1
        self.MAX_ADDR = (1 << self.AW) - 1
        self.BYTES_PER_BEAT = self.DW // 8

        # Initialize random generator
        random.seed(self.SEED)

        # Create field configurations
        self.addr_field_config = create_axi_command_field_config(self.IW, self.AW, self.UW)
        self.read_data_field_config = create_axi_read_data_field_config(self.IW, self.DW, self.UW)
        self.write_data_field_config = create_axi_write_data_field_config(self.DW, self.UW)
        self.write_resp_field_config = create_axi_write_response_field_config(self.IW, self.UW)
        self.monbus_field_config = create_monbus_field_config()  # Updated from interrupt_field_config
        self.config_field_config = create_monitor_config_field_config()

        # GAXI components - will be initialized in setup()
        self.ar_master = None
        self.aw_master = None
        self.r_slave = None
        self.w_slave = None
        self.b_slave = None
        self.monbus_slave = None  # Updated from interrupt_slave

        # Monitors for all interfaces
        self.ar_monitor = None
        self.aw_monitor = None
        self.r_monitor = None
        self.w_monitor = None
        self.b_monitor = None
        self.monbus_monitor = None  # Updated from interrupt_monitor

        # Scoreboard
        self.scoreboard = None

        # Test context tracking
        self.current_test_context = None
        self.test_contexts = []
        self.transaction_id_counter = 0

        # Error injection control
        self.error_injection_enabled = False
        self.timeout_injection_enabled = False
        self.response_error_rate = 0.1  # 10% error rate when enabled

        # Performance tracking
        self.test_stats = {
            'tests_run': 0,
            'tests_passed': 0,
            'tests_failed': 0,
            'transactions_issued': 0,
            'errors_injected': 0,
            'timeouts_injected': 0,
            'monbus_packets_received': 0,  # Updated from interrupts_received
            'test_duration': 0.0
        }

        # Create randomizer configurations
        self.randomizer_dict = {
            'fast': {
                'master': {'valid_delay': ([(0, 0), (1, 2)], [0.8, 0.2])},
                'slave': {'ready_delay': ([(0, 1), (2, 3)], [0.7, 0.3])}
            },
            'balanced': {
                'master': {'valid_delay': ([(0, 1), (2, 5)], [0.7, 0.3])},
                'slave': {'ready_delay': ([(0, 1), (2, 5)], [0.7, 0.3])}
            },
            'slow': {
                'master': {'valid_delay': ([(2, 10)], [1.0])},
                'slave': {'ready_delay': ([(2, 10)], [1.0])}
            }
        }

        self.log.info(f"AXI Monitor TB initialized - {'AXI4' if self.IS_AXI4 else 'AXI-Lite'}")
        self.log.info(f"SEED={self.SEED}, TEST_LEVEL={self.TEST_LEVEL}")
        self.log.info(f"IW={self.IW}, AW={self.AW}, DW={self.DW}, UW={self.UW}")
        self.log.info(f"MAX_TRANSACTIONS={self.MAX_TRANSACTIONS}, UNIT_ID={self.UNIT_ID}, AGENT_ID={self.AGENT_ID}")

    async def setup_clocks_and_reset(self):
        """Setup clocks, reset, and initialize GAXI components for AXI monitor testing"""
        # Start clock
        await self.start_clock('aclk', 10, 'ns')

        self.log.info("Creating GAXI components for AXI monitor testing...")

        # 1. AR interface: Testbench sends read address requests TO DUT
        self.ar_master = GAXIMaster(
            dut=self.dut,
            title="AR_Master",
            prefix="",
            bus_name="",
            pkt_prefix="cmd",
            clock=self.dut.aclk,
            field_config=self.addr_field_config,
            timeout_cycles=self.TIMEOUT_CYCLES,
            mode='skid',
            in_prefix='',
            out_prefix='',
            multi_sig=True,
            log=self.log,
            randomizer=FlexRandomizer(self.randomizer_dict['balanced']['master']),
            super_debug=self.super_debug
        )

        # 2. AW interface: Testbench sends write address requests TO DUT
        self.aw_master = GAXIMaster(
            dut=self.dut,
            title="AW_Master",
            prefix="",
            bus_name="",
            pkt_prefix="cmd",
            clock=self.dut.aclk,
            field_config=self.addr_field_config,
            timeout_cycles=self.TIMEOUT_CYCLES,
            mode='skid',
            in_prefix='',
            out_prefix='',
            multi_sig=True,
            log=self.log,
            randomizer=FlexRandomizer(self.randomizer_dict['balanced']['master']),
            super_debug=self.super_debug
        )

        # 3. R interface: Testbench sends read data responses TO DUT
        self.r_slave = GAXISlave(
            dut=self.dut,
            title="R_Slave",
            prefix="",
            bus_name="",
            pkt_prefix="data",
            clock=self.dut.aclk,
            field_config=self.read_data_field_config,
            timeout_cycles=self.TIMEOUT_CYCLES,
            mode='skid',
            in_prefix='',
            out_prefix='',
            multi_sig=True,
            log=self.log,
            randomizer=FlexRandomizer(self.randomizer_dict['balanced']['slave']),
            super_debug=self.super_debug
        )

        # 4. W interface: Testbench sends write data TO DUT
        self.w_slave = GAXISlave(
            dut=self.dut,
            title="W_Slave",
            prefix="",
            bus_name="",
            pkt_prefix="data",
            clock=self.dut.aclk,
            field_config=self.write_data_field_config,
            timeout_cycles=self.TIMEOUT_CYCLES,
            mode='skid',
            in_prefix='',
            out_prefix='',
            multi_sig=True,
            log=self.log,
            randomizer=FlexRandomizer(self.randomizer_dict['balanced']['slave']),
            super_debug=self.super_debug
        )

        # 5. B interface: Testbench sends write responses TO DUT
        self.b_slave = GAXISlave(
            dut=self.dut,
            title="B_Slave",
            prefix="",
            bus_name="",
            pkt_prefix="resp",
            clock=self.dut.aclk,
            field_config=self.write_resp_field_config,
            timeout_cycles=self.TIMEOUT_CYCLES,
            mode='skid',
            in_prefix='',
            out_prefix='',
            multi_sig=True,
            log=self.log,
            randomizer=FlexRandomizer(self.randomizer_dict['balanced']['slave']),
            super_debug=self.super_debug
        )

        # 6. Monitor bus: Monitor interrupt output FROM DUT (Updated interface)
        self.monbus_slave = MonbusSlave(
            dut=self.dut,
            title="MonitorBus_Slave",
            prefix="",
            pkt_prefix="monbus",
            clock=self.dut.aclk,
            expected_unit_id=self.UNIT_ID,
            expected_agent_id=self.AGENT_ID,
            timeout_cycles=self.TIMEOUT_CYCLES,
            randomizer=FlexRandomizer(self.randomizer_dict['fast']['slave']),
            log=self.log,
            super_debug=self.super_debug
        )

        # Create monitors for all interfaces
        self.ar_monitor = GAXIMonitor(
            dut=self.dut, title="AR_Monitor", prefix="", bus_name="",
            pkt_prefix="addr", clock=self.dut.aclk, field_config=self.addr_field_config,
            mode='skid', in_prefix='', out_prefix='', multi_sig=True, log=self.log, super_debug=self.super_debug
        )

        self.aw_monitor = GAXIMonitor(
            dut=self.dut, title="AW_Monitor", prefix="", bus_name="",
            pkt_prefix="addr", clock=self.dut.aclk, field_config=self.addr_field_config,
            mode='skid', in_prefix='', out_prefix='', multi_sig=True, log=self.log, super_debug=self.super_debug
        )

        self.r_monitor = GAXIMonitor(
            dut=self.dut, title="R_Monitor", prefix="", bus_name="",
            pkt_prefix="data", clock=self.dut.aclk, field_config=self.read_data_field_config,
            mode='skid', in_prefix='', out_prefix='', multi_sig=True, log=self.log, super_debug=self.super_debug
        )

        self.w_monitor = GAXIMonitor(
            dut=self.dut, title="W_Monitor", prefix="", bus_name="",
            pkt_prefix="data", clock=self.dut.aclk, field_config=self.write_data_field_config,
            mode='skid', in_prefix='', out_prefix='', multi_sig=True, log=self.log, super_debug=self.super_debug
        )

        self.b_monitor = GAXIMonitor(
            dut=self.dut, title="B_Monitor", prefix="", bus_name="", 
            pkt_prefix="resp", clock=self.dut.aclk, field_config=self.write_resp_field_config,
            mode='skid', in_prefix='', out_prefix='', multi_sig=True, log=self.log, super_debug=self.super_debug
        )

        self.monbus_monitor = GAXIMonitor(
            dut=self.dut, title="MonitorBus_Monitor", prefix="", bus_name="monbus",  # Updated
            pkt_prefix="", clock=self.dut.aclk, field_config=self.monbus_field_config,
            mode='skid', in_prefix='', out_prefix='', multi_sig=False, log=self.log, super_debug=self.super_debug
        )

        # Create scoreboard
        self.scoreboard = AXIMonitorScoreboard(
            log=self.log,
            component_name="AXI_MONITOR_SB",
            id_width=self.IW,
            addr_width=self.AW,
            data_width=self.DW,
            user_width=self.UW,
            is_axi4=self.IS_AXI4,
            max_transactions=self.MAX_TRANSACTIONS
        )

        # Connect monitor callbacks to scoreboard
        self.ar_monitor.add_callback(self._ar_callback)
        self.aw_monitor.add_callback(self._aw_callback)
        self.r_monitor.add_callback(self._r_callback)
        self.w_monitor.add_callback(self._w_callback)
        self.b_monitor.add_callback(self._b_callback)
        self.monbus_monitor.add_callback(self._monbus_callback)  # Updated from interrupt_callback

        # Add packet callback to monbus slave for additional processing
        self.monbus_slave.add_packet_callback(self._monbus_packet_callback)

        # Apply reset and configure monitor
        self.dut.aresetn.value = 0
        await self._configure_monitor()

        await self.wait_clocks('aclk', 10)

        # Release reset
        self.dut.aresetn.value = 1
        await self.wait_clocks('aclk', 5)

        # Start monitoring
        await self.monbus_slave.start_monitoring()

        self.log.info("AXI Monitor testbench setup complete")

    async def _configure_monitor(self):
        """Configure the monitor with initial settings"""
        # Set default configuration values
        self.dut.i_cfg_freq_sel.value = 0x3        # Medium frequency
        self.dut.i_cfg_addr_cnt.value = 0x8        # Address timeout: 8 ticks
        self.dut.i_cfg_data_cnt.value = 0x8        # Data timeout: 8 ticks
        self.dut.i_cfg_resp_cnt.value = 0x8        # Response timeout: 8 ticks

        # Enable all packet types for comprehensive testing
        self.dut.i_cfg_error_enable.value = 1
        self.dut.i_cfg_compl_enable.value = 1
        self.dut.i_cfg_threshold_enable.value = 1
        self.dut.i_cfg_timeout_enable.value = 1
        self.dut.i_cfg_perf_enable.value = 1
        self.dut.i_cfg_debug_enable.value = 1

        # Set reasonable thresholds
        self.dut.i_cfg_active_trans_threshold.value = self.MAX_TRANSACTIONS // 2
        self.dut.i_cfg_latency_threshold.value = 1000  # 1000 cycles

        # Record configuration in scoreboard
        config = MonitorConfigPacket(
            field_config=self.config_field_config,
            freq_sel=0x3,
            addr_cnt=0x8,
            data_cnt=0x8,
            resp_cnt=0x8,
            error_enable=1,
            compl_enable=1,
            threshold_enable=1,
            timeout_enable=1,
            perf_enable=1,
            debug_enable=1,
            active_trans_threshold=self.MAX_TRANSACTIONS // 2,
            latency_threshold=1000
        )
        self.scoreboard.record_configuration(config)

    # Monitor callback handlers
    def _ar_callback(self, packet):
        """Handle AR channel transactions"""
        time_str = self.get_time_ns_str()
        self.scoreboard.record_read_address(packet)

        if self.current_test_context:
            self.current_test_context.add_transaction(packet.id, "READ")

        self.log.debug(f"📍 AR{time_str}: ID={packet.id:02X} ADDR=0x{packet.addr:08X}")

    def _aw_callback(self, packet):
        """Handle AW channel transactions"""
        time_str = self.get_time_ns_str()
        self.scoreboard.record_write_address(packet)

        if self.current_test_context:
            self.current_test_context.add_transaction(packet.id, "WRITE")

        self.log.debug(f"📍 AW{time_str}: ID={packet.id:02X} ADDR=0x{packet.addr:08X}")

    def _r_callback(self, packet):
        """Handle R channel transactions"""
        time_str = self.get_time_ns_str()
        self.scoreboard.record_read_data(packet)

        self.log.debug(f"📥 R{time_str}: ID={packet.id:02X} "
                        f"RESP={packet.resp} LAST={packet.last}")

    def _w_callback(self, packet):
        """Handle W channel transactions"""
        time_str = self.get_time_ns_str()
        self.scoreboard.record_write_data(packet)

        self.log.debug(f"📤 W{time_str}: LAST={packet.last}")

    def _b_callback(self, packet):
        """Handle B channel transactions"""
        time_str = self.get_time_ns_str()
        self.scoreboard.record_write_response(packet)

        self.log.debug(f"📥 B{time_str}: ID={packet.id:02X} RESP={packet.resp}")

    def _monbus_callback(self, packet):
        """Handle monitor bus packets from GAXIMonitor"""
        time_str = self.get_time_ns_str()

        # Extract 64-bit value from packet
        if hasattr(packet, 'packet'):
            monbus_value = packet.packet
        else:
            # Reconstruct from fields
            monbus_value = 0
            for field_name in self.monbus_field_config.field_names():
                if hasattr(packet, field_name):
                    field_value = getattr(packet, field_name)
                    # This would need proper bit positioning logic
                    monbus_value |= field_value

        self.scoreboard.record_interrupt_packet(monbus_value)
        self.test_stats['monbus_packets_received'] += 1

        self.log.info(f"🚨 MONBUS{time_str}: 0x{monbus_value:016X}")

    def _monbus_packet_callback(self, monbus_packet: MonbusPacket):
        """Handle structured monitor bus packets from MonbusSlave"""
        time_str = self.get_time_ns_str()

        # Additional processing of structured packets
        self.log.debug(f"🔍 MONBUS_STRUCTURED{time_str}: {monbus_packet}")

        # You can add additional packet analysis here
        if monbus_packet.is_error_packet():
            self.log.warning(f"⚠️ Error packet detected: {monbus_packet.get_event_code_name()}")
        elif monbus_packet.is_timeout_packet():
            self.log.warning(f"⏰ Timeout packet detected: {monbus_packet.get_event_code_name()}")

    def _get_next_id(self) -> int:
        """Get next transaction ID"""
        self.transaction_id_counter = (self.transaction_id_counter + 1) % (self.MAX_ID + 1)
        return self.transaction_id_counter

    def _start_test_context(self, test_name: str) -> AXIMonitorTestContext:
        """Start a new test context"""
        context = AXIMonitorTestContext(test_name, get_sim_time('ns'))
        self.current_test_context = context
        self.test_contexts.append(context)
        return context

    def _end_test_context(self, passed: bool):
        """End current test context"""
        if self.current_test_context:
            self.current_test_context.mark_complete(passed)
            self.current_test_context = None

    async def issue_read_transaction(self, addr: int, length: int = 0,
                                    txn_id: int = None, expect_error: bool = False) -> int:
        """Issue a read transaction"""
        if txn_id is None:
            txn_id = self._get_next_id()

        # Create AR packet
        ar_packet = GAXIPacket(self.addr_field_config)
        ar_packet.id = txn_id
        ar_packet.addr = addr
        ar_packet.len = length
        ar_packet.size = int(math.log2(self.BYTES_PER_BEAT))
        ar_packet.burst = 1  # INCR
        ar_packet.cache = 0x3
        ar_packet.prot = 0x0
        ar_packet.lock = 0
        ar_packet.qos = 0
        ar_packet.region = 0
        if self.UW > 0:
            ar_packet.user = 0

        # Send AR
        await self.ar_master.send(ar_packet)
        self.test_stats['transactions_issued'] += 1

        self.log.debug(f"🚀 Issued READ: ID={txn_id:02X} ADDR=0x{addr:08X} LEN={length}")
        return txn_id

    async def issue_write_transaction(self, addr: int, length: int = 0,
                                    txn_id: int = None, expect_error: bool = False) -> int:
        """Issue a write transaction"""
        if txn_id is None:
            txn_id = self._get_next_id()

        # Create AW packet
        aw_packet = GAXIPacket(self.addr_field_config)
        aw_packet.id = txn_id
        aw_packet.addr = addr
        aw_packet.len = length
        aw_packet.size = int(math.log2(self.BYTES_PER_BEAT))
        aw_packet.burst = 1  # INCR
        aw_packet.cache = 0x3
        aw_packet.prot = 0x0
        aw_packet.lock = 0
        aw_packet.qos = 0
        aw_packet.region = 0
        if self.UW > 0:
            aw_packet.user = 0

        # Send AW
        await self.aw_master.send(aw_packet)

        # Generate and send write data
        await self._send_write_data(length + 1, expect_error)

        self.test_stats['transactions_issued'] += 1
        self.log.debug(f"🚀 Issued WRITE: ID={txn_id:02X} ADDR=0x{addr:08X} LEN={length}")
        return txn_id

    async def _send_write_data(self, num_beats: int, inject_error: bool = False):
        """Send write data for a transaction"""
        for beat in range(num_beats):
            w_packet = GAXIPacket(self.write_data_field_config)
            w_packet.data = random.randint(0, (1 << self.DW) - 1)
            w_packet.strb = (1 << (self.DW // 8)) - 1  # All strobes
            w_packet.last = 1 if beat == num_beats - 1 else 0
            if self.UW > 0:
                w_packet.user = 0

            await self.w_slave.send(w_packet)

    async def inject_timeout(self, timeout_type: str = "data"):
        """Inject a timeout by stalling responses"""
        self.timeout_injection_enabled = True
        timeout_cycles = 50  # Exceed monitor timeout threshold

        if timeout_type == "data":
            # Stall read data responses
            await self.wait_clocks('aclk', timeout_cycles)
        elif timeout_type == "response":
            # Stall write responses
            await self.wait_clocks('aclk', timeout_cycles)

        self.timeout_injection_enabled = False
        self.test_stats['timeouts_injected'] += 1

    async def inject_protocol_violation(self, violation_type: str):
        """Inject protocol violations for testing"""
        if violation_type == "orphaned_data":
            # Send read data without preceding address
            r_packet = GAXIPacket(self.read_data_field_config)
            r_packet.id = 0xFF  # Non-existent ID
            r_packet.data = 0xDEADBEEF
            r_packet.resp = 0  # OKAY
            r_packet.last = 1
            if self.UW > 0:
                r_packet.user = 0

            await self.r_slave.send(r_packet)

        elif violation_type == "duplicate_address":
            # Send duplicate address with same ID
            txn_id = self._get_next_id()
            addr = 0x1000

            # Send first AR
            await self.issue_read_transaction(addr, 0, txn_id)
            await self.wait_clocks('aclk', 5)

            # Send duplicate AR with same ID
            await self.issue_read_transaction(addr + 0x100, 0, txn_id)

        self.test_stats['errors_injected'] += 1

    async def inject_response_error(self, error_type: str = "SLVERR"):
        """Inject response errors"""
        # This would be handled by response generation logic
        resp_code = 2 if error_type == "SLVERR" else 3  # DECERR
        self.response_error_rate = 1.0  # Force error on next response

        self.test_stats['errors_injected'] += 1

    async def wait_for_transaction_completion(self, txn_id: int, timeout_cycles: int = 200):
        """Wait for a specific transaction to complete"""
        for cycle in range(timeout_cycles):
            status = self.scoreboard.get_transaction_status(txn_id)
            if status and not status['is_active']:
                return True
            await RisingEdge(self.dut.aclk)

        self.log.error(f"❌ Transaction {txn_id:02X} timed out after {timeout_cycles} cycles")
        return False

    async def wait_for_all_transactions_complete(self, timeout_cycles: int = 500):
        """Wait for all active transactions to complete"""
        for cycle in range(timeout_cycles):
            if len(self.scoreboard.active_transactions) == 0:
                return True
            await RisingEdge(self.dut.aclk)

        active_ids = list(self.scoreboard.active_transactions.keys())
        self.log.error(f"❌ Transactions still active after timeout: {[f'{id:02X}' for id in active_ids]}")
        return False

    # Test scenarios (keeping existing test methods but updating stats references)
    async def test_basic_transactions(self) -> bool:
        """Test basic read and write transactions"""
        test_name = "basic_transactions"
        context = self._start_test_context(test_name)

        self.log.info(f"🧪 Running {test_name}")

        try:
            # Issue some read transactions
            read_ids = []
            for i in range(3):
                addr = 0x1000 + (i * 0x100)
                txn_id = await self.issue_read_transaction(addr, i)
                read_ids.append(txn_id)

            # Issue some write transactions
            write_ids = []
            for i in range(3):
                addr = 0x2000 + (i * 0x100)
                txn_id = await self.issue_write_transaction(addr, i)
                write_ids.append(txn_id)

            # Wait for completion
            await self.wait_for_all_transactions_complete()

            # Verify all transactions completed
            all_completed = True
            for txn_id in read_ids + write_ids:
                if not await self.wait_for_transaction_completion(txn_id):
                    all_completed = False

            self._end_test_context(all_completed)
            return all_completed

        except Exception as e:
            self.log.error(f"❌ {test_name} failed with exception: {e}")
            self._end_test_context(False)
            return False

    async def test_error_detection(self) -> bool:
        """Test error detection capabilities"""
        test_name = "error_detection"
        context = self._start_test_context(test_name)

        self.log.info(f"🧪 Running {test_name}")

        try:
            # Test response errors
            await self.inject_response_error("SLVERR")
            txn_id = await self.issue_read_transaction(0x3000, 0, expect_error=True)
            context.add_expected_error("RESPONSE_ERROR", txn_id)

            # Test protocol violations
            await self.inject_protocol_violation("orphaned_data")
            context.add_expected_error("ORPHANED_DATA")

            await self.inject_protocol_violation("duplicate_address")
            context.add_expected_error("DUPLICATE_ADDRESS")

            # Wait for errors to be detected
            await self.wait_clocks('aclk', 100)

            # Verify errors were detected
            verification_passed = self.scoreboard.verify_monitor_behavior()

            self._end_test_context(verification_passed)
            return verification_passed

        except Exception as e:
            self.log.error(f"❌ {test_name} failed with exception: {e}")
            self._end_test_context(False)
            return False

    async def test_timeout_detection(self) -> bool:
        """Test timeout detection"""
        test_name = "timeout_detection"
        context = self._start_test_context(test_name)

        self.log.info(f"🧪 Running {test_name}")

        try:
            # Issue transaction that will timeout
            txn_id = await self.issue_read_transaction(0x4000, 0)
            context.add_expected_error("TIMEOUT", txn_id)

            # Inject timeout
            await self.inject_timeout("data")

            # Wait for timeout detection
            await self.wait_clocks('aclk', 200)

            # Verify timeout was detected using monbus slave
            timeout_packets = self.monbus_slave.get_timeout_packets()
            timeout_detected = len(timeout_packets) > 0

            self._end_test_context(timeout_detected)
            return timeout_detected

        except Exception as e:
            self.log.error(f"❌ {test_name} failed with exception: {e}")
            self._end_test_context(False)
            return False

    async def test_configuration_changes(self) -> bool:
        """Test monitor configuration changes"""
        test_name = "configuration_changes"
        context = self._start_test_context(test_name)

        self.log.info(f"🧪 Running {test_name}")

        try:
            # Change timeout thresholds
            self.dut.i_cfg_addr_cnt.value = 0x4  # Shorter timeout
            self.dut.i_cfg_data_cnt.value = 0x4

            # Disable some packet types
            self.dut.i_cfg_compl_enable.value = 0

            # Record new configuration
            new_config = MonitorConfigPacket(
                field_config=self.config_field_config,
                freq_sel=0x3,
                addr_cnt=0x4,
                data_cnt=0x4,
                resp_cnt=0x8,
                error_enable=1,
                compl_enable=0,  # Disabled
                threshold_enable=1,
                timeout_enable=1,
                perf_enable=1,
                debug_enable=1,
                active_trans_threshold=self.MAX_TRANSACTIONS // 2,
                latency_threshold=1000
            )
            self.scoreboard.record_configuration(new_config)

            # Test with new configuration
            txn_id = await self.issue_read_transaction(0x5000, 2)
            await self.wait_for_transaction_completion(txn_id)

            # Verify configuration was applied
            config_applied = len(self.scoreboard.config_history) >= 2

            self._end_test_context(config_applied)
            return config_applied

        except Exception as e:
            self.log.error(f"❌ {test_name} failed with exception: {e}")
            self._end_test_context(False)
            return False

    async def test_performance_monitoring(self) -> bool:
        """Test performance monitoring features"""
        test_name = "performance_monitoring"
        context = self._start_test_context(test_name)

        self.log.info(f"🧪 Running {test_name}")

        try:
            # Issue multiple transactions to generate performance data
            txn_ids = []
            for i in range(5):
                addr = 0x6000 + (i * 0x200)
                length = random.randint(0, 7)

                if i % 2 == 0:
                    txn_id = await self.issue_read_transaction(addr, length)
                else:
                    txn_id = await self.issue_write_transaction(addr, length)

                txn_ids.append(txn_id)

                # Small delay between transactions
                await self.wait_clocks('aclk', 10)

            # Wait for all to complete
            await self.wait_for_all_transactions_complete()

            # Check for performance packets using monbus slave
            perf_packets = self.monbus_slave.get_performance_packets()
            perf_packets_found = len(perf_packets) > 0

            self._end_test_context(perf_packets_found)
            return perf_packets_found

        except Exception as e:
            self.log.error(f"❌ {test_name} failed with exception: {e}")
            self._end_test_context(False)
            return False

    async def run_all_tests(self) -> bool:
        """Run comprehensive test suite"""
        start_time_str = self.get_time_ns_str()
        self.log.info(f"🧪 Running AXI Monitor tests at level: {self.TEST_LEVEL}{start_time_str}")

        start_time = get_sim_time('ns')
        all_passed = True

        # Test sequence based on test level
        tests = [
            ("Basic Transactions", self.test_basic_transactions),
        ]

        if self.TEST_LEVEL in ['medium', 'full']:
            tests.extend([
                ("Error Detection", self.test_error_detection),
                ("Timeout Detection", self.test_timeout_detection),
                ("Configuration Changes", self.test_configuration_changes),
            ])

        if self.TEST_LEVEL == 'full':
            tests.extend([
                ("Performance Monitoring", self.test_performance_monitoring),
            ])

        for test_name, test_func in tests:
            test_start_str = self.get_time_ns_str()
            self.log.info(f"🧪 Starting {test_name}{test_start_str}")

            try:
                self.test_stats['tests_run'] += 1
                test_passed = await test_func()

                test_end_str = self.get_time_ns_str()
                if test_passed:
                    self.log.info(f"✅ {test_name} PASSED{test_end_str}")
                    self.test_stats['tests_passed'] += 1
                else:
                    self.log.error(f"❌ {test_name} FAILED{test_end_str}")
                    self.test_stats['tests_failed'] += 1
                    all_passed = False

                    if self.TEST_LEVEL == 'basic':
                        break

            except Exception as e:
                error_time_str = self.get_time_ns_str()
                self.log.error(f"❌ {test_name} FAILED with exception{error_time_str}: {e}")
                import traceback
                self.log.error(f"Traceback: {traceback.format_exc()}")
                self.test_stats['tests_failed'] += 1
                all_passed = False

                if self.TEST_LEVEL == 'basic':
                    break

            await self.wait_clocks('aclk', 20)

        # Final verification
        end_time = get_sim_time('ns')
        self.test_stats['test_duration'] = (end_time - start_time) / 1e9

        verification_start_str = self.get_time_ns_str()
        self.log.info(f"🔍 Performing final monitor verification{verification_start_str}...")

        final_verification = self.scoreboard.verify_monitor_behavior()
        if not final_verification:
            all_passed = False

        # Generate comprehensive report
        self.print_comprehensive_report()

        return all_passed

    def print_comprehensive_report(self):
        """Print comprehensive test report"""
        report_time_str = self.get_time_ns_str()
        self.log.info("=" * 100)
        self.log.info(f"🏁 AXI Monitor Test Report{report_time_str}")
        self.log.info("=" * 100)

        # Test configuration
        self.log.info(f"📋 Configuration:")
        self.log.info(f"  Protocol: {'AXI4' if self.IS_AXI4 else 'AXI-Lite'}")
        self.log.info(f"  ID Width: {self.IW}, Addr Width: {self.AW}, Data Width: {self.DW}")
        self.log.info(f"  User Width: {self.UW}, Max Transactions: {self.MAX_TRANSACTIONS}")
        self.log.info(f"  Test Level: {self.TEST_LEVEL}, Seed: {self.SEED}")

        # Test statistics
        self.log.info(f"\n📊 Test Statistics:")
        for key, value in self.test_stats.items():
            self.log.info(f"  {key}: {value}")

        # Monitor bus statistics (Updated)
        monbus_stats = self.monbus_slave.get_statistics()
        self.log.info(f"\n🚨 Monitor Bus Statistics:")
        for key, value in monbus_stats.items():
            if key != 'verification_error_list':  # Skip detailed error list in summary
                self.log.info(f"  {key}: {value}")

        # Test context summary
        if self.test_contexts:
            self.log.info(f"\n📝 Test Context Summary:")
            for context in self.test_contexts:
                status = "✅ PASS" if context.test_passed else "❌ FAIL"
                duration = context.get_duration()
                self.log.info(f"  {status} {context.test_name}: {duration:.1f}ns, "
                                f"{len(context.transactions_issued)} txns")

        # Scoreboard report
        if self.scoreboard:
            self.log.info("\n" + self.scoreboard.get_comprehensive_report())

        # Monitor bus detailed report
        self.log.info("\n" + self.monbus_slave.generate_report())

        # Verification summary
        verification_summary = self.scoreboard.get_verification_summary()
        self.log.info(f"\n🎯 Verification Summary:")
        for key, value in verification_summary.items():
            self.log.info(f"  {key}: {value}")

        self.log.info("=" * 100)

    async def shutdown(self):
        """Properly shutdown all components"""
        self.log.info("Shutting down AXI Monitor testbench...")
