# SPDX-License-Identifier: MIT
# SPDX-FileCopyrightText: 2024-2025 sean galloway
#
# RTL Design Sherpa - Industry-Standard RTL Design and Verification
# https://github.com/sean-galloway/RTLDesignSherpa
#
# Module: AXITransactionContext
# Purpose: Final AXI Monitor Testbench
#
# Documentation: bin/CocoTBFramework/README.md
# Subsystem: framework
#
# Author: sean galloway
# Created: 2025-10-18

"""
Final AXI Monitor Testbench

Correct architecture with three masters (CMD, DATA, RESP) and TB-controlled ready signals.
Uses simplified AXI assumptions for practical monitor testing.

Architecture:
- CMD Master: Drives cmd_* interface (AR when IS_READ=1, AW when IS_READ=0)
- DATA Master: Drives data_* interface (R when IS_READ=1, W when IS_READ=0)
- RESP Master: Drives resp_* interface (B responses for writes only)
- TB Ready Control: Independent ready signal control with FlexRandomizer
- Monitor: Observes all transactions passively

Simplified AXI Assumptions:
1. Address always aligned to data bus width
2. Fixed transfer size = bus width
3. Incrementing bursts only (INCR)
4. No address wraparound
"""

import os
import random
import asyncio
import math
from typing import Dict, List, Optional, Tuple, Any

import cocotb
from cocotb.triggers import RisingEdge, Timer, FallingEdge
from cocotb.utils import get_sim_time

from CocoTBFramework.tbclasses.shared.tbbase import TBBase
from CocoTBFramework.tbclasses.monbus.monbus_components import MonbusProtocol
from CocoTBFramework.components.shared.flex_randomizer import FlexRandomizer
from CocoTBFramework.components.shared.flex_config_gen import quick_config

from CocoTBFramework.components.gaxi.gaxi_master import GAXIMaster
from CocoTBFramework.components.gaxi.gaxi_monitor import GAXIMonitor
from CocoTBFramework.components.gaxi.gaxi_packet import GAXIPacket

from .axi_monitor_scoreboard import AXIMonitorScoreboard
from .axi_monitor_packets import (
    create_axi_command_field_config, create_axi_read_data_field_config,
    create_axi_write_data_field_config, create_axi_write_response_field_config
)
from .ready_controller import ReadyController
from ..monbus.monbus_components import MonbusSlave


class AXITransactionContext:
    """Context for tracking AXI transactions across CMD/DATA/RESP phases"""

    def __init__(self, txn_id: int, is_read: bool, addr: int, length: int):
        self.txn_id = txn_id
        self.is_read = is_read
        self.addr = addr
        self.length = length
        self.beats_total = length + 1
        self.beats_sent = 0
        self.cmd_sent = False
        self.data_complete = False
        self.resp_sent = False
        self.start_time = get_sim_time('ns')

    def is_complete(self) -> bool:
        if self.is_read:
            return self.cmd_sent and self.data_complete
        else:
            return self.cmd_sent and self.data_complete and self.resp_sent

    def next_data_beat(self) -> bool:
        """Return True if this is the last beat"""
        self.beats_sent += 1
        return self.beats_sent >= self.beats_total


class AXIMonitorTB(TBBase):
    """
    Final AXI Monitor Testbench with correct three-master architecture
    and simplified AXI assumptions.
    """

    def __init__(self, dut):
        """Initialize the final AXI monitor testbench"""
        super().__init__(dut)

        # Get test parameters
        self.SEED = self.convert_to_int(os.environ.get('SEED', '42'))
        self.TEST_LEVEL = os.environ.get('TEST_LEVEL', 'basic')
        self.IW = self.convert_to_int(os.environ.get('TEST_IW', '8'))
        self.AW = self.convert_to_int(os.environ.get('TEST_AW', '32'))
        self.DW = self.convert_to_int(os.environ.get('TEST_DW', '32'))
        self.UW = self.convert_to_int(os.environ.get('TEST_UW', '1'))
        self.IS_READ = self.convert_to_int(os.environ.get('TEST_IS_READ', '1')) == 1
        self.IS_AXI4 = self.convert_to_int(os.environ.get('TEST_IS_AXI4', '1')) == 1
        self.MAX_TRANSACTIONS = self.convert_to_int(os.environ.get('TEST_MAX_TRANSACTIONS', '16'))
        self.UNIT_ID = self.convert_to_int(os.environ.get('TEST_UNIT_ID', '9'))
        self.AGENT_ID = self.convert_to_int(os.environ.get('TEST_AGENT_ID', '99'))

        self.super_debug = True
        self.TIMEOUT_CYCLES = 1000

        # Calculate derived parameters based on simplified assumptions
        self.MAX_ID = (1 << self.IW) - 1
        self.MAX_ADDR = (1 << self.AW) - 1
        self.BYTES_PER_BEAT = self.DW // 8
        self.ADDR_ALIGNMENT = self.BYTES_PER_BEAT  # Assumption 1: Always aligned to bus width
        self.FIXED_SIZE = int(math.log2(self.BYTES_PER_BEAT))  # Assumption 2: Size = bus width
        self.BURST_TYPE = 1  # Assumption 3: Always INCR

        # Initialize random generator
        random.seed(self.SEED)

        # Create field configurations
        self.cmd_field_config = create_axi_command_field_config(self.IW, self.AW, self.UW)
        if self.IS_READ:
            self.data_field_config = create_axi_read_data_field_config(self.IW, self.DW, self.UW)
        else:
            self.data_field_config = create_axi_write_data_field_config(self.DW, self.UW)
        self.resp_field_config = create_axi_write_response_field_config(self.IW, self.UW)

        # Three masters for the three monitor interfaces
        self.cmd_master = None    # Drives cmd_* (AR when read, AW when write)
        self.data_master = None   # Drives data_* (R when read, W when write)
        self.resp_master = None   # Drives resp_* (B when write, unused when read)

        # TB-controlled ready signals
        self.cmd_ready_controller = None
        self.data_ready_controller = None
        self.resp_ready_controller = None

        # Monitors for transaction observation
        self.cmd_monitor = None
        self.data_monitor = None
        self.resp_monitor = None

        # Monitor bus slave
        self.monbus_slave = None

        # Scoreboard
        self.scoreboard = None

        # Transaction management
        self.transaction_id_counter = random.randint(1, min(15, self.MAX_ID)) if self.MAX_ID > 1 else 0
        self.active_transactions = {}  # txn_id -> AXITransactionContext
        self.pending_data_queue = asyncio.Queue()
        self.pending_resp_queue = asyncio.Queue()

        # Test statistics
        self.test_stats = {
            'tests_run': 0,
            'tests_passed': 0,
            'transactions_issued': 0,
            'cmd_packets': 0,
            'data_packets': 0,
            'resp_packets': 0,
            'handshake_events': 0
        }

        self.log.info(f"Final AXI Monitor TB initialized")
        self.log.info(f"  Mode: {'READ' if self.IS_READ else 'WRITE'} {'AXI4' if self.IS_AXI4 else 'AXI-Lite'}")
        self.log.info(f"  IW={self.IW}, AW={self.AW}, DW={self.DW}")
        self.log.info(f"  Alignment={self.ADDR_ALIGNMENT}, Size={self.FIXED_SIZE}, Burst=INCR")

    async def setup_clocks_and_reset(self):
        """Setup clocks, reset, and initialize components"""
        # Start clock
        await self.start_clock('aclk', 10, 'ns')

        self.log.info("Creating final testbench components...")

        # Create default randomizer for masters (no ready delay - TB controls ready)
        master_randomizer = FlexRandomizer({
            'valid_delay': ([(0, 0), (1, 2)], [8, 2])  # Mostly immediate valid
        })

        # 1. Create CMD Master (drives cmd_* interface)
        self.cmd_master = GAXIMaster(
            dut=self.dut,
            title="CMD_Master",
            prefix="",
            bus_name="",
            pkt_prefix="cmd",
            clock=self.dut.aclk,
            field_config=self.cmd_field_config,
            timeout_cycles=self.TIMEOUT_CYCLES,
            mode='skid',
            randomizer=master_randomizer,
            log=self.log,
            super_debug=self.super_debug
        )

        # 2. Create DATA Master (drives data_* interface)
        self.data_master = GAXIMaster(
            dut=self.dut,
            title="DATA_Master",
            prefix="",
            bus_name="",
            pkt_prefix="data",
            clock=self.dut.aclk,
            field_config=self.data_field_config,
            timeout_cycles=self.TIMEOUT_CYCLES,
            mode='skid',
            randomizer=master_randomizer,
            log=self.log,
            super_debug=self.super_debug
        )

        # 3. Create RESP Master (drives resp_* interface, only for writes)
        if not self.IS_READ:
            self.resp_master = GAXIMaster(
                dut=self.dut,
                title="RESP_Master",
                prefix="",
                bus_name="",
                pkt_prefix="resp",
                clock=self.dut.aclk,
                field_config=self.resp_field_config,
                timeout_cycles=self.TIMEOUT_CYCLES,
                mode='skid',
                randomizer=master_randomizer,
                log=self.log,
                super_debug=self.super_debug
            )

        # 4. Create TB-controlled ready signal controllers using helper
        from .ready_controller import create_ready_controllers_for_monitor
        self.ready_controllers = create_ready_controllers_for_monitor(self.dut, self.IS_READ, self.log)

        # Add handshake callbacks
        self.ready_controllers['cmd_ready'].add_handshake_callback(self._cmd_handshake_callback)
        self.ready_controllers['data_ready'].add_handshake_callback(self._data_handshake_callback)
        if not self.IS_READ:
            self.ready_controllers['resp_ready'].add_handshake_callback(self._resp_handshake_callback)

        # 5. Create monitors for transaction observation
        self.cmd_monitor = GAXIMonitor(
            dut=self.dut, title="CMD_Monitor", prefix="", bus_name="",
            pkt_prefix="cmd", clock=self.dut.aclk, field_config=self.cmd_field_config,
            mode='skid', log=self.log, super_debug=self.super_debug
        )

        self.data_monitor = GAXIMonitor(
            dut=self.dut, title="DATA_Monitor", prefix="", bus_name="",
            pkt_prefix="data", clock=self.dut.aclk, field_config=self.data_field_config,
            mode='skid', log=self.log, super_debug=self.super_debug
        )

        if not self.IS_READ:
            self.resp_monitor = GAXIMonitor(
                dut=self.dut, title="RESP_Monitor", prefix="", bus_name="",
                pkt_prefix="resp", clock=self.dut.aclk, field_config=self.resp_field_config,
                mode='skid', log=self.log, super_debug=self.super_debug
            )

        # 6. Create monitor bus slave
        self.monbus_slave = MonbusSlave(
            dut=self.dut,
            title="MonitorBus_Slave",
            prefix="",
            pkt_prefix="monbus",
            clock=self.dut.aclk,
            expected_unit_id=self.UNIT_ID,
            expected_agent_id=self.AGENT_ID,
            expected_protocol=MonbusProtocol.AXI,  # NEW: Expect AXI protocol
            timeout_cycles=self.TIMEOUT_CYCLES,
            log=self.log,
            super_debug=self.super_debug
        )

        # 7. Create scoreboard
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

        # 8. Connect monitor callbacks
        self.cmd_monitor.add_callback(self._cmd_callback)
        self.data_monitor.add_callback(self._data_callback)
        if not self.IS_READ:
            self.resp_monitor.add_callback(self._resp_callback)

        # 9. Configure monitor and apply reset
        self.dut.aresetn.value = 0
        await self._configure_monitor()
        await self.wait_clocks('aclk', 10)

        # 10. Release reset
        self.dut.aresetn.value = 1
        await self.wait_clocks('aclk', 5)

        # 11. Start ready controllers with immediate ready using helpers
        from .ready_controller import start_all_controllers, setup_all_controllers_immediate
        await start_all_controllers(self.ready_controllers)
        await setup_all_controllers_immediate(self.ready_controllers)

        # 12. Start monitor bus slave
        await self.monbus_slave.start_monitoring()

        # 13. Start background tasks for data and response generation
        cocotb.start_soon(self._data_generation_task())
        if not self.IS_READ:
            cocotb.start_soon(self._resp_generation_task())

        self.log.info("Final AXI Monitor testbench setup complete")

    async def _configure_monitor(self):
        """Configure the monitor with initial settings"""
        self.dut.cfg_freq_sel.value = 0x3
        self.dut.cfg_addr_cnt.value = 0x8
        self.dut.cfg_data_cnt.value = 0x8
        self.dut.cfg_resp_cnt.value = 0x8

        # Enable all packet types
        self.dut.cfg_error_enable.value = 1
        self.dut.cfg_compl_enable.value = 1
        self.dut.cfg_threshold_enable.value = 1
        self.dut.cfg_timeout_enable.value = 1
        self.dut.cfg_perf_enable.value = 1
        self.dut.cfg_debug_enable.value = 1

        # Set thresholds
        self.dut.cfg_active_trans_threshold.value = self.MAX_TRANSACTIONS // 2
        self.dut.cfg_latency_threshold.value = 1000

    async def _cleanup_completed_transactions(self):
        """Clean up any transactions that should be completed"""
        to_remove = []
        for txn_id, txn in self.active_transactions.items():
            if txn.is_complete():
                to_remove.append(txn_id)
        
        for txn_id in to_remove:
            self.log.debug(f"🧹 Cleaning up completed transaction {txn_id:02X}")
            del self.active_transactions[txn_id]

    def _get_next_id(self) -> int:
        """Get next transaction ID with duplicate prevention"""
        max_attempts = self.MAX_ID + 1
        
        for attempt in range(max_attempts):
            # Increment counter and wrap
            self.transaction_id_counter = (self.transaction_id_counter + 1) % (self.MAX_ID + 1)
            candidate_id = self.transaction_id_counter
            
            # Check if this ID is already in use
            if candidate_id not in self.active_transactions:
                return candidate_id
        
        # If we can't find a free ID, log error and use a random one
        self.log.error(f"❌ Cannot find free transaction ID - {len(self.active_transactions)} active transactions")
        
        # Try to find any free ID
        for test_id in range(self.MAX_ID + 1):
            if test_id not in self.active_transactions:
                self.log.warning(f"⚠️ Using emergency ID {test_id:02X}")
                return test_id
        
        # Last resort - use 0 and log the problem
        self.log.error(f"❌ All transaction IDs in use! Using 0 as last resort")
        return 0

    def _align_address(self, addr: int) -> int:
        """Align address to bus width (Assumption 1)"""
        return (addr // self.ADDR_ALIGNMENT) * self.ADDR_ALIGNMENT

    def _generate_aligned_address(self) -> int:
        """Generate a random aligned address (Assumption 4: no wraparound)"""
        # Generate address that won't wraparound
        max_safe_addr = self.MAX_ADDR - (256 * self.ADDR_ALIGNMENT)  # Leave safety margin
        addr = random.randint(0x1000, max_safe_addr)
        return self._align_address(addr)

    async def setup_ready_profile(self, cmd_profile: str = 'immediate',
                                 data_profile: str = 'immediate',
                                 resp_profile: str = 'immediate'):
        """
        Setup ready controller profiles using FlexRandomizer.

        Args:
            cmd_profile: Profile for cmd_ready
            data_profile: Profile for data_ready
            resp_profile: Profile for resp_ready (writes only)
        """
        from .ready_controller import setup_all_controllers_immediate, setup_all_controllers_delayed

        # Helper function to apply profile to a controller
        async def apply_profile(controller, profile_name):
            if profile_name == 'immediate':
                await controller.set_immediate_ready(True)
            elif profile_name == 'delayed':
                await controller.set_delayed_ready(5)
            else:
                # Create randomizer for this profile
                config = quick_config([profile_name], ['ready_delay'])
                if profile_name == 'balanced':
                    config.balanced.ready_delay.weighted_ranges([
                        ((0, 0), 5), ((1, 3), 3), ((4, 8), 2)
                    ])
                elif profile_name == 'stress':
                    config.stress.ready_delay.weighted_ranges([
                        ((0, 0), 2), ((1, 5), 3), ((6, 20), 3), ((21, 50), 2)
                    ])
                elif profile_name == 'fast':
                    config.fast.ready_delay.mostly_zero(9, (1, 3), 1)
                elif profile_name == 'slow':
                    config.slow.ready_delay.weighted_ranges([
                        ((2, 5), 3), ((6, 15), 2)
                    ])

                randomizer = config.build()[profile_name]
                await controller.set_random_ready(randomizer, 'ready_delay')

        # Apply profiles to each controller
        await apply_profile(self.ready_controllers['cmd_ready'], cmd_profile)
        await apply_profile(self.ready_controllers['data_ready'], data_profile)
        if not self.IS_READ and 'resp_ready' in self.ready_controllers:
            await apply_profile(self.ready_controllers['resp_ready'], resp_profile)

        self.log.info(f"Ready profiles: CMD={cmd_profile}, DATA={data_profile}, RESP={resp_profile}")

    async def issue_transaction(self, addr: int = None, length: int = 0, txn_id: int = None) -> int:
        """Issue an AXI transaction (read or write based on IS_READ parameter)"""
        if txn_id is None:
            txn_id = self._get_next_id()
        else:
            # If explicit ID provided, check it's not in use
            if txn_id in self.active_transactions:
                self.log.error(f"❌ Transaction ID {txn_id:02X} already in use!")
                txn_id = self._get_next_id()

        if addr is None:
            addr = self._generate_aligned_address()
        else:
            addr = self._align_address(addr)

        # Double check ID is not in use before creating transaction
        if txn_id in self.active_transactions:
            self.log.error(f"❌ CRITICAL: Transaction ID {txn_id:02X} collision detected!")
            # Try to clean up any completed transactions
            await self._cleanup_completed_transactions()
            # Get a truly new ID
            txn_id = self._get_next_id()

        # Create transaction context
        txn_context = AXITransactionContext(txn_id, self.IS_READ, addr, length)
        self.active_transactions[txn_id] = txn_context

        # Create and send CMD packet (AR for reads, AW for writes)
        cmd_packet = GAXIPacket(self.cmd_field_config)
        cmd_packet.id = txn_id
        cmd_packet.addr = addr
        cmd_packet.len = length
        cmd_packet.size = self.FIXED_SIZE  # Assumption 2: Fixed size = bus width
        cmd_packet.burst = self.BURST_TYPE  # Assumption 3: Always INCR
        cmd_packet.cache = 0x3
        cmd_packet.prot = 0x0
        cmd_packet.lock = 0
        cmd_packet.qos = 0
        cmd_packet.region = 0
        if self.UW > 0:
            cmd_packet.user = 0

        await self.cmd_master.send(cmd_packet)
        txn_context.cmd_sent = True

        # Ensure proper ordering for write transactions
        if not self.IS_READ:
            await self._ensure_transaction_ordering()

        # Queue data generation (with small delay for writes to ensure address is processed first)
        if not self.IS_READ:
            # For writes, delay data slightly to ensure address is processed first
            cocotb.start_soon(self._delayed_data_queue(txn_context, 3))
        else:
            await self.pending_data_queue.put(txn_context)

        # Queue response generation (writes only)
        if not self.IS_READ:
            await self.pending_resp_queue.put(txn_context)

        self.test_stats['transactions_issued'] += 1
        txn_type = "READ" if self.IS_READ else "WRITE"
        self.log.debug(f"🚀 Issued {txn_type}: ID={txn_id:02X} ADDR=0x{addr:08X} LEN={length}")
        return txn_id

    async def _delayed_data_queue(self, txn_context, delay_cycles: int):
        """Add transaction to data queue after a delay"""
        await self.wait_clocks('aclk', delay_cycles)
        await self.pending_data_queue.put(txn_context)

    async def _data_generation_task(self):
        """Background task to generate data packets"""
        while True:
            try:
                # Get next transaction needing data
                txn_context = await self.pending_data_queue.get()

                # Small delay before starting data
                await self.wait_clocks('aclk', random.randint(1, 5))

                # Generate data beats
                for beat in range(txn_context.beats_total):
                    data_packet = GAXIPacket(self.data_field_config)

                    if self.IS_READ:
                        # Read data packet (R channel)
                        data_packet.id = txn_context.txn_id
                        data_packet.data = random.randint(0, (1 << self.DW) - 1)
                        data_packet.resp = 0  # OKAY
                        data_packet.last = txn_context.next_data_beat()
                        if self.UW > 0:
                            data_packet.user = 0
                    else:
                        # Write data packet (W channel)
                        data_packet.data = random.randint(0, (1 << self.DW) - 1)
                        data_packet.strb = (1 << self.BYTES_PER_BEAT) - 1  # All strobes
                        data_packet.last = txn_context.next_data_beat()
                        if self.UW > 0:
                            data_packet.user = 0

                    await self.data_master.send(data_packet)

                    # Small delay between beats for multi-beat bursts
                    if beat < txn_context.beats_total - 1:
                        await self.wait_clocks('aclk', random.randint(0, 2))

                txn_context.data_complete = True

            except Exception as e:
                self.log.error(f"Data generation task error: {e}")
                await self.wait_clocks('aclk', 10)

    async def _resp_generation_task(self):
        """Background task to generate response packets (writes only)"""
        if self.IS_READ:
            return

        while True:
            try:
                # Get next transaction needing response
                txn_context = await self.pending_resp_queue.get()

                # Wait for data to complete
                while not txn_context.data_complete:
                    await self.wait_clocks('aclk', 5)

                # Additional delay for response
                await self.wait_clocks('aclk', random.randint(5, 15))

                # Generate response packet with correct field name
                resp_packet = GAXIPacket(self.resp_field_config)
                resp_packet.id = txn_context.txn_id
                resp_packet.resp = 0  # Changed from 'resp' to 'resp' (this was correct)
                if self.UW > 0:
                    resp_packet.user = 0

                await self.resp_master.send(resp_packet)
                txn_context.resp_sent = True

            except Exception as e:
                self.log.error(f"Response generation task error: {e}")
                await self.wait_clocks('aclk', 10)

    async def _ensure_transaction_ordering(self):
        """Ensure proper transaction ordering for write transactions"""
        if self.IS_READ:
            return
        
        # For write transactions, ensure address comes before data
        # This is a simple delay to let address packets get processed first
        await self.wait_clocks('aclk', 2)

    # Monitor callbacks
    def _cmd_callback(self, packet):
        """Handle CMD channel transactions"""
        if self.IS_READ:
            self.scoreboard.record_read_address(packet)
        else:
            self.scoreboard.record_write_address(packet)
        self.test_stats['cmd_packets'] += 1

        time_str = self.get_time_ns_str()
        channel = "AR" if self.IS_READ else "AW"
        self.log.debug(f"📍 {channel}{time_str}: ID={packet.id:02X} ADDR=0x{packet.addr:08X}")

    def _data_callback(self, packet):
        """Handle DATA channel transactions"""
        if self.IS_READ:
            self.scoreboard.record_read_data(packet)
        else:
            self.scoreboard.record_write_data(packet)
        self.test_stats['data_packets'] += 1

        time_str = self.get_time_ns_str()
        channel = "R" if self.IS_READ else "W"
        if self.IS_READ:
            self.log.debug(f"📥 {channel}{time_str}: ID={packet.id:02X} LAST={packet.last}")
        else:
            self.log.debug(f"📤 {channel}{time_str}: LAST={packet.last}")

    def _resp_callback(self, packet):
        """Handle RESP channel transactions (writes only)"""
        self.scoreboard.record_write_response(packet)
        self.test_stats['resp_packets'] += 1

        time_str = self.get_time_ns_str()
        self.log.debug(f"📥 B{time_str}: ID={packet.id:02X} RESP={packet.resp}")

    # Handshake callbacks
    def _cmd_handshake_callback(self, event):
        """Handle CMD ready handshake events"""
        self.test_stats['handshake_events'] += 1
        self.log.debug(f"🤝 CMD_HANDSHAKE: {event}")

    def _data_handshake_callback(self, event):
        """Handle DATA ready handshake events"""
        self.test_stats['handshake_events'] += 1
        self.log.debug(f"🤝 DATA_HANDSHAKE: {event}")

    def _resp_handshake_callback(self, event):
        """Handle RESP ready handshake events"""
        self.test_stats['handshake_events'] += 1
        self.log.debug(f"🤝 RESP_HANDSHAKE: {event}")

    async def wait_for_transaction_completion(self, txn_id: int, timeout_cycles: int = 500) -> bool:
        """Wait for a specific transaction to complete"""
        for cycle in range(timeout_cycles):
            if txn_id in self.active_transactions:
                if self.active_transactions[txn_id].is_complete():
                    return True
            else:
                # Transaction not found - might already be complete
                return True
            await RisingEdge(self.dut.aclk)

        self.log.error(f"❌ Transaction {txn_id:02X} timed out after {timeout_cycles} cycles")
        return False

    async def wait_for_all_transactions_complete(self, timeout_cycles: int = 1000) -> bool:
        """Wait for all active transactions to complete"""
        for cycle in range(timeout_cycles):
            active_incomplete = [txn for txn in self.active_transactions.values()
                               if not txn.is_complete()]
            if not active_incomplete:
                return True
            await RisingEdge(self.dut.aclk)

        incomplete_ids = [txn.txn_id for txn in self.active_transactions.values()
                         if not txn.is_complete()]
        self.log.error(f"❌ Transactions still active: {[f'{id:02X}' for id in incomplete_ids]}")
        return False

    async def test_basic_transactions_with_ready_patterns(self) -> bool:
        """Test basic transactions with different ready patterns"""
        self.log.info(f"🧪 Testing basic {'READ' if self.IS_READ else 'WRITE'} transactions with ready patterns")

        try:
            # Test 1: All immediate ready
            await self.setup_ready_profile('immediate', 'immediate', 'immediate')
            for i in range(5):
                addr = 0x10000 + i * 0x1000  # Will be aligned automatically
                await self.issue_transaction(addr, i % 4)
            await self.wait_clocks('aclk', 100)

            # Test 2: Mixed ready patterns
            await self.setup_ready_profile('immediate', 'balanced', 'delayed')
            for i in range(3):
                await self.issue_transaction(length=i % 8)
            await self.wait_clocks('aclk', 200)

            # Test 3: Stress patterns
            await self.setup_ready_profile('balanced', 'stress', 'immediate')
            for i in range(4):
                await self.issue_transaction(length=i % 6)
                await self.wait_clocks('aclk', random.randint(5, 15))
            await self.wait_clocks('aclk', 300)

            # Wait for all transactions to complete
            completion_success = await self.wait_for_all_transactions_complete()

            # Verify monitor behavior
            verification_passed = self.scoreboard.verify_monitor_behavior()

            return completion_success and verification_passed

        except Exception as e:
            self.log.error(f"❌ Basic transaction test failed: {e}")
            return False

    def get_ready_statistics(self) -> Dict[str, Any]:
        """Get statistics from all ready controllers"""
        from .ready_controller import get_combined_statistics
        return get_combined_statistics(self.ready_controllers)

    def print_comprehensive_report(self):
        """Print comprehensive test report"""
        self.log.info("=" * 100)
        mode = "READ" if self.IS_READ else "WRITE"
        self.log.info(f"🏁 Final AXI Monitor {mode.upper()} Test Report{self.get_time_ns_str()}")
        self.log.info("=" * 100)

        # Test configuration
        self.log.info(f"📋 Test Configuration:")
        self.log.info(f"  Mode: {mode.upper()} {'AXI4' if self.IS_AXI4 else 'AXI-Lite'}")
        self.log.info(f"  Bus Width: {self.DW}-bit, Alignment: {self.ADDR_ALIGNMENT} bytes")
        self.log.info(f"  Fixed Size: {self.FIXED_SIZE} ({self.BYTES_PER_BEAT} bytes), Burst: INCR")

        # Test statistics
        self.log.info(f"\n📊 Test Statistics:")
        for key, value in self.test_stats.items():
            self.log.info(f"  {key}: {value}")

        # Ready controller statistics
        ready_stats = self.get_ready_statistics()
        self.log.info(f"\n🤝 Ready Controller Statistics:")
        for channel, stats in ready_stats.items():
            self.log.info(f"  {channel}:")
            for key, value in stats.items():
                self.log.info(f"    {key}: {value}")

        # Active transactions
        if self.active_transactions:
            self.log.info(f"\n⏳ Active Transactions: {len(self.active_transactions)}")
            for txn_id, txn in self.active_transactions.items():
                complete = "✅" if txn.is_complete() else "⏳"
                self.log.info(f"  {complete} ID={txn_id:02X}: beats={txn.beats_sent}/{txn.beats_total}")

        # Scoreboard report
        if self.scoreboard:
            self.log.info("\n" + self.scoreboard.get_comprehensive_report())

        # Monitor bus report
        if self.monbus_slave:
            self.log.info("\n" + self.monbus_slave.generate_report())

        self.log.info("=" * 100)

    async def shutdown(self):
        """Properly shutdown all components"""
        self.log.info("Shutting down final AXI Monitor testbench...")

        # Stop ready controllers using helper
        from .ready_controller import stop_all_controllers
        await stop_all_controllers(self.ready_controllers)

    async def run_all_tests(self) -> bool:
        """
        Main test runner method expected by the test framework.

        Runs appropriate tests based on configuration and returns overall pass/fail status.
        """
        self.log.info(f"🚀 Starting AXI Monitor test suite...")

        # Get test configuration
        protocol_str = "AXI4" if self.IS_AXI4 else "AXI-Lite"
        monitor_type = "READ" if self.IS_READ else "WRITE"

        self.log.info(f"Running {protocol_str} {monitor_type} monitor tests")
        self.log.info(f"Parameters: IW={self.IW}, AW={self.AW}, DW={self.DW}")

        all_tests_passed = True

        try:
            # Run appropriate tests based on configuration
            if self.IS_READ:
                # Run read monitor tests
                read_passed = await self._test_simple_reads()
                all_tests_passed = all_tests_passed and read_passed
            else:
                # Run write monitor tests
                write_passed = await self._test_simple_writes()
                all_tests_passed = all_tests_passed and write_passed

            # Run basic transaction patterns test (works for both read/write)
            patterns_passed = await self.test_basic_transactions_with_ready_patterns()
            all_tests_passed = all_tests_passed and patterns_passed

            # Final verification
            final_verification = await self._final_verification()
            all_tests_passed = all_tests_passed and final_verification

        except Exception as e:
            self.log.error(f"❌ Test suite failed with exception: {e}")
            import traceback
            self.log.error(f"Traceback: {traceback.format_exc()}")
            all_tests_passed = False

        # Print final results
        status = "✅ PASSED" if all_tests_passed else "❌ FAILED"
        self.log.info(f"{status} AXI Monitor {protocol_str} {monitor_type} test suite")

        return all_tests_passed

    # Add this method to AXIMonitorTB class
    async def _test_simple_reads(self) -> bool:
        """Simple read transaction test"""
        self.log.info("📖 Testing simple READ transactions...")

        try:
            # Set immediate ready for simple test
            await self.setup_ready_profile('immediate', 'immediate', 'immediate')

            # Issue a few simple read transactions
            for i in range(3):
                addr = 0x10000 + i * 0x1000
                txn_id = await self.issue_transaction(addr, length=i % 3)
                self.log.info(f"Issued READ transaction {txn_id:02X} to 0x{addr:08X}")

            # Wait for completion
            completion_success = await self.wait_for_all_transactions_complete(timeout_cycles=500)

            if not completion_success:
                self.log.error("❌ READ transactions did not complete")
                return False

            # Check monitor bus for completion packets
            monbus_packets = len(self.monbus_slave.packets_received)
            self.log.info(f"📦 Monitor bus received {monbus_packets} packets")

            # Check scoreboard
            completed_txns = len(self.scoreboard.completed_transactions)
            self.log.info(f"📊 Scoreboard shows {completed_txns} completed transactions")

            self.log.info("✅ Simple READ transactions completed successfully")
            return True

        except Exception as e:
            self.log.error(f"❌ Simple READ test failed: {e}")
            return False

    # Add this method to AXIMonitorTB class
    async def _test_simple_writes(self) -> bool:
        """Simple write transaction test - validates cmd/data/resp masters and monbus"""
        self.log.info("✍️ Testing simple WRITE transactions...")

        try:
            # Set immediate ready for simple test
            await self.setup_ready_profile('immediate', 'immediate', 'immediate')

            # Issue a few simple write transactions
            transaction_ids = []
            for i in range(3):
                addr = 0x20000 + i * 0x1000
                length = i % 3  # 0, 1, 2 beats
                txn_id = await self.issue_transaction(addr, length=length)
                transaction_ids.append(txn_id)
                self.log.info(f"Issued WRITE transaction {txn_id:02X} to 0x{addr:08X} with {length+1} beats")

                # Small delay between transactions
                await self.wait_clocks('aclk', 10)

            self.log.info(f"Issued {len(transaction_ids)} write transactions: {[f'{id:02X}' for id in transaction_ids]}")

            # Wait for all transactions to complete
            self.log.info("Waiting for write transactions to complete...")
            completion_success = await self.wait_for_all_transactions_complete(timeout_cycles=1000)

            if not completion_success:
                self.log.error("❌ WRITE transactions did not complete within timeout")
                active_txns = [f'{txn.txn_id:02X}' for txn in self.active_transactions.values()]
                self.log.error(f"Active transactions still pending: {active_txns}")
                return False

            # Give monitor a bit more time to process and generate packets
            await self.wait_clocks('aclk', 50)

            # Check monitor bus packets
            monbus_packets = self.monbus_slave.packets_received
            self.log.info(f"📦 Monitor bus received {len(monbus_packets)} packets")

            if len(monbus_packets) == 0:
                self.log.warning("⚠️ No monitor bus packets received - this may indicate an issue")
            else:
                # Log received packets
                for i, packet in enumerate(monbus_packets[-5:]):  # Show last 5 packets
                    self.log.info(f"  Packet {i}: {packet.get_packet_type_name()}.{packet.get_event_code_name()} "
                                f"Ch={packet.channel_id:02X} Data=0x{packet.data:X}")

            # Check scoreboard
            completed_txns = len(self.scoreboard.completed_transactions)
            active_txns = len(self.scoreboard.active_transactions)
            self.log.info(f"📊 Scoreboard: {completed_txns} completed, {active_txns} active transactions")

            if completed_txns < len(transaction_ids):
                self.log.warning(f"⚠️ Expected {len(transaction_ids)} completed transactions, got {completed_txns}")

            # Check for any verification errors
            verification_errors = len(self.scoreboard.verification_errors)
            protocol_violations = len(self.scoreboard.protocol_violations)

            if verification_errors > 0:
                self.log.error(f"❌ {verification_errors} verification errors detected")
                for error in self.scoreboard.verification_errors[-3:]:  # Show last 3
                    self.log.error(f"  Error: {error['message']}")
                return False

            if protocol_violations > 0:
                self.log.error(f"❌ {protocol_violations} protocol violations detected")
                for violation in self.scoreboard.protocol_violations[-3:]:  # Show last 3
                    self.log.error(f"  Violation: {violation['message']}")
                return False

            # Success criteria
            success = (
                completion_success and  # All transactions completed
                completed_txns >= len(transaction_ids) and  # Scoreboard tracked them
                verification_errors == 0 and  # No verification errors
                protocol_violations == 0  # No protocol violations
            )

            if success:
                self.log.info("✅ Simple WRITE transactions completed successfully")
                self.log.info(f"   - {len(transaction_ids)} transactions issued and completed")
                self.log.info(f"   - {len(monbus_packets)} monitor bus packets generated")
                self.log.info(f"   - 0 verification errors or protocol violations")
            else:
                self.log.error("❌ Simple WRITE test failed validation checks")

            return success

        except Exception as e:
            self.log.error(f"❌ Simple WRITE test failed with exception: {e}")
            import traceback
            self.log.error(f"Traceback: {traceback.format_exc()}")
            return False

    # Add this method to AXIMonitorTB class
    async def _final_verification(self) -> bool:
        """Final verification of overall monitor behavior"""
        self.log.info("🔍 Running final verification...")

        try:
            # Run scoreboard verification
            scoreboard_passed = self.scoreboard.verify_monitor_behavior()

            if not scoreboard_passed:
                self.log.error("❌ Scoreboard verification failed")
                return False

            # Check monitor bus slave for any errors
            if self.monbus_slave.has_verification_errors():
                self.log.error("❌ Monitor bus slave reported verification errors")
                return False

            # Print summary statistics
            self.log.info("📈 Final Test Statistics:")
            self.log.info(f"   - Transactions issued: {self.test_stats['transactions_issued']}")
            self.log.info(f"   - CMD packets: {self.test_stats['cmd_packets']}")
            self.log.info(f"   - DATA packets: {self.test_stats['data_packets']}")
            self.log.info(f"   - RESP packets: {self.test_stats['resp_packets']}")
            self.log.info(f"   - Handshake events: {self.test_stats['handshake_events']}")

            # Get ready controller statistics
            ready_stats = self.get_ready_statistics()
            total_handshakes = sum(stats['handshakes'] for stats in ready_stats.values())
            self.log.info(f"   - Ready handshakes: {total_handshakes}")

            # Get monitor bus statistics
            monbus_stats = self.monbus_slave.get_statistics()
            self.log.info(f"   - Monitor bus packets: {monbus_stats['packets_received']}")

            self.log.info("✅ Final verification passed")
            return True

        except Exception as e:
            self.log.error(f"❌ Final verification failed: {e}")
            return False
