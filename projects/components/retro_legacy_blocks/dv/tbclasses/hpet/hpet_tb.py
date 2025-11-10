# SPDX-License-Identifier: MIT
# SPDX-FileCopyrightText: 2024-2025 sean galloway
#
# RTL Design Sherpa - Industry-Standard RTL Design and Verification
# https://github.com/sean-galloway/RTLDesignSherpa
#
# Module: HPETRegisterMap
# Purpose: HPET (High Precision Event Timer) Testbench - Scalable Version
#
# Documentation: projects/components/apb_hpet/PRD.md
# Subsystem: apb_hpet
#
# Author: sean galloway
# Created: 2025-10-18

"""
HPET (High Precision Event Timer) Testbench - Scalable Version

Comprehensive testbench base for the APB HPET module providing:
- Scalable timer support (2, 3, 8 timers)
- Automatic address width calculation
- Dual clock domain testing (APB and HPET clocks)
- Configuration register access testing
- Timer functionality verification
- Interrupt generation testing
- CDC (Clock Domain Crossing) verification
- Performance and timing analysis

Features:
- Auto-configures address space based on timer count
- Supports 2-timer (6-bit), 3-timer (7-bit), 8-timer (8-bit) configurations
- Modular test structure for different complexity levels
- Timer precision and accuracy testing
- Interrupt latency measurement
- Clock domain crossing validation
- Register access pattern testing
"""

import os
import random
import asyncio
from typing import Dict, List, Optional, Tuple
from collections import deque
import time

import cocotb
from cocotb.utils import get_sim_time
from cocotb.triggers import RisingEdge, Timer, FallingEdge, ClockCycles
from cocotb.clock import Clock

from CocoTBFramework.components.shared.memory_model import MemoryModel
from CocoTBFramework.components.shared.flex_randomizer import FlexRandomizer
from CocoTBFramework.components.apb.apb_packet import APBPacket
from CocoTBFramework.components.apb.apb_components import APBMaster
from CocoTBFramework.components.apb.apb_factories import create_apb_monitor
from CocoTBFramework.tbclasses.shared.tbbase import TBBase
from CocoTBFramework.tbclasses.amba.amba_random_configs import APB_MASTER_RANDOMIZER_CONFIGS


class HPETRegisterMap:
    """HPET Register address definitions - fixed address space for 2-8 timers."""

    # Global registers (fixed addresses)
    HPET_ID = 0x000         # 0x000: Identification register
    HPET_CONFIG = 0x004     # 0x004: Global configuration
    HPET_STATUS = 0x008     # 0x008: Interrupt status
    HPET_RESERVED = 0x00C   # 0x00C: Reserved

    # Main Counter (64-bit split into two 32-bit registers)
    HPET_COUNTER_LO = 0x010 # 0x010: Counter low 32 bits
    HPET_COUNTER_HI = 0x014 # 0x014: Counter high 32 bits

    # Timer base address (fixed layout)
    HPET_TIMER_BASE = 0x100 # 0x100: Timer registers start here
    TIMER_BLOCK_SIZE = 0x20 # 32 bytes per timer

    # Bit definitions
    CONFIG_ENABLE = 0
    CONFIG_LEGACY_REPLACEMENT = 1

    TIMER_ENABLE = 2
    TIMER_INT_ENABLE = 3
    TIMER_TYPE = 4  # 0=one-shot, 1=periodic
    TIMER_SIZE = 5  # 0=32-bit, 1=64-bit
    TIMER_VALUE_SET = 6

    @classmethod
    def get_timer_config_addr(cls, timer_id: int) -> int:
        """Get timer configuration register address."""
        return cls.HPET_TIMER_BASE + (timer_id * cls.TIMER_BLOCK_SIZE) + 0x0

    @classmethod
    def get_timer_comp_lo_addr(cls, timer_id: int) -> int:
        """Get timer comparator low register address."""
        return cls.HPET_TIMER_BASE + (timer_id * cls.TIMER_BLOCK_SIZE) + 0x4

    @classmethod
    def get_timer_comp_hi_addr(cls, timer_id: int) -> int:
        """Get timer comparator high register address."""
        return cls.HPET_TIMER_BASE + (timer_id * cls.TIMER_BLOCK_SIZE) + 0x8

    @classmethod
    def get_timer_reserved_addr(cls, timer_id: int) -> int:
        """Get timer reserved register address."""
        return cls.HPET_TIMER_BASE + (timer_id * cls.TIMER_BLOCK_SIZE) + 0xC

    @classmethod
    def get_required_addr_width(cls) -> int:
        """Get the fixed address width for HPET."""
        return 12  # Fixed 12-bit addressing for 4KB space

    @classmethod
    def get_register_name(cls, addr: int, num_timers: int) -> str:
        """Get human-readable register name for any timer count."""
        if addr == cls.HPET_ID:
            return "HPET_ID"
        elif addr == cls.HPET_CONFIG:
            return "HPET_CONFIG"
        elif addr == cls.HPET_STATUS:
            return "HPET_STATUS"
        elif addr == cls.HPET_RESERVED:
            return "HPET_RESERVED"
        elif addr == cls.HPET_COUNTER_LO:
            return "HPET_COUNTER_LO"
        elif addr == cls.HPET_COUNTER_HI:
            return "HPET_COUNTER_HI"
        else:
            # Check timer registers
            for timer_id in range(num_timers):
                if addr == cls.get_timer_config_addr(timer_id):
                    return f"HPET_T{timer_id}_CONFIG"
                elif addr == cls.get_timer_comp_lo_addr(timer_id):
                    return f"HPET_T{timer_id}_COMP_LO"
                elif addr == cls.get_timer_comp_hi_addr(timer_id):
                    return f"HPET_T{timer_id}_COMP_HI"
                elif addr == cls.get_timer_reserved_addr(timer_id):
                    return f"HPET_T{timer_id}_RESERVED"

        return f"UNKNOWN_0x{addr:02X}"


class HPETScoreboard:
    """Scoreboard for HPET functionality verification."""

    def __init__(self, log, num_timers: int):
        self.log = log
        self.num_timers = num_timers
        self.reset()

    def reset(self):
        """Reset scoreboard state."""
        self.apb_transactions = []
        self.timer_events = []
        self.interrupt_events = []
        self.config_state = {}
        self.counter_writes = []
        self.timer_comparator_writes = []
        self.errors = []

        # Expected behavior tracking
        self.expected_interrupts = {}
        self.interrupt_timing = {}

    def add_apb_transaction(self, packet: APBPacket):
        """Record APB transaction."""
        # Access fields from the packet's fields dictionary
        addr = packet.fields.get('paddr', 0)
        pwrite = packet.fields.get('pwrite', 0)
        pwdata = packet.fields.get('pwdata', 0)
        prdata = packet.fields.get('prdata', 0)
        direction = 'WRITE' if pwrite else 'READ'

        self.apb_transactions.append({
            'time': get_sim_time('ns'),
            'packet': packet,
            'addr': addr,
            'data': pwdata if direction == 'WRITE' else prdata,
            'direction': direction
        })

        # Track configuration changes
        if direction == 'WRITE':
            self._track_config_write(packet)

    def _track_config_write(self, packet: APBPacket):
        """Track configuration register writes."""
        addr = packet.fields.get('paddr', 0)
        data = packet.fields.get('pwdata', 0)

        if addr == HPETRegisterMap.HPET_CONFIG:
            self.config_state['hpet_enable'] = bool(data & (1 << HPETRegisterMap.CONFIG_ENABLE))
            self.config_state['legacy_replacement'] = bool(data & (1 << HPETRegisterMap.CONFIG_LEGACY_REPLACEMENT))

        elif addr == HPETRegisterMap.HPET_COUNTER_LO:
            self.counter_writes.append({
                'time': get_sim_time('ns'),
                'value': data,
                'reg': 'low'
            })

        elif addr == HPETRegisterMap.HPET_COUNTER_HI:
            self.counter_writes.append({
                'time': get_sim_time('ns'),
                'value': data,
                'reg': 'high'
            })
        else:
            # Check timer configuration registers
            for timer_id in range(self.num_timers):
                if addr == HPETRegisterMap.get_timer_config_addr(timer_id):
                    self.config_state[f'timer_{timer_id}'] = {
                        'enable': bool(data & (1 << HPETRegisterMap.TIMER_ENABLE)),
                        'int_enable': bool(data & (1 << HPETRegisterMap.TIMER_INT_ENABLE)),
                        'type': bool(data & (1 << HPETRegisterMap.TIMER_TYPE)),  # 0=one-shot, 1=periodic
                        'size': bool(data & (1 << HPETRegisterMap.TIMER_SIZE)),  # 0=32-bit, 1=64-bit
                        'value_set': bool(data & (1 << HPETRegisterMap.TIMER_VALUE_SET))
                    }
                    break

    def add_timer_event(self, timer_id: int, event_type: str, counter_value: int):
        """Record timer event."""
        self.timer_events.append({
            'time': get_sim_time('ns'),
            'timer_id': timer_id,
            'event_type': event_type,  # 'match', 'reload', 'disable'
            'counter_value': counter_value
        })

    def add_interrupt_event(self, timer_id: int, event_type: str):
        """Record interrupt event."""
        event = {
            'time': get_sim_time('ns'),
            'timer_id': timer_id,
            'event_type': event_type  # 'assert', 'deassert'
        }
        self.interrupt_events.append(event)

        # Track interrupt timing
        if timer_id not in self.interrupt_timing:
            self.interrupt_timing[timer_id] = []

        if event_type == 'assert':
            self.interrupt_timing[timer_id].append({'assert_time': event['time']})
        elif event_type == 'deassert' and self.interrupt_timing[timer_id]:
            last_event = self.interrupt_timing[timer_id][-1]
            if 'deassert_time' not in last_event:
                last_event['deassert_time'] = event['time']
                last_event['duration'] = event['time'] - last_event['assert_time']

    def verify_register_access(self) -> bool:
        """Verify register access patterns."""
        if not self.apb_transactions:
            self.errors.append("No APB transactions recorded")
            return False

        # Check for successful transactions
        successful_writes = sum(1 for tx in self.apb_transactions
                            if tx['direction'] == 'WRITE')
        successful_reads = sum(1 for tx in self.apb_transactions
                            if tx['direction'] == 'READ')

        self.log.info(f"Register access verification: {successful_writes} writes, {successful_reads} reads")

        if successful_writes == 0 and successful_reads == 0:
            self.errors.append("No successful register accesses")
            return False

        return True

    def verify_timer_functionality(self, expected_timer_fires: Dict[int, int]) -> bool:
        """Verify timer functionality against expected behavior."""
        success = True

        for timer_id, expected_fires in expected_timer_fires.items():
            timer_events = [e for e in self.timer_events
                        if e['timer_id'] == timer_id and e['event_type'] == 'match']

            actual_fires = len(timer_events)

            if actual_fires != expected_fires:
                self.errors.append(f"Timer {timer_id}: expected {expected_fires} fires, got {actual_fires}")
                success = False
            else:
                self.log.info(f"Timer {timer_id}: verified {actual_fires} fires")

        return success

    def verify_interrupt_behavior(self) -> bool:
        """Verify interrupt assertion and timing."""
        success = True

        for timer_id in range(self.num_timers):
            timer_interrupts = [e for e in self.interrupt_events
                            if e['timer_id'] == timer_id]

            if not timer_interrupts:
                continue

            # Check for proper assert/deassert pairing
            asserts = [e for e in timer_interrupts if e['event_type'] == 'assert']
            deasserts = [e for e in timer_interrupts if e['event_type'] == 'deassert']

            if len(asserts) != len(deasserts):
                self.errors.append(f"Timer {timer_id}: unmatched interrupt assert/deassert "
                                f"({len(asserts)} asserts, {len(deasserts)} deasserts)")
                success = False

        return success

    def get_statistics(self) -> Dict:
        """Get comprehensive statistics."""
        stats = {
            'total_apb_transactions': len(self.apb_transactions),
            'apb_writes': len([t for t in self.apb_transactions if t['direction'] == 'WRITE']),
            'apb_reads': len([t for t in self.apb_transactions if t['direction'] == 'READ']),
            'timer_events': len(self.timer_events),
            'interrupt_events': len(self.interrupt_events),
            'counter_writes': len(self.counter_writes),
            'errors': len(self.errors),
            'config_changes': len([t for t in self.apb_transactions
                                if t['addr'] == HPETRegisterMap.HPET_CONFIG and t['direction'] == 'WRITE'])
        }

        # Calculate interrupt statistics
        for timer_id in range(self.num_timers):
            timer_timing = self.interrupt_timing.get(timer_id, [])
            completed_interrupts = [t for t in timer_timing if 'duration' in t]

            if completed_interrupts:
                durations = [t['duration'] for t in completed_interrupts]
                stats[f'timer_{timer_id}_avg_interrupt_duration'] = sum(durations) / len(durations)
                stats[f'timer_{timer_id}_interrupt_count'] = len(completed_interrupts)

        return stats


class HPETTB(TBBase):
    """HPET Testbench with comprehensive testing capabilities - Scalable version."""

    def __init__(self, dut):
        TBBase.__init__(self, dut)

        # Get test parameters from environment
        self.NUM_TIMERS = int(os.environ.get('TEST_NUM_TIMERS', '2'))  # Default to 2 timers
        self.ADDR_WIDTH = 12  # Fixed 12-bit addressing for all configurations
        self.DATA_WIDTH = 32   # Fixed 32-bit data width
        self.COUNTER_WIDTH = 64  # Fixed 64-bit counter

        # Validate timer count
        if self.NUM_TIMERS < 2 or self.NUM_TIMERS > 8:
            raise ValueError(f"NUM_TIMERS={self.NUM_TIMERS} out of supported range (2-8)")

        # Clock configuration
        self.APB_CLOCK_PERIOD = int(os.environ.get('TEST_APB_CLOCK_PERIOD', '20'))  # 50MHz
        self.HPET_CLOCK_PERIOD = int(os.environ.get('TEST_HPET_CLOCK_PERIOD', '10'))  # 100MHz

        # Test configuration
        self.MAX_TEST_TIME = int(os.environ.get('TEST_MAX_TIME', '100000'))  # ns
        self.INTERRUPT_TIMEOUT = int(os.environ.get('TEST_INTERRUPT_TIMEOUT', '25000'))  # ns - allow for 1000 * 10ns HPET clocks plus APB transaction delays

        # State tracking
        self.test_phase = "INIT"
        self.timer_interrupt_state = [False] * self.NUM_TIMERS
        self.expected_timer_events = {}

        # Components will be initialized in setup
        self.apb_master = None
        self.apb_monitor = None
        self.scoreboard = None

        self.log.info(f"HPET TB initialized: {self.NUM_TIMERS} timers, 12-bit addressing (4KB)")
        self.log.info(f"Fixed parameters: DW={self.DATA_WIDTH}, CounterW={self.COUNTER_WIDTH}")
        self.log.info(f"Clock periods: APB={self.APB_CLOCK_PERIOD}ns, HPET={self.HPET_CLOCK_PERIOD}ns")

    async def setup_clocks_and_reset(self):
        """Setup dual clock domains and reset sequence."""
        self.log.info("Setting up HPET clocks and reset")

        # Start both clock domains
        apb_clock = Clock(self.dut.pclk, self.APB_CLOCK_PERIOD, units="ns")
        hpet_clock = Clock(self.dut.hpet_clk, self.HPET_CLOCK_PERIOD, units="ns")

        cocotb.start_soon(apb_clock.start())
        cocotb.start_soon(hpet_clock.start())

        # Initial reset state
        self.dut.presetn.value = 0
        self.dut.hpet_resetn.value = 0

        # Wait for clocks to stabilize
        await Timer(100, units="ns")

        # Release resets (APB first, then HPET)
        self.dut.presetn.value = 1
        await Timer(50, units="ns")
        self.dut.hpet_resetn.value = 1

        # Wait for reset deassertion to propagate
        await Timer(100, units="ns")

        self.log.info("Clock and reset setup complete")

    async def setup_components(self):
        """Initialize APB components and scoreboard."""
        self.log.info("Setting up HPET testbench components")

        try:
            # Create APB Master directly and initialize it properly
            self.apb_master = APBMaster(
                entity=self.dut,
                title='HPET APB Master',
                prefix='s_apb',
                clock=self.dut.pclk,
                bus_width=32,       # Fixed 32-bit data
                addr_width=12,      # Fixed 12-bit addressing
                randomizer=FlexRandomizer(APB_MASTER_RANDOMIZER_CONFIGS['fixed']),
                log=self.log
            )

            # Properly initialize the APB master
            await self.apb_master.reset_bus()

            self.log.info(f"✓ APB Master created and initialized: {type(self.apb_master)}")

        except Exception as e:
            self.log.error(f"Failed to create APB Master: {e}")
            raise

        try:
            # APB Monitor for transaction tracking
            self.apb_monitor = create_apb_monitor(
                self.dut, 'HPET APB Monitor', 's_apb', self.dut.pclk,
                addr_width=12, data_width=32,  # Fixed 12-bit addr, 32-bit data
                log=self.log
            )
            self.log.info(f"✓ APB Monitor created: {type(self.apb_monitor)}")

        except Exception as e:
            self.log.error(f"Failed to create APB Monitor: {e}")
            raise

        # Scoreboard for verification
        self.scoreboard = HPETScoreboard(self.log, self.NUM_TIMERS)

        # Connect monitor callback
        self.apb_monitor.add_callback(self.apb_transaction_callback)

        # Start interrupt monitoring
        cocotb.start_soon(self.monitor_interrupts())

        self.log.info("HPET testbench components setup complete")

    def apb_transaction_callback(self, packet: APBPacket):
        """Callback for APB transactions."""
        self.scoreboard.add_apb_transaction(packet)

        # Access fields from the packet's fields dictionary
        addr = packet.fields.get('paddr', 0)
        pwrite = packet.fields.get('pwrite', 0)
        pwdata = packet.fields.get('pwdata', 0)
        prdata = packet.fields.get('prdata', 0)
        direction = 'WRITE' if pwrite else 'READ'

        # Log register access
        reg_name = HPETRegisterMap.get_register_name(addr, self.NUM_TIMERS)
        self.log.debug(f"APB {direction}: {reg_name} (0x{addr:02X}) = "
                    f"0x{pwdata if direction == 'WRITE' else prdata:08X}{self.get_time_ns_str()}")

    async def monitor_interrupts(self):
        """Monitor timer interrupts for changes."""
        prev_state = [False] * self.NUM_TIMERS

        while True:
            await RisingEdge(self.dut.hpet_clk)

            # Get the timer_irq vector value
            irq_vector = self.dut.timer_irq.value

            current_state = []
            for i in range(self.NUM_TIMERS):
                # Extract bit i from the vector
                if irq_vector is not None:
                    irq_val = bool((int(irq_vector) >> i) & 1)
                else:
                    irq_val = False
                current_state.append(irq_val)

                # Detect state changes
                if irq_val != prev_state[i]:
                    event_type = 'assert' if irq_val else 'deassert'
                    self.scoreboard.add_interrupt_event(i, event_type)
                    self.log.info(f"Timer {i} interrupt {event_type}{self.get_time_ns_str()}")

            prev_state = current_state
            self.timer_interrupt_state = current_state

    async def write_register(self, addr: int, data: int) -> APBPacket:
        """Write to HPET register using correct APB master API."""
        try:
            # Create APB packet with proper field configuration
            write_packet = APBPacket(
                pwrite=1,
                paddr=addr,
                pwdata=data,
                pstrb=0xF,  # All 4 bytes enabled for 32-bit
                pprot=0,
                data_width=32,  # Fixed 32-bit data
                addr_width=12,  # Fixed 12-bit addressing
                strb_width=4    # Fixed 4-byte strobe
            )

            # Ensure the packet has a direction attribute
            write_packet.direction = 'WRITE'

            # Initialize transmit_coroutine if needed
            if not hasattr(self.apb_master, 'transmit_coroutine'):
                self.apb_master.transmit_coroutine = None

            # Send using APB master
            await self.apb_master.send(write_packet)

            # Wait for the APB transaction to complete
            # Need to wait for both PSEL and PENABLE, then PREADY
            timeout = 0
            while timeout < 100:
                await RisingEdge(self.dut.pclk)
                if (self.dut.s_apb_PSEL.value and
                    self.dut.s_apb_PENABLE.value and
                    self.dut.s_apb_PREADY.value):
                    break
                timeout += 1

            # Wait one more cycle for transaction to fully complete
            await RisingEdge(self.dut.pclk)

            return write_packet

        except Exception as e:
            self.log.error(f"Write register failed: {e}")
            raise

    async def read_register(self, addr: int) -> Tuple[APBPacket, int]:
        """Read from HPET register using correct APB master API."""
        try:
            # Create APB packet with proper field configuration
            read_packet = APBPacket(
                pwrite=0,
                paddr=addr,
                pwdata=0,
                pstrb=0xF,  # All 4 bytes enabled for 32-bit
                pprot=0,
                data_width=32,  # Fixed 32-bit data
                addr_width=12,  # Fixed 12-bit addressing
                strb_width=4    # Fixed 4-byte strobe
            )

            # Ensure the packet has a direction attribute
            read_packet.direction = 'READ'

            # Initialize transmit_coroutine if needed
            if not hasattr(self.apb_master, 'transmit_coroutine'):
                self.apb_master.transmit_coroutine = None

            # Send using APB master
            await self.apb_master.send(read_packet)

            # Wait for the APB transaction to complete
            # Need to wait for both PSEL and PENABLE, then PREADY
            timeout = 0
            while timeout < 100:
                await RisingEdge(self.dut.pclk)
                if (self.dut.s_apb_PSEL.value and
                    self.dut.s_apb_PENABLE.value and
                    self.dut.s_apb_PREADY.value):
                    break
                timeout += 1

            # Capture the read data from the bus
            read_data = int(self.dut.s_apb_PRDATA.value)
            read_packet.fields['prdata'] = read_data

            # Wait one more cycle for transaction to fully complete
            await RisingEdge(self.dut.pclk)

            return read_packet, read_data

        except Exception as e:
            self.log.error(f"Read register failed: {e}")
            raise

    async def wait_apb_idle(self):
        """Wait for APB master to be idle."""
        # Wait for a few APB clock cycles to ensure completion
        for _ in range(10):
            await RisingEdge(self.dut.pclk)

    def generate_test_report(self) -> Dict:
        """Generate comprehensive test report."""
        stats = self.scoreboard.get_statistics()

        report = {
            'test_summary': {
                'total_tests_run': stats.get('tests_run', 0),
                'tests_passed': stats.get('tests_passed', 0),
                'test_phase': self.test_phase,
                'total_time': get_sim_time('ns'),
                'version': f'{self.NUM_TIMERS}-timer/{self.ADDR_WIDTH}-bit'
            },
            'configuration': {
                'num_timers': self.NUM_TIMERS,
                'addr_width': self.ADDR_WIDTH,
                'data_width': self.DATA_WIDTH,
                'counter_width': self.COUNTER_WIDTH,
                'apb_clock_period': self.APB_CLOCK_PERIOD,
                'hpet_clock_period': self.HPET_CLOCK_PERIOD
            },
            'apb_statistics': {
                'total_transactions': stats['total_apb_transactions'],
                'writes': stats['apb_writes'],
                'reads': stats['apb_reads'],
                'config_changes': stats['config_changes']
            },
            'timer_statistics': {
                'timer_events': stats['timer_events'],
                'interrupt_events': stats['interrupt_events'],
                'counter_writes': stats['counter_writes'],
                'timers_available': self.NUM_TIMERS
            },
            'verification_results': {
                'register_access_verified': stats['total_apb_transactions'] > 0,
                'timer_functionality_verified': stats['timer_events'] > 0,
                'interrupt_behavior_verified': stats['interrupt_events'] > 0,
                'errors_detected': stats['errors']
            }
        }

        # Add interrupt timing statistics
        for timer_id in range(self.NUM_TIMERS):
            avg_duration_key = f'timer_{timer_id}_avg_interrupt_duration'
            count_key = f'timer_{timer_id}_interrupt_count'

            if avg_duration_key in stats:
                report['timer_statistics'][f'timer_{timer_id}_avg_duration'] = stats[avg_duration_key]
                report['timer_statistics'][f'timer_{timer_id}_count'] = stats[count_key]

        return report
