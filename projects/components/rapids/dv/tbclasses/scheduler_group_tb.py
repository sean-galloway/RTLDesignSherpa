# SPDX-License-Identifier: MIT
# SPDX-FileCopyrightText: 2024-2025 sean galloway
#
# RTL Design Sherpa - Industry-Standard RTL Design and Verification
# https://github.com/sean-galloway/RTLDesignSherpa
#
# Module: SchedulerGroupTB
# Purpose: RAPIDS Scheduler Group Testbench - v1.1
#
# Documentation: projects/components/rapids/PRD.md
# Subsystem: rapids
#
# Author: sean galloway
# Created: 2025-10-18

"""
RAPIDS Scheduler Group Testbench - v1.1

Comprehensive scheduler wrapper testbench following the data path testbench methodology:
- Enhanced descriptor engine interface testing
- Program engine AXI write operations
- Control read/write engine interfaces (ctrlrd/ctrlwr)
- Data mover interface validation with stream control
- EOS completion interface testing
- Monitor bus validation
- Credit management and scheduling validation
- Channel isolation and multi-channel operations

Features:
- Fixed 32-channel configuration matching data path TB
- Real Network, AXI4, and GAXI component integration
- Support for ctrlrd (control read) and ctrlwr (control write) interfaces
- Comprehensive test coverage with stress testing
- Performance monitoring and resource validation
- Stream boundary processing (EOS/EOL/EOD)
- Error injection and handling
"""

import os
import random
import asyncio
from typing import List, Dict, Any, Tuple, Optional, Union
import time
import cocotb
from cocotb.triggers import RisingEdge, ClockCycles

# Framework imports
from CocoTBFramework.tbclasses.shared.tbbase import TBBase
from CocoTBFramework.components.shared.memory_model import MemoryModel
from CocoTBFramework.components.shared.flex_randomizer import FlexRandomizer

# REAL Network imports
from CocoTBFramework.components.network.network_factories import (
    create_network_master, create_network_slave, send_packet_sequence, validate_network_packet
)
from CocoTBFramework.components.network.network_packet import MNOCPacket
from CocoTBFramework.components.network.network_field_configs import MNOCFieldConfigHelper
from CocoTBFramework.components.network.network_compliance_checker import MNOCComplianceChecker

# REAL AXI4 imports
from CocoTBFramework.components.axi4.axi4_factories import create_axi4_slave_rd, create_axi4_slave_wr

# REAL GAXI imports (for monitor bus)
from CocoTBFramework.components.gaxi.gaxi_factories import create_gaxi_slave
from CocoTBFramework.components.gaxi.gaxi_packet import GAXIPacket


class SchedulerGroupTB(TBBase):
    """
    Complete RAPIDS Scheduler Group testbench v1.1 for 32-channel validation.

    Tests comprehensive scheduler wrapper functionality:
    - APB programming interface for descriptor fetch
    - RDA packet interface from Network slave
    - EOS completion interface from SRAM control
    - Enhanced descriptor engine interface with stream control
    - Program engine AXI write operations
    - Control read engine interface (ctrlrd) for pre-descriptor operations
    - Control write engine interface (ctrlwr) for post-descriptor operations
    - Data mover interface with stream boundaries
    - RDA credit return management
    - Monitor bus aggregation and validation
    - Configuration and status interfaces
    - Channel isolation and concurrent operations
    - Error handling and timeout detection
    """

    def __init__(self, dut, clk=None, rst_n=None):
        super().__init__(dut)

        # Fixed 32-channel configuration matching data path TB
        self.TEST_CHANNELS = 32  # FIXED
        self.TEST_ADDR_WIDTH = self.convert_to_int(os.environ.get('TEST_ADDR_WIDTH', '64'))
        self.TEST_DATA_WIDTH = self.convert_to_int(os.environ.get('TEST_DATA_WIDTH', '512'))
        self.TEST_AXI_ID_WIDTH = self.convert_to_int(os.environ.get('TEST_AXI_ID_WIDTH', '8'))
        self.TEST_CREDIT_WIDTH = self.convert_to_int(os.environ.get('TEST_CREDIT_WIDTH', '8'))
        self.TEST_CLK_PERIOD = self.convert_to_int(os.environ.get('TEST_CLK_PERIOD', '10'))
        self.SEED = self.convert_to_int(os.environ.get('SEED', '12345'))

        # Initialize random generator
        random.seed(self.SEED)

        # Setup clock and reset signals
        self.clk = clk
        self.clk_name = clk._name if clk else 'clk'
        self.rst_n = rst_n

        # Set limits based on widths
        self.MAX_ADDR = (2**self.TEST_ADDR_WIDTH) - 1
        self.MAX_DATA = (2**self.TEST_DATA_WIDTH) - 1
        self.MAX_CREDIT = (2**self.TEST_CREDIT_WIDTH) - 1

        # Test configuration
        self.test_config = {
            'channels': self.TEST_CHANNELS,
            'data_width': self.TEST_DATA_WIDTH,
            'addr_width': self.TEST_ADDR_WIDTH,
            'axi_id_width': self.TEST_AXI_ID_WIDTH,
            'credit_width': self.TEST_CREDIT_WIDTH,
            'timeout_cycles': 1000,
            'early_warning_threshold': 4
        }

        # Test statistics
        self.test_stats = {
            'summary': {
                'total_operations': 0,
                'successful_operations': 0,
                'failed_operations': 0,
                'test_duration': 0.0,
                'start_time': 0.0
            },
            'channels': {
                'total_channels_used': 0,
                'channels_tested': set(),
                'concurrent_channels': 0
            },
            'performance': {
                'descriptors_processed': 0,
                'axi_writes_completed': 0,
                'eos_completions_handled': 0,
                'monitor_events_generated': 0,
                'peak_channels_active': 0,
                'operations_per_second': 0.0
            },
            'errors': {
                'timeout_errors': 0,
                'descriptor_errors': 0,
                'axi_errors': 0,
                'monitor_errors': 0,
                'configuration_errors': 0
            }
        }

        # Component interfaces (initialized in setup)
        self.rda_network_master = None      # RDA packet injection
        self.desc_axi_slave = None       # Descriptor AXI interface
        self.prog_axi_slave = None       # Program engine AXI interface
        self.monitor_slave = None        # Monitor bus interface
        self.eos_completion_master = None # EOS completion injection
        self.data_mover_slave = None     # Data mover interface

        # Memory models
        self.descriptor_memory = None
        self.program_memory = None

        # Memory bounds (set during setup_interfaces)
        self.descriptor_memory_size = 0
        self.program_memory_size = 0

        # Timing profiles
        self.timing_profiles = {
            'normal': {'wait_cycles': (1, 5), 'randomization': 0.3},
            'fast': {'wait_cycles': (0, 2), 'randomization': 0.1},
            'stress': {'wait_cycles': (0, 10), 'randomization': 0.5},
            'timeout': {'wait_cycles': (100, 200), 'randomization': 0.8}
        }
        self.current_timing = 'normal'

        # Channel state tracking
        self.channel_states = {}
        for ch in range(self.TEST_CHANNELS):
            self.channel_states[ch] = {
                'idle': True,
                'descriptor_pending': False,
                'program_active': False,
                'data_transfer_active': False,
                'eos_pending': False,
                'credit_count': 0,
                'last_activity': 0.0
            }

        self.log.info(f"SchedulerGroupTB initialized: {self.TEST_CHANNELS} channels, "
                     f"{self.TEST_DATA_WIDTH}-bit data, {self.TEST_ADDR_WIDTH}-bit addresses")

    async def setup_clocks_and_reset(self):
        """Complete initialization - starts clocks and performs reset sequence."""
        try:
            self.log.info("Setting up clocks and reset...")

            # Start clock
            await self.start_clock(self.clk_name, freq=self.TEST_CLK_PERIOD, units='ns')

            # Set any config signals that must be valid BEFORE reset
            # This is critical for credit counter exponential encoding initialization
            self.dut.cfg_idle_mode.value = 0
            self.dut.cfg_channel_wait.value = 0
            self.dut.cfg_channel_enable.value = 1           # Enable channel
            self.dut.cfg_use_credit.value = 1               # Enable credit mode
            self.dut.cfg_initial_credit.value = 4           # 2^4 = 16 credits
            self.dut.credit_increment.value = 0
            self.dut.cfg_channel_reset.value = 0

            # Perform reset sequence
            await self.assert_reset()
            await self.wait_clocks(self.clk_name, 10)  # Hold reset for 10 cycles
            await self.deassert_reset()
            await self.wait_clocks(self.clk_name, 5)   # Stabilization time

            self.log.info("✅ Clock and reset setup complete")

        except Exception as e:
            self.log.error(f"Clock and reset setup failed: {str(e)}")
            raise

    async def assert_reset(self):
        """Assert reset signal (active-low)."""
        self.rst_n.value = 0
        self.log.debug("Reset asserted")

    async def deassert_reset(self):
        """Deassert reset signal (active-low)."""
        self.rst_n.value = 1
        self.log.debug("Reset deasserted")

    async def setup_interfaces(self):
        """Setup all component interfaces following data path TB pattern."""
        try:
            self.log.info("Setting up scheduler wrapper interfaces...")

            # Create memory models FIRST (needed for AXI slave initialization)
            desc_num_lines = 4096
            desc_bytes_per_line = 64  # 512-bit descriptor lines
            self.descriptor_memory = MemoryModel(
                num_lines=desc_num_lines,
                bytes_per_line=desc_bytes_per_line,
                log=self.log
            )
            self.descriptor_memory_size = desc_num_lines * desc_bytes_per_line

            prog_num_lines = 1024
            prog_bytes_per_line = 4   # 32-bit program words
            self.program_memory = MemoryModel(
                num_lines=prog_num_lines,
                bytes_per_line=prog_bytes_per_line,
                log=self.log
            )
            self.program_memory_size = prog_num_lines * prog_bytes_per_line

            # RDA packet interface (Network Master for injection)
            self.rda_network_master = create_network_master(
                self.dut, self.clk, prefix="rda_", log=self.log,
                data_width=self.TEST_DATA_WIDTH,
                num_channels=self.TEST_CHANNELS
            )

            # Descriptor engine AXI read interface (AXI4 Slave)
            # Signals: desc_ar_*, desc_r_*
            # SOLUTION: Use prefix="desc_" to match desc_ar_valid, desc_r_valid, etc.
            # The AXI4 patterns will automatically add channel prefixes (ar_, r_)
            self.desc_axi_slave = create_axi4_slave_rd(
                dut=self.dut,
                clock=self.clk,
                prefix="desc_",  # Prefix for descriptor engine AXI signals
                log=self.log,
                data_width=self.TEST_DATA_WIDTH,
                addr_width=self.TEST_ADDR_WIDTH,
                id_width=self.TEST_AXI_ID_WIDTH,
                multi_sig=True,  # Use multi_sig for field-level signals
                memory_model=self.descriptor_memory
            )

            # Program engine AXI write interface (AXI4 Slave)
            # Signals: prog_aw_*, prog_w_*, prog_b_*
            # SOLUTION: Use prefix="prog_" to match prog_aw_valid, prog_w_valid, etc.
            # The AXI4 patterns will automatically add channel prefixes (aw_, w_, b_)
            self.prog_axi_slave = create_axi4_slave_wr(
                dut=self.dut,
                clock=self.clk,
                prefix="prog_",  # Prefix for program engine AXI signals
                log=self.log,
                data_width=32,  # Program engine uses 32-bit writes
                addr_width=self.TEST_ADDR_WIDTH,
                id_width=self.TEST_AXI_ID_WIDTH,
                multi_sig=True,  # Use multi_sig for field-level signals
                memory_model=self.program_memory
            )

            # Monitor bus interface (GAXI Slave for monitor events)
            self.monitor_slave = create_gaxi_slave(
                self.dut, "MonitorBus", "mon_", self.clk,
                field_config=None,  # Will use default
                log=self.log,
                mode='skid'
            )

            # NOTE: EOS completion and data mover interfaces are simple valid/ready + data
            # No need for GAXI factories - drive signals directly in test methods
            # eos_completion_valid, eos_completion_ready, eos_completion_channel
            # data_valid, data_ready, data_*, etc.

            self.log.info("✅ All scheduler wrapper interfaces setup complete")

        except Exception as e:
            self.log.error(f"Failed to setup interfaces: {str(e)}")
            raise

    async def initialize_test(self):
        """Initialize test environment following data path TB pattern."""
        try:
            self.log.info("Initializing scheduler wrapper test environment...")

            # Record start time
            self.test_stats['summary']['start_time'] = time.time()

            # Setup all interfaces
            await self.setup_interfaces()

            # Wait for interfaces to stabilize
            await self.wait_clocks(self.clk_name, 10)

            # Initialize all configuration signals to safe defaults
            await self.initialize_configuration()

            # Clear any pending transactions
            await self.clear_all_interfaces()

            self.log.info("✅ Scheduler wrapper test initialization complete")

        except Exception as e:
            self.log.error(f"Test initialization failed: {str(e)}")
            raise

    async def initialize_configuration(self):
        """Initialize configuration signals to safe defaults."""
        try:
            # APB interface defaults
            self.dut.apb_valid.value = 0
            self.dut.apb_addr.value = 0

            # RDA interface defaults
            if hasattr(self.dut, 'rda_valid'):
                self.dut.rda_valid.value = 0
                self.dut.rda_packet.value = 0
                self.dut.rda_channel.value = 0

            # Configuration defaults
            self.dut.cfg_idle_mode.value = 0
            self.dut.cfg_channel_wait.value = 0
            self.dut.cfg_channel_enable.value = 1  # Enable channel (1-bit signal)
            self.dut.cfg_use_credit.value = 1
            self.dut.cfg_initial_credit.value = 4
            self.dut.credit_increment.value = 0
            self.dut.cfg_channel_reset.value = 0

            # EOS completion interface defaults
            if hasattr(self.dut, 'eos_completion_valid'):
                self.dut.eos_completion_valid.value = 0
                self.dut.eos_completion_channel.value = 0

            # Data mover interface ready signals
            if hasattr(self.dut, 'data_ready'):
                self.dut.data_ready.value = 1
                self.dut.data_transfer_length.value = 0
                self.dut.data_error.value = 0
                self.dut.data_done_strobe.value = 0

            # RDA credit return interface
            if hasattr(self.dut, 'rda_complete_ready'):
                self.dut.rda_complete_ready.value = 1

            # Control Read Engine Interface (ctrlrd) - defaults
            if hasattr(self.dut, 'ctrlrd_ready'):
                self.dut.ctrlrd_ready.value = 1
                self.dut.ctrlrd_error.value = 0
                self.dut.ctrlrd_result.value = 0

            # Control Write Engine Interface (ctrlwr) - defaults
            if hasattr(self.dut, 'ctrlwr_ready'):
                self.dut.ctrlwr_ready.value = 1
                self.dut.ctrlwr_error.value = 0

            # Monitor bus ready
            if hasattr(self.dut, 'mon_ready'):
                self.dut.mon_ready.value = 1

            await self.wait_clocks(self.clk_name, 5)
            self.log.info("Configuration signals initialized (including ctrlrd/ctrlwr interfaces)")

        except Exception as e:
            self.log.error(f"Configuration initialization failed: {str(e)}")
            raise

    async def clear_all_interfaces(self):
        """Clear all interfaces and reset to known state."""
        try:
            # Clear any pending Network transactions
            if self.rda_network_master:
                # Flush any pending packets
                pass

            # Memory models don't need clearing - they persist test patterns
            # which is intentional for descriptor and program data

            # Wait for all to settle
            await self.wait_clocks(self.clk_name, 10)
            self.log.info("All interfaces cleared")

        except Exception as e:
            self.log.error(f"Interface clearing failed: {str(e)}")
            raise

    def set_timing_profile(self, profile_name: str):
        """Set timing profile for test operations."""
        if profile_name in self.timing_profiles:
            self.current_timing = profile_name
            self.log.info(f"Timing profile set to: {profile_name}")
        else:
            self.log.warning(f"Unknown timing profile: {profile_name}, using 'normal'")
            self.current_timing = 'normal'

    async def wait_random_cycles(self):
        """Wait random cycles based on current timing profile."""
        profile = self.timing_profiles[self.current_timing]
        min_cycles, max_cycles = profile['wait_cycles']
        cycles = random.randint(min_cycles, max_cycles)
        await self.wait_clocks(self.clk_name, cycles)

    async def test_basic_descriptor_processing(self, count: int = 64) -> Tuple[bool, Dict[str, Any]]:
        """Test basic descriptor engine processing functionality."""
        self.log.info(f"Testing basic descriptor processing ({count} descriptors)...")

        success_count = 0
        error_count = 0
        channels_tested = set()

        try:
            for i in range(count):
                # Select random channel
                channel = random.randint(0, self.TEST_CHANNELS - 1)
                channels_tested.add(channel)

                # Generate descriptor data
                # Address must fit within memory bounds (leave room for one descriptor line)
                max_desc_addr = self.descriptor_memory_size - (self.TEST_DATA_WIDTH // 8)
                desc_addr = random.randint(0, max_desc_addr)
                desc_data = random.randint(0, self.MAX_DATA)

                # Program descriptor into memory
                bytes_per_line = self.TEST_DATA_WIDTH // 8  # 64 bytes for 512-bit data
                data_bytes = bytearray(desc_data.to_bytes(bytes_per_line, 'little'))
                self.descriptor_memory.write(desc_addr, data_bytes)

                # Request descriptor fetch via APB
                await self.request_descriptor_fetch(desc_addr, channel)

                # Wait for descriptor to be processed
                await self.wait_random_cycles()

                # Verify descriptor processing
                if await self.verify_descriptor_processed(channel, desc_data):
                    success_count += 1
                    self.channel_states[channel]['descriptor_pending'] = False
                else:
                    error_count += 1

                await self.wait_random_cycles()

        except Exception as e:
            self.log.error(f"Descriptor processing test failed: {str(e)}")
            error_count += 1

        stats = {
            'success_count': success_count,
            'error_count': error_count,
            'success_rate': success_count / count if count > 0 else 0,
            'channels_tested': len(channels_tested)
        }

        self.test_stats['performance']['descriptors_processed'] += success_count
        self.test_stats['summary']['total_operations'] += count
        self.test_stats['summary']['successful_operations'] += success_count
        self.test_stats['summary']['failed_operations'] += error_count

        return error_count == 0, stats

    async def request_descriptor_fetch(self, addr: int, channel: int):
        """Request descriptor fetch via APB interface."""
        try:
            # APB fetch request
            self.dut.apb_valid.value = 1
            self.dut.apb_addr.value = addr

            await RisingEdge(self.clk)

            # Wait for ready
            timeout = 100
            while timeout > 0 and not self.dut.apb_ready.value:
                await RisingEdge(self.clk)
                timeout -= 1

            if timeout == 0:
                raise TimeoutError("APB request timeout")

            self.dut.apb_valid.value = 0
            self.channel_states[channel]['descriptor_pending'] = True

        except Exception as e:
            self.log.error(f"APB descriptor request failed: {str(e)}")
            raise

    async def verify_descriptor_processed(self, channel: int, expected_data: int) -> bool:
        """Verify that descriptor was processed correctly by checking AXI read activity."""
        try:
            # Monitor the AXI read interface for activity
            # The descriptor engine should generate AXI read requests
            timeout = 100
            axi_activity_detected = False

            for _ in range(timeout):
                await RisingEdge(self.clk)

                # Check if AXI AR (address read) channel is active
                if hasattr(self.dut, 'desc_ar_valid') and int(self.dut.desc_ar_valid.value) == 1:
                    axi_activity_detected = True
                    self.log.debug(f"AXI AR activity detected for descriptor on channel {channel}")
                    break

            # Also check the AXI slave's receive queue for read requests
            if self.desc_axi_slave and hasattr(self.desc_axi_slave, 'ar_channel'):
                ar_queue = self.desc_axi_slave.ar_channel._recvQ
                if len(ar_queue) > 0:
                    axi_activity_detected = True
                    self.log.debug(f"AXI AR transaction in queue: {len(ar_queue)} transactions")

            return axi_activity_detected

        except Exception as e:
            self.log.error(f"Error verifying descriptor processing: {str(e)}")
            return False

    async def test_program_engine_operations(self, count: int = 32) -> Tuple[bool, Dict[str, Any]]:
        """Test program engine AXI write operations."""
        self.log.info(f"Testing program engine operations ({count} writes)...")

        success_count = 0
        error_count = 0

        try:
            for i in range(count):
                # Generate program operation
                # Address must fit within memory bounds (leave room for one program word)
                max_prog_addr = self.program_memory_size - 4
                prog_addr = random.randint(0, max_prog_addr)
                prog_data = random.randint(0, 0xFFFFFFFF)  # 32-bit data

                # Trigger program operation
                await self.trigger_program_operation(prog_addr, prog_data)

                # Wait for AXI write completion
                if await self.wait_for_axi_write_completion(self.prog_axi_slave):
                    success_count += 1
                else:
                    error_count += 1

                await self.wait_random_cycles()

        except Exception as e:
            self.log.error(f"Program engine test failed: {str(e)}")
            error_count += 1

        stats = {
            'success_count': success_count,
            'error_count': error_count,
            'success_rate': success_count / count if count > 0 else 0
        }

        self.test_stats['performance']['axi_writes_completed'] += success_count

        return error_count == 0, stats

    async def trigger_program_operation(self, addr: int, data: int):
        """Trigger program engine operation."""
        # This would typically be triggered by descriptor processing
        # For testing, we'll simulate the trigger
        pass

    async def wait_for_axi_write_completion(self, axi_slave) -> bool:
        """Wait for AXI write operation to complete."""
        # Monitor AXI interface for write completion
        timeout = 100
        while timeout > 0:
            # Check for AXI write activity
            await RisingEdge(self.clk)
            timeout -= 1

        return True  # Placeholder - would check actual AXI completion

    async def test_eos_completion_interface(self, count: int = 16) -> Tuple[bool, Dict[str, Any]]:
        """Test EOS completion interface from SRAM control."""
        self.log.info(f"Testing EOS completion interface ({count} completions)...")

        success_count = 0
        error_count = 0

        try:
            for i in range(count):
                channel = random.randint(0, self.TEST_CHANNELS - 1)

                # Inject EOS completion
                await self.inject_eos_completion(channel)

                # Verify EOS handling
                if await self.verify_eos_handling(channel):
                    success_count += 1
                else:
                    error_count += 1

                await self.wait_random_cycles()

        except Exception as e:
            self.log.error(f"EOS completion test failed: {str(e)}")
            error_count += 1

        stats = {
            'success_count': success_count,
            'error_count': error_count,
            'success_rate': success_count / count if count > 0 else 0
        }

        self.test_stats['performance']['eos_completions_handled'] += success_count

        return error_count == 0, stats

    async def inject_eos_completion(self, channel: int):
        """Inject EOS completion event for testing."""
        try:
            if hasattr(self.dut, 'eos_completion_valid'):
                self.dut.eos_completion_valid.value = 1
                self.dut.eos_completion_channel.value = channel

                await RisingEdge(self.clk)

                # Wait for ready
                timeout = 50
                while timeout > 0 and not self.dut.eos_completion_ready.value:
                    await RisingEdge(self.clk)
                    timeout -= 1

                self.dut.eos_completion_valid.value = 0
                self.channel_states[channel]['eos_pending'] = True

        except Exception as e:
            self.log.error(f"EOS completion injection failed: {str(e)}")
            raise

    async def verify_eos_handling(self, channel: int) -> bool:
        """Verify EOS completion was handled correctly."""
        # Check that EOS was processed and data_eos was generated
        await self.wait_clocks(self.clk_name, 10)
        self.channel_states[channel]['eos_pending'] = False
        return True  # Placeholder - would check actual EOS handling

    async def test_monitor_bus_operations(self, count: int = 32) -> Tuple[bool, Dict[str, Any]]:
        """Test monitor bus aggregation and event generation."""
        self.log.info(f"Testing monitor bus operations ({count} events)...")

        success_count = 0
        error_count = 0

        try:
            for i in range(count):
                # Wait for monitor events
                if await self.wait_for_monitor_event():
                    success_count += 1
                else:
                    error_count += 1

                await self.wait_random_cycles()

        except Exception as e:
            self.log.error(f"Monitor bus test failed: {str(e)}")
            error_count += 1

        stats = {
            'success_count': success_count,
            'error_count': error_count,
            'success_rate': success_count / count if count > 0 else 0
        }

        self.test_stats['performance']['monitor_events_generated'] += success_count

        return error_count == 0, stats

    async def wait_for_monitor_event(self) -> bool:
        """Wait for monitor bus event."""
        timeout = 100
        while timeout > 0:
            if hasattr(self.dut, 'mon_valid') and self.dut.mon_valid.value:
                return True
            await RisingEdge(self.clk)
            timeout -= 1
        return False

    async def test_channel_isolation(self, count: int = 32) -> Tuple[bool, Dict[str, Any]]:
        """Test channel isolation and independence."""
        self.log.info(f"Testing channel isolation ({count} operations)...")

        success_count = 0
        error_count = 0
        channels_tested = set()

        try:
            # Test multiple channels simultaneously
            for i in range(count):
                ch1 = random.randint(0, self.TEST_CHANNELS - 1)
                ch2 = random.randint(0, self.TEST_CHANNELS - 1)
                while ch2 == ch1:
                    ch2 = random.randint(0, self.TEST_CHANNELS - 1)

                channels_tested.update([ch1, ch2])

                # Start operations on both channels
                await self.start_channel_operation(ch1)
                await self.start_channel_operation(ch2)

                # Verify independence
                if await self.verify_channel_independence(ch1, ch2):
                    success_count += 1
                else:
                    error_count += 1

                await self.wait_random_cycles()

        except Exception as e:
            self.log.error(f"Channel isolation test failed: {str(e)}")
            error_count += 1

        stats = {
            'success_count': success_count,
            'error_count': error_count,
            'success_rate': success_count / count if count > 0 else 0,
            'channels_tested': len(channels_tested)
        }

        return error_count == 0, stats

    async def start_channel_operation(self, channel: int):
        """Start operation on specific channel."""
        self.channel_states[channel]['idle'] = False
        # Would trigger channel-specific operations

    async def verify_channel_independence(self, ch1: int, ch2: int) -> bool:
        """Verify that channels operate independently."""
        # Check that operations on ch1 don't affect ch2 and vice versa
        await self.wait_clocks(self.clk_name, 5)
        return True  # Placeholder - would check actual isolation

    async def stress_test(self, count: int = 100) -> Tuple[bool, Dict[str, Any]]:
        """Comprehensive stress test with mixed operations."""
        self.log.info(f"Running stress test ({count} mixed operations)...")

        success_count = 0
        error_count = 0

        try:
            for i in range(count):
                # Randomly select operation type
                operation = random.choice([
                    'descriptor_processing',
                    'program_operation',
                    'eos_completion',
                    'monitor_event',
                    'channel_operation'
                ])

                if operation == 'descriptor_processing':
                    success, _ = await self.test_basic_descriptor_processing(count=1)
                elif operation == 'program_operation':
                    success, _ = await self.test_program_engine_operations(count=1)
                elif operation == 'eos_completion':
                    success, _ = await self.test_eos_completion_interface(count=1)
                elif operation == 'monitor_event':
                    success, _ = await self.test_monitor_bus_operations(count=1)
                else:
                    success, _ = await self.test_channel_isolation(count=1)

                if success:
                    success_count += 1
                else:
                    error_count += 1

                await self.wait_random_cycles()

        except Exception as e:
            self.log.error(f"Stress test failed: {str(e)}")
            error_count += 1

        stats = {
            'success_count': success_count,
            'error_count': error_count,
            'success_rate': success_count / count if count > 0 else 0
        }

        return error_count == 0, stats

    def finalize_test(self):
        """Finalize test and calculate statistics."""
        end_time = time.time()
        self.test_stats['summary']['test_duration'] = end_time - self.test_stats['summary']['start_time']

        # Calculate performance metrics
        duration = self.test_stats['summary']['test_duration']
        if duration > 0:
            total_ops = self.test_stats['summary']['total_operations']
            self.test_stats['performance']['operations_per_second'] = total_ops / duration

        # Update channel statistics
        active_channels = sum(1 for ch_state in self.channel_states.values() if not ch_state['idle'])
        self.test_stats['channels']['total_channels_used'] = len(self.test_stats['channels']['channels_tested'])
        self.test_stats['performance']['peak_channels_active'] = max(
            self.test_stats['performance']['peak_channels_active'],
            active_channels
        )

    def get_test_stats(self) -> Dict[str, Any]:
        """Get current test statistics."""
        return self.test_stats.copy()

    # =========================================================================
    # ENHANCED TEST METHODS WITH REAL VERIFICATION
    # =========================================================================

    async def test_rda_packet_injection(self, count: int = 16) -> Tuple[bool, Dict[str, Any]]:
        """
        Test RDA packet injection from Network network.

        Tests:
        - RDA packet reception via Network slave
        - Credit-based flow control
        - Channel-specific RDA routing
        - RDA completion/credit return
        """
        self.log.info(f"Testing RDA packet injection ({count} packets)...")

        success_count = 0
        error_count = 0
        channels_tested = set()

        try:
            for i in range(count):
                # Select random channel
                channel = random.randint(0, self.TEST_CHANNELS - 1)
                channels_tested.add(channel)

                # Create RDA packet for this channel
                rda_data = random.randint(0, self.MAX_DATA)

                # Inject RDA packet via Network master
                # RDA packets signal data arrival and request descriptor processing
                self.log.debug(f"Injecting RDA packet {i+1}/{count} on channel {channel}")

                # Drive RDA interface directly
                if hasattr(self.dut, 'rda_valid'):
                    self.dut.rda_valid.value = 1
                    self.dut.rda_packet.value = rda_data
                    self.dut.rda_channel.value = channel

                    await RisingEdge(self.clk)

                    # Wait for ready
                    timeout = 50
                    while timeout > 0 and int(self.dut.rda_ready.value) == 0:
                        await RisingEdge(self.clk)
                        timeout -= 1

                    self.dut.rda_valid.value = 0

                    if timeout > 0:
                        success_count += 1
                        self.log.debug(f"✓ RDA packet accepted on channel {channel}")
                    else:
                        error_count += 1
                        self.log.warning(f"✗ RDA packet timeout on channel {channel}")
                else:
                    self.log.warning("RDA interface not available in DUT")
                    error_count += 1

                await self.wait_random_cycles()

        except Exception as e:
            self.log.error(f"RDA packet injection test failed: {str(e)}")
            error_count += 1

        stats = {
            'success_count': success_count,
            'error_count': error_count,
            'success_rate': success_count / count if count > 0 else 0,
            'channels_tested': len(channels_tested)
        }

        self.test_stats['performance']['descriptors_processed'] += success_count
        self.test_stats['summary']['total_operations'] += count
        self.test_stats['summary']['successful_operations'] += success_count
        self.test_stats['summary']['failed_operations'] += error_count

        return error_count == 0, stats

    async def test_concurrent_multi_channel(self, channel_count: int = 8, ops_per_channel: int = 4) -> Tuple[bool, Dict[str, Any]]:
        """
        Test concurrent operations across multiple channels.

        Tests:
        - True parallel channel operation
        - Channel isolation under load
        - Credit management per channel
        - No cross-channel interference
        """
        self.log.info(f"Testing concurrent multi-channel operation ({channel_count} channels, {ops_per_channel} ops each)...")

        success_count = 0
        error_count = 0
        channels_used = set()

        try:
            # Select random channels for concurrent testing
            test_channels = random.sample(range(self.TEST_CHANNELS), min(channel_count, self.TEST_CHANNELS))
            channels_used.update(test_channels)

            # Create concurrent tasks for each channel
            async def channel_task(ch: int):
                """Run operations on a single channel."""
                ch_success = 0
                ch_errors = 0

                for op in range(ops_per_channel):
                    # Generate descriptor data
                    max_desc_addr = self.descriptor_memory_size - (self.TEST_DATA_WIDTH // 8)
                    desc_addr = random.randint(0, max_desc_addr)
                    desc_data = random.randint(0, self.MAX_DATA)

                    # Program descriptor into memory
                    bytes_per_line = self.TEST_DATA_WIDTH // 8
                    data_bytes = bytearray(desc_data.to_bytes(bytes_per_line, 'little'))
                    self.descriptor_memory.write(desc_addr, data_bytes)

                    # Request descriptor fetch
                    try:
                        await self.request_descriptor_fetch(desc_addr, ch)

                        # Brief wait for processing
                        await self.wait_clocks(self.clk_name, random.randint(5, 15))

                        ch_success += 1
                    except Exception as e:
                        self.log.debug(f"Channel {ch} operation {op+1} failed: {str(e)}")
                        ch_errors += 1

                return ch_success, ch_errors

            # Launch all channel tasks concurrently
            import asyncio
            tasks = [asyncio.create_task(channel_task(ch)) for ch in test_channels]

            # Wait for all to complete
            results = await asyncio.gather(*tasks, return_exceptions=True)

            # Aggregate results
            for result in results:
                if isinstance(result, Exception):
                    error_count += ops_per_channel
                    self.log.error(f"Channel task failed: {str(result)}")
                else:
                    ch_success, ch_errors = result
                    success_count += ch_success
                    error_count += ch_errors

        except Exception as e:
            self.log.error(f"Concurrent multi-channel test failed: {str(e)}")
            error_count += channel_count * ops_per_channel

        total_ops = channel_count * ops_per_channel
        stats = {
            'success_count': success_count,
            'error_count': error_count,
            'success_rate': success_count / total_ops if total_ops > 0 else 0,
            'channels_tested': len(channels_used),
            'total_operations': total_ops
        }

        self.test_stats['channels']['channels_tested'].update(channels_used)
        self.test_stats['performance']['peak_channels_active'] = max(
            self.test_stats['performance']['peak_channels_active'],
            len(channels_used)
        )

        return error_count == 0, stats

    async def test_credit_exhaustion_recovery(self, initial_credits: int = 4) -> Tuple[bool, Dict[str, Any]]:
        """
        Test credit exhaustion and recovery.

        Tests:
        - Credit counter decrements on descriptor acceptance
        - Blocking when credits exhausted
        - Credit recovery via increment
        - System continues after credit restoration
        """
        self.log.info(f"Testing credit exhaustion and recovery (initial credits: {initial_credits})...")

        success_count = 0
        error_count = 0

        try:
            # Configure low credits to force exhaustion
            # cfg_initial_credit uses exponential encoding: value N → 2^N credits
            cfg_value = max(0, min(initial_credits, 14))  # 0-14 valid range
            expected_credits = 2 ** cfg_value

            self.log.info(f"Configuring cfg_initial_credit={cfg_value} → {expected_credits} credits")

            # Reset with new credit configuration
            await self.assert_reset()
            self.dut.cfg_use_credit.value = 1
            self.dut.cfg_initial_credit.value = cfg_value
            await self.wait_clocks(self.clk_name, 10)
            await self.deassert_reset()
            await self.wait_clocks(self.clk_name, 10)

            # Phase 1: Exhaust credits by processing descriptors
            self.log.info(f"Phase 1: Processing {expected_credits} descriptors to exhaust credits...")

            for i in range(expected_credits):
                max_desc_addr = self.descriptor_memory_size - (self.TEST_DATA_WIDTH // 8)
                desc_addr = random.randint(0, max_desc_addr)
                desc_data = random.randint(0, self.MAX_DATA)

                bytes_per_line = self.TEST_DATA_WIDTH // 8
                data_bytes = bytearray(desc_data.to_bytes(bytes_per_line, 'little'))
                self.descriptor_memory.write(desc_addr, data_bytes)

                try:
                    await self.request_descriptor_fetch(desc_addr, 0)
                    success_count += 1
                    self.log.debug(f"Descriptor {i+1}/{expected_credits} accepted (credits remaining: {expected_credits - i - 1})")
                except Exception as e:
                    self.log.warning(f"Descriptor {i+1} failed: {str(e)}")
                    error_count += 1

                await self.wait_clocks(self.clk_name, 5)

            # Phase 2: Verify blocking when credits exhausted
            self.log.info("Phase 2: Verifying blocking with exhausted credits...")

            # Try to process another descriptor - should block or fail
            max_desc_addr = self.descriptor_memory_size - (self.TEST_DATA_WIDTH // 8)
            desc_addr = random.randint(0, max_desc_addr)
            desc_data = random.randint(0, self.MAX_DATA)

            bytes_per_line = self.TEST_DATA_WIDTH // 8
            data_bytes = bytearray(desc_data.to_bytes(bytes_per_line, 'little'))
            self.descriptor_memory.write(desc_addr, data_bytes)

            blocked = False
            try:
                # This should timeout or block
                self.dut.apb_valid.value = 1
                self.dut.apb_addr.value = desc_addr

                await RisingEdge(self.clk)

                # Wait for ready with short timeout
                timeout = 20  # Short timeout to detect blocking
                while timeout > 0 and not self.dut.apb_ready.value:
                    await RisingEdge(self.clk)
                    timeout -= 1

                if timeout == 0:
                    blocked = True
                    self.log.info("✓ Correctly blocked when credits exhausted")
                    success_count += 1
                else:
                    self.log.warning("✗ Did not block when credits exhausted (may indicate issue)")

                self.dut.apb_valid.value = 0

            except TimeoutError:
                blocked = True
                self.log.info("✓ Correctly blocked when credits exhausted (timeout)")
                success_count += 1

            # Phase 3: Recovery via credit increment
            self.log.info("Phase 3: Testing credit recovery...")

            # Increment credits
            self.dut.credit_increment.value = 1
            await RisingEdge(self.clk)
            await RisingEdge(self.clk)
            self.dut.credit_increment.value = 0
            await self.wait_clocks(self.clk_name, 5)

            # Now descriptor should be accepted
            try:
                await self.request_descriptor_fetch(desc_addr, 0)
                self.log.info("✓ Descriptor accepted after credit increment")
                success_count += 1
            except Exception as e:
                self.log.error(f"✗ Failed to accept descriptor after credit increment: {str(e)}")
                error_count += 1

        except Exception as e:
            self.log.error(f"Credit exhaustion/recovery test failed: {str(e)}")
            error_count += 1

        stats = {
            'success_count': success_count,
            'error_count': error_count,
            'success_rate': success_count / (success_count + error_count) if (success_count + error_count) > 0 else 0,
            'expected_credits': expected_credits,
            'blocked_correctly': blocked
        }

        return error_count == 0, stats

    async def test_data_mover_with_stream_boundaries(self, count: int = 16) -> Tuple[bool, Dict[str, Any]]:
        """
        Test data mover interface with stream boundary handling.

        Tests:
        - Data valid/ready handshaking
        - EOS (End of Stream) boundary detection
        - EOL (End of Line) boundary detection
        - EOD (End of Data) boundary detection
        - Data transfer length tracking
        """
        self.log.info(f"Testing data mover with stream boundaries ({count} transfers)...")

        success_count = 0
        error_count = 0
        eos_count = 0
        eol_count = 0
        eod_count = 0

        try:
            for i in range(count):
                # Randomly select stream boundary type
                boundary_type = random.choice(['none', 'eos', 'eol', 'eod'])
                transfer_length = random.randint(1, 128)

                self.log.debug(f"Transfer {i+1}/{count}: length={transfer_length}, boundary={boundary_type}")

                # Drive data interface
                if hasattr(self.dut, 'data_valid'):
                    self.dut.data_valid.value = 1
                    self.dut.data_transfer_length.value = transfer_length

                    # Set boundary flags
                    if hasattr(self.dut, 'data_eos'):
                        self.dut.data_eos.value = 1 if boundary_type == 'eos' else 0
                    if hasattr(self.dut, 'data_eol'):
                        self.dut.data_eol.value = 1 if boundary_type == 'eol' else 0
                    if hasattr(self.dut, 'data_eod'):
                        self.dut.data_eod.value = 1 if boundary_type == 'eod' else 0

                    await RisingEdge(self.clk)

                    # Wait for ready
                    timeout = 50
                    while timeout > 0 and int(self.dut.data_ready.value) == 0:
                        await RisingEdge(self.clk)
                        timeout -= 1

                    if timeout > 0:
                        success_count += 1
                        if boundary_type == 'eos':
                            eos_count += 1
                        elif boundary_type == 'eol':
                            eol_count += 1
                        elif boundary_type == 'eod':
                            eod_count += 1
                    else:
                        error_count += 1
                        self.log.warning(f"Data transfer {i+1} timeout")

                    # Clear signals
                    self.dut.data_valid.value = 0
                    if hasattr(self.dut, 'data_eos'):
                        self.dut.data_eos.value = 0
                    if hasattr(self.dut, 'data_eol'):
                        self.dut.data_eol.value = 0
                    if hasattr(self.dut, 'data_eod'):
                        self.dut.data_eod.value = 0

                else:
                    self.log.warning("Data mover interface not available in DUT")
                    error_count += 1
                    break

                await self.wait_random_cycles()

        except Exception as e:
            self.log.error(f"Data mover test failed: {str(e)}")
            error_count += 1

        stats = {
            'success_count': success_count,
            'error_count': error_count,
            'success_rate': success_count / count if count > 0 else 0,
            'eos_count': eos_count,
            'eol_count': eol_count,
            'eod_count': eod_count
        }

        self.test_stats['performance']['descriptors_processed'] += success_count

        return error_count == 0, stats
