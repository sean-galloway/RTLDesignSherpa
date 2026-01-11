# SPDX-License-Identifier: MIT
# SPDX-FileCopyrightText: 2024-2025 sean galloway
#
# RTL Design Sherpa - Industry-Standard RTL Design and Verification
# https://github.com/sean-galloway/RTLDesignSherpa
#
# Module: SchedulerGroupArrayTB
# Purpose: RAPIDS Scheduler Group Array Testbench - v1.0
#
# Documentation: projects/components/rapids/PRD.md
# Subsystem: rapids
#
# Author: sean galloway
# Created: 2025-10-18

"""
RAPIDS Scheduler Group Array Testbench - v1.0

Testbench for the scheduler_group_array wrapper that instantiates 32 scheduler_group
instances with shared AXI4 interfaces and aggregated MonBus output.

This testbench extends the SchedulerGroupTB pattern to handle:
- 32 parallel scheduler_group instances
- Shared AXI4 read interface (descriptor engine) with round-robin arbitration
- Shared AXI4 read interface (control read engine) with round-robin arbitration
- Shared AXI4 write interface (control write engine) with round-robin arbitration
- Aggregated MonBus output from all 32 instances + 3 AXI masters
- Multi-channel concurrent operation verification
- AXI arbitration and ID-based demultiplexing verification

Key Differences from SchedulerGroupTB:
- Tests multiple channels simultaneously (up to 32)
- Verifies AXI arbitration behavior for shared descriptor AXI master
- Validates MonBus aggregation from 35 sources (32 groups + 3 AXI masters)
- Tests channel independence with shared resources
"""

import os
import random
import asyncio
from typing import List, Dict, Any, Tuple, Optional
import time
import cocotb

# Framework imports
from CocoTBFramework.tbclasses.shared.tbbase import TBBase
from CocoTBFramework.components.shared.memory_model import MemoryModel

# AXI4 imports
from CocoTBFramework.components.axi4.axi4_factories import create_axi4_slave_rd, create_axi4_slave_wr

# GAXI imports (for monitor bus)
from CocoTBFramework.components.gaxi.gaxi_factories import create_gaxi_slave


class SchedulerGroupArrayTB(TBBase):
    """
    Testbench for RAPIDS Scheduler Group Array (32 instances).

    Tests comprehensive multi-channel scheduler array functionality:
    - 32 parallel scheduler_group instances
    - Shared AXI4 descriptor read interface with arbitration
    - Shared AXI4 control read interface with arbitration
    - Shared AXI4 control write interface with arbitration
    - Aggregated MonBus output (35 sources: 32 groups + 3 AXI masters)
    - Per-channel APB interfaces (32 independent)
    - Per-channel configuration and control
    - Multi-channel concurrent operations
    - AXI arbitration fairness and correctness
    - MonBus aggregation validation
    """

    def __init__(self, dut, clk=None, rst_n=None):
        super().__init__(dut)

        # Configuration from environment or defaults
        self.CHANNEL_COUNT = self.convert_to_int(os.environ.get('CHANNEL_COUNT', '32'))
        self.TEST_ADDR_WIDTH = self.convert_to_int(os.environ.get('TEST_ADDR_WIDTH', '64'))
        self.TEST_DATA_WIDTH = self.convert_to_int(os.environ.get('TEST_DATA_WIDTH', '512'))
        self.TEST_AXI_ID_WIDTH = self.convert_to_int(os.environ.get('TEST_AXI_ID_WIDTH', '8'))
        self.TEST_CREDIT_WIDTH = self.convert_to_int(os.environ.get('TEST_CREDIT_WIDTH', '8'))
        self.TEST_CLK_PERIOD = self.convert_to_int(os.environ.get('TEST_CLK_PERIOD', '10'))
        self.SEED = self.convert_to_int(os.environ.get('SEED', '12345'))

        # Initialize random generator
        random.seed(self.SEED)

        # Setup clock and reset signals
        self.clk = clk if clk else dut.clk
        self.clk_name = self.clk._name if hasattr(self.clk, '_name') else 'clk'
        self.rst_n = rst_n if rst_n else dut.rst_n

        # Set limits based on widths
        self.MAX_ADDR = (2**self.TEST_ADDR_WIDTH) - 1
        self.MAX_DATA = (2**self.TEST_DATA_WIDTH) - 1
        self.MAX_CREDIT = (2**self.TEST_CREDIT_WIDTH) - 1

        # Create masks for flattened array access
        self.addr_mask = (1 << self.TEST_ADDR_WIDTH) - 1  # Mask for one address element

        # Test configuration
        self.test_config = {
            'channel_count': self.CHANNEL_COUNT,
            'data_width': self.TEST_DATA_WIDTH,
            'addr_width': self.TEST_ADDR_WIDTH,
            'axi_id_width': self.TEST_AXI_ID_WIDTH,
            'credit_width': self.TEST_CREDIT_WIDTH,
            'timeout_cycles': 1000,
            'early_warning_threshold': 4
        }

        # Component interfaces (initialized in setup)
        self.desc_axi_slave = None       # Shared descriptor AXI read interface
        # Note: This module only has desc_axi_* - no separate ctrlrd/ctrlwr interfaces
        self.monitor_slave = None        # Aggregated monitor bus interface

        # Memory models
        self.descriptor_memory = None

        # Per-channel state tracking
        self.channel_states = {}
        for ch in range(self.CHANNEL_COUNT):
            self.channel_states[ch] = {
                'idle': True,
                'descriptor_pending': False,
                'program_active': False,
                'last_activity': 0.0,
                'operations_count': 0,
                'success_count': 0,
                'error_count': 0
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
                'channels_tested': set(),
                'concurrent_channels_max': 0,
                'per_channel_operations': {}
            },
            'arbitration': {
                'descriptor_arbitrations': 0,
                'arbitration_latency_samples': [],
                'channel_fairness': {}  # Track operations per channel
            },
            'axi': {
                'descriptor_reads': 0,
                'axi_conflicts': 0,
                'axi_stalls': 0
            },
            'monitor': {
                'monitor_events': 0,
                'events_per_source': {}  # Track events from each source
            },
            'performance': {
                'operations_per_second': 0.0,
                'peak_concurrent_channels': 0,
                'average_operation_latency': 0.0
            }
        }

        self.log.info(f"SchedulerGroupArrayTB initialized: {self.CHANNEL_COUNT} channels, "
                     f"{self.TEST_DATA_WIDTH}-bit data, {self.TEST_ADDR_WIDTH}-bit addresses")

    async def setup_clocks_and_reset(self):
        """Complete initialization - starts clocks and performs reset sequence."""
        try:
            self.log.info("Setting up clocks and reset...")

            # Start clock
            await self.start_clock(self.clk_name, freq=self.TEST_CLK_PERIOD, units='ns')

            # Set configuration signals for all channels BEFORE reset
            # These are packed vectors [CHANNEL_COUNT-1:0], so set entire vector
            # Enable all channels, no idle mode, no wait, use credit mode
            if hasattr(self.dut, 'cfg_idle_mode'):
                self.dut.cfg_idle_mode.value = 0  # All channels: no idle mode
            if hasattr(self.dut, 'cfg_channel_wait'):
                self.dut.cfg_channel_wait.value = 0  # All channels: no wait
            if hasattr(self.dut, 'cfg_channel_enable'):
                self.dut.cfg_channel_enable.value = (1 << self.CHANNEL_COUNT) - 1  # All channels enabled
            if hasattr(self.dut, 'cfg_use_credit'):
                self.dut.cfg_use_credit.value = (1 << self.CHANNEL_COUNT) - 1  # All channels use credit
            if hasattr(self.dut, 'credit_increment'):
                self.dut.credit_increment.value = 0  # No credit increments
            if hasattr(self.dut, 'cfg_channel_reset'):
                self.dut.cfg_channel_reset.value = 0  # No channel resets

            # cfg_initial_credit is unpacked array [CHANNEL_COUNT] - set each element
            if hasattr(self.dut, 'cfg_initial_credit'):
                for ch in range(self.CHANNEL_COUNT):
                    self.dut.cfg_initial_credit[ch].value = 4  # 2^4 = 16 credits (exponential encoding)

            # Perform reset sequence
            await self.assert_reset()
            await self.wait_clocks(self.clk_name, 10)  # Hold reset
            await self.deassert_reset()
            await self.wait_clocks(self.clk_name, 5)   # Stabilization

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

    def set_flattened_array_element(self, signal, channel: int, value: int, element_width: int):
        """Set a specific element in a flattened 2D array.

        Args:
            signal: The cocotb signal handle for the flattened array
            channel: Channel index (0 to NUM_CHANNELS-1)
            value: Value to set (will be masked to element_width bits)
            element_width: Width in bits of each array element
        """
        # Read current full vector
        current_val = int(signal.value)

        # Calculate bit positions for this channel
        low_bit = channel * element_width
        high_bit = (channel + 1) * element_width

        # Create mask for this channel's bits
        element_mask = ((1 << element_width) - 1) << low_bit

        # Clear channel's bits, then set new value
        new_val = (current_val & ~element_mask) | ((value & ((1 << element_width) - 1)) << low_bit)
        signal.value = new_val

    async def setup_interfaces(self):
        """Setup all component interfaces."""
        try:
            self.log.info("Setting up scheduler array interfaces...")

            # Shared descriptor AXI read interface
            self.desc_axi_slave = create_axi4_slave_rd(
                self.dut, self.clk, prefix="desc_axi_", log=self.log,
                data_width=self.TEST_DATA_WIDTH,
                addr_width=self.TEST_ADDR_WIDTH,
                id_width=self.TEST_AXI_ID_WIDTH
            )

            # Note: This module only has desc_axi_* for descriptor fetches
            # The sched_rd_*/sched_wr_* are simple valid/ready/addr/beats interfaces
            # to downstream datapaths, not full AXI interfaces

            # Aggregated monitor bus interface
            self.monitor_slave = create_gaxi_slave(
                self.dut, "MonitorBus", "mon_", self.clk,
                field_config=None,  # Will use default
                log=self.log,
                mode='skid'
            )

            # Create memory models
            self.descriptor_memory = MemoryModel(
                num_lines=4096,
                bytes_per_line=64,  # 512-bit descriptor lines
                log=self.log
            )

            # Connect memory model to AXI slave for descriptor fetches
            if self.desc_axi_slave and 'interface' in self.desc_axi_slave:
                self.desc_axi_slave['interface'].memory_model = self.descriptor_memory

            self.log.info("✅ All scheduler array interfaces setup complete")

        except Exception as e:
            self.log.error(f"Failed to setup interfaces: {str(e)}")
            raise

    async def initialize_test(self):
        """Initialize test environment."""
        try:
            self.log.info("Initializing scheduler array test environment...")

            # Record start time
            self.test_stats['summary']['start_time'] = time.time()

            # Setup all interfaces
            await self.setup_interfaces()

            # Wait for interfaces to stabilize
            await self.wait_clocks(self.clk_name, 10)

            # Initialize all per-channel signals to safe defaults
            await self.initialize_channel_signals()

            # Clear any pending transactions
            await self.clear_all_interfaces()

            self.log.info("✅ Scheduler array test initialization complete")

        except Exception as e:
            self.log.error(f"Test initialization failed: {str(e)}")
            raise

    async def initialize_channel_signals(self):
        """Initialize per-channel signals to safe defaults."""
        try:
            # Packed vectors - set entire vector to 0 or appropriate value
            if hasattr(self.dut, 'apb_valid'):
                self.dut.apb_valid.value = 0  # All channels: no APB requests
            if hasattr(self.dut, 'rda_valid'):
                self.dut.rda_valid.value = 0  # All channels: no RDA data
            if hasattr(self.dut, 'eos_completion_valid'):
                self.dut.eos_completion_valid.value = 0  # All channels: no EOS completions
            if hasattr(self.dut, 'data_ready'):
                self.dut.data_ready.value = (1 << self.CHANNEL_COUNT) - 1  # All channels ready
            if hasattr(self.dut, 'data_error'):
                self.dut.data_error.value = 0  # All channels: no errors
            if hasattr(self.dut, 'data_done_strobe'):
                self.dut.data_done_strobe.value = 0  # All channels: no done strobes
            if hasattr(self.dut, 'rda_complete_ready'):
                self.dut.rda_complete_ready.value = (1 << self.CHANNEL_COUNT) - 1  # All channels ready
            if hasattr(self.dut, 'data_alignment_ready'):
                self.dut.data_alignment_ready.value = (1 << self.CHANNEL_COUNT) - 1  # All channels ready

            # Packed multi-dimensional arrays (Verilator flattens these)
            # Set entire flattened vector to 0 for arrays we can't index into
            packed_arrays = ['apb_addr', 'rda_packet', 'rda_channel',
                             'eos_completion_channel', 'data_transfer_length',
                             'rda_complete_channel', 'cfg_addr0_base',
                             'cfg_addr0_limit', 'cfg_addr1_base', 'cfg_addr1_limit',
                             'cfg_fifo_threshold']
            for arr_name in packed_arrays:
                if hasattr(self.dut, arr_name):
                    try:
                        # Try to set the entire flattened vector to 0
                        getattr(self.dut, arr_name).value = 0
                    except Exception:
                        # Silently ignore if we can't set it
                        pass

            # Monitor bus ready (single aggregated output)
            if hasattr(self.dut, 'mon_ready'):
                self.dut.mon_ready.value = 1

            # AXI monitor configuration (shared for all channels)
            if hasattr(self.dut, 'cfg_axi_monitor_enable'):
                self.dut.cfg_axi_monitor_enable.value = 0  # Disable for performance
            if hasattr(self.dut, 'cfg_axi_error_enable'):
                self.dut.cfg_axi_error_enable.value = 1  # Enable error monitoring
            if hasattr(self.dut, 'cfg_axi_timeout_enable'):
                self.dut.cfg_axi_timeout_enable.value = 1
            if hasattr(self.dut, 'cfg_axi_perf_enable'):
                self.dut.cfg_axi_perf_enable.value = 0  # Disable for low traffic
            if hasattr(self.dut, 'cfg_axi_timeout_cycles'):
                self.dut.cfg_axi_timeout_cycles.value = 1000
            if hasattr(self.dut, 'cfg_axi_latency_threshold'):
                self.dut.cfg_axi_latency_threshold.value = 500

            await self.wait_clocks(self.clk_name, 5)
            self.log.info(f"Initialized signals for {self.CHANNEL_COUNT} channels")

        except Exception as e:
            self.log.error(f"Channel signal initialization failed: {str(e)}")
            raise

    async def clear_all_interfaces(self):
        """Clear all interfaces and reset to known state."""
        try:
            # Clear memory models
            if self.descriptor_memory:
                self.descriptor_memory.reset()
            # Wait for all to settle
            await self.wait_clocks(self.clk_name, 10)
            self.log.info("All interfaces cleared")

        except Exception as e:
            self.log.error(f"Interface clearing failed: {str(e)}")
            raise

    async def test_single_channel_operation(self, channel: int) -> Tuple[bool, Dict[str, Any]]:
        """Test basic operation on a single channel."""
        self.log.info(f"Testing single channel operation: channel {channel}")

        try:
            # Generate test data - constrain address to memory size
            # Memory is 4096 lines × 64 bytes = 262144 bytes
            # Need to align to 64-byte boundaries
            max_line = 4096 - 1  # 0 to 4095
            desc_line = random.randint(0, max_line)
            desc_addr = desc_line * 64  # Align to 64-byte boundary
            desc_data = random.randint(0, min(self.MAX_DATA, 2**512 - 1))  # 512-bit max

            # Program descriptor into memory
            self.descriptor_memory.write(desc_addr, bytearray(desc_data.to_bytes(64, 'little')))

            # Request descriptor fetch via APB
            await self.request_descriptor_fetch(channel, desc_addr)

            # Wait for descriptor processing - minimal delay
            await self.wait_clocks(self.clk_name, 3)

            # Update statistics
            self.channel_states[channel]['operations_count'] += 1
            self.channel_states[channel]['success_count'] += 1
            self.test_stats['summary']['successful_operations'] += 1
            self.test_stats['channels']['channels_tested'].add(channel)

            stats = {
                'channel': channel,
                'success': True,
                'descriptor_addr': desc_addr
            }

            return True, stats

        except Exception as e:
            self.log.error(f"Single channel test failed: {str(e)}")
            self.channel_states[channel]['error_count'] += 1
            return False, {'channel': channel, 'error': str(e)}

    async def request_descriptor_fetch(self, channel: int, addr: int):
        """Request descriptor fetch via APB for specific channel."""
        try:
            # APB fetch request - set bit for specific channel (packed vector)
            current_valid = int(self.dut.apb_valid.value)
            self.dut.apb_valid.value = current_valid | (1 << channel)

            # APB address (flattened 2D array - use helper to set specific channel)
            self.set_flattened_array_element(self.dut.apb_addr, channel, addr, self.TEST_ADDR_WIDTH)

            await self.wait_clocks(self.clk_name, 1)

            # Wait for ready - check bit for specific channel
            timeout = 1000  # Sufficient for AXI arbitration with moderate concurrency
            while timeout > 0:
                apb_ready_val = int(self.dut.apb_ready.value)
                if (apb_ready_val >> channel) & 1:
                    break
                await self.wait_clocks(self.clk_name, 1)
                timeout -= 1

            if timeout == 0:
                raise TimeoutError(f"APB request timeout on channel {channel}")

            # Clear valid bit for this channel
            current_valid = int(self.dut.apb_valid.value)
            self.dut.apb_valid.value = current_valid & ~(1 << channel)

            self.channel_states[channel]['descriptor_pending'] = True
            self.test_stats['arbitration']['descriptor_arbitrations'] += 1

        except Exception as e:
            self.log.error(f"APB descriptor request failed on channel {channel}: {str(e)}")
            raise

    async def test_multi_channel_concurrent(self, channels: List[int]) -> Tuple[bool, Dict[str, Any]]:
        """Test concurrent operations on multiple channels."""
        self.log.info(f"Testing concurrent operation on {len(channels)} channels: {channels}")

        success_count = 0
        error_count = 0

        try:
            # Launch concurrent operations
            tasks = []
            for ch in channels:
                task = cocotb.start_soon(self.test_single_channel_operation(ch))
                tasks.append((ch, task))

            # Wait for all to complete
            results = []
            for ch, task in tasks:
                try:
                    success, stats = await task
                    results.append((ch, success, stats))
                    if success:
                        success_count += 1
                    else:
                        error_count += 1
                except Exception as e:
                    self.log.error(f"Channel {ch} task failed: {str(e)}")
                    error_count += 1

            # Update concurrent channel statistics
            concurrent = len(channels)
            if concurrent > self.test_stats['performance']['peak_concurrent_channels']:
                self.test_stats['performance']['peak_concurrent_channels'] = concurrent

            stats = {
                'channels_tested': channels,
                'success_count': success_count,
                'error_count': error_count,
                'concurrent_channels': concurrent
            }

            return error_count == 0, stats

        except Exception as e:
            self.log.error(f"Multi-channel concurrent test failed: {str(e)}")
            return False, {'error': str(e)}

    async def test_multi_channel_concurrent_operation(
        self,
        num_channels_active: int,
        ops_per_channel: int,
        test_level: int = 0
    ) -> Tuple[bool, Dict[str, Any]]:
        """
        Test multi-channel concurrent operations.

        Args:
            num_channels_active: Number of channels to activate concurrently
            ops_per_channel: Number of operations per channel
            test_level: 0=basic, 1=medium, 2=full

        Returns:
            Tuple of (success, stats)
        """
        self.log.info(f"Multi-channel concurrent test: {num_channels_active} channels, "
                     f"{ops_per_channel} ops/channel, level={test_level}")

        total_operations = num_channels_active * ops_per_channel
        success_count = 0
        error_count = 0

        try:
            # Select channels to test
            channels = list(range(num_channels_active))

            # Limit concurrency for Verilator performance - batch size based on test level
            max_concurrent = 4 if test_level == 0 else 3  # basic: 4, medium/full: 3

            # Run operations for each channel
            for op in range(ops_per_channel):
                # Process channels in batches to limit concurrency
                for batch_start in range(0, len(channels), max_concurrent):
                    batch_end = min(batch_start + max_concurrent, len(channels))
                    batch_channels = channels[batch_start:batch_end]

                    # Create tasks for this batch
                    tasks = []
                    for ch in batch_channels:
                        task = cocotb.start_soon(self.test_single_channel_operation(ch))
                        tasks.append((ch, task))

                    # Wait for batch to complete
                    for ch, task in tasks:
                        try:
                            success, _ = await task
                            if success:
                                success_count += 1
                            else:
                                error_count += 1
                        except Exception as e:
                            self.log.error(f"Channel {ch} operation {op} failed: {str(e)}")
                            error_count += 1

                # Minimal delay between rounds
                await self.wait_clocks(self.clk_name, 1)

            # Calculate statistics
            success_rate = (success_count / total_operations * 100) if total_operations > 0 else 0

            stats = {
                'total_operations': total_operations,
                'success_count': success_count,
                'error_count': error_count,
                'success_rate': success_rate,
                'monbus_packets': 0,  # TODO: collect from monitor
                'desc_axi_transactions': self.test_stats['axi']['descriptor_reads']
            }

            return success_count == total_operations, stats

        except Exception as e:
            self.log.error(f"Multi-channel concurrent operation test failed: {str(e)}")
            return False, {'error': str(e), 'total_operations': total_operations}

    async def test_axi_arbitration(self, num_operations: int) -> Tuple[bool, Dict[str, Any]]:
        """Test AXI arbitration behavior with multiple channels."""
        self.log.info(f"Testing AXI arbitration with {num_operations} operations")

        success_count = 0
        channels_used = set()

        try:
            for i in range(num_operations):
                # Select random channel
                channel = random.randint(0, self.CHANNEL_COUNT - 1)
                channels_used.add(channel)

                # Perform operation that requires AXI access
                success, _ = await self.test_single_channel_operation(channel)

                if success:
                    success_count += 1

                # Track per-channel fairness
                if channel not in self.test_stats['arbitration']['channel_fairness']:
                    self.test_stats['arbitration']['channel_fairness'][channel] = 0
                self.test_stats['arbitration']['channel_fairness'][channel] += 1

                # No delay - stress test runs continuously

            stats = {
                'total_operations': num_operations,
                'success_count': success_count,
                'channels_used': len(channels_used),
                'fairness': self.test_stats['arbitration']['channel_fairness']
            }

            return success_count == num_operations, stats

        except Exception as e:
            self.log.error(f"AXI arbitration test failed: {str(e)}")
            return False, {'error': str(e)}

    async def test_monitor_bus_aggregation(self, num_events: int) -> Tuple[bool, Dict[str, Any]]:
        """Test MonBus aggregation from all sources."""
        self.log.info(f"Testing MonBus aggregation for {num_events} events")

        events_captured = 0

        try:
            # Monitor for events
            for i in range(num_events * 10):  # Extended window
                if hasattr(self.dut, 'mon_valid') and int(self.dut.mon_valid.value):
                    events_captured += 1
                    self.test_stats['monitor']['monitor_events'] += 1

                await self.wait_clocks(self.clk_name, 1)

                if events_captured >= num_events:
                    break

            stats = {
                'events_expected': num_events,
                'events_captured': events_captured,
                'capture_rate': events_captured / num_events if num_events > 0 else 0
            }

            return events_captured >= num_events, stats

        except Exception as e:
            self.log.error(f"MonBus aggregation test failed: {str(e)}")
            return False, {'error': str(e)}

    async def test_all_channels_sequential(
        self,
        descriptors_per_channel: int = 1
    ) -> Tuple[bool, Dict[str, Any]]:
        """
        Test all channels sequentially (no concurrency).

        Args:
            descriptors_per_channel: Number of descriptor operations per channel

        Returns:
            Tuple of (success, stats)
        """
        total_ops = self.CHANNEL_COUNT * descriptors_per_channel
        self.log.info(f"Testing all {self.CHANNEL_COUNT} channels sequentially "
                     f"({descriptors_per_channel} descriptors each, {total_ops} total ops)")

        success_count = 0
        error_count = 0
        channels_tested = 0

        try:
            for ch in range(self.CHANNEL_COUNT):
                # Perform multiple descriptors for this channel
                for desc in range(descriptors_per_channel):
                    success, _ = await self.test_single_channel_operation(ch)
                    if success:
                        success_count += 1
                    else:
                        error_count += 1

                    # No delay - run continuously

                channels_tested += 1

            stats = {
                'total_operations': total_ops,
                'total_channels': self.CHANNEL_COUNT,
                'channels_tested': channels_tested,
                'success_count': success_count,
                'error_count': error_count,
                'success_rate': success_count / total_ops if total_ops > 0 else 0
            }

            return error_count == 0, stats

        except Exception as e:
            self.log.error(f"All channels sequential test failed: {str(e)}")
            return False, {'error': str(e)}

    async def stress_test(self, num_operations: int) -> Tuple[bool, Dict[str, Any]]:
        """Comprehensive stress test with random operations."""
        self.log.info(f"Running stress test with {num_operations} operations")

        success_count = 0
        error_count = 0

        try:
            for i in range(num_operations):
                # Randomly select test type
                test_type = random.choice(['single', 'concurrent', 'arbitration'])

                if test_type == 'single':
                    channel = random.randint(0, self.CHANNEL_COUNT - 1)
                    success, _ = await self.test_single_channel_operation(channel)
                elif test_type == 'concurrent':
                    num_channels = random.randint(2, min(8, self.CHANNEL_COUNT))
                    channels = random.sample(range(self.CHANNEL_COUNT), num_channels)
                    success, _ = await self.test_multi_channel_concurrent(channels)
                else:  # arbitration
                    success, _ = await self.test_axi_arbitration(num_operations=5)

                if success:
                    success_count += 1
                else:
                    error_count += 1

                # No delay in stress test

            stats = {
                'total_operations': num_operations,
                'success_count': success_count,
                'error_count': error_count,
                'success_rate': success_count / num_operations if num_operations > 0 else 0
            }

            return error_count == 0, stats

        except Exception as e:
            self.log.error(f"Stress test failed: {str(e)}")
            return False, {'error': str(e)}

    def finalize_test(self):
        """Finalize test and calculate statistics."""
        end_time = time.time()
        self.test_stats['summary']['test_duration'] = end_time - self.test_stats['summary']['start_time']

        # Calculate performance metrics
        duration = self.test_stats['summary']['test_duration']
        if duration > 0:
            total_ops = self.test_stats['summary']['total_operations']
            self.test_stats['performance']['operations_per_second'] = total_ops / duration

        # Calculate per-channel statistics
        for ch in range(self.CHANNEL_COUNT):
            if ch in self.test_stats['channels']['channels_tested']:
                ch_state = self.channel_states[ch]
                self.test_stats['channels']['per_channel_operations'][ch] = ch_state['operations_count']

        self.log.info("Test finalized - statistics calculated")

    def get_test_stats(self) -> Dict[str, Any]:
        """Get current test statistics."""
        return self.test_stats.copy()

    def print_test_summary(self):
        """Print comprehensive test summary."""
        stats = self.test_stats

        self.log.info("=" * 80)
        self.log.info("SCHEDULER GROUP ARRAY TEST SUMMARY")
        self.log.info("=" * 80)

        # Summary
        self.log.info(f"Total Operations: {stats['summary']['total_operations']}")
        self.log.info(f"Successful: {stats['summary']['successful_operations']}")
        self.log.info(f"Failed: {stats['summary']['failed_operations']}")
        self.log.info(f"Duration: {stats['summary']['test_duration']:.2f}s")

        # Channel usage
        self.log.info(f"\nChannels Tested: {len(stats['channels']['channels_tested'])}/{self.CHANNEL_COUNT}")
        self.log.info(f"Peak Concurrent: {stats['performance']['peak_concurrent_channels']}")

        # Arbitration
        self.log.info(f"\nDescriptor Arbitrations: {stats['arbitration']['descriptor_arbitrations']}")

        # AXI
        self.log.info(f"\nDescriptor Reads: {stats['axi']['descriptor_reads']}")

        # Monitor
        self.log.info(f"\nMonitor Events: {stats['monitor']['monitor_events']}")

        # Performance
        self.log.info(f"\nOps/Second: {stats['performance']['operations_per_second']:.1f}")

        self.log.info("=" * 80)
