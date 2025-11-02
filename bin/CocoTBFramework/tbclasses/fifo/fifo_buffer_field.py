# SPDX-License-Identifier: MIT
# SPDX-FileCopyrightText: 2024-2025 sean galloway
#
# RTL Design Sherpa - Industry-Standard RTL Design and Verification
# https://github.com/sean-galloway/RTLDesignSherpa
#
# Module: FifoFieldBufferTB
# Purpose: Testbench for FIFO buffer components with multiple fields - Refactored to use Fl
#
# Documentation: bin/CocoTBFramework/README.md
# Subsystem: framework
#
# Author: sean galloway
# Created: 2025-10-18

"""Testbench for FIFO buffer components with multiple fields - Refactored to use FlexConfigGen only

Key changes:
- Eliminated manual FlexRandomizer instantiation throughout
- FlexConfigGen now returns FlexRandomizer instances directly via return_flexrandomizer=True
- Simplified randomizer profile management with direct instance access
- Cleaner architecture using single randomization source
"""
import os
import random
import cocotb

from CocoTBFramework.tbclasses.shared.tbbase import TBBase
from CocoTBFramework.components.shared.field_config import FieldConfig

from CocoTBFramework.components.fifo.fifo_packet import FIFOPacket
from CocoTBFramework.components.fifo.fifo_master import FIFOMaster
from CocoTBFramework.components.fifo.fifo_slave import FIFOSlave
from CocoTBFramework.components.fifo.fifo_monitor import FIFOMonitor
from CocoTBFramework.components.fifo.fifo_sequence import FIFOSequence
from CocoTBFramework.components.fifo.fifo_command_handler import FIFOCommandHandler
from CocoTBFramework.components.shared.memory_model import MemoryModel
from CocoTBFramework.components.shared.flex_config_gen import FlexConfigGen
from CocoTBFramework.tbclasses.fifo.fifo_buffer_configs import FIELD_CONFIGS


class FifoFieldBufferTB(TBBase):
    """Testbench for multi-field FIFO components using FlexConfigGen only for randomization"""

    def __init__(self, dut,
                    wr_clk=None, wr_rstn=None,
                    rd_clk=None, rd_rstn=None,
                    super_debug=False):
        super().__init__(dut)

        # Get test parameters from environment
        self.TEST_DEPTH = self.convert_to_int(os.environ.get('TEST_DEPTH', '0'))
        self.TEST_ADDR_WIDTH = self.convert_to_int(os.environ.get('TEST_ADDR_WIDTH', '0'))
        self.TEST_CTRL_WIDTH = self.convert_to_int(os.environ.get('TEST_CTRL_WIDTH', '0'))
        self.TEST_DATA_WIDTH = self.convert_to_int(os.environ.get('TEST_DATA_WIDTH', '0'))
        self.TEST_MODE = os.environ.get('TEST_MODE', 'fifo_mux')
        self.TEST_KIND = os.environ.get('TEST_KIND', 'sync')
        self.TEST_CLK_WR = self.convert_to_int(os.environ.get('TEST_CLK_WR', '10'))
        self.TEST_CLK_RD = self.convert_to_int(os.environ.get('TEST_CLK_RD', '10'))
        self.super_debug = super_debug
        self.SEED = self.convert_to_int(os.environ.get('SEED', '12345'))

        # Initialize random generator
        random.seed(self.SEED)

        # Setup widths and limits
        self.AW = self.TEST_ADDR_WIDTH
        self.MAX_ADDR = (2**self.TEST_ADDR_WIDTH)-1
        self.CW = self.TEST_CTRL_WIDTH
        self.MAX_CTRL = (2**self.TEST_CTRL_WIDTH)-1
        self.DW = self.TEST_DATA_WIDTH
        self.MAX_DATA = (2**self.TEST_DATA_WIDTH)-1
        self.TIMEOUT_CYCLES = 1000
        self.total_errors = 0

        # Setup clock and reset signals
        self.wr_clk = wr_clk
        self.wr_clk_name = wr_clk.name
        self.wr_rstn = wr_rstn
        self.rd_clk = self.wr_clk if self.TEST_KIND == 'sync' else rd_clk
        self.rd_clk_name = self.wr_clk_name if self.TEST_KIND == 'sync' else rd_clk.name
        self.rd_rstn = self.wr_rstn if self.TEST_KIND == 'sync' else rd_rstn

        # Log the test configuration
        msg = '\n'
        msg += '='*80 + "\n"
        msg += ' Settings:\n'
        msg += '-'*80 + "\n"
        msg += f' Depth:    {self.TEST_DEPTH}\n'
        msg += f' AddrW:    {self.TEST_ADDR_WIDTH}\n'
        msg += f' CtrlW:    {self.TEST_CTRL_WIDTH}\n'
        msg += f' DataW:    {self.TEST_DATA_WIDTH}\n'
        msg += f' Max Addr: {self.MAX_ADDR}\n'
        msg += f' Max Ctrl: {self.MAX_CTRL}\n'
        msg += f' Max Data: {self.MAX_DATA}\n'
        msg += f' MODE:     {self.TEST_MODE}\n'
        msg += f' clk_wr:   {self.TEST_CLK_WR}\n'
        msg += f' clk_rd:   {self.TEST_CLK_RD}\n'
        msg += f' Debug:    {self.super_debug}\n'
        msg += '='*80 + "\n"
        self.log.info(msg)

        # Create FlexConfigGen manager and get randomizer instances directly
        self.randomizer_manager = self._create_robust_randomizer_manager()

        # Create field configuration
        self.field_config = FieldConfig.from_dict(field_dict=FIELD_CONFIGS['field'], lsb_first=True)
        self.field_config.update_field_width('addr', self.AW)
        self.field_config.update_field_width('ctrl', self.CW)
        self.field_config.update_field_width('data0', self.DW)
        self.field_config.update_field_width('data1', self.DW)

        self.log.debug(f"\n{self.field_config}")

        # Create memory model
        self.memory_model = MemoryModel(
            num_lines=self.TEST_DEPTH,
            bytes_per_line=(self.AW + self.CW + 2*self.DW) // 8 or 1,
            log=self.log
        )

        # Define memory regions for better diagnostics
        self.memory_model.define_region('addr_fields', 0, self.TEST_DEPTH // 4 - 1, 'Address fields')
        self.memory_model.define_region('ctrl_fields', self.TEST_DEPTH // 4, self.TEST_DEPTH // 2 - 1, 'Control fields')
        self.memory_model.define_region('data_fields', self.TEST_DEPTH // 2, self.TEST_DEPTH - 1, 'Data fields')

        # Create BFM components using FlexConfigGen randomizer instances
        default_write_randomizer = self.get_randomizer('balanced', 'write')
        self.write_master = FIFOMaster(
            dut=dut,
            title='write_master',
            prefix='',
            clock=self.wr_clk,
            field_config=self.field_config,
            timeout_cycles=self.TIMEOUT_CYCLES,
            mode=self.TEST_MODE,
            log=self.log,
            super_debug=self.super_debug
        )
        # Set default randomizer from FlexConfigGen
        self.write_master.set_randomizer(default_write_randomizer)

        default_read_randomizer = self.get_randomizer('balanced', 'read')
        self.read_slave = FIFOSlave(
            dut=dut,
            title='read_slave',
            prefix='',
            clock=self.rd_clk,
            field_config=self.field_config,
            timeout_cycles=self.TIMEOUT_CYCLES,
            mode=self.TEST_MODE,
            log=self.log,
            super_debug=self.super_debug
        )
        # Set default randomizer from FlexConfigGen
        self.read_slave.set_randomizer(default_read_randomizer)

        # Set up monitors
        self.wr_monitor = FIFOMonitor(
            dut=dut,
            title='Write monitor',
            prefix='',
            clock=self.wr_clk,
            field_config=self.field_config,
            is_slave=False,  # Monitor write port (master side)
            mode=self.TEST_MODE,
            log=self.log,
            fifo_depth=self.TEST_DEPTH,
            super_debug=self.super_debug
        )

        self.rd_monitor = FIFOMonitor(
            dut=dut,
            title='Read monitor',
            prefix='',
            clock=self.rd_clk,
            field_config=self.field_config,
            is_slave=True,  # Monitor read port (slave side)
            mode=self.TEST_MODE,
            log=self.log,
            fifo_depth=self.TEST_DEPTH,
            super_debug=self.super_debug
        )

        # Create command handler to coordinate transactions
        self.command_handler = FIFOCommandHandler(
            self.write_master,
            self.read_slave,
            log=self.log
        )

        self.log.info(f"FifoFieldBufferTB initialized with mode={self.TEST_MODE}, "
                        f"addr_width={self.AW}, ctrl_width={self.CW}, data_width={self.DW}, depth={self.TEST_DEPTH}")

    def _create_robust_randomizer_manager(self):
        """Create FlexConfigGen manager that returns FlexRandomizer instances directly"""

        # Define custom FIFO-specific profiles for multi-field testing
        fifo_field_custom_profiles = {
            # Field-specific patterns
            'field_stress': ([(0, 0), (1, 3), (8, 15), (25, 40)], [4, 3, 2, 1]),                      # Mixed timing for field stress
            'field_pipeline': ([(2, 4), (5, 7)], [3, 1]),                                             # Pipeline-friendly for fields
            'field_burst': ([(0, 0), (20, 35)], [10, 1]),                                             # Burst pattern for fields
            'field_realistic': ([(0, 1), (3, 6), (10, 15), (25, 30)], [5, 3, 2, 1]),                  # Real-world field patterns
            'field_fine_grain': ([(0, 2), (3, 5), (6, 8), (9, 12)], [4, 3, 2, 1]),                    # Fine control for fields
            'field_depth_aware': ([(0, 0), (1, 2), (self.TEST_DEPTH, self.TEST_DEPTH*2)], [7, 2, 1])  # Depth-aware for fields
        }

        # Create FlexConfigGen - NOTE: return_flexrandomizer=True
        config_gen = FlexConfigGen(
            profiles=[
                # Standard canned profiles
                'backtoback', 'fast', 'constrained', 'bursty', 'slow', 'stress',
                'moderate', 'balanced', 'heavy_pause', 'gradual', 'jittery',
                'pipeline', 'throttled', 'chaotic', 'smooth', 'efficient',
                # Custom field-specific profiles
                'field_stress', 'field_pipeline', 'field_burst', 'field_realistic',
                'field_fine_grain', 'field_depth_aware'
            ],
            fields=['write_delay', 'read_delay'],
            custom_profiles=fifo_field_custom_profiles
        )

        # Customize profiles for field-specific behavior
        self._customize_profiles(config_gen)

        # Build and get FlexRandomizer instances directly
        self.randomizer_instances = config_gen.build(return_flexrandomizer=True)

        # Create write/read domain mapping for easier access
        self.domain_randomizers = {}
        for profile_name, randomizer in self.randomizer_instances.items():
            self.domain_randomizers[profile_name] = {
                'write': randomizer,  # Write domain gets the randomizer instance
                'read': randomizer    # Read domain gets the same randomizer instance
            }

        self.log.info(f"Created {len(self.randomizer_instances)} robust field randomizer instances via FlexConfigGen:")
        for profile_name in self.randomizer_instances.keys():
            self.log.info(f"  - {profile_name}")

        return config_gen

    def _customize_profiles(self, config_gen):
        """Customize FlexConfigGen profiles for field-specific behavior"""

        # Aggressive backtoback for field testing
        config_gen.backtoback.write_delay.fixed_value(0)
        config_gen.backtoback.read_delay.fixed_value(0)

        # Fast patterns optimized for field processing
        config_gen.fast.write_delay.mostly_zero(zero_weight=25, fallback_range=(1, 2), fallback_weight=1)
        config_gen.fast.read_delay.mostly_zero(zero_weight=20, fallback_range=(1, 4), fallback_weight=2)

        # Stress test with field-aware variations
        config_gen.stress.write_delay.weighted_ranges([
            ((0, 0), 5), ((1, 4), 4), ((8, 12), 3), ((20, 30), 2), ((35, 50), 1)
        ])
        config_gen.stress.read_delay.weighted_ranges([
            ((0, 1), 4), ((2, 6), 4), ((10, 18), 3), ((25, 35), 2), ((40, 55), 1)
        ])

        # Field-optimized pipeline timing
        config_gen.pipeline.write_delay.uniform_range(2, 4)
        config_gen.pipeline.read_delay.uniform_range(3, 6)

        # Chaotic field testing
        config_gen.chaotic.write_delay.probability_split([
            ((0, 1), 0.35), ((3, 8), 0.3), ((12, 20), 0.2), ((30, 50), 0.15)
        ])
        config_gen.chaotic.read_delay.probability_split([
            ((0, 2), 0.4), ((4, 10), 0.3), ((15, 25), 0.2), ((35, 55), 0.1)
        ])

        # Field burst patterns
        config_gen.bursty.write_delay.burst_pattern(fast_cycles=0, pause_range=(12, 20), burst_ratio=15)
        config_gen.bursty.read_delay.burst_pattern(fast_cycles=0, pause_range=(15, 25), burst_ratio=10)

    def get_randomizer(self, profile_name, domain='write'):
        """Get FlexRandomizer instance for specified profile and domain"""
        if profile_name in self.domain_randomizers:
            return self.domain_randomizers[profile_name][domain]
        else:
            # Fallback to balanced profile
            self.log.warning(f"Profile '{profile_name}' not found, using 'balanced'")
            return self.domain_randomizers['balanced'][domain]

    def get_randomizer_config_names(self):
        """Get list of available randomizer configuration names"""
        return list(self.randomizer_instances.keys())

    def get_available_profiles(self):
        """Get list of available profiles (alias for compatibility)"""
        return self.get_randomizer_config_names()

    def set_randomizer_profile(self, profile_name):
        """Set randomizer profile for write and read components using FlexConfigGen instances"""
        write_randomizer = self.get_randomizer(profile_name, 'write')
        read_randomizer = self.get_randomizer(profile_name, 'read')

        # Apply randomizers from FlexConfigGen instances
        self.write_master.set_randomizer(write_randomizer)
        self.read_slave.set_randomizer(read_randomizer)

        self.log.info(f"Set randomizers to profile '{profile_name}' using FlexConfigGen instances")

    async def clear_interface(self):
        """Clear the interface signals"""
        await self.write_master.reset_bus()
        await self.read_slave.reset_bus()

    async def assert_reset(self):
        """Assert reset"""
        self.wr_rstn.value = 0
        if self.rd_rstn != self.wr_rstn:
            self.rd_rstn.value = 0
        await self.clear_interface()

    async def deassert_reset(self):
        """Deassert reset"""
        self.wr_rstn.value = 1
        if self.rd_rstn != self.wr_rstn:
            self.rd_rstn.value = 1
        self.log.info(f"Reset complete{self.get_time_ns_str()}")

    def compare_packets(self, msg, expected_count):
        """
        Compare packets captured by monitors.
        Logs any mismatches and updates self.total_errors.
        """
        # Check packet counts
        wr_mon_count = len(self.wr_monitor._recvQ)
        rd_mon_count = len(self.rd_monitor._recvQ)

        if wr_mon_count != rd_mon_count:
            self.log.error(
                f"Packet count mismatch: "
                f"{wr_mon_count} sent vs "
                f"{rd_mon_count} received"
            )
            self.total_errors += 1

        if expected_count != wr_mon_count:
            self.log.error(
                f"Packet count mismatch on Write Monitor: "
                f"{wr_mon_count} sent vs "
                f"{expected_count} expected"
            )
            self.total_errors += 1

        if expected_count != rd_mon_count:
            self.log.error(
                f"Packet count mismatch on Read Monitor: "
                f"{rd_mon_count} received vs "
                f"{expected_count} expected"
            )
            self.total_errors += 1

        # Compare packets
        while self.wr_monitor._recvQ and self.rd_monitor._recvQ:
            wr_pkt = self.wr_monitor._recvQ.popleft()
            rd_pkt = self.rd_monitor._recvQ.popleft()

            # Compare the two packets
            if wr_pkt != rd_pkt:
                self.log.error(
                    f"{msg}: Packet mismatch – WR: {wr_pkt.formatted(compact=True)} "
                    f"vs RD: {rd_pkt.formatted(compact=True)}"
                )

                # Provide detailed field comparison
                for field_name in self.field_config.field_names():
                    wr_val = getattr(wr_pkt, field_name, None)
                    rd_val = getattr(rd_pkt, field_name, None)
                    if wr_val != rd_val:
                        self.log.error(f"  Field '{field_name}' mismatch: write={wr_val}, read={rd_val}")

                self.total_errors += 1

        # Log any leftover packets
        while self.wr_monitor._recvQ:
            pkt = self.wr_monitor._recvQ.popleft()
            self.log.error(f"{msg}: Unmatched extra packet in WR monitor: {pkt.formatted(compact=True)}")
            self.total_errors += 1

        while self.rd_monitor._recvQ:
            pkt = self.rd_monitor._recvQ.popleft()
            self.log.error(f"{msg}: Unmatched extra packet in RD monitor: {pkt.formatted(compact=True)}")
            self.total_errors += 1

    def get_component_statistics(self):
        """Get statistics from all components for analysis"""
        stats = {
            'write_master': self.write_master.get_stats(),
            'read_slave': self.read_slave.get_stats(),
            'write_monitor': self.wr_monitor.get_stats(),
            'read_monitor': self.rd_monitor.get_stats(),
            'memory_model': self.memory_model.get_stats(),
            'command_handler': self.command_handler.get_stats(),
            'total_errors': self.total_errors,
            'available_profiles': len(self.randomizer_instances)
        }

        # Get memory region statistics
        for region in ['addr_fields', 'ctrl_fields', 'data_fields']:
            region_stats = self.memory_model.get_region_access_stats(region)
            if region_stats:
                stats[f'memory_region_{region}'] = region_stats

        return stats

    async def simple_incremental_loops(self, count, delay_key, delay_clks_after):
        """Run simple incremental tests using FlexConfigGen randomizer instances"""
        self.log.info('='*80)
        self.log.info(f'simple_incremental_loops({count=}, {delay_key=}, {delay_clks_after=}){self.get_time_ns_str()}')

        # Set randomizer profile using FlexConfigGen instances
        self.set_randomizer_profile(delay_key)

        # Reset and prepare for test
        await self.assert_reset()
        await self.wait_clocks(self.wr_clk_name, 10)
        await self.deassert_reset()
        await self.wait_clocks(self.wr_clk_name, 10)

        # Start the command handler
        await self.command_handler.start()

        # Send packets
        for i in range(count):
            # Create packet with multiple fields
            addr = i & self.MAX_ADDR  # Mask address to avoid overflow
            ctrl = i & self.MAX_CTRL  # Mask control to avoid overflow
            data0 = i & self.MAX_DATA  # Mask data to avoid overflow
            data1 = (i * 2) & self.MAX_DATA  # Mask data to avoid overflow

            packet = FIFOPacket(self.field_config)
            packet.addr = addr
            packet.ctrl = ctrl
            packet.data0 = data0
            packet.data1 = data1

            # Queue the packet for transmission
            await self.write_master.send(packet)

        # Wait for all packets to be transmitted
        while self.write_master.transfer_busy:
            await self.wait_clocks(self.wr_clk_name, 1)

        # Read data from the buffer
        await self.wait_clocks(self.wr_clk_name, delay_clks_after*5)

        # Wait for all packets to be received
        timeout_counter = 0
        while len(self.rd_monitor._recvQ) < count and timeout_counter < self.TIMEOUT_CYCLES:
            await self.wait_clocks(self.wr_clk_name, 1)
            timeout_counter += 1

        if timeout_counter >= self.TIMEOUT_CYCLES:
            self.log.error(f"Timeout waiting for packets! Only received {len(self.rd_monitor._recvQ)} of {count}{self.get_time_ns_str()}")
            self.total_errors += 1

        # Additional delay for stable results
        await self.wait_clocks(self.wr_clk_name, delay_clks_after)

        # Stop the command handler
        await self.command_handler.stop()

        # Compare the packets
        self.compare_packets("Simple Incremental Loops", count)

        # Print statistics
        stats = self.get_component_statistics()
        self.log.info(f"Test Statistics: {stats}")

        assert self.total_errors == 0, f'Simple Incremental Loops found {self.total_errors} Errors{self.get_time_ns_str()}'

    async def comprehensive_randomizer_sweep(self, packets_per_config=15):
        """Test all available randomizer configurations using FlexConfigGen instances"""
        self.log.info('='*80)
        self.log.info(f'Running comprehensive field randomizer sweep with {packets_per_config} packets per config')

        total_configs = len(self.randomizer_instances)
        failures = 0

        for i, config_name in enumerate(self.randomizer_instances.keys()):
            self.log.info(f'Testing field config {i+1}/{total_configs}: {config_name}')

            try:
                await self.simple_incremental_loops(
                    count=packets_per_config,
                    delay_key=config_name,
                    delay_clks_after=8
                )
                self.log.info(f'✓ Field config {config_name} passed')
            except Exception as e:
                self.log.error(f'✗ Field config {config_name} failed: {e}')
                failures += 1

        self.log.info(f"Field randomizer sweep completed: {total_configs - failures}/{total_configs} profiles passed")
        return failures == 0

    async def dependency_test(self, count=10, delay_key='field_stress'):
        """Test transaction dependencies with complex field sequence using FlexConfigGen"""

        self.log.info('='*80)
        self.log.info(f"Running field dependency test with {count} packets and {delay_key} delays{self.get_time_ns_str()}")

        # Set randomizer profile using FlexConfigGen instances
        self.set_randomizer_profile(delay_key)

        # Reset environment
        await self.assert_reset()
        await self.wait_clocks(self.wr_clk_name, 10)
        await self.deassert_reset()
        await self.wait_clocks(self.wr_clk_name, 10)

        # Start command handler
        await self.command_handler.start()

        # Create sequence with dependency chain
        sequence = FIFOSequence.create_dependency_chain(
            name="field_dependency_chain",
            count=count,
            data_start=0xA000,
            data_step=0x100,
            delay=1
        )

        # Set field configuration to match our testbench
        sequence.field_config = self.field_config

        # Process the sequence to generate packets
        self.log.info(f"Processing field sequence with {count} packets")
        response_map = await self.command_handler.process_sequence(sequence)

        # Validate responses
        if len(response_map) != count:
            self.log.error(f"Expected {count} responses, but got {len(response_map)}")
            self.total_errors += 1

        # Wait for processing to complete
        await self.wait_clocks(self.wr_clk_name, 20)

        # Stop command handler
        await self.command_handler.stop()

        # Check results and print statistics
        stats = self.get_component_statistics()
        self.log.info(f"Field Dependency Test Statistics: {stats}")

        # Check monitored transactions
        self.compare_packets("Field Dependency Test", count)

        return self.total_errors == 0

    async def field_pattern_test(self, pattern_type='comprehensive', count=25):
        """Test field-specific patterns using FlexConfigGen randomizers"""
        self.log.info('='*80)
        self.log.info(f"Running field pattern test: {pattern_type} with {count} packets{self.get_time_ns_str()}")

        # Use field-specific randomizer from FlexConfigGen
        self.set_randomizer_profile('field_realistic')

        # Reset environment
        await self.assert_reset()
        await self.wait_clocks(self.wr_clk_name, 10)
        await self.deassert_reset()
        await self.wait_clocks(self.wr_clk_name, 10)

        # Start command handler
        await self.command_handler.start()

        # Create field-specific test patterns
        patterns = []

        if pattern_type == 'comprehensive':
            # Test all field corner cases

            # Corner values for each field
            patterns.extend([
                {'addr': 0, 'ctrl': 0, 'data0': 0, 'data1': 0},                                    # All zeros
                {'addr': self.MAX_ADDR, 'ctrl': self.MAX_CTRL, 'data0': self.MAX_DATA, 'data1': self.MAX_DATA},  # All max
                {'addr': 0, 'ctrl': self.MAX_CTRL, 'data0': 0, 'data1': self.MAX_DATA},           # Mixed
                {'addr': self.MAX_ADDR, 'ctrl': 0, 'data0': self.MAX_DATA, 'data1': 0},           # Mixed reverse
            ])

            # Walking patterns in addr field
            for bit in range(min(16, self.AW)):
                patterns.append({'addr': 1 << bit, 'ctrl': bit & self.MAX_CTRL, 'data0': bit, 'data1': bit * 2})

            # Walking patterns in ctrl field
            for bit in range(min(8, self.CW)):
                patterns.append({'addr': bit, 'ctrl': 1 << bit, 'data0': bit * 3, 'data1': bit * 4})

        elif pattern_type == 'alternating':
            # Alternating bit patterns
            for i in range(count):
                if i % 2 == 0:
                    patterns.append({
                        'addr': 0x55555555 & self.MAX_ADDR,
                        'ctrl': 0x55 & self.MAX_CTRL,
                        'data0': 0x55555555 & self.MAX_DATA,
                        'data1': 0xAAAAAAAA & self.MAX_DATA
                    })
                else:
                    patterns.append({
                        'addr': 0xAAAAAAAA & self.MAX_ADDR,
                        'ctrl': 0xAA & self.MAX_CTRL,
                        'data0': 0xAAAAAAAA & self.MAX_DATA,
                        'data1': 0x55555555 & self.MAX_DATA
                    })

        elif pattern_type == 'incremental':
            # Simple incremental patterns
            for i in range(count):
                patterns.append({
                    'addr': (i * 0x10) & self.MAX_ADDR,
                    'ctrl': (i * 0x3) & self.MAX_CTRL,
                    'data0': (i * 0x100) & self.MAX_DATA,
                    'data1': (i * 0x200) & self.MAX_DATA
                })

        # Trim to requested count
        patterns = patterns[:count]

        # Send patterns
        for i, pattern in enumerate(patterns):
            packet = FIFOPacket(self.field_config)
            packet.addr = pattern['addr']
            packet.ctrl = pattern['ctrl']
            packet.data0 = pattern['data0']
            packet.data1 = pattern['data1']

            await self.write_master.send(packet)

            # Add occasional delay to prevent overwhelming
            if i % 8 == 7:
                await self.wait_clocks(self.wr_clk_name, 3)

        # Wait for completion
        while self.write_master.transfer_busy:
            await self.wait_clocks(self.wr_clk_name, 1)

        # Allow time for all packets to be received
        await self.wait_clocks(self.wr_clk_name, 30)

        # Wait for all packets to be received
        timeout_counter = 0
        while len(self.rd_monitor._recvQ) < len(patterns) and timeout_counter < self.TIMEOUT_CYCLES:
            await self.wait_clocks(self.wr_clk_name, 1)
            timeout_counter += 1

        if timeout_counter >= self.TIMEOUT_CYCLES:
            self.log.error(f"Timeout waiting for field patterns! Only received {len(self.rd_monitor._recvQ)} of {len(patterns)}{self.get_time_ns_str()}")
            self.total_errors += 1

        # Stop command handler
        await self.command_handler.stop()

        # Compare results
        self.compare_packets(f"Field Pattern Test ({pattern_type})", len(patterns))

        # Get statistics
        stats = self.get_component_statistics()
        self.log.info(f"Field Pattern Test Statistics: {stats}")

        return self.total_errors == 0