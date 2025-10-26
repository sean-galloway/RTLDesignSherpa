# SPDX-License-Identifier: MIT
# SPDX-FileCopyrightText: 2024-2025 sean galloway
#
# RTL Design Sherpa - Industry-Standard RTL Design and Verification
# https://github.com/sean-galloway/RTLDesignSherpa
#
# Module: FifoMultiBufferTB
# Purpose: Testbench for FIFO buffer components with multiple signals - Refactored to use F
#
# Documentation: bin/CocoTBFramework/README.md
# Subsystem: framework
#
# Author: sean galloway
# Created: 2025-10-18

"""Testbench for FIFO buffer components with multiple signals - Refactored to use FlexConfigGen only

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


class FifoMultiBufferTB(TBBase):
    """Testbench for multi-signal FIFO components using FlexConfigGen only for randomization"""

    def __init__(self, dut,
                    wr_clk=None, wr_rstn=None,
                    rd_clk=None, rd_rstn=None,
                    super_debug=True):
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
        self.memory_model.define_region('addr_signals', 0, self.TEST_DEPTH // 4 - 1, 'Address signals')
        self.memory_model.define_region('ctrl_signals', self.TEST_DEPTH // 4, self.TEST_DEPTH // 2 - 1, 'Control signals')
        self.memory_model.define_region('data_signals', self.TEST_DEPTH // 2, self.TEST_DEPTH - 1, 'Data signals')

        # Create BFM components using FlexConfigGen randomizer instances
        default_write_randomizer = self.get_randomizer('balanced', 'write')
        self.write_master = FIFOMaster(
            dut=dut,
            title='write_master',
            prefix='',
            clock=self.wr_clk,
            field_config=self.field_config,
            multi_sig=True,
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
            multi_sig=True,
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
            multi_sig=True,
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
            multi_sig=True,
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

        self.log.info(f"FifoMultiBufferTB initialized with mode={self.TEST_MODE}, "
                        f"addr_width={self.AW}, ctrl_width={self.CW}, data_width={self.DW}, depth={self.TEST_DEPTH}")

    def _create_robust_randomizer_manager(self):
        """Create FlexConfigGen manager that returns FlexRandomizer instances directly"""

        # Define custom multi-signal specific profiles
        multi_signal_custom_profiles = {
            # Multi-signal specific patterns
            'multi_stress': ([(0, 0), (1, 2), (5, 8), (15, 25), (30, 45)], [5, 4, 3, 2, 1]),            # Multi-signal stress
            'multi_pipeline': ([(1, 3), (4, 6), (7, 9)], [4, 3, 2]),                                    # Multi-signal pipeline
            'multi_burst': ([(0, 0), (12, 20), (35, 50)], [12, 3, 1]),                                  # Multi-signal burst
            'multi_realistic': ([(0, 1), (2, 5), (8, 12), (20, 28)], [6, 4, 3, 2]),                     # Real-world multi-signal
            'multi_fine_grain': ([(0, 1), (2, 4), (5, 7), (8, 11), (12, 16)], [5, 4, 3, 2, 1]),         # Fine multi-signal control
            'multi_signal_aware': ([(0, 0), (1, 1), (self.TEST_DEPTH//2, self.TEST_DEPTH)], [8, 3, 1])  # Signal-count aware
        }

        # Create FlexConfigGen - NOTE: return_flexrandomizer=True
        config_gen = FlexConfigGen(
            profiles=[
                # Standard canned profiles
                'backtoback', 'fast', 'constrained', 'bursty', 'slow', 'stress',
                'moderate', 'balanced', 'heavy_pause', 'gradual', 'jittery',
                'pipeline', 'throttled', 'chaotic', 'smooth', 'efficient',
                # Custom multi-signal profiles
                'multi_stress', 'multi_pipeline', 'multi_burst', 'multi_realistic',
                'multi_fine_grain', 'multi_signal_aware'
            ],
            fields=['write_delay', 'read_delay'],
            custom_profiles=multi_signal_custom_profiles
        )

        # Customize profiles for multi-signal behavior
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

        self.log.info(f"Created {len(self.randomizer_instances)} robust multi-signal randomizer instances via FlexConfigGen:")
        for profile_name in self.randomizer_instances.keys():
            self.log.info(f"  - {profile_name}")

        return config_gen

    def _customize_profiles(self, config_gen):
        """Customize FlexConfigGen profiles for multi-signal behavior"""

        # Ultra-aggressive backtoback for multi-signal
        config_gen.backtoback.write_delay.fixed_value(0)
        config_gen.backtoback.read_delay.fixed_value(0)

        # Fast patterns optimized for multi-signal processing
        config_gen.fast.write_delay.mostly_zero(zero_weight=30, fallback_range=(1, 2), fallback_weight=1)
        config_gen.fast.read_delay.mostly_zero(zero_weight=25, fallback_range=(1, 3), fallback_weight=2)

        # Stress test with multi-signal variations
        config_gen.stress.write_delay.weighted_ranges([
            ((0, 0), 6), ((1, 3), 5), ((4, 8), 4), ((12, 18), 3), ((25, 35), 2), ((40, 60), 1)
        ])
        config_gen.stress.read_delay.weighted_ranges([
            ((0, 1), 5), ((2, 5), 5), ((6, 12), 4), ((18, 28), 3), ((35, 45), 2), ((50, 70), 1)
        ])

        # Multi-signal optimized pipeline timing
        config_gen.pipeline.write_delay.uniform_range(1, 3)
        config_gen.pipeline.read_delay.uniform_range(2, 5)

        # Chaotic multi-signal testing
        config_gen.chaotic.write_delay.probability_split([
            ((0, 1), 0.4), ((2, 6), 0.3), ((8, 15), 0.2), ((20, 40), 0.1)
        ])
        config_gen.chaotic.read_delay.probability_split([
            ((0, 2), 0.45), ((3, 8), 0.3), ((12, 20), 0.15), ((25, 50), 0.1)
        ])

        # Multi-signal burst patterns
        config_gen.bursty.write_delay.burst_pattern(fast_cycles=0, pause_range=(8, 15), burst_ratio=20)
        config_gen.bursty.read_delay.burst_pattern(fast_cycles=0, pause_range=(10, 18), burst_ratio=12)

        # Heavy pause for multi-signal overflow testing
        config_gen.heavy_pause.write_delay.mostly_zero(zero_weight=15, fallback_range=(1, 2), fallback_weight=1)
        config_gen.heavy_pause.read_delay.weighted_ranges([((0, 0), 3), ((20, 35), 1)])

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

                # Provide detailed field comparison for debugging
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
        for region in ['addr_signals', 'ctrl_signals', 'data_signals']:
            region_stats = self.memory_model.get_region_access_stats(region)
            if region_stats:
                stats[f'memory_region_{region}'] = region_stats

        return stats

    async def simple_incremental_loops(self, count, delay_key, delay_clks_after):
        """Run simple incremental tests with multi-signal packets using FlexConfigGen instances"""
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
            self.log.error(f"Timeout waiting for multi-signal packets! Only received {len(self.rd_monitor._recvQ)} of {count}{self.get_time_ns_str()}")
            self.total_errors += 1

        # Additional delay for stable results
        await self.wait_clocks(self.wr_clk_name, delay_clks_after)

        # Stop the command handler
        await self.command_handler.stop()

        # Compare the packets
        self.compare_packets("Multi-Signal Simple Incremental Loops", count)

        # Print statistics
        stats = self.get_component_statistics()
        self.log.info(f"Multi-Signal Test Statistics: {stats}")

        assert self.total_errors == 0, f'Multi-Signal Simple Incremental Loops found {self.total_errors} Errors{self.get_time_ns_str()}'

    async def comprehensive_randomizer_sweep(self, packets_per_config=12):
        """Test all available randomizer configurations using FlexConfigGen instances"""
        self.log.info('='*80)
        self.log.info(f'Running comprehensive multi-signal randomizer sweep with {packets_per_config} packets per config')

        total_configs = len(self.randomizer_instances)
        failures = 0

        for i, config_name in enumerate(self.randomizer_instances.keys()):
            self.log.info(f'Testing multi-signal config {i+1}/{total_configs}: {config_name}')

            try:
                await self.simple_incremental_loops(
                    count=packets_per_config,
                    delay_key=config_name,
                    delay_clks_after=6
                )
                self.log.info(f'✓ Multi-signal config {config_name} passed')
            except Exception as e:
                self.log.error(f'✗ Multi-signal config {config_name} failed: {e}')
                failures += 1

        self.log.info(f"Multi-signal randomizer sweep completed: {total_configs - failures}/{total_configs} profiles passed")
        return failures == 0

    async def run_sequence_test(self, sequence_type='comprehensive', count=20):
        """Run a test using predefined FIFO sequences with multi-signal support"""

        self.log.info('='*80)
        self.log.info(f"Running multi-signal {sequence_type} sequence test with {count} packets{self.get_time_ns_str()}")

        # Use multi-signal optimized randomizer from FlexConfigGen
        self.set_randomizer_profile('multi_realistic')

        # Reset the environment
        await self.assert_reset()
        await self.wait_clocks(self.wr_clk_name, 10)
        await self.deassert_reset()
        await self.wait_clocks(self.wr_clk_name, 10)

        # Start the command handler
        await self.command_handler.start()

        # Create the appropriate sequence
        if sequence_type == 'comprehensive':
            sequence = FIFOSequence.create_comprehensive_test(
                name="multi_comprehensive_test",
                capacity=self.TEST_DEPTH,
                data_width=self.DW
            )
        elif sequence_type == 'stress':
            sequence = FIFOSequence.create_data_stress_test(
                name="multi_stress_test",
                data_width=self.DW,
                delay=1
            )
        elif sequence_type == 'capacity':
            sequence = FIFOSequence.create_fifo_capacity_test(
                name="multi_capacity_test",
                capacity=self.TEST_DEPTH
            )
        else:
            self.log.error(f"Unknown sequence type: {sequence_type}")
            return False

        # Set field configuration to match our testbench
        sequence.field_config = self.field_config

        # Generate the packets
        packets = sequence.generate_packets(count=count, apply_fifo_metadata=True)
        self.log.info(f"Generated {len(packets)} multi-signal packets for sequence test")

        # Process the packets through the command handler
        response_map = await self.command_handler.process_sequence(sequence)

        # Wait for all transactions to complete
        await self.wait_clocks(self.wr_clk_name, 40)

        # Stop the command handler
        await self.command_handler.stop()

        # Compare monitored packets
        self.compare_packets(f"Multi-Signal {sequence_type.capitalize()} Sequence Test", len(packets))

        # Get and report statistics
        stats = self.get_component_statistics()
        sequence_stats = sequence.get_stats()
        self.log.info(f"Multi-Signal Sequence Test Statistics - Components: {stats}")
        self.log.info(f"Multi-Signal Sequence Test Statistics - Sequence: {sequence_stats}")

        return self.total_errors == 0

    async def signal_isolation_test(self, count=20):
        """Test that individual signals work independently using FlexConfigGen"""
        self.log.info('='*80)
        self.log.info(f"Running multi-signal isolation test with {count} packets{self.get_time_ns_str()}")

        # Use fast randomizer for isolation testing from FlexConfigGen
        self.set_randomizer_profile('fast')

        # Reset environment
        await self.assert_reset()
        await self.wait_clocks(self.wr_clk_name, 10)
        await self.deassert_reset()
        await self.wait_clocks(self.wr_clk_name, 10)

        # Start command handler
        await self.command_handler.start()

        # Test each field independently
        test_patterns = [
            # Test addr field isolation
            {'name': 'addr_isolation', 'addr_vary': True, 'ctrl_vary': False, 'data0_vary': False, 'data1_vary': False},
            # Test ctrl field isolation
            {'name': 'ctrl_isolation', 'addr_vary': False, 'ctrl_vary': True, 'data0_vary': False, 'data1_vary': False},
            # Test data0 field isolation
            {'name': 'data0_isolation', 'addr_vary': False, 'ctrl_vary': False, 'data0_vary': True, 'data1_vary': False},
            # Test data1 field isolation
            {'name': 'data1_isolation', 'addr_vary': False, 'ctrl_vary': False, 'data0_vary': False, 'data1_vary': True},
            # Test combinations
            {'name': 'addr_ctrl_combo', 'addr_vary': True, 'ctrl_vary': True, 'data0_vary': False, 'data1_vary': False},
            {'name': 'data_combo', 'addr_vary': False, 'ctrl_vary': False, 'data0_vary': True, 'data1_vary': True},
        ]

        for pattern in test_patterns:
            self.log.info(f"Testing pattern: {pattern['name']}")

            # Send packets according to pattern
            for i in range(count // len(test_patterns)):
                packet = FIFOPacket(self.field_config)

                # Set fields based on pattern
                packet.addr = (i if pattern['addr_vary'] else 0x1000) & self.MAX_ADDR
                packet.ctrl = (i if pattern['ctrl_vary'] else 0x55) & self.MAX_CTRL
                packet.data0 = (i * 0x100 if pattern['data0_vary'] else 0xDEAD) & self.MAX_DATA
                packet.data1 = (i * 0x200 if pattern['data1_vary'] else 0xBEEF) & self.MAX_DATA

                await self.write_master.send(packet)

            # Small delay between patterns
            await self.wait_clocks(self.wr_clk_name, 5)

        # Wait for completion
        while self.write_master.transfer_busy:
            await self.wait_clocks(self.wr_clk_name, 1)

        # Allow time for all packets to be received
        await self.wait_clocks(self.wr_clk_name, 25)

        # Wait for all packets to be received
        expected_packets = (count // len(test_patterns)) * len(test_patterns)
        timeout_counter = 0
        while len(self.rd_monitor._recvQ) < expected_packets and timeout_counter < self.TIMEOUT_CYCLES:
            await self.wait_clocks(self.wr_clk_name, 1)
            timeout_counter += 1

        if timeout_counter >= self.TIMEOUT_CYCLES:
            self.log.error(f"Timeout waiting for isolation test packets! Only received {len(self.rd_monitor._recvQ)} of {expected_packets}{self.get_time_ns_str()}")
            self.total_errors += 1

        # Stop command handler
        await self.command_handler.stop()

        # Compare results
        self.compare_packets("Multi-Signal Isolation Test", expected_packets)

        # Get statistics
        stats = self.get_component_statistics()
        self.log.info(f"Signal Isolation Test Statistics: {stats}")

        return self.total_errors == 0

    async def back_to_back_multi_signal_test(self, count=30):
        """Test back-to-back multi-signal transactions using FlexConfigGen backtoback profile"""
        self.log.info('='*80)
        self.log.info(f'Running back-to-back multi-signal test with {count} packets{self.get_time_ns_str()}')

        # Use the aggressive backtoback randomizer profile from FlexConfigGen
        self.set_randomizer_profile('backtoback')

        # Reset the environment
        await self.assert_reset()
        await self.wait_clocks(self.wr_clk_name, 10)
        await self.deassert_reset()
        await self.wait_clocks(self.wr_clk_name, 10)

        # Start command handler
        await self.command_handler.start()

        # Send packets back-to-back with distinct patterns for each field
        for i in range(count):
            packet = FIFOPacket(self.field_config)
            packet.addr = (i * 0x4) & self.MAX_ADDR        # Incremental addresses
            packet.ctrl = (i % 16) & self.MAX_CTRL         # Cycling control values
            packet.data0 = (i * 0x100 + 0x1000) & self.MAX_DATA  # Incremental data0
            packet.data1 = ((count - i) * 0x200) & self.MAX_DATA  # Decremental data1

            await self.write_master.send(packet)

        # Wait for completion
        while self.write_master.transfer_busy:
            await self.wait_clocks(self.wr_clk_name, 1)

        # Allow time for all packets to propagate
        await self.wait_clocks(self.wr_clk_name, count + 25)

        # Stop command handler
        await self.command_handler.stop()

        # Compare results
        self.compare_packets("Back-to-Back Multi-Signal Test", count)

        # Report statistics
        stats = self.get_component_statistics()
        self.log.info(f"Back-to-Back Multi-Signal Test Statistics: {stats}")

        return self.total_errors == 0