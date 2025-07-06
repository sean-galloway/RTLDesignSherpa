"""Testbench for GAXI buffer components - Refactored to use FlexConfigGen only

Key changes:
- Eliminated manual FlexRandomizer instantiation
- FlexConfigGen now returns FlexRandomizer instances directly  
- Simplified randomizer management with direct profile access
- Cleaner architecture using single randomization source
"""
import os
import random
import cocotb

from CocoTBFramework.tbclasses.tbbase import TBBase
from CocoTBFramework.components.shared.field_config import FieldConfig

from CocoTBFramework.components.gaxi.gaxi_packet import GAXIPacket
from CocoTBFramework.components.gaxi.gaxi_master import GAXIMaster
from CocoTBFramework.components.gaxi.gaxi_slave import GAXISlave
from CocoTBFramework.components.gaxi.gaxi_monitor import GAXIMonitor
from CocoTBFramework.components.shared.flex_config_gen import FlexConfigGen


class GaxiBufferTB(TBBase):
    """Testbench for GAXI buffer components using FlexConfigGen only for randomization"""

    def __init__(self, dut,
                    wr_clk=None, wr_rstn=None,
                    rd_clk=None, rd_rstn=None):
        super().__init__(dut)

        # Get test parameters from environment
        self.TEST_DEPTH = self.convert_to_int(os.environ.get('TEST_DEPTH', '0'))
        self.TEST_DATA_WIDTH = self.convert_to_int(os.environ.get('TEST_DATA_WIDTH', '0'))
        self.TEST_MODE = os.environ.get('TEST_MODE', 'skid')
        self.TEST_KIND = os.environ.get('TEST_KIND', 'sync')
        self.TEST_CLK_WR = self.convert_to_int(os.environ.get('TEST_CLK_WR', '10'))
        self.TEST_CLK_RD = self.convert_to_int(os.environ.get('TEST_CLK_RD', '10'))
        self.super_debug = False

        # Setup widths and limits
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
        msg += f' DataW:    {self.TEST_DATA_WIDTH}\n'
        msg += f' Max Data: {self.MAX_DATA}\n'
        msg += f' MODE:     {self.TEST_MODE}\n'
        msg += f' clk_wr:   {self.TEST_CLK_WR}\n'
        msg += f' clk_rd:   {self.TEST_CLK_RD}\n'
        msg += '='*80 + "\n"
        self.log.info(msg)

        # Create FlexConfigGen manager and get randomizer instances directly
        self.randomizer_manager = self._create_randomizer_manager()

        # Define field configuration with correct data width
        self.field_config = FieldConfig.from_dict({'data': {'bits': self.DW, 'default': 0}})

        self.log.debug(f"\n{self.field_config}")

        # Create BFM components using modern simplified interface
        # Write Master - uses automatic signal generation
        self.write_master = GAXIMaster(
            dut=dut,
            title='write_master',
            prefix='',
            clock=self.wr_clk,
            field_config=self.field_config,
            timeout_cycles=self.TIMEOUT_CYCLES,
            mode=self.TEST_MODE,
            in_prefix='i_',
            out_prefix='o_',
            bus_name='',
            pkt_prefix='',
            multi_sig=False,
            log=self.log,
            super_debug=self.super_debug
        )

        # Read Slave - uses automatic signal generation
        self.read_slave = GAXISlave(
            dut=dut,
            title='read_slave',
            prefix='',
            clock=self.rd_clk,
            field_config=self.field_config,
            timeout_cycles=self.TIMEOUT_CYCLES,
            mode=self.TEST_MODE,
            in_prefix='i_',
            out_prefix='o_',
            bus_name='',
            pkt_prefix='',
            multi_sig=False,
            log=self.log,
            super_debug=self.super_debug
        )

        # Write Monitor - monitors write port
        self.wr_monitor = GAXIMonitor(
            dut=dut,
            title='Write monitor',
            prefix='',
            clock=self.wr_clk,
            field_config=self.field_config,
            is_slave=False,  # Monitor write port (master side)
            mode=self.TEST_MODE,
            in_prefix='i_',
            out_prefix='o_',
            bus_name='',
            pkt_prefix='',
            multi_sig=False,
            log=self.log,
            super_debug=self.super_debug
        )

        # Read Monitor - monitors read port
        self.rd_monitor = GAXIMonitor(
            dut=dut,
            title='Read monitor',
            prefix='',
            clock=self.rd_clk,
            field_config=self.field_config,
            is_slave=True,   # Monitor read port (slave side)
            mode=self.TEST_MODE,
            in_prefix='i_',
            out_prefix='o_',
            bus_name='',
            pkt_prefix='',
            multi_sig=False,
            log=self.log,
            super_debug=self.super_debug
        )

        # Set default randomizer profile
        self.set_randomizer_profile('balanced')

        self.log.info(f"GaxiBufferTB initialized with mode={self.TEST_MODE}, "
                        f"data_width={self.DW}, depth={self.TEST_DEPTH}")

    def _create_randomizer_manager(self):
        """Create FlexConfigGen manager that returns FlexRandomizer instances directly"""

        # Define custom GAXI-specific profiles for different test scenarios
        gaxi_custom_profiles = {
            # Specific patterns for GAXI testing
            'gaxi_stress': ([(0, 0), (1, 2), (5, 10), (20, 30)], [3, 4, 2, 1]),      # Mixed fast/slow for stress
            'gaxi_pipeline': ([(2, 3), (4, 6)], [3, 1]),                              # Pipeline-friendly timing
            'gaxi_backpressure': ([(0, 0), (30, 50)], [8, 1]),                        # Test backpressure protection
            'gaxi_realistic': ([(0, 1), (2, 4), (8, 12), (20, 25)], [4, 3, 2, 1]),   # Real-world-like pattern
            'gaxi_burst_heavy': ([(0, 0), (50, 80)], [15, 1]),                        # Heavy burst pattern
            'gaxi_fine_grain': ([(0, 1), (2, 3), (4, 5), (6, 8)], [4, 3, 2, 1]),     # Fine-grained control
            'gaxi_depth_aware': ([(0, 0), (1, 1), (self.TEST_DEPTH, self.TEST_DEPTH*2)], [6, 2, 1])  # Depth-aware delays
        }

        # Create FlexConfigGen for comprehensive testing - NOTE: return_flexrandomizer=True
        config_gen = FlexConfigGen(
            profiles=[
                # Standard canned profiles
                'backtoback', 'fast', 'constrained', 'bursty', 'slow', 'stress',
                'moderate', 'balanced', 'heavy_pause', 'gradual', 'jittery',
                'pipeline', 'throttled', 'chaotic', 'smooth', 'efficient',
                # Custom GAXI-specific profiles
                'gaxi_stress', 'gaxi_pipeline', 'gaxi_backpressure',
                'gaxi_realistic', 'gaxi_burst_heavy', 'gaxi_fine_grain', 'gaxi_depth_aware'
            ],
            fields=['valid_delay', 'ready_delay'],
            custom_profiles=gaxi_custom_profiles
        )

        # Customize some profiles for GAXI-specific behavior
        self._customize_profiles(config_gen)

        # Build configurations and get FlexRandomizer instances directly
        self.randomizer_instances = config_gen.build(return_flexrandomizer=True)

        # Create write/read domain mapping for easier access
        self.domain_randomizers = {}
        for profile_name, randomizer in self.randomizer_instances.items():
            self.domain_randomizers[profile_name] = {
                'write': randomizer,  # Write domain gets the randomizer
                'read': randomizer    # Read domain gets the same randomizer
            }

        self.log.info(f"Created {len(self.randomizer_instances)} FlexRandomizer instances via FlexConfigGen:")
        for profile_name in self.randomizer_instances.keys():
            self.log.info(f"  - {profile_name}")

        return config_gen

    def _customize_profiles(self, config_gen):
        """Customize FlexConfigGen profiles for GAXI-specific behavior"""

        # Make backtoback truly aggressive for both valid and ready
        config_gen.backtoback.valid_delay.fixed_value(0)
        config_gen.backtoback.ready_delay.fixed_value(0)

        # Create asymmetric patterns (different valid vs ready behaviors)
        config_gen.fast.valid_delay.mostly_zero(zero_weight=20, fallback_range=(1, 3), fallback_weight=1)
        config_gen.fast.ready_delay.mostly_zero(zero_weight=15, fallback_range=(1, 5), fallback_weight=2)

        # Stress test with wider variations
        config_gen.stress.valid_delay.weighted_ranges([
            ((0, 0), 4), ((1, 5), 3), ((10, 15), 2), ((25, 40), 1)
        ])
        config_gen.stress.ready_delay.weighted_ranges([
            ((0, 1), 3), ((2, 8), 4), ((15, 25), 2), ((35, 50), 1)
        ])

        # Pipeline-friendly - consistent moderate delays
        config_gen.pipeline.valid_delay.uniform_range(3, 5)
        config_gen.pipeline.ready_delay.uniform_range(4, 7)

        # Chaotic - completely unpredictable for robustness testing
        config_gen.chaotic.valid_delay.probability_split([
            ((0, 2), 0.3), ((5, 10), 0.25), ((15, 25), 0.25), ((40, 60), 0.2)
        ])
        config_gen.chaotic.ready_delay.probability_split([
            ((0, 1), 0.35), ((3, 8), 0.3), ((12, 20), 0.2), ((30, 45), 0.15)
        ])

        # Burst patterns for testing GAXI buffering capabilities
        config_gen.bursty.valid_delay.burst_pattern(fast_cycles=0, pause_range=(15, 25), burst_ratio=12)
        config_gen.bursty.ready_delay.burst_pattern(fast_cycles=0, pause_range=(20, 35), burst_ratio=8)

        # Heavy pause for backpressure testing
        config_gen.heavy_pause.valid_delay.mostly_zero(zero_weight=10, fallback_range=(1, 3), fallback_weight=1)
        config_gen.heavy_pause.ready_delay.weighted_ranges([((0, 0), 2), ((30, 50), 1)])

    def get_randomizer(self, profile_name, domain='write'):
        """Get FlexRandomizer instance for specified profile and domain"""
        if profile_name in self.domain_randomizers:
            return self.domain_randomizers[profile_name][domain]
        else:
            # Fallback to balanced profile
            self.log.warning(f"Profile '{profile_name}' not found, using 'balanced'")
            return self.domain_randomizers['balanced'][domain]

    def set_randomizer_profile(self, profile_name):
        """Set randomizer profile for write and read components"""
        write_randomizer = self.get_randomizer(profile_name, 'write')
        read_randomizer = self.get_randomizer(profile_name, 'read')

        # Apply randomizers to components
        self.write_master.set_randomizer(write_randomizer)
        self.read_slave.set_randomizer(read_randomizer)

        self.log.info(f"Set randomizers to profile '{profile_name}' for write/read domains")

    def get_randomizer_config_names(self):
        """Get list of available randomizer configuration names"""
        return list(self.randomizer_instances.keys())

    def get_available_profiles(self):
        """Get list of available profiles (alias for compatibility)"""
        return self.get_randomizer_config_names()

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
        }

        # Add error tracking
        stats['total_errors'] = self.total_errors
        stats['available_profiles'] = len(self.randomizer_instances)

        return stats

    async def simple_incremental_loops(self, count, delay_key, delay_clks_after):
        """Run simple incremental tests with FlexConfigGen randomizer instances"""
        self.log.info('='*80)
        self.log.info(f'simple_incremental_loops({count=}, {delay_key=}, {delay_clks_after=}{self.get_time_ns_str()}')

        # Set randomizer profile using FlexConfigGen instances
        self.set_randomizer_profile(delay_key)

        # Reset and prepare for test
        await self.assert_reset()
        await self.wait_clocks(self.wr_clk_name, 10)
        await self.deassert_reset()
        await self.wait_clocks(self.wr_clk_name, 10)

        # Send packets
        for i in range(count):
            # Create packet using modern packet factory
            data = i & self.MAX_DATA  # Mask data to avoid overflow
            packet = GAXIPacket(self.field_config)
            packet.data = data

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

        # Compare the packets
        self.compare_packets("Simple Incremental Loops", count)

        # Print statistics
        stats = self.get_component_statistics()
        self.log.info(f"Test Statistics: {stats}")

        assert self.total_errors == 0, f'Simple Incremental Loops found {self.total_errors} Errors{self.get_time_ns_str()}'

    async def comprehensive_randomizer_sweep(self, packets_per_config=20):
        """Test all available randomizer configurations using FlexConfigGen instances"""
        self.log.info('='*80)
        self.log.info(f'Running comprehensive randomizer sweep with {packets_per_config} packets per config')

        total_configs = len(self.randomizer_instances)
        failures = 0

        for i, config_name in enumerate(self.randomizer_instances.keys()):
            self.log.info(f'Testing config {i+1}/{total_configs}: {config_name}')

            try:
                await self.simple_incremental_loops(
                    count=packets_per_config,
                    delay_key=config_name,
                    delay_clks_after=10
                )
                self.log.info(f'✓ Config {config_name} passed')
            except Exception as e:
                self.log.error(f'✗ Config {config_name} failed: {e}')
                failures += 1

        self.log.info(f'Randomizer sweep completed: {total_configs - failures}/{total_configs} profiles passed')
        return failures == 0

    async def stress_test_with_random_patterns(self, count=100, delay_key='gaxi_stress'):
        """Run a stress test with complex patterns using FlexConfigGen randomizer"""
        self.log.info('='*80)
        self.log.info(f'Running stress test with {count} packets and delay profile {delay_key}{self.get_time_ns_str()}')

        # Set randomizer profile using FlexConfigGen instances
        self.set_randomizer_profile(delay_key)

        # Reset the environment
        await self.assert_reset()
        await self.wait_clocks(self.wr_clk_name, 10)
        await self.deassert_reset()
        await self.wait_clocks(self.wr_clk_name, 10)

        # Create varied test patterns
        patterns = []

        # Pattern 1: Walking ones
        for bit in range(min(32, self.DW)):
            patterns.append(1 << bit)

        # Pattern 2: Walking zeros
        all_ones = (1 << self.DW) - 1
        for bit in range(min(32, self.DW)):
            patterns.append(all_ones & ~(1 << bit))

        # Pattern 3: Alternating bits
        patterns.extend([
            0x55555555 & self.MAX_DATA,  # 0101...
            0xAAAAAAAA & self.MAX_DATA,  # 1010...
            0x33333333 & self.MAX_DATA,  # 0011...
            0xCCCCCCCC & self.MAX_DATA,  # 1100...
        ])

        # Pattern 4: Random values
        random.seed(12345)  # For reproducibility
        for _ in range(count - len(patterns)):
            patterns.append(random.randint(0, self.MAX_DATA))

        # Send all patterns
        for i, pattern in enumerate(patterns):
            packet = GAXIPacket(self.field_config)
            packet.data = pattern

            # Queue the packet for transmission
            await self.write_master.send(packet)

            # Add occasional delay to prevent overwhelming the buffer
            if i % 10 == 9:
                await self.wait_clocks(self.wr_clk_name, 5)

        # Wait for all packets to be transmitted
        while self.write_master.transfer_busy:
            await self.wait_clocks(self.wr_clk_name, 1)

        # Allow time for all packets to be received
        await self.wait_clocks(self.wr_clk_name, 50)

        # Wait for all packets to be received
        timeout_counter = 0
        while len(self.rd_monitor._recvQ) < len(patterns) and timeout_counter < self.TIMEOUT_CYCLES:
            await self.wait_clocks(self.wr_clk_name, 1)
            timeout_counter += 1

        if timeout_counter >= self.TIMEOUT_CYCLES:
            self.log.error(f"Timeout waiting for packets! Only received {len(self.rd_monitor._recvQ)} of {len(patterns)}{self.get_time_ns_str()}")
            self.total_errors += 1

        # Compare the packets
        self.compare_packets("Stress Test With Random Patterns", len(patterns))

        # Get and report statistics
        stats = self.get_component_statistics()
        self.log.info(f"Stress Test Statistics: {stats}")

        # Return test result
        return self.total_errors == 0

    async def back_to_back_test(self, count=50):
        """Test back-to-back transactions using FlexConfigGen backtoback profile"""
        self.log.info('='*80)
        self.log.info(f'Running back-to-back test with {count} packets{self.get_time_ns_str()}')

        # Use the aggressive backtoback randomizer profile from FlexConfigGen
        self.set_randomizer_profile('backtoback')

        # Reset the environment
        await self.assert_reset()
        await self.wait_clocks(self.wr_clk_name, 10)
        await self.deassert_reset()
        await self.wait_clocks(self.wr_clk_name, 10)

        # Send packets back-to-back
        for i in range(count):
            packet = GAXIPacket(self.field_config)
            packet.data = (i * 3 + 7) & self.MAX_DATA  # Simple pattern
            await self.write_master.send(packet)

        # Wait for completion
        while self.write_master.transfer_busy:
            await self.wait_clocks(self.wr_clk_name, 1)

        # Allow time for all packets to propagate
        await self.wait_clocks(self.wr_clk_name, count + 20)

        # Compare results
        self.compare_packets("Back-to-Back Test", count)

        # Report statistics
        stats = self.get_component_statistics()
        self.log.info(f"Back-to-Back Test Statistics: {stats}")

        return self.total_errors == 0