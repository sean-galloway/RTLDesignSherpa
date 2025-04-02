"""Basic test methods for GAXI testbenches"""
from CocoTBFramework.components.gaxi.gaxi_sequence import GAXISequence

# Import the infrastructure base class
from .gaxi_basic_all_test_infra import GAXIBasicTestInfra, GAXITestSequences


class GAXIBasicTestMethods(GAXIBasicTestInfra):
    """Basic test methods for GAXI testbenches"""

    async def simple_incremental_loops(self, count, use_fast=True, delay_clks_after=20):
        """
        Run simple incremental tests with different packet sizes.

        Args:
            count: Number of packets to send
            use_fast: Use fast randomizer mode if True
            delay_clks_after: Cycles to wait after completing transfer
        """
        wr_mon_count, rd_mon_count = self._get_monitor_counts()
        self.log.info(f'simple_incremental_loops({count=}, {use_fast=}, {delay_clks_after=} {wr_mon_count=} {rd_mon_count=})')

        # Choose the type of randomizer
        self.set_randomizer_mode('fast' if use_fast else 'constrained')

        # Reset and prepare for test
        await self.reset_sequence()

        # Create a sequence with incrementing values using the enhanced sequence generator
        sequence = GAXITestSequences.create_incremental_sequence(
            "incremental",
            self.field_config,
            count=count
        )

        # Set randomizers for sequence
        sequence.set_master_randomizer(self.write_randomizer)
        sequence.set_slave_randomizer(self.read_randomizer)

        # Generate packets
        packets = sequence.generate_packets()

        # Send all packets
        await self.send_packets(packets)

        # Extra wait for async designs
        if self.is_async:
            # Wait for data to cross between clock domains
            adjusted_delay = delay_clks_after * max(self.config.clk_wr_period, self.config.clk_rd_period) // min(self.config.clk_wr_period, self.config.clk_rd_period)
            await self.wait_clocks(self.rd_clk_name, adjusted_delay*5)
        else:
            # Standard synchronous wait
            await self.wait_clocks(self.wr_clk_name, delay_clks_after*5)

        # Wait for packets to be received
        await self.wait_for_packets(count)

        # Final stabilization delay
        if self.is_async:
            await self.wait_clocks(self.rd_clk_name, delay_clks_after)
        else:
            await self.wait_clocks(self.wr_clk_name, delay_clks_after)

        # Compare results
        self.compare_results(count, "simple_incremental_loops")
        assert self.total_errors == 0, f'Simple Incremental Loops Test found {self.total_errors} Errors'

    async def random_payload_test(self, count, use_fast=True, delay_clks_after=20):
        """
        Test with random data values.

        Args:
            count: Number of packets to send
            use_fast: Use fast randomizer mode if True
            delay_clks_after: Cycles to wait after completing transfer
        """
        wr_mon_count, rd_mon_count = self._get_monitor_counts()
        self.log.info(f'random_payload_test({count=}, {use_fast=}, {delay_clks_after=} {wr_mon_count=} {rd_mon_count=})')

        # Choose the type of randomizer
        self.set_randomizer_mode('fast' if use_fast else 'constrained')

        # Reset and prepare for test
        await self.reset_sequence()

        # Create a random sequence using the enhanced sequence generator
        sequence = GAXITestSequences.create_random_sequence(
            "random",
            self.field_config,
            count=count,
            varies_valid_ready=not use_fast
        )

        # Set randomizers for sequence
        sequence.set_master_randomizer(self.write_randomizer)
        sequence.set_slave_randomizer(self.read_randomizer)

        # Generate packets
        packets = sequence.generate_packets()

        # Send all packets
        await self.send_packets(packets)

        # Extra wait for async designs
        if self.is_async:
            # Wait for data to cross between clock domains
            adjusted_delay = delay_clks_after * max(self.config.clk_wr_period, self.config.clk_rd_period) // min(self.config.clk_wr_period, self.config.clk_rd_period)
            await self.wait_clocks(self.rd_clk_name, adjusted_delay*5)
        else:
            # Standard synchronous wait
            await self.wait_clocks(self.wr_clk_name, delay_clks_after*5)

        # Wait for packets to be received
        await self.wait_for_packets(count)

        # Final stabilization delay
        if self.is_async:
            await self.wait_clocks(self.rd_clk_name, delay_clks_after)
        else:
            await self.wait_clocks(self.wr_clk_name, delay_clks_after)

        # Compare results
        self.compare_results(count, 'random_payload_test')
        assert self.total_errors == 0, f'Random Payload Test found {self.total_errors} Errors'

    async def back_to_back_test(self, count, delay_clks_after=20):
        """
        Maximum throughput testing with back-to-back transactions.

        Args:
            count: Number of packets to send
            delay_clks_after: Cycles to wait after completing transfer
        """
        self.log.info(f'back_to_back_test({count=}, {delay_clks_after=})')

        # Use back-to-back mode for maximum throughput
        self.set_randomizer_mode('backtoback')

        # Reset and prepare for test
        await self.reset_sequence()

        # Create a burst sequence using the enhanced sequence generator
        sequence = GAXITestSequences.create_back_to_back_sequence(
            "back_to_back",
            self.field_config,
            count=count
        )

        # Set randomizers for sequence
        sequence.set_master_randomizer(self.write_randomizer)
        sequence.set_slave_randomizer(self.read_randomizer)

        # Generate packets
        packets = sequence.generate_packets()

        # Send all packets
        await self.send_packets(packets)

        # Extra wait for async designs
        if self.is_async:
            # Wait for data to cross between clock domains
            adjusted_delay = delay_clks_after * max(self.config.clk_wr_period, self.config.clk_rd_period) // min(self.config.clk_wr_period, self.config.clk_rd_period)
            await self.wait_clocks(self.rd_clk_name, adjusted_delay*5)
        else:
            # Standard synchronous wait
            await self.wait_clocks(self.wr_clk_name, delay_clks_after*5)

        # Wait for packets to be received
        await self.wait_for_packets(count)

        # Final stabilization delay
        if self.is_async:
            await self.wait_clocks(self.rd_clk_name, delay_clks_after)
        else:
            await self.wait_clocks(self.wr_clk_name, delay_clks_after)

        # Compare results
        self.compare_results(count, 'back_to_back_test')
        assert self.total_errors == 0, f'Back-to-Back Test found {self.total_errors} Errors'

    async def burst_pause_test(self, burst_size=10, num_bursts=5, delay_clks_after=20):
        """
        Test burst traffic pattern with pauses between bursts.

        Args:
            burst_size: Number of packets in each burst
            num_bursts: Number of bursts to send
            delay_clks_after: Cycles to wait after completing transfer
        """
        self.log.info(f'burst_pause_test({burst_size=}, {num_bursts=}, {delay_clks_after=})')

        # Total packets to send
        total_packets = burst_size * num_bursts

        # Reset and prepare for test
        await self.reset_sequence()

        # Create a burst-pause sequence using the enhanced sequence generator
        sequence = GAXITestSequences.create_burst_pause_sequence(
            "burst_pause",
            self.field_config,
            burst_size=burst_size,
            num_bursts=num_bursts,
            pause_length=20
        )

        # Use burst pause randomizer mode
        self.set_randomizer_mode('burst_pause')

        # Set randomizers for sequence
        sequence.set_master_randomizer(self.write_randomizer)
        sequence.set_slave_randomizer(self.read_randomizer)

        # Generate packets
        packets = sequence.generate_packets()

        # Send all packets
        await self.send_packets(packets)

        # Extra wait for async designs
        if self.is_async:
            # Wait for data to cross between clock domains
            adjusted_delay = delay_clks_after * max(self.config.clk_wr_period, self.config.clk_rd_period) // min(self.config.clk_wr_period, self.config.clk_rd_period)
            await self.wait_clocks(self.rd_clk_name, adjusted_delay*5)
        else:
            # Standard synchronous wait
            await self.wait_clocks(self.wr_clk_name, delay_clks_after*5)

        # Wait for packets to be received
        await self.wait_for_packets(total_packets)

        # Final stabilization delay
        if self.is_async:
            await self.wait_clocks(self.rd_clk_name, delay_clks_after)
        else:
            await self.wait_clocks(self.wr_clk_name, delay_clks_after)

        # Compare results
        self.compare_results(total_packets, 'burst_pause_test')
        assert self.total_errors == 0, f'Burst-Pause Test found {self.total_errors} Errors'

    async def full_empty_test(self, delay_clks_after=20):
        """
        Test buffer full and empty conditions.

        Args:
            delay_clks_after: Cycles to wait after completing transfer
        """
        self.log.info(f'full_empty_test({delay_clks_after=})')

        # Step 1: Fast producer, slow consumer to create full condition
        self.log.info("Testing buffer full condition - fast producer, slow consumer")
        self.set_randomizer_mode('fast', write_only=True)
        self.set_randomizer_mode('slow_consumer', read_only=True)

        # Reset and prepare for test
        await self.reset_sequence()

        # Create a full/empty test sequence using the enhanced sequence generator
        sequence = GAXITestSequences.create_full_empty_test_sequence(
            "full_empty",
            self.field_config,
            buffer_depth=self.config.depth,
            overflow_factor=1.5
        )

        # Generate packets to fill the buffer (using twice the depth to ensure fullness)
        count = self.config.depth * 2

        # Set randomizers for sequence
        sequence.set_master_randomizer(self.write_randomizer)
        sequence.set_slave_randomizer(self.read_randomizer)

        # Generate packets
        packets = sequence.generate_packets(count)

        # Send packets to fill the buffer
        await self.send_packets(packets)

        # Allow time for all packets to be received
        if self.is_async:
            adjusted_delay = delay_clks_after * 3 * max(self.config.clk_wr_period, self.config.clk_rd_period) // min(self.config.clk_wr_period, self.config.clk_rd_period)
            await self.wait_clocks(self.rd_clk_name, adjusted_delay)
        else:
            await self.wait_clocks(self.wr_clk_name, delay_clks_after*3)

        # Wait for packets to be received
        await self.wait_for_packets(count, timeout_factor=10)

        # Compare results for full test
        full_errors = self.compare_results(count, 'full_empty_test, part 1')

        # Reset monitors and clear scoreboard for empty test
        if hasattr(self.wr_monitor, 'observed_queue'):
            self.wr_monitor.observed_queue.clear()
        if hasattr(self.rd_monitor, 'observed_queue'):
            self.rd_monitor.observed_queue.clear()
        self.scoreboard.clear()
        self.total_errors = 0

        # Step 2: Slow producer, fast consumer to create empty condition
        self.log.info("Testing buffer empty condition - slow producer, fast consumer")
        self.set_randomizer_mode('slow_producer', write_only=True)
        self.set_randomizer_mode('fast', read_only=True)

        # Reset and prepare for test
        await self.reset_sequence()

        # Send a small number of packets
        small_count = max(2, self.config.depth // 2)

        # Create a short sequence
        short_sequence = GAXISequence("empty_test", self.field_config)

        # Add a few writes
        for i in range(small_count):
            if self.use_multi_field_packets:
                addr = i & self.config.max_addr
                data = i & self.config.max_data
            else:
                addr = 0
                data = i & self.config.max_data

            short_sequence.add_write(addr, data)

        # Set randomizers
        short_sequence.set_master_randomizer(self.write_randomizer)
        short_sequence.set_slave_randomizer(self.read_randomizer)

        # Generate packets
        packets = short_sequence.generate_packets()

        # Send all packets
        await self.send_packets(packets)

        # Allow time for all packets to be received
        if self.is_async:
            adjusted_delay = delay_clks_after * 2 * max(self.config.clk_wr_period, self.config.clk_rd_period) // min(self.config.clk_wr_period, self.config.clk_rd_period)
            await self.wait_clocks(self.rd_clk_name, adjusted_delay)
        else:
            await self.wait_clocks(self.wr_clk_name, delay_clks_after*2)

        # Wait for packets to be received
        await self.wait_for_packets(small_count)

        # Compare results for empty test
        empty_errors = self.compare_results(small_count, 'full_empty_test, part 2')

        # Report overall results
        total_errors = full_errors + empty_errors
        assert total_errors == 0, f'Full/Empty Test found {total_errors} errors ({full_errors} in full test, {empty_errors} in empty test)'
