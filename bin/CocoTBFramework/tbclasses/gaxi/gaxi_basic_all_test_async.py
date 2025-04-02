"""Async-specific test methods for GAXI testbenches"""
# Import the multi-field test methods class
from CocoTBFramework.tbclasses.gaxi.gaxi_basic_all_test_multi import GAXIMultiFieldTestMethods
from CocoTBFramework.tbclasses.gaxi.gaxi_basic_all_test_infra import GAXITestSequences
from CocoTBFramework.components.gaxi.gaxi_sequence import GAXISequence


class GAXIAsyncTestMethods(GAXIMultiFieldTestMethods):
    """Async-specific test methods for GAXI testbenches"""

    async def async_cdc_test(self, count, delay_clks_after=20):
        """
        Test CDC (Clock Domain Crossing) functionality for async buffers.
        This test is only applicable for async buffers.

        Args:
            count: Number of packets to send
            delay_clks_after: Cycles to wait after completing transfer
        """
        if not self.is_async:
            self.log.info("Skipping async_cdc_test for non-async buffer")
            return

        self.log.info(f'async_cdc_test({count=}, {delay_clks_after=})')

        # Set fast randomizer mode for this test
        self.set_randomizer_mode('fast')

        # Reset and prepare for test
        await self.reset_sequence()

        # Create a sequence with varying delays to stress CDC logic
        sequence = GAXISequence("cdc_test", self.field_config)

        # Add packets with varying delays
        for i in range(count):
            if self.use_multi_field_packets:
                addr = i & self.config.max_addr
                ctrl = i & self.config.max_ctrl
            else:
                addr = 0
            data = i & self.config.max_data
            sequence.add_write(addr, data)

            # Add varying delays to stress CDC logic
            if i % 5 == 0:
                sequence.add_delay(2)
            else:
                sequence.add_delay(0)

        # Set randomizers
        sequence.set_master_randomizer(self.write_randomizer)
        sequence.set_slave_randomizer(self.read_randomizer)

        # Generate packets
        packets = sequence.generate_packets()

        # Send all packets
        await self.send_packets(packets)

        # Wait for data to cross between clock domains
        adjusted_delay = delay_clks_after * max(self.config.clk_wr_period, self.config.clk_rd_period) // min(self.config.clk_wr_period, self.config.clk_rd_period)
        await self.wait_clocks(self.rd_clk_name, adjusted_delay*5)

        # Wait for packets to be received
        await self.wait_for_packets(count)

        # Final stabilization delay
        await self.wait_clocks(self.rd_clk_name, delay_clks_after)

        # Compare results
        self.compare_results(count, 'async_cdc_test')
        assert self.total_errors == 0, f'Async CDC Test found {self.total_errors} Errors'

    async def clock_ratio_test(self, count, delay_clks_after=20):
        """
        Test asynchronous buffer with different clock ratios.
        This test is only applicable for async buffers.

        Args:
            count: Number of packets to send
            delay_clks_after: Cycles to wait after completing transfer
        """
        if not self.is_async:
            self.log.info("Skipping clock_ratio_test for non-async buffer")
            return

        self.log.info(f'clock_ratio_test({count=}, {delay_clks_after=})')

        # Original clock periods
        original_wr_period = self.config.clk_wr_period
        original_rd_period = self.config.clk_rd_period

        # Clock ratio test configurations
        # Each tuple has (write_period, read_period, description)
        clock_ratios = [
            (10, 10, "1:1 - Same frequency"),
            (10, 20, "1:2 - Read clock slower"),
            (20, 10, "2:1 - Write clock slower"),
            (10, 15, "2:3 - Non-integer ratio"),
            (12, 8, "3:2 - Non-integer ratio inverse")
        ]

        for wr_period, rd_period, description in clock_ratios:
            self.log.info(f"Testing clock ratio {description} ({wr_period}:{rd_period})")

            # Skip if this is the same as the current ratio (likely already tested)
            if wr_period == self.config.clk_wr_period and rd_period == self.config.clk_rd_period:
                self.log.info(f"Skipping already tested ratio {wr_period}:{rd_period}")
                continue

            # Update clock periods in config
            self.config.clk_wr_period = wr_period
            self.config.clk_rd_period = rd_period

            # Reset for clean test
            await self.reset_sequence()

            # Set moderate randomizer mode for this test
            self.set_randomizer_mode('constrained')

            # Create a sequence for clock ratio test
            sequence = GAXITestSequences.create_clock_ratio_test_sequence(
                "clock_ratio",
                self.field_config,
                count=count
            )

            # Set randomizers
            sequence.set_master_randomizer(self.write_randomizer)
            sequence.set_slave_randomizer(self.read_randomizer)

            # Generate packets
            packets = sequence.generate_packets()

            # Send all packets
            await self.send_packets(packets)

            # Calculate appropriate wait time based on the slower clock
            slower_period = max(wr_period, rd_period)
            faster_period = min(wr_period, rd_period)

            # Scale delay based on clock ratio to ensure enough time
            delay_factor = (slower_period / faster_period) * 2
            adjusted_delay = int(delay_clks_after * delay_factor)

            # Wait for data to cross between clock domains using the read clock
            await self.wait_clocks(self.rd_clk_name, adjusted_delay)

            # Wait for packets to be received with a timeout appropriate for this clock ratio
            timeout_factor = int(max(5, delay_factor * 2))
            await self.wait_for_packets(count, timeout_factor)

            # Final stabilization delay
            await self.wait_clocks(self.rd_clk_name, adjusted_delay // 2)

            # Compare results for this clock ratio
            errors = self.compare_results(count)
            if errors > 0:
                self.log.error(f"Clock ratio test {description} failed with {errors} errors")
            else:
                self.log.info(f"Clock ratio test {description} passed")

        # Restore original clock periods
        self.config.clk_wr_period = original_wr_period
        self.config.clk_rd_period = original_rd_period

        # Final assertion
        assert self.total_errors == 0, f'Clock Ratio Test found {self.total_errors} Errors'
