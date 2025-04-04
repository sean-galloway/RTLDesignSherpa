"""Multi-field test methods for GAXI testbenches"""
# Import the basic test methods class
from CocoTBFramework.tbclasses.gaxi.gaxi_basic_all_test_basic import GAXIBasicTestMethods
from CocoTBFramework.tbclasses.gaxi.gaxi_basic_all_test_infra import GAXITestSequences
from CocoTBFramework.components.gaxi.gaxi_sequence import GAXISequence


class GAXIMultiFieldTestMethods(GAXIBasicTestMethods):
    """Multi-field specific test methods for GAXI testbenches"""

    def __init__(self, dut, wr_clk=None, wr_rstn=None, rd_clk=None, rd_rstn=None,
                config=None, field_mode='standard', multi_sig=False, 
                is_async=False, gaxi_mode='skid'):
        """
        Initialize the multi-field test methods.

        Args:
            dut: Device under test
            wr_clk: Write clock signal
            wr_rstn: Write reset signal (active low)
            rd_clk: Read clock signal (defaults to wr_clk if None)
            rd_rstn: Read reset signal (defaults to wr_rstn if None)
            config: TestConfig object
            field_mode: Field configuration mode ('standard', 'multi', or 'multi_data')
            multi_sig: Whether to use multi-signal mode
            is_async: Whether this is an asynchronous buffer
            gaxi_mode: GAXI mode ('skid', 'fifo_mux', or 'fifo_flop')
        """
        # Pass parameters to parent class
        super().__init__(
            dut,
            wr_clk, wr_rstn,
            rd_clk, rd_rstn,
            config,
            field_mode=field_mode,
            multi_sig=multi_sig,
            is_async=is_async,
            gaxi_mode=gaxi_mode
        )

    async def addr_ctrl_data_crossing_test(self, count, delay_clks_after=20):
        """
        Test signal crossing for multi-signal buffers by varying field patterns.
        This test is only applicable for multi-signal buffers.

        Args:
            count: Number of packets to send
            delay_clks_after: Cycles to wait after completing transfer
        """
        if not self.use_multi_field_packets:
            self.log.info("Skipping addr_ctrl_data_crossing_test for non-multi-field buffer")
            return

        self.log.info(f'addr_ctrl_data_crossing_test({count=}, {delay_clks_after=})')

        # Use fast mode for throughput
        self.set_randomizer_mode('fast')

        # Reset and prepare for test
        await self.reset_sequence()

        # Create a specialized crossing test sequence using the enhanced sequence generator
        sequence = GAXITestSequences.create_addr_ctrl_crossing_sequence(
            "field_crossing",
            self.field_config,
            count=count
        )

        if sequence is None:
            self.log.warning("Could not create addr_ctrl_crossing sequence for this configuration, skipping test")
            return

        # Set randomizers
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
        self.compare_results(count, 'addr_ctrl_data_crossing_test')
        assert self.total_errors == 0, f'Addr/Ctrl/Data Crossing Test found {self.total_errors} Errors'

    async def alternating_field_values_test(self, count, delay_clks_after=20):
        """
        Pattern-based test for multi-signal buffers using alternating 1s and 0s.
        This test is only applicable for multi-signal buffers.

        Args:
            count: Number of packets to send
            delay_clks_after: Cycles to wait after completing transfer
        """
        if not self.use_multi_field_packets:
            self.log.info("Skipping alternating_field_values_test for non-multi-field buffer")
            return

        self.log.info(f'alternating_field_values_test({count=}, {delay_clks_after=})')

        # Use fast mode for throughput
        self.set_randomizer_mode('fast')

        # Reset and prepare for test
        await self.reset_sequence()

        # Create a specialized alternating bit patterns test sequence
        sequence = GAXITestSequences.create_alternating_field_values_sequence(
            "alternating_patterns",
            self.field_config,
            count=count
        )

        if sequence is None:
            self.log.warning("Could not create alternating field values sequence for this configuration, skipping test")
            return

        # Set randomizers
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
        self.compare_results(count, 'alternating_field_values_test')
        assert self.total_errors == 0, f'Alternating Field Values Test found {self.total_errors} Errors'

    async def edge_value_test(self, count, delay_clks_after=20):
        """
        Testing with edge case values (all 0s, all 1s, alternating bits).

        Args:
            count: Number of packets to send
            delay_clks_after: Cycles to wait after completing transfer
        """
        self.log.info(f'edge_value_test({count=}, {delay_clks_after=})')

        # Use fast mode for throughput
        self.set_randomizer_mode('fast')

        # Reset and prepare for test
        await self.reset_sequence()

        # Create pattern test sequence for edge cases
        sequence = GAXITestSequences.create_pattern_test_sequence(
            "edge_values",
            self.field_config,
            addr=0,
            pattern_type="edges"
        )

        # Set randomizers
        sequence.set_master_randomizer(self.write_randomizer)
        sequence.set_slave_randomizer(self.read_randomizer)

        # Generate packets (limit to what we have)
        actual_count = min(count, len(sequence.cmd_seq))
        packets = sequence.generate_packets(actual_count)

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
        await self.wait_for_packets(actual_count)

        # Final stabilization delay
        if self.is_async:
            await self.wait_clocks(self.rd_clk_name, delay_clks_after)
        else:
            await self.wait_clocks(self.wr_clk_name, delay_clks_after)

        # Compare results
        self.compare_results(actual_count, 'edge_value_test')
        assert self.total_errors == 0, f'Edge Value Test found {self.total_errors} Errors'
