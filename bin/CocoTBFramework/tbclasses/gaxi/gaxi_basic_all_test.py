"""Main integration module for GAXI testbenches"""
# Import the async test methods class
from .gaxi_basic_all_test_async import GAXIAsyncTestMethods
from .gaxi_basic_all_test_config import TestConfig


class GAXIBasicTestBase(GAXIAsyncTestMethods):
    """Main test base class for GAXI testbenches with all methods

    Module Hierarchy

        GAXIBasicTestInfra (in gaxi_basic_all_test_infra.py)
            Base infrastructure with common methods like reset, packet handling, etc.

        GAXIBasicTestMethods (in gaxi_basic_all_test_basic.py)
            Inherits from GAXIBasicTestInfra
            Adds basic test methods like simple_incremental_loops, random_payload_test, etc.

        GAXIMultiFieldTestMethods (in gaxi_basic_all_test_multi.py)
            Inherits from GAXIBasicTestMethods
            Adds multi-field specific test methods like addr_ctrl_data_crossing_test

        GAXIAsyncTestMethods (in gaxi_basic_all_test_async.py)
            Inherits from GAXIMultiFieldTestMethods
            Adds async-specific test methods like async_cdc_test, clock_ratio_test

        GAXIBasicTestBase (in gaxi_basic_all_test.py)
            Inherits from GAXIAsyncTestMethods (which contains all previous test methods)
            Adds the run_comprehensive_test_suite method that calls all the inherited test methods
            This is the class that will be imported by the testbench implementation
    """

    async def run_comprehensive_test_suite(self, short_test=False):
        """
        Run a comprehensive test suite covering all aspects of the buffer.

        Args:
            short_test: If True, run a reduced test set for quicker validation
        """
        self.log.info(f"Starting comprehensive test suite (short_test={short_test})")

        # Basic test - always run
        count_basic = 10 * self.config.depth if short_test else 100 * self.config.depth
        await self.simple_incremental_loops(count=count_basic, use_fast=True, delay_clks_after=20)

        if not short_test:
            # More extensive incremental test
            await self.simple_incremental_loops(count=100*self.config.depth, use_fast=False, delay_clks_after=20)

        # Random payload test
        count_random = 20 * self.config.depth if short_test else 50 * self.config.depth
        await self.random_payload_test(count=count_random, use_fast=True)

        # Back-to-back test
        count_b2b = 10 * self.config.depth if short_test else 20 * self.config.depth
        await self.back_to_back_test(count=count_b2b)

        # Burst-pause test
        burst_size = 5 if short_test else 10
        num_bursts = 2 if short_test else 5
        await self.burst_pause_test(burst_size=burst_size, num_bursts=num_bursts)

        # Full/empty buffer test
        await self.full_empty_test()

        # Field-specific tests
        if self.field_mode in ['multi', 'multi_data']:
            count_field = 20 if short_test else 50
            await self.addr_ctrl_data_crossing_test(count=count_field)
            await self.alternating_field_values_test(count=count_field)

        # Edge value test
        count_edge = 10 if short_test else 20
        await self.edge_value_test(count=count_edge)

        # Async-specific tests
        if self.is_async:
            # Test different clock ratios
            if not short_test:
                await self.clock_ratio_test(count=20)

            # Test CDC functionality
            count_cdc = 20 if short_test else 50
            await self.async_cdc_test(count=count_cdc)

        self.log.info("Comprehensive test suite completed successfully")
        self.log.info(f"Total errors: {self.total_errors}")
        assert self.total_errors == 0, f"Test suite failed with {self.total_errors} errors"


# Export these for convenience
__all__ = ['GAXIBasicTestBase', 'TestConfig']