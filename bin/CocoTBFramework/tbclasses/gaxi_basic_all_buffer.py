"""Unified GAXI Buffer Testbench for all buffer types including async designs"""
from CocoTBFramework.components.gaxi.gaxi_components import GAXIMaster, GAXISlave, GAXIMonitor
from CocoTBFramework.tbclasses.gaxi_basic_all_test_base import GAXIBasicTestBase, TestConfig
from CocoTBFramework.scoreboards.gaxi_scoreboard import GAXIScoreboard


class GaxiBasicBufferAllTB(GAXIBasicTestBase):
    """
    Universal testbench for AXI buffers that supports:
    1. Standard mode (single data field)
    2. Multi-signal mode (separate addr/ctrl/data signals)
    3. Field mode (combined field structure with flexible field configuration)
    4. Asynchronous buffers (separate read/write clocks)
    """
    def __init__(self, dut, wr_clk=None, wr_rstn=None, rd_clk=None, rd_rstn=None,
                buffer_type='standard', config=None):
        """
        Initialize the unified GAXI buffer testbench.

        Args:
            dut: Device under test
            wr_clk: Write clock signal
            wr_rstn: Write reset signal (active low)
            rd_clk: Read clock signal (defaults to wr_clk if None)
            rd_rstn: Read reset signal (defaults to wr_rstn if None)
            buffer_type: The type of buffer to test:
                - 'standard': Standard buffer with single data field
                - 'multi': Multi-signal buffer with separate addr/ctrl/data signals
                - 'field': Field-based buffer with combined signal structure
                - 'async': Asynchronous buffer with separate read/write clocks
            config: TestConfig object (created from environment if None)
        """
        # Create a config object if none provided
        if config is None:
            config = TestConfig.from_env()

        # Override buffer type from init parameter
        config.buffer_type = buffer_type

        # Detect if this is an async design
        is_async = (rd_clk is not None and rd_clk != wr_clk) or ('async' in buffer_type)

        # Determine the configuration flags
        use_multi_signals = 'multi' in buffer_type
        use_multi_field_packets = buffer_type in ['multi', 'field']

        # Choose the appropriate field mode for base class
        field_mode = 'multi' if use_multi_field_packets else 'standard'

        # Initialize the base class with these settings
        super().__init__(dut, wr_clk, wr_rstn, rd_clk, rd_rstn, config, field_mode)

        # Ensure our async flag matches the base class
        self.is_async = is_async  # Explicitly set property

        # Store the configuration flags
        self.use_multi_signals = use_multi_signals
        self.use_multi_field_packets = use_multi_field_packets

        # Set up BFM components based on buffer type
        self._setup_bfm_components()

        # Configure monitor callbacks - MUST come after monitors are created in _setup_bfm_components
        if self.wr_monitor:
            self.wr_monitor.add_callback(self._wr_monitor_callback)
        else:
            self.log.warning("Write monitor not initialized, scoreboard will not work properly")

        if self.rd_monitor:
            self.rd_monitor.add_callback(self._rd_monitor_callback)
        else:
            self.log.warning("Read monitor not initialized, scoreboard will not work properly")

        self.log.info(f"GaxiBufferAllTB initialized for buffer type: {buffer_type}, mode: {self.config.mode}")
        self.log.info(f"  - Async: {self.is_async}")
        self.log.info(f"  - Multi-signal: {self.use_multi_signals}")
        self.log.info(f"  - Multi-field packets: {self.use_multi_field_packets}")

    def _wr_monitor_callback(self, transaction):
        """Callback for write monitor"""
        self.log.debug(f"Write monitor captured: {transaction.formatted(compact=True)}")
        # Add to scoreboard expected queue
        self.scoreboard.add_expected(transaction)

    def _rd_monitor_callback(self, transaction):
        """Callback for read monitor"""
        self.log.debug(f"Read monitor captured: {transaction.formatted(compact=True)}")
        # Add to scoreboard actual queue
        self.scoreboard.add_actual(transaction)

    def _setup_bfm_components(self):
        """Set up BFM components based on clock and signal configuration"""
        # Define function naming based on configuration
        clk_type = "async" if self.is_async else "sync"
        sig_type = "multi" if self.use_multi_signals else "standard"

        # Create method name like _setup_async_multi_components or _setup_sync_standard_components
        method_name = f"_setup_{clk_type}_{sig_type}_components"

        self.log.info(f"Setting up components using method: {method_name}")

        # Call the appropriate method
        if hasattr(self, method_name):
            setup_method = getattr(self, method_name)
            setup_method()
        else:
            self.log.error(f"Missing setup method: {method_name}")
            raise NotImplementedError(f"Buffer configuration not supported: {clk_type}_{sig_type}")

    def _setup_sync_standard_components(self):
        """Set up BFM components for synchronous buffer with standard interfaces"""
        self.log.info("Setting up synchronous standard components")

        # Standard mode (single data signal)
        self.write_master = GAXIMaster(
            self.dut, 'write_master', '', self.wr_clk,
            field_config=self.field_config,
            randomizer=self.write_randomizer,
            timeout_cycles=self.config.timeout_cycles,
            signal_map=None,  # Explicitly specify standard mode
            log=self.log,
            multi_sig=self.use_multi_signals
        )

        self.read_slave = GAXISlave(
            self.dut, 'read_slave', '', self.rd_clk,
            mode=self.config.mode,
            field_config=self.field_config,
            randomizer=self.read_randomizer,
            timeout_cycles=self.config.timeout_cycles,
            signal_map=None,  # Explicitly specify standard mode
            log=self.log,
            multi_sig=self.use_multi_signals
        )

        self.wr_monitor = GAXIMonitor(
            self.dut, 'Write monitor', '', self.wr_clk,
            field_config=self.field_config,
            is_slave=False,
            signal_map=None,  # Explicitly specify standard mode
            log=self.log,
            multi_sig=self.use_multi_signals
        )

        self.rd_monitor = GAXIMonitor(
            self.dut, 'Read monitor', '', self.rd_clk,
            mode=self.config.mode,
            field_config=self.field_config,
            is_slave=True,
            signal_map=None,  # Explicitly specify standard mode
            log=self.log,
            multi_sig=self.use_multi_signals
        )

    def _setup_sync_multi_components(self):
        """Set up BFM components for synchronous buffer with multi-signal interfaces"""
        self.log.info("Setting up synchronous multi-signal components")

        # Define signal mappings for multi-signal mode
        # Required signals (valid/ready) for master
        master_signal_map = {
            'm2s_valid': 'i_wr_valid',
            's2m_ready': 'o_wr_ready'
        }

        # Optional signals (data fields) for master
        master_optional_map = {
            'm2s_pkt_addr': 'i_wr_addr',
            'm2s_pkt_ctrl': 'i_wr_ctrl',
            'm2s_pkt_data': 'i_wr_data'
        }

        # Required signals (valid/ready) for slave
        slave_signal_map = {
            'm2s_valid': 'o_rd_valid',
            's2m_ready': 'i_rd_ready'
        }

        # Optional signals (data fields) for slave
        slave_optional_map = {
            'm2s_pkt_addr': 'o_rd_addr',
            'm2s_pkt_ctrl': 'o_rd_ctrl',
            'm2s_pkt_data': 'o_rd_data'
        }

        # For fifo_mux mode, we also need to map to ow_rd_* signals
        if self.config.mode == 'fifo_mux':
            slave_optional_map['m2s_pkt_addr'] = 'ow_rd_addr'
            slave_optional_map['m2s_pkt_ctrl'] = 'ow_rd_ctrl'
            slave_optional_map['m2s_pkt_data'] = 'ow_rd_data'

        # Create BFM components with signal maps
        self.write_master = GAXIMaster(
            self.dut, 'write_master', '', self.wr_clk,
            field_config=self.field_config,
            randomizer=self.write_randomizer,
            timeout_cycles=self.config.timeout_cycles,
            signal_map=master_signal_map,
            optional_signal_map=master_optional_map,
            log=self.log,
            multi_sig=True
        )

        self.read_slave = GAXISlave(
            self.dut, 'read_slave', '', self.rd_clk,
            mode=self.config.mode,
            field_config=self.field_config,
            randomizer=self.read_randomizer,
            timeout_cycles=self.config.timeout_cycles,
            signal_map=slave_signal_map,
            optional_signal_map=slave_optional_map,
            log=self.log,
            multi_sig=True
        )

        self.wr_monitor = GAXIMonitor(
            self.dut, 'Write monitor', '', self.wr_clk,
            field_config=self.field_config,
            is_slave=False,
            signal_map=master_signal_map,
            optional_signal_map=master_optional_map,
            log=self.log,
            multi_sig=True
        )

        self.rd_monitor = GAXIMonitor(
            self.dut, 'Read monitor', '', self.rd_clk,
            mode=self.config.mode,
            field_config=self.field_config,
            is_slave=True,
            signal_map=slave_signal_map,
            optional_signal_map=slave_optional_map,
            log=self.log,
            multi_sig=True
        )

    def _setup_async_standard_components(self):
        """Set up BFM components for asynchronous buffer with standard interfaces"""
        self.log.info("Setting up asynchronous standard components")

        # Asynchronous standard buffer setup (different clocks, standard signals)
        self.write_master = GAXIMaster(
            self.dut, 'write_master', '', self.wr_clk,
            field_config=self.field_config,
            randomizer=self.write_randomizer,
            timeout_cycles=self.config.timeout_cycles,
            signal_map=None,  # Standard signals
            log=self.log
        )

        self.read_slave = GAXISlave(
            self.dut, 'read_slave', '', self.rd_clk,  # Note the rd_clk - different from wr_clk
            mode=self.config.mode,
            field_config=self.field_config,
            randomizer=self.read_randomizer,
            timeout_cycles=self.config.timeout_cycles,
            signal_map=None,  # Standard signals
            log=self.log
        )

        self.wr_monitor = GAXIMonitor(
            self.dut, 'Write monitor', '', self.wr_clk,
            field_config=self.field_config,
            is_slave=False,
            signal_map=None,  # Standard signals
            log=self.log
        )

        self.rd_monitor = GAXIMonitor(
            self.dut, 'Read monitor', '', self.rd_clk,  # Note the rd_clk
            mode=self.config.mode,
            field_config=self.field_config,
            is_slave=True,
            signal_map=None,  # Standard signals
            log=self.log
        )

    def _setup_async_multi_components(self):
        """Set up BFM components for asynchronous buffer with multi-signal interfaces"""
        self.log.info("Setting up asynchronous multi-signal components")

        # Signal maps for the multi-signal async buffer
        master_signal_map = {
            'm2s_valid': 'i_wr_valid',
            's2m_ready': 'o_wr_ready'
        }

        # Optional signals (data fields) for master
        master_optional_map = {
            'm2s_pkt_addr': 'i_wr_addr',
            'm2s_pkt_ctrl': 'i_wr_ctrl',
            'm2s_pkt_data': 'i_wr_data'
        }

        # Required signals (valid/ready) for slave
        slave_signal_map = {
            'm2s_valid': 'o_rd_valid',
            's2m_ready': 'i_rd_ready'
        }

        # Optional signals (data fields) for slave
        slave_optional_map = {
            'm2s_pkt_addr': 'o_rd_addr',
            'm2s_pkt_ctrl': 'o_rd_ctrl',
            'm2s_pkt_data': 'o_rd_data'
        }

        # For fifo_mux mode, we also need to map to ow_rd_* signals
        if self.config.mode == 'fifo_mux':
            slave_optional_map['m2s_pkt_addr'] = 'ow_rd_addr'
            slave_optional_map['m2s_pkt_ctrl'] = 'ow_rd_ctrl'
            slave_optional_map['m2s_pkt_data'] = 'ow_rd_data'

        # Create BFM components with signal maps
        self.write_master = GAXIMaster(
            self.dut, 'write_master', '', self.wr_clk,
            field_config=self.field_config,
            randomizer=self.write_randomizer,
            timeout_cycles=self.config.timeout_cycles,
            signal_map=master_signal_map,
            optional_signal_map=master_optional_map,
            log=self.log,
            multi_sig=True
        )

        self.read_slave = GAXISlave(
            self.dut, 'read_slave', '', self.rd_clk,  # Note the rd_clk
            mode=self.config.mode,
            field_config=self.field_config,
            randomizer=self.read_randomizer,
            timeout_cycles=self.config.timeout_cycles,
            signal_map=slave_signal_map,
            optional_signal_map=slave_optional_map,
            log=self.log,
            multi_sig=True
        )

        self.wr_monitor = GAXIMonitor(
            self.dut, 'Write monitor', '', self.wr_clk,
            field_config=self.field_config,
            is_slave=False,
            signal_map=master_signal_map,
            optional_signal_map=master_optional_map,
            log=self.log,
            multi_sig=True
        )

        self.rd_monitor = GAXIMonitor(
            self.dut, 'Read monitor', '', self.rd_clk,  # Note the rd_clk
            mode=self.config.mode,
            field_config=self.field_config,
            is_slave=True,
            signal_map=slave_signal_map,
            optional_signal_map=slave_optional_map,
            log=self.log,
            multi_sig=True
        )

    # Run a comprehensive test suite for the current buffer
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
        if self.field_mode == 'multi':
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
