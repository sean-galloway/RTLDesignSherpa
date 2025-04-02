"""Unified GAXI Buffer Testbench for all buffer types including async designs"""
import os
from CocoTBFramework.components.gaxi.gaxi_components import GAXIMaster, GAXISlave, GAXIMonitor
from CocoTBFramework.scoreboards.gaxi_scoreboard import GAXIScoreboard
from CocoTBFramework.tbclasses.gaxi.gaxi_basic_all_test_config import TestConfig, get_field_mode, get_is_async
from CocoTBFramework.tbclasses.gaxi.gaxi_basic_all_test import GAXIBasicTestBase


class GaxiBasicBufferAllTB(GAXIBasicTestBase):
    """
    Universal testbench for AXI buffers that supports:
    1. Standard mode (single data field)
    2. Multi-signal mode (separate addr/ctrl/data signals)
    3. Field mode (combined field structure with flexible field configuration)
    4. Asynchronous buffers (separate read/write clocks)
    5. Multi-data mode (data0/data1 fields)
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

        # Get DUT name from environment
        dut_name = os.environ.get('DUT', '')

        # Determine configuration flags based on parameters only, not DUT inspection
        is_async = get_is_async(buffer_type, dut_name)

        # Allow field mode for skid buffers - override with explicit field mode for field buffer_type
        if buffer_type == 'field':
            field_mode = 'multi'
        else:
            field_mode = get_field_mode(buffer_type, dut_name)

        # Tell parent class about is_async for clock handling
        self.is_async = is_async

        # Store configuration information
        self.buffer_type = buffer_type
        self.field_mode = field_mode

        # Log the configuration for debugging
        print(f"Buffer Type: {buffer_type}, Field Mode: {field_mode}, Config Mode: {config.mode}")

        # Call the parent class constructor
        super().__init__(
            dut,
            wr_clk, wr_rstn,
            rd_clk, rd_rstn,
            config,
            field_mode
        )

        # Setup BFM components based purely on configured buffer type
        self._setup_bfm_components()

        # Configure monitor callbacks after BFM components are created
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
        self.log.info(f"  - Field mode: {self.field_mode}")

    def _setup_bfm_components(self):
        """Set up BFM components based on configuration parameters"""
        # Define function naming based on configuration
        clk_type = "async" if self.is_async else "sync"

        # Handle special case: if config.mode is 'field' but buffer_type is 'standard',
        # we need to use the multi-signal setup even though field_mode might be 'standard'
        if self.config.mode == 'field' and self.buffer_type == 'standard':
            sig_type = 'multi'
            self.log.info("Using multi-signal setup for field mode on standard buffer")
        else:
            sig_type = self.field_mode  # 'standard', 'multi', or 'multi_data'

        # Create method name like _setup_async_multi_data_components or _setup_sync_standard_components
        method_name = f"_setup_{clk_type}_{sig_type}_components"

        self.log.info(f"Setting up components using method: {method_name}")

        # Call the appropriate method
        if hasattr(self, method_name):
            setup_method = getattr(self, method_name)
            setup_method()
        elif sig_type == 'multi_data' and hasattr(self, f"_setup_{clk_type}_multi_components"):
            self.log.warning("Using multi signal method for multi_data buffer type")
            getattr(self, f"_setup_{clk_type}_multi_components")()
        else:
            self.log.error(f"Missing setup method: {method_name}")
            raise NotImplementedError(f"Buffer configuration not supported: {clk_type}_{sig_type}")

    def _setup_sync_standard_components(self):
        """Set up BFM components for synchronous buffer with standard interfaces"""
        self.log.info("Setting up synchronous standard components")

        # Check if we're in field mode for a standard buffer
        if self.config.mode == 'field' and self.buffer_type == 'standard':
            self.log.info("Using multi-signal setup for field mode on standard buffer")
            return self._setup_sync_multi_components()

        # Standard mode (single data signal)
        self.write_master = GAXIMaster(
            self.dut, 'write_master', '', self.wr_clk,
            field_config=self.field_config,
            randomizer=self.write_randomizer,
            timeout_cycles=self.config.timeout_cycles,
            signal_map=None,  # Explicitly specify standard mode
            log=self.log,
            multi_sig=False
        )

        self.read_slave = GAXISlave(
            self.dut, 'read_slave', '', self.rd_clk,
            mode=self.config.mode,
            field_config=self.field_config,
            randomizer=self.read_randomizer,
            timeout_cycles=self.config.timeout_cycles,
            signal_map=None,  # Explicitly specify standard mode
            log=self.log,
            multi_sig=False
        )

        self.wr_monitor = GAXIMonitor(
            self.dut, 'Write monitor', '', self.wr_clk,
            field_config=self.field_config,
            is_slave=False,
            signal_map=None,  # Explicitly specify standard mode
            log=self.log,
            multi_sig=False
        )

        self.rd_monitor = GAXIMonitor(
            self.dut, 'Read monitor', '', self.rd_clk,
            mode=self.config.mode,
            field_config=self.field_config,
            is_slave=True,
            signal_map=None,  # Explicitly specify standard mode
            log=self.log,
            multi_sig=False
        )

    def _setup_sync_multi_components(self):
        # sourcery skip: class-extract-method
        """Set up BFM components for synchronous buffer with multi-signal interfaces"""
        self.log.info("Setting up synchronous multi-signal components")

        # Determine if we're using a standard buffer in field mode
        using_standard_in_field_mode = self.config.mode == 'field' and self.buffer_type == 'standard'

        if using_standard_in_field_mode:
            self.log.info("Configuring standard buffer for field mode operation")

        # Define signal mappings for multi-signal mode
        # Required signals (valid/ready) for master
        master_signal_map = {
            'm2s_valid': 'i_wr_valid',
            's2m_ready': 'o_wr_ready'
        }

        # Optional signals (data fields) for master
        # For standard buffer in field mode, we assume the data field can carry the combined fields
        master_optional_map = {
            'm2s_pkt_addr': 'i_wr_data' if using_standard_in_field_mode else 'i_wr_addr',
            'm2s_pkt_ctrl': 'i_wr_data' if using_standard_in_field_mode else 'i_wr_ctrl',
            'm2s_pkt_data': 'i_wr_data'
        }

        # Required signals (valid/ready) for slave
        slave_signal_map = {
            'm2s_valid': 'o_rd_valid',
            's2m_ready': 'i_rd_ready'
        }

        # Optional signals (data fields) for slave
        slave_optional_map = {
            'm2s_pkt_addr': 'o_rd_data' if using_standard_in_field_mode else 'o_rd_addr',
            'm2s_pkt_ctrl': 'o_rd_data' if using_standard_in_field_mode else 'o_rd_ctrl',
            'm2s_pkt_data': 'o_rd_data'
        }

        # For fifo_mux mode, we also need to map to ow_rd_* signals
        if self.config.mode == 'fifo_mux':
            if not using_standard_in_field_mode:
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

    def _setup_sync_multi_data_components(self):
        """Set up BFM components for synchronous buffer with multi-data interfaces"""
        self.log.info("Setting up synchronous multi-data components")

        # Define signal mappings for multi-data mode
        # Required signals (valid/ready) for master
        master_signal_map = {
            'm2s_valid': 'i_wr_valid',
            's2m_ready': 'o_wr_ready'
        }

        # Optional signals (data fields) for master
        master_optional_map = {
            'm2s_pkt_addr': 'i_wr_addr',
            'm2s_pkt_ctrl': 'i_wr_ctrl',
            'm2s_pkt_data0': 'i_wr_data0',
            'm2s_pkt_data1': 'i_wr_data1'
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
            'm2s_pkt_data0': 'o_rd_data0',
            'm2s_pkt_data1': 'o_rd_data1'
        }

        # For fifo_mux mode, we also need to map to ow_rd_* signals
        if self.config.mode == 'fifo_mux':
            slave_optional_map['m2s_pkt_addr'] = 'ow_rd_addr'
            slave_optional_map['m2s_pkt_ctrl'] = 'ow_rd_ctrl'
            slave_optional_map['m2s_pkt_data0'] = 'ow_rd_data0'
            slave_optional_map['m2s_pkt_data1'] = 'ow_rd_data1'

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

        # Check if we're in field mode for a standard buffer
        if self.config.mode == 'field' and self.buffer_type == 'standard':
            self.log.info("Using multi-signal setup for field mode on standard buffer")
            return self._setup_async_multi_components()

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

        # Determine if we're using a standard buffer in field mode
        using_standard_in_field_mode = self.config.mode == 'field' and self.buffer_type == 'standard'

        if using_standard_in_field_mode:
            self.log.info("Configuring standard buffer for field mode operation")

        # Signal maps for the multi-signal async buffer
        master_signal_map = {
            'm2s_valid': 'i_wr_valid',
            's2m_ready': 'o_wr_ready'
        }

        # Optional signals (data fields) for master
        master_optional_map = {
            'm2s_pkt_addr': 'i_wr_addr' if not using_standard_in_field_mode else 'i_wr_data',
            'm2s_pkt_ctrl': 'i_wr_ctrl' if not using_standard_in_field_mode else 'i_wr_data',
            'm2s_pkt_data': 'i_wr_data'
        }

        # Required signals (valid/ready) for slave
        slave_signal_map = {
            'm2s_valid': 'o_rd_valid',
            's2m_ready': 'i_rd_ready'
        }

        # Optional signals (data fields) for slave
        slave_optional_map = {
            'm2s_pkt_addr': 'o_rd_addr' if not using_standard_in_field_mode else 'o_rd_data',
            'm2s_pkt_ctrl': 'o_rd_ctrl' if not using_standard_in_field_mode else 'o_rd_data',
            'm2s_pkt_data': 'o_rd_data'
        }

        # For fifo_mux mode, we also need to map to ow_rd_* signals
        if self.config.mode == 'fifo_mux':
            if not using_standard_in_field_mode:
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

    def _setup_async_multi_data_components(self):
        """Set up BFM components for asynchronous buffer with multi-data interfaces"""
        self.log.info("Setting up asynchronous multi-data components")

        # Signal maps for the multi-data async buffer
        master_signal_map = {
            'm2s_valid': 'i_wr_valid',
            's2m_ready': 'o_wr_ready'
        }

        # Optional signals (data fields) for master
        master_optional_map = {
            'm2s_pkt_addr': 'i_wr_addr',
            'm2s_pkt_ctrl': 'i_wr_ctrl',
            'm2s_pkt_data0': 'i_wr_data0',
            'm2s_pkt_data1': 'i_wr_data1'
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
            'm2s_pkt_data0': 'o_rd_data0',
            'm2s_pkt_data1': 'o_rd_data1'
        }

        # For fifo_mux mode, we also need to map to ow_rd_* signals
        if self.config.mode == 'fifo_mux':
            slave_optional_map['m2s_pkt_addr'] = 'ow_rd_addr'
            slave_optional_map['m2s_pkt_ctrl'] = 'ow_rd_ctrl'
            slave_optional_map['m2s_pkt_data0'] = 'ow_rd_data0'
            slave_optional_map['m2s_pkt_data1'] = 'ow_rd_data1'

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
