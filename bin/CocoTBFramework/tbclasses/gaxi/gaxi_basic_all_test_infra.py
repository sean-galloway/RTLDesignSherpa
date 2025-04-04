"""Infrastructure and base methods for GAXI testbenches"""
import importlib.util
import logging
import random

from CocoTBFramework.tbclasses.tbbase import TBBase
from CocoTBFramework.components.flex_randomizer import FlexRandomizer
from CocoTBFramework.components.field_config import FieldConfig
from CocoTBFramework.components.gaxi.gaxi_sequence import GAXISequence
from CocoTBFramework.scoreboards.gaxi_scoreboard import GAXIScoreboard

# Import specialized GAXI test sequences if available
try:
    from .gaxi_basic_all_test_seq import GAXITestSequences
except ImportError:
    # Define a placeholder class if the specialized sequences are not available
    class GAXITestSequences:
        @staticmethod
        def create_incremental_sequence(*args, **kwargs):
            return GAXISequence.create_address_sweep(*args, **kwargs)

        @staticmethod
        def create_random_sequence(*args, **kwargs):
            return GAXISequence.create_random(*args, **kwargs)

        @staticmethod
        def create_back_to_back_sequence(*args, **kwargs):
            return GAXISequence.create_burst(*args, **kwargs)

        @staticmethod
        def create_burst_pause_sequence(*args, **kwargs):
            return GAXISequence(*args, **kwargs)

        @staticmethod
        def create_full_empty_test_sequence(*args, **kwargs):
            return GAXISequence(*args, **kwargs)


class GAXIBasicTestInfra(TBBase):
    """Infrastructure base class for GAXI testbenches with common methods"""

    def __init__(self, dut, wr_clk=None, wr_rstn=None, rd_clk=None, rd_rstn=None,
                config=None, field_mode='standard', multi_sig=False, 
                is_async=False, gaxi_mode='skid', 
                field_configs=None, randomizer_configs=None):
        """
        Initialize the base GAXI testbench.

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
            field_configs: Dictionary of field configurations (optional)
            randomizer_configs: Dictionary of randomizer configurations (optional)
        """
        super().__init__(dut)

        # Import configuration if provided, otherwise import from config module
        if field_configs is None or randomizer_configs is None:
            from CocoTBFramework.tbclasses.gaxi.gaxi_basic_all_test_config import (
                TestConfig, FIELD_CONFIGS, RANDOMIZER_CONFIGS
            )
            self.FIELD_CONFIGS = field_configs or FIELD_CONFIGS
            self.RANDOMIZER_CONFIGS = randomizer_configs or RANDOMIZER_CONFIGS
        else:
            self.FIELD_CONFIGS = field_configs
            self.RANDOMIZER_CONFIGS = randomizer_configs

        # Store configuration parameters
        self.config = config if config is not None else TestConfig.from_env()
        self.field_mode = field_mode
        self.multi_sig = multi_sig
        self.is_async = is_async
        self.gaxi_mode = gaxi_mode

        # Store clock and reset signals
        self.wr_clk = wr_clk
        self.wr_clk_name = wr_clk.name if wr_clk else None
        self.wr_rstn = wr_rstn
        self.rd_clk = self.wr_clk if rd_clk is None else rd_clk
        self.rd_clk_name = self.wr_clk_name if rd_clk is None else rd_clk.name
        self.rd_rstn = self.wr_rstn if rd_rstn is None else rd_rstn

        # Determine packet and signal configuration
        self.use_multi_field_packets = self.field_mode in ['multi', 'multi_data']
        self.use_multi_signals = self.multi_sig
        self.use_multi_data = self.field_mode == 'multi_data'

        # Create and configure field definitions
        self.field_config = self._create_field_config()

        # Create the scoreboard
        self.scoreboard = GAXIScoreboard(f"{self.__class__.__name__} Scoreboard", self.field_config, self.log)

        # Set up error tracking
        self.total_errors = 0

        # Log configuration
        self._log_config()

        # Initialize randomizers
        self._init_randomizers()

        # Create sequence generator
        self.sequence = GAXISequence("test_sequence", self.field_config)

        # Initialize BFM components - will be set up by derived classes
        self.write_master = None
        self.read_slave = None
        self.wr_monitor = None
        self.rd_monitor = None

    def _log_config(self):
        """Log the test configuration"""
        msg = '\n'
        msg += '='*80 + "\n"
        msg += ' Settings:\n'
        msg += '-'*80 + "\n"
        msg += f' Buffer Type: {self.config.buffer_type}\n'
        msg += f' Field Mode: {self.field_mode}\n'
        if self.config.depth > 0:
            msg += f' Depth:    {self.config.depth}\n'
        if self.config.addr_width > 0:
            msg += f' AddrW:    {self.config.addr_width}\n'
            msg += f' Max Addr: {self.config.max_addr}\n'
        if self.config.ctrl_width > 0:
            msg += f' CtrlW:    {self.config.ctrl_width}\n'
            msg += f' Max Ctrl: {self.config.max_ctrl}\n'
        if self.config.data_width > 0:
            msg += f' DataW:    {self.config.data_width}\n'
            msg += f' Max Data: {self.config.max_data}\n'
        msg += f' MODE:     {self.config.mode}\n'
        msg += f' clk_wr:   {self.config.clk_wr_period}\n'
        msg += f' clk_rd:   {self.config.clk_rd_period}\n'
        if self.is_async:
            msg += f' N_FLOP_CROSS: {self.config.n_flop_cross}\n'
        msg += f' Seed:     {self.config.seed}\n'
        msg += f' Is Async: {self.is_async}\n'
        msg += f' Multi-field packets: {self.use_multi_field_packets}\n'
        msg += f' Multi-signal: {self.use_multi_signals}\n'
        msg += f' Multi-data: {self.use_multi_data}\n'
        msg += '='*80 + "\n"
        self.log.info(msg)

    def _create_field_config(self):
        """Create field configuration based on test parameters"""
        # Use multi-field config for both multi-signal and field modes
        if self.use_multi_data and self.field_mode in ['multi', 'multi_data']:
            config_type = 'multi_data'
        elif self.use_multi_field_packets:
            config_type = 'multi'
        else:
            config_type = 'standard'

        field_config = self.FIELD_CONFIGS.get(config_type, self.FIELD_CONFIGS['standard']).copy()

        # Update field configurations based on bit widths
        if 'data' in field_config:
            field_config['data']['bits'] = self.config.data_width
            field_config['data']['active_bits'] = (self.config.data_width-1, 0)

        if 'addr' in field_config:
            field_config['addr']['bits'] = self.config.addr_width
            field_config['addr']['active_bits'] = (self.config.addr_width-1, 0)

        if 'ctrl' in field_config:
            field_config['ctrl']['bits'] = self.config.ctrl_width
            field_config['ctrl']['active_bits'] = (self.config.ctrl_width-1, 0)

        # Update data0/data1 fields for multi-data configuration
        if 'data0' in field_config:
            field_config['data0']['bits'] = self.config.data_width
            field_config['data0']['active_bits'] = (self.config.data_width-1, 0)

        if 'data1' in field_config:
            field_config['data1']['bits'] = self.config.data_width
            field_config['data1']['active_bits'] = (self.config.data_width-1, 0)

        return FieldConfig.validate_and_create(field_config)

    def _init_randomizers(self):
        """Initialize delay randomizers"""
        # Create initial randomizers - these can be changed during tests
        self.write_randomizer = FlexRandomizer(self.RANDOMIZER_CONFIGS['fast']['write'])
        self.read_randomizer = FlexRandomizer(self.RANDOMIZER_CONFIGS['fast']['read'])

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

    def _get_monitor_counts(self):
        """Get packet counts from monitors"""
        wr_mon_count = len(self.wr_monitor.observed_queue) if hasattr(self.wr_monitor, 'observed_queue') else 0
        rd_mon_count = len(self.rd_monitor.observed_queue) if hasattr(self.rd_monitor, 'observed_queue') else 0
        return wr_mon_count, rd_mon_count

    def generate_alternating_ones(self, width):
        """Generate a value with alternating 1s and 0s."""
        result = 0
        for i in range(0, width, 2):
            result |= (1 << i)
        return result

    def invert_bits(self, value, width):
        """Invert all bits in a value."""
        mask = (1 << width) - 1
        return (~value) & mask

    def compare_results(self, expected_count, msg=''):
        """
        Compare test results against expected count and check for errors.

        Args:
            expected_count: Expected number of transactions
            msg: Message prefix for logs

        Returns:
            Number of errors found
        """
        # Check packet counts
        wr_mon_count, rd_mon_count = self._get_monitor_counts()
        self.log.debug(f'Compare Results for {msg} (expected={expected_count}, write={wr_mon_count}, read={rd_mon_count})')

        # Run scoreboard check
        errors = self.scoreboard.report()

        # Log result
        if errors == 0:
            self.log.debug(f'Compare Results for {msg} PASSED')
        else:
            self.log.error(f'Compare Results for {msg} FAILED with {errors} errors')
            # Update total error count
            self.total_errors += errors

        # Clear scoreboard for next test
        self.scoreboard.clear()

        return errors

    def set_randomizer_mode(self, mode='fast', write_only=False, read_only=False):
        """
        Change the randomizer configuration.

        Args:
            mode: Mode name from RANDOMIZER_CONFIGS
            write_only: Only update write randomizer if True
            read_only: Only update read randomizer if True
        """
        if mode not in self.RANDOMIZER_CONFIGS:
            self.log.error(f"Unknown randomizer mode: {mode}")
            return

        if not read_only:
            self.write_randomizer = FlexRandomizer(self.RANDOMIZER_CONFIGS[mode]['write'])
            if self.write_master:
                self.write_master.set_randomizer(self.write_randomizer)

        if not write_only:
            self.read_randomizer = FlexRandomizer(self.RANDOMIZER_CONFIGS[mode]['read'])
            if self.read_slave:
                self.read_slave.set_randomizer(self.read_randomizer)

    async def clear_interface(self):
        """Clear the interface signals"""
        if self.write_master and self.read_slave:
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
        self.log.info("Reset complete")

    async def reset_sequence(self):
        """Common reset sequence for tests"""
        await self.assert_reset()
        # For async designs, wait on write clock
        await self.wait_clocks(self.wr_clk_name, 10)
        await self.deassert_reset()

        # Additional delay for stable clock domain crossing in async designs
        if self.is_async:
            await self.wait_clocks(self.wr_clk_name, 10)
            await self.wait_clocks(self.rd_clk_name, 10)
        else:
            await self.wait_clocks(self.wr_clk_name, 10)

        # Clear scoreboard after reset
        self.scoreboard.clear()

    async def send_packets(self, packets):
        """
        Send a list of packets and wait for completion.

        Args:
            packets: List of GAXIPacket objects to send
        """
        # Queue all packets
        for packet in packets:
            await self.write_master.send(packet)

        # Wait for all transfers to complete
        while self.write_master.transfer_busy:
            await self.wait_clocks(self.wr_clk_name, 1)

    async def wait_for_packets(self, count, timeout_factor=5):
        """
        Wait until the specified number of packets have been received.

        Args:
            count: Expected number of packets
            timeout_factor: Multiplier for timeout calculation

        Returns:
            True if all packets received, False if timeout occurred
        """
        timeout_cycles = self.config.timeout_cycles * timeout_factor
        cycles_waited = 0

        # Wait for all packets to be received
        while len(self.rd_monitor.observed_queue) < count and cycles_waited < timeout_cycles:
            await self.wait_clocks(self.rd_clk_name, 1)
            cycles_waited += 1

        if cycles_waited >= timeout_cycles:
            self.log.error(f"Timeout waiting for packets! Only received {len(self.rd_monitor.observed_queue)} of {count}")
            return False

        return True
