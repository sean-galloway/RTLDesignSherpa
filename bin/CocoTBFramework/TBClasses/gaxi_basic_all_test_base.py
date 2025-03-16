"""Enhanced base class for GAXI testbenches with common functionality for all buffer types"""
import os
from dataclasses import dataclass, field
from collections import deque
import random

from CocoTBFramework.TBClasses.tbbase import TBBase
from CocoTBFramework.Components.flex_randomizer import FlexRandomizer
from CocoTBFramework.Components.gaxi.gaxi_packet import GAXIPacket


@dataclass
class TestConfig:
    """Configuration parameters for GAXI testbenches"""
    # Core test parameters
    depth: int = 0
    addr_width: int = 0
    ctrl_width: int = 0
    data_width: int = 0
    mode: str = 'skid'
    buffer_type: str = 'standard'  # 'standard', 'multi', 'field', 'async'
    clk_wr_period: int = 10
    clk_rd_period: int = 10
    n_flop_cross: int = 2  # For async buffers

    # Derived limits
    max_addr: int = field(init=False, default=0)
    max_ctrl: int = field(init=False, default=0)
    max_data: int = field(init=False, default=0)

    # Test control
    timeout_cycles: int = 1000
    seed: int = 0

    def __post_init__(self):
        """Calculate derived values after initialization"""
        self.max_addr = (2**self.addr_width)-1 if self.addr_width > 0 else 0
        self.max_ctrl = (2**self.ctrl_width)-1 if self.ctrl_width > 0 else 0
        self.max_data = (2**self.data_width)-1 if self.data_width > 0 else 0

    @classmethod
    def from_env(cls):
        """Create configuration from environment variables"""
        buffer_type = os.environ.get('BUFFER_TYPE', 'standard')
        mode = os.environ.get('TEST_MODE', 'skid')

        # Adjust mode for skid buffer types which only support 'skid' mode
        if buffer_type == 'standard' and 'skid' in os.environ.get('DUT', ''):
            mode = 'skid'

        return cls(
            depth=int(os.environ.get('TEST_DEPTH', '0')),
            addr_width=int(os.environ.get('TEST_ADDR_WIDTH', '0')),
            ctrl_width=int(os.environ.get('TEST_CTRL_WIDTH', '0')),
            data_width=int(os.environ.get('TEST_WIDTH', '0')),
            mode=mode,
            buffer_type=buffer_type,
            clk_wr_period=int(os.environ.get('TEST_CLK_WR', '10')),
            clk_rd_period=int(os.environ.get('TEST_CLK_RD', '10')),
            n_flop_cross=int(os.environ.get('TEST_N_FLOP_CROSS', '2')),
            timeout_cycles=1000,
            seed=int(os.environ.get('SEED', '0'))
        )


class GAXIBasicTestBase(TBBase):
    """Base class for all GAXI testbenches with common functionality"""

    # Field configurations for different test modes
    FIELD_CONFIGS = {
        # Standard mode - single data field
        'standard': {
            'data': {
                'bits': 32,  # Will be updated based on config
                'default': 0,
                'format': 'hex',
                'display_width': 8,
                'active_bits': (31, 0),  # Will be updated based on config
                'description': 'Data value'
            }
        },

        # Multi-signal mode - addr, ctrl, data fields
        'multi': {
            'addr': {
                'bits': 32,  # Will be updated based on config
                'default': 0,
                'format': 'hex',
                'display_width': 2,
                'active_bits': (31, 0),  # Will be updated based on config
                'description': 'Address value'
            },
            'ctrl': {
                'bits': 8,  # Will be updated based on config
                'default': 0,
                'format': 'hex',
                'display_width': 2,
                'active_bits': (7, 0),  # Will be updated based on config
                'description': 'Control value'
            },
            'data': {
                'bits': 32,  # Will be updated based on config
                'default': 0,
                'format': 'hex',
                'display_width': 4,
                'active_bits': (31, 0),  # Will be updated based on config
                'description': 'Data value'
            }
        }
    }

    # Randomizer configurations
    RANDOMIZER_CONFIGS = {
        'constrained': {
            'write': {
                'valid_delay': ([[0, 0], [1, 8], [9, 20]], [5, 2, 1])
            },
            'read': {
                'ready_delay': ([[0, 1], [2, 8], [9, 30]], [5, 2, 1])
            }
        },
        'fast': {
            'write': {
                'valid_delay': ([[0, 0], [1, 8], [9, 20]], [5, 0, 0])
            },
            'read': {
                'ready_delay': ([[0, 0], [1, 8], [9, 30]], [5, 0, 0])
            }
        },
        'backtoback': {
            'write': {
                'valid_delay': ([[0, 0]], [1])
            },
            'read': {
                'ready_delay': ([[0, 0]], [1])
            }
        },
        'burst_pause': {
            'write': {
                'valid_delay': ([[0, 0], [15, 25]], [10, 1])
            },
            'read': {
                'ready_delay': ([[0, 0], [1, 5]], [10, 1])
            }
        },
        'slow_consumer': {
            'write': {
                'valid_delay': ([[0, 0]], [1])
            },
            'read': {
                'ready_delay': ([[10, 20]], [1])
            }
        },
        'slow_producer': {
            'write': {
                'valid_delay': ([[10, 20]], [1])
            },
            'read': {
                'ready_delay': ([[0, 0]], [1])
            }
        }
    }

    def __init__(self, dut,
                wr_clk=None, wr_rstn=None,
                rd_clk=None, rd_rstn=None,
                config=None,
                field_mode='standard'):
        """
        Initialize the base GAXI testbench.

        Args:
            dut: Device under test
            wr_clk: Write clock signal
            wr_rstn: Write reset signal (active low)
            rd_clk: Read clock signal (defaults to wr_clk if None)
            rd_rstn: Read reset signal (defaults to wr_rstn if None)
            config: TestConfig object (created from environment if None)
            field_mode: Field configuration mode ('standard' or 'multi')
        """
        super().__init__(dut)

        # Load or create configuration
        self.config = config if config is not None else TestConfig.from_env()

        # Set random seed
        random.seed(self.config.seed)
        self.log.info(f'Using random seed: {self.config.seed}')

        # Store clock and reset signals
        self.wr_clk = wr_clk
        self.wr_clk_name = wr_clk.name if wr_clk else None
        self.wr_rstn = wr_rstn
        self.rd_clk = self.wr_clk if rd_clk is None else rd_clk
        self.rd_clk_name = self.wr_clk_name if rd_clk is None else rd_clk.name
        self.rd_rstn = self.wr_rstn if rd_rstn is None else rd_rstn

        # Is this an async buffer?
        self.is_async = (self.rd_clk != self.wr_clk) or ('async' in self.config.buffer_type)

        # Determine packet and signal configuration
        self.use_multi_field_packets = hasattr(self, 'use_multi_field_packets') and self.use_multi_field_packets
        self.use_multi_signals = hasattr(self, 'use_multi_signals') and self.use_multi_signals

        if not hasattr(self, 'use_multi_field_packets'):
            # If not already set by derived class
            self.use_multi_field_packets = self.config.buffer_type in ['multi', 'field']

        if not hasattr(self, 'use_multi_signals'):
            # If not already set by derived class
            self.use_multi_signals = self.config.buffer_type == 'multi'

        # Create and configure field definitions
        self.field_mode = field_mode
        self.field_config = self._create_field_config()

        # Set up error tracking
        self.total_errors = 0

        # Log configuration
        self._log_config()

        # Initialize randomizers
        self._init_randomizers()

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
        msg += '='*80 + "\n"
        self.log.info(msg)

    def _create_field_config(self):
        """Create field configuration based on test parameters"""
        # Use multi-field config for both multi-signal and field modes
        config_type = 'multi' if self.use_multi_field_packets else 'standard'
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

        return field_config

    def _init_randomizers(self):
        """Initialize delay randomizers"""
        # Create initial randomizers - these can be changed during tests
        self.write_randomizer = FlexRandomizer(self.RANDOMIZER_CONFIGS['fast']['write'])
        self.read_randomizer = FlexRandomizer(self.RANDOMIZER_CONFIGS['fast']['read'])

    def _wr_monitor_callback(self, transaction):
        """Callback for write monitor"""
        self.log.debug(f"Write monitor captured: {transaction.formatted(compact=True)}")

    def _rd_monitor_callback(self, transaction):
        """Callback for read monitor"""
        self.log.debug(f"Read monitor captured: {transaction.formatted(compact=True)}")

    def compare_results(self, expected_count, msg=''):
        """
        Compare test results against expected count and check for errors.

        Args:
            expected_count: Expected number of transactions

        Returns:
            Number of errors found
        """
        # Use compare_packets for all comparisons
        self.log.debug(f'Compare Results for {msg}')
        errors = self.compare_packets(f"Test Results for {msg}", expected_count)
        if errors == 0:
            self.log.debug(f'Compare Results for {msg} PASSED')
        else:
            self.log.debug(f'Compare Results for {msg} FAILED with {errors} errors')
        return errors

    def _get_monitor_counts(self):
        wr_mon_count = len(self.wr_monitor.observed_queue) if hasattr(self.wr_monitor, 'observed_queue') else 0
        rd_mon_count = len(self.rd_monitor.observed_queue) if hasattr(self.rd_monitor, 'observed_queue') else 0
        return wr_mon_count, rd_mon_count

    def compare_packets(self, msg, expected_count):
        """
        Method for comparing packets captured by monitors.

        Args:
            msg: Message prefix for logs
            expected_count: Expected number of transactions

        Returns:
            Number of errors found
        """
        # Check packet counts
        # wr_mon_count = len(self.wr_monitor.observed_queue) if hasattr(self.wr_monitor, 'observed_queue') else 0
        # rd_mon_count = len(self.rd_monitor.observed_queue) if hasattr(self.rd_monitor, 'observed_queue') else 0
        wr_mon_count, rd_mon_count = self._get_monitor_counts()
        errors = 0
        self.log.debug(f'Compare Packets for {msg} {expected_count=} {wr_mon_count=} {rd_mon_count=}')

        # Store references to queues for safety
        wr_queue = None
        rd_queue = None

        if hasattr(self.wr_monitor, 'observed_queue'):
            # Make a copy of the queue to avoid modifying the original
            wr_queue = self.wr_monitor.observed_queue

        if hasattr(self.rd_monitor, 'observed_queue'):
            # Make a copy of the queue to avoid modifying the original
            rd_queue = self.rd_monitor.observed_queue

        if wr_mon_count != rd_mon_count:
            self.log.error(
                f"{msg}: Packet count mismatch: "
                f"{wr_mon_count} sent vs "
                f"{rd_mon_count} received"
            )
            errors += 1
            self.total_errors += 1

        if expected_count != wr_mon_count:
            self.log.error(
                f"{msg}: Packet count mismatch on Write Monitor: "
                f"{wr_mon_count} sent vs "
                f"{expected_count} expected"
            )
            errors += 1
            self.total_errors += 1

        if expected_count != rd_mon_count:
            self.log.error(
                f"{msg}: Packet count mismatch on Read Monitor: "
                f"{rd_mon_count} received vs "
                f"{expected_count} expected"
            )
            errors += 1
            self.total_errors += 1

        # Compare packets if we have both queues
        if wr_queue and rd_queue:
            # Compare as many packets as we can
            while wr_queue and rd_queue:
                wr_pkt = wr_queue.popleft()
                rd_pkt = rd_queue.popleft()

                # Compare the two packets
                if wr_pkt != rd_pkt:
                    self.log.error(
                        f"{msg}: Packet mismatch – WR: {wr_pkt.formatted(compact=True)} "
                        f"vs RD: {rd_pkt.formatted(compact=True)}"
                    )
                    errors += 1
                    self.total_errors += 1

            # Log any leftover packets
            while wr_queue:
                pkt = wr_queue.popleft()
                self.log.error(f"{msg}: Unmatched extra packet in WR monitor: {pkt.formatted(compact=True)}")
                errors += 1
                self.total_errors += 1

            while rd_queue:
                pkt = rd_queue.popleft()
                self.log.error(f"{msg}: Unmatched extra packet in RD monitor: {pkt.formatted(compact=True)}")
                errors += 1
                self.total_errors += 1
        elif not wr_queue and not rd_queue:
            self.log.warning(f"{msg}: Both monitor queues unavailable, skipping packet comparison")
        elif not wr_queue:
            self.log.warning(f"{msg}: Write monitor queue unavailable, skipping packet comparison")
        else:
            self.log.warning(f"{msg}: Read monitor queue unavailable, skipping packet comparison")

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

    # Base test methods that can be overridden or used directly
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

        # Create and send packets
        for i in range(count):
            # Create packet based on field configuration
            if self.use_multi_field_packets:
                # Multi-field packet (for both multi-signal and field modes)
                addr = i & self.config.max_addr
                ctrl = i & self.config.max_ctrl
                data = i & self.config.max_data
                packet = GAXIPacket(self.field_config, addr=addr, ctrl=ctrl, data=data)
            else:
                # Standard single-field packet
                data = i & self.config.max_data
                packet = GAXIPacket(self.field_config, data=data)

            # Queue the packet for transmission
            await self.write_master.send(packet)

        # Wait for all packets to be transmitted
        while self.write_master.transfer_busy:
            await self.wait_clocks(self.wr_clk_name, 1)

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

        # Create and send packets with random values
        for _ in range(count):
            if self.use_multi_field_packets:
                # Multi-field packet with random values
                addr = random.randint(0, self.config.max_addr)
                ctrl = random.randint(0, self.config.max_ctrl)
                data = random.randint(0, self.config.max_data)
                packet = GAXIPacket(self.field_config, addr=addr, ctrl=ctrl, data=data)
            else:
                # Standard packet with random value
                data = random.randint(0, self.config.max_data)
                packet = GAXIPacket(self.field_config, data=data)

            # Queue the packet for transmission
            await self.write_master.send(packet)

        # Wait for all packets to be transmitted
        while self.write_master.transfer_busy:
            await self.wait_clocks(self.wr_clk_name, 1)

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

        # Create and send packets with increasing values
        for i in range(count):
            if self.use_multi_field_packets:
                # Multi-field packet
                addr = i & self.config.max_addr
                ctrl = i & self.config.max_ctrl
                data = i & self.config.max_data
                packet = GAXIPacket(self.field_config, addr=addr, ctrl=ctrl, data=data)
            else:
                # Standard packet
                data = i & self.config.max_data
                packet = GAXIPacket(self.field_config, data=data)

            # Queue the packet for transmission
            await self.write_master.send(packet)

        # Wait for all packets to be transmitted
        while self.write_master.transfer_busy:
            await self.wait_clocks(self.wr_clk_name, 1)

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

        packet_count = 0
        for burst in range(num_bursts):
            # Use burst_pause mode for burst traffic pattern
            self.set_randomizer_mode('burst_pause')
            self.log.info(f"Starting burst {burst+1} of {num_bursts}")

            # Send a burst of packets
            for _ in range(burst_size):
                if self.use_multi_field_packets:
                    # Multi-field packet
                    addr = packet_count & self.config.max_addr
                    ctrl = packet_count & self.config.max_ctrl
                    data = packet_count & self.config.max_data
                    packet = GAXIPacket(self.field_config, addr=addr, ctrl=ctrl, data=data)
                else:
                    # Standard packet
                    data = packet_count & self.config.max_data
                    packet = GAXIPacket(self.field_config, data=data)

                # Queue the packet for transmission
                await self.write_master.send(packet)
                packet_count += 1

            # Wait for burst to complete
            while self.write_master.transfer_busy:
                await self.wait_clocks(self.wr_clk_name, 1)

            # Wait between bursts (only if not the last burst)
            if burst < num_bursts - 1:
                await self.wait_clocks(self.wr_clk_name, 20)

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

        # Number of packets to send (using buffer depth + extra to ensure fullness)
        count = self.config.depth * 2

        # Step 1: Fast producer, slow consumer to create full condition
        self.log.info("Testing buffer full condition - fast producer, slow consumer")
        self.set_randomizer_mode('fast', write_only=True)
        self.set_randomizer_mode('slow_consumer', read_only=True)

        # Reset and prepare for test
        await self.reset_sequence()

        # Send packets to fill the buffer
        sent_packets = []
        for i in range(count):
            if self.use_multi_field_packets:
                packet = GAXIPacket(self.field_config,
                                    addr=i & self.config.max_addr,
                                    ctrl=i & self.config.max_ctrl,
                                    data=i & self.config.max_data)
            else:
                packet = GAXIPacket(self.field_config, data=i & self.config.max_data)

            sent_packets.append(packet)
            await self.write_master.send(packet)

        # Wait for all packets to be transmitted (this should experience backpressure)
        while self.write_master.transfer_busy:
            await self.wait_clocks(self.wr_clk_name, 1)

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

        # Reset monitors and error count for empty test
        if hasattr(self.wr_monitor, 'observed_queue'):
            self.wr_monitor.observed_queue.clear()
        if hasattr(self.rd_monitor, 'observed_queue'):
            self.rd_monitor.observed_queue.clear()
        self.total_errors = 0

        # Step 2: Slow producer, fast consumer to create empty condition
        self.log.info("Testing buffer empty condition - slow producer, fast consumer")
        self.set_randomizer_mode('slow_producer', write_only=True)
        self.set_randomizer_mode('fast', read_only=True)

        # Reset and prepare for test
        await self.reset_sequence()

        # Send a small number of packets
        count = max(2, self.config.depth // 2)
        for i in range(count):
            if self.use_multi_field_packets:
                packet = GAXIPacket(self.field_config,
                                    addr=i & self.config.max_addr,
                                    ctrl=i & self.config.max_ctrl,
                                    data=i & self.config.max_data)
            else:
                packet = GAXIPacket(self.field_config, data=i & self.config.max_data)

            await self.write_master.send(packet)

        # Wait for all packets to be transmitted
        while self.write_master.transfer_busy:
            await self.wait_clocks(self.wr_clk_name, 1)

        # Allow time for all packets to be received
        if self.is_async:
            adjusted_delay = delay_clks_after * 2 * max(self.config.clk_wr_period, self.config.clk_rd_period) // min(self.config.clk_wr_period, self.config.clk_rd_period)
            await self.wait_clocks(self.rd_clk_name, adjusted_delay)
        else:
            await self.wait_clocks(self.wr_clk_name, delay_clks_after*2)

        # Wait for packets to be received
        await self.wait_for_packets(count)

        # Compare results for empty test
        empty_errors = self.compare_results(count, 'full_empty_test, part 2')

        # Report overall results
        total_errors = full_errors + empty_errors
        assert total_errors == 0, f'Full/Empty Test found {total_errors} errors ({full_errors} in full test, {empty_errors} in empty test)'

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

        # Create packets with different values in each field to test field crossing
        for i in range(count):
            # Use different patterns for each field to ensure they don't accidentally match
            addr = (i * 3) & self.config.max_addr
            ctrl = (i * 5) & self.config.max_ctrl
            data = (i * 7) & self.config.max_data

            packet = GAXIPacket(self.field_config, addr=addr, ctrl=ctrl, data=data)
            await self.write_master.send(packet)

        # Wait for all packets to be transmitted
        while self.write_master.transfer_busy:
            await self.wait_clocks(self.wr_clk_name, 1)

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

        # Create pattern packets with alternating bits
        for i in range(count):
            if i % 4 == 0:
                # All 1s in addr, alternating in ctrl and data
                addr = self.config.max_addr
                ctrl = self.generate_alternating_ones(self.config.ctrl_width)
                data = self.generate_alternating_ones(self.config.data_width)
            elif i % 4 == 1:
                # All 0s in addr, inverted alternating in ctrl and data
                addr = 0
                ctrl = self.invert_bits(self.generate_alternating_ones(self.config.ctrl_width), self.config.ctrl_width)
                data = self.invert_bits(self.generate_alternating_ones(self.config.data_width), self.config.data_width)
            elif i % 4 == 2:
                # Alternating in addr, all 1s in ctrl, all 0s in data
                addr = self.generate_alternating_ones(self.config.addr_width)
                ctrl = self.config.max_ctrl
                data = 0
            else:
                # Inverted alternating in addr, all 0s in ctrl, all 1s in data
                addr = self.invert_bits(self.generate_alternating_ones(self.config.addr_width), self.config.addr_width)
                ctrl = 0
                data = self.config.max_data

            packet = GAXIPacket(self.field_config, addr=addr, ctrl=ctrl, data=data)
            await self.write_master.send(packet)

        # Wait for all packets to be transmitted
        while self.write_master.transfer_busy:
            await self.wait_clocks(self.wr_clk_name, 1)

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

        # List of edge case values to test
        value_patterns = []

        # For standard buffer, test data edge cases
        if not self.use_multi_field_packets:
            value_patterns = [
                # (data value)
                (0),                                                   # All 0s
                (self.config.max_data),                                # All 1s
                (self.generate_alternating_ones(self.config.data_width)),  # Alternating 1/0 starting with 1
                (self.invert_bits(self.generate_alternating_ones(self.config.data_width), self.config.data_width))  # Alternating 0/1 starting with 0
            ]
        else:
            # For multi-field buffers, test combinations of edge cases
            value_patterns = [
                # (addr, ctrl, data)
                (0, 0, 0),                                     # All fields 0
                (self.config.max_addr, self.config.max_ctrl, self.config.max_data),  # All fields 1s

                # Various alternating patterns
                (self.generate_alternating_ones(self.config.addr_width),
                    self.generate_alternating_ones(self.config.ctrl_width),
                    self.generate_alternating_ones(self.config.data_width)),

                # Inverted alternating patterns
                (self.invert_bits(self.generate_alternating_ones(self.config.addr_width), self.config.addr_width),
                    self.invert_bits(self.generate_alternating_ones(self.config.ctrl_width), self.config.ctrl_width),
                    self.invert_bits(self.generate_alternating_ones(self.config.data_width), self.config.data_width)),

                # Mixed patterns
                (0, self.config.max_ctrl, self.generate_alternating_ones(self.config.data_width)),
                (self.config.max_addr, 0, self.invert_bits(self.generate_alternating_ones(self.config.data_width), self.config.data_width))
            ]

        # Send packets with edge case values
        packets_sent = 0
        while packets_sent < count:
            # Choose a pattern based on iteration
            pattern_idx = packets_sent % len(value_patterns)
            pattern = value_patterns[pattern_idx]

            if not self.use_multi_field_packets:
                # Single value pattern for standard buffer
                packet = GAXIPacket(self.field_config, data=pattern)
            else:
                # Multi-value pattern for multi-field buffer
                addr, ctrl, data = pattern
                packet = GAXIPacket(self.field_config, addr=addr, ctrl=ctrl, data=data)

            await self.write_master.send(packet)
            packets_sent += 1

        # Wait for all packets to be transmitted
        while self.write_master.transfer_busy:
            await self.wait_clocks(self.wr_clk_name, 1)

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
        self.compare_results(count, 'edge_value_test')
        assert self.total_errors == 0, f'Edge Value Test found {self.total_errors} Errors'

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

        # Create packets with incrementing values to ensure order is preserved across CDC
        for i in range(count):
            if self.use_multi_field_packets:
                addr = i & self.config.max_addr
                ctrl = i & self.config.max_ctrl
                data = i & self.config.max_data
                packet = GAXIPacket(self.field_config, addr=addr, ctrl=ctrl, data=data)
            else:
                data = i & self.config.max_data
                packet = GAXIPacket(self.field_config, data=data)

            await self.write_master.send(packet)

            # Apply a small delay after each packet to stress CDC logic
            if i % 5 == 0:
                await self.wait_clocks(self.wr_clk_name, 2)

        # Wait for all packets to be transmitted
        while self.write_master.transfer_busy:
            await self.wait_clocks(self.wr_clk_name, 1)

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

            # Create and send packets with incrementing values
            for i in range(count):
                if self.use_multi_field_packets:
                    addr = i & self.config.max_addr
                    ctrl = i & self.config.max_ctrl
                    data = i & self.config.max_data
                    packet = GAXIPacket(self.field_config, addr=addr, ctrl=ctrl, data=data)
                else:
                    data = i & self.config.max_data
                    packet = GAXIPacket(self.field_config, data=data)

                await self.write_master.send(packet)

                # Add a small periodic delay to stress the CDC logic
                if i % 5 == 0:
                    await self.wait_clocks(self.wr_clk_name, 3)

            # Wait for all packets to be transmitted
            while self.write_master.transfer_busy:
                await self.wait_clocks(self.wr_clk_name, 1)

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
