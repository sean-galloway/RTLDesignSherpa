"""Testbench for AXI-style multi-signal components using sequence generators"""
import os

from CocoTBFramework.tbclasses.tbbase import TBBase
from CocoTBFramework.components.flex_randomizer import FlexRandomizer
from CocoTBFramework.components.field_config import FieldConfig

from CocoTBFramework.components.gaxi.gaxi_packet import GAXIPacket
from CocoTBFramework.components.gaxi.gaxi_master import GAXIMaster
from CocoTBFramework.components.gaxi.gaxi_slave import GAXISlave
from CocoTBFramework.components.gaxi.gaxi_monitor import GAXIMonitor
from CocoTBFramework.tbclasses.gaxi.gaxi_buffer_seq import GAXIBufferSequence
from CocoTBFramework.tbclasses.gaxi.gaxi_buffer_configs import FIELD_CONFIGS, RANDOMIZER_CONFIGS


class GaxiMultiBufferTB(TBBase):
    """Testbench for multi-signal AXI components like axi_fifo_sync_multi and axi_skid_buffer_multi"""

    def __init__(self, dut,
                    wr_clk=None, wr_rstn=None,
                    rd_clk=None, rd_rstn=None):
        super().__init__(dut)

        # Get test parameters from environment
        self.TEST_DEPTH = self.convert_to_int(os.environ.get('TEST_DEPTH', '0'))
        self.TEST_ADDR_WIDTH = self.convert_to_int(os.environ.get('TEST_ADDR_WIDTH', '0'))
        self.TEST_CTRL_WIDTH = self.convert_to_int(os.environ.get('TEST_CTRL_WIDTH', '0'))
        self.TEST_DATA_WIDTH = self.convert_to_int(os.environ.get('TEST_DATA_WIDTH', '0'))
        self.TEST_MODE = os.environ.get('TEST_MODE', 'skid')
        self.TEST_CLK_WR = self.convert_to_int(os.environ.get('TEST_CLK_WR', '10'))
        self.TEST_CLK_RD = self.convert_to_int(os.environ.get('TEST_CLK_RD', '10'))

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
        self.rd_clk = self.wr_clk if rd_clk is None else rd_clk
        self.rd_clk_name = self.wr_clk_name if rd_clk is None else rd_clk.name
        self.rd_rstn = self.wr_rstn if rd_rstn is None else rd_rstn

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
        msg += '='*80 + "\n"
        self.log.info(msg)

        # Define field configuration for multi-signal components
        self.field_config = FieldConfig.from_dict(FIELD_CONFIGS['field'])
        self.field_config.update_field_width('addr', self.AW)
        self.field_config.update_field_width('ctrl', self.CW)
        self.field_config.update_field_width('data0', self.DW)
        self.field_config.update_field_width('data1', self.DW)

        self.log.debug(f"\n{self.field_config}")

        # Set up signal mappings for multi-signal mode
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
            'm2s_pkt_data1': 'o_rd_data1',
        }

        # For fifo_mux mode, we also need to map to ow_rd_* signals
        if self.TEST_MODE == 'fifo_mux':
            slave_optional_map['m2s_pkt_addr'] = 'ow_rd_addr'
            slave_optional_map['m2s_pkt_ctrl'] = 'ow_rd_ctrl'
            slave_optional_map['m2s_pkt_data0'] = 'ow_rd_data0'
            slave_optional_map['m2s_pkt_data1'] = 'ow_rd_data1'

        # Create BFM components - use multi-signal mode with signal maps
        self.write_master = GAXIMaster(
            dut, 'write_master', '', self.wr_clk,
            field_config=self.field_config,
            timeout_cycles=self.TIMEOUT_CYCLES,
            signal_map=master_signal_map,
            optional_signal_map=master_optional_map,
            log=self.log,
            multi_sig=True
        )

        self.read_slave = GAXISlave(
            dut, 'read_slave', '', self.rd_clk,
            mode=self.TEST_MODE,
            field_config=self.field_config,
            timeout_cycles=self.TIMEOUT_CYCLES,
            signal_map=slave_signal_map,
            optional_signal_map=slave_optional_map,
            log=self.log,
            multi_sig=True
        )

        # Set up monitors
        self.wr_monitor = GAXIMonitor(
            dut, 'Write monitor', '', self.wr_clk,
            field_config=self.field_config,
            is_slave=False,
            signal_map=master_signal_map,
            optional_signal_map=master_optional_map,
            log=self.log,
            multi_sig=True
        )

        self.rd_monitor = GAXIMonitor(
            dut, 'Read monitor', '', self.rd_clk,
            mode=self.TEST_MODE,
            field_config=self.field_config,
            is_slave=True,
            signal_map=slave_signal_map,
            optional_signal_map=slave_optional_map,
            log=self.log,
            multi_sig=True
        )

        # Create sequence generators for different test patterns
        self.create_sequences()

    def create_sequences(self):
        """Create sequence generators for different test patterns"""
        # Create basic sequence with incrementing patterns
        self.basic_sequence = GAXIBufferSequence("basic_test", self.field_config)
        self.basic_sequence.add_incrementing_pattern(count=20, delay=0)

        # Create walking ones sequence
        self.walking_ones_sequence = GAXIBufferSequence("walking_ones", self.field_config)
        self.walking_ones_sequence.add_walking_ones_pattern(delay=1)

        # Create alternating patterns sequence
        self.alternating_sequence = GAXIBufferSequence("alternating", self.field_config)
        self.alternating_sequence.add_alternating_patterns(count=2, delay=0)

        # Create random data sequence
        self.random_sequence = GAXIBufferSequence("random_data", self.field_config)
        self.random_sequence.add_random_data_pattern(count=20, delay=1)

        # Create comprehensive test sequence
        self.comprehensive_sequence = GAXIBufferSequence("comprehensive_test", self.field_config)
        self.comprehensive_sequence.add_incrementing_pattern(10, delay=1)
        self.comprehensive_sequence.add_walking_ones_pattern(delay=1)
        self.comprehensive_sequence.add_field_test_pattern(delay=1)
        self.comprehensive_sequence.add_alternating_patterns(1, delay=1)
        self.comprehensive_sequence.add_boundary_values(delay=2)
        self.comprehensive_sequence.add_overflow_test(delay=2)
        self.comprehensive_sequence.add_random_data_pattern(10, delay=1)

        # Create burst test sequence
        self.burst_sequence = GAXIBufferSequence("burst_test", self.field_config)
        self.burst_sequence.add_incrementing_pattern(30, delay=0)
        # Set fast randomizers
        self.burst_sequence.set_master_randomizer(FlexRandomizer({
            'valid_delay': ([[0, 0]], [1]),  # No delay
        }))
        self.burst_sequence.set_slave_randomizer(FlexRandomizer({
            'ready_delay': ([[0, 0]], [1]),  # No delay
        }))

        # Create stress test sequence
        self.stress_sequence = GAXIBufferSequence("stress_test", self.field_config)
        # Add burst of 5 transactions with no delay
        self.stress_sequence.add_incrementing_pattern(5, delay=0)
        # Add transactions with increasing delays
        for i in range(1, 6):
            addr = i * 100
            ctrl = i * 10
            data0 = i * 1000
            data1 = i * 10000
            self.stress_sequence.add_multi_field_transaction(addr, ctrl, data0, data1, delay=i)
        # Add more varied patterns
        self.stress_sequence.add_walking_ones_pattern(delay=0)
        self.stress_sequence.add_random_data_pattern(5, delay=1)
        self.stress_sequence.add_boundary_values(delay=2)
        self.stress_sequence.add_alternating_patterns(1, delay=0)
        self.stress_sequence.add_overflow_test(delay=3)
        # Add final burst with no delay
        self.stress_sequence.add_incrementing_pattern(5, start_value=0xAA, delay=0)

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
        self.log.info("Reset complete")

    def compare_packets(self, msg, expected_count):
        """
        Compare packets captured by monitors.
        Logs any mismatches and updates self.total_errors.
        """
        # Check packet counts
        wr_mon_count = len(self.wr_monitor.observed_queue)
        rd_mon_count = len(self.rd_monitor.observed_queue)

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
        while self.wr_monitor.observed_queue and self.rd_monitor.observed_queue:
            wr_pkt = self.wr_monitor.observed_queue.popleft()
            rd_pkt = self.rd_monitor.observed_queue.popleft()

            # Compare the two packets
            if wr_pkt != rd_pkt:
                self.log.error(
                    f"{msg}: Packet mismatch – WR: {wr_pkt.formatted(compact=True)} "
                    f"vs RD: {rd_pkt.formatted(compact=True)}"
                )
                self.total_errors += 1

        # Log any leftover packets
        while self.wr_monitor.observed_queue:
            pkt = self.wr_monitor.observed_queue.popleft()
            self.log.error(f"{msg}: Unmatched extra packet in WR monitor: {pkt.formatted(compact=True)}")
            self.total_errors += 1

        while self.rd_monitor.observed_queue:
            pkt = self.rd_monitor.observed_queue.popleft()
            self.log.error(f"{msg}: Unmatched extra packet in RD monitor: {pkt.formatted(compact=True)}")
            self.total_errors += 1

    async def run_sequence_test(self, sequence, delay_key='fixed', delay_clks_after=5):
        """
        Run a test with the specified sequence.

        Args:
            sequence: GAXIBufferSequence to use for the test
            delay_key: Key for the randomizer configuration to use
            delay_clks_after: Additional delay clocks after sending all packets
        """
        # Get randomizers
        if sequence.master_randomizer:
            self.write_master.set_randomizer(sequence.master_randomizer)
        else:
            self.write_master.set_randomizer(FlexRandomizer(RANDOMIZER_CONFIGS[delay_key]['write']))

        if sequence.slave_randomizer:
            self.read_slave.set_randomizer(sequence.slave_randomizer)
        else:
            self.read_slave.set_randomizer(FlexRandomizer(RANDOMIZER_CONFIGS[delay_key]['read']))

        # Reset and prepare for test
        await self.assert_reset()
        await self.wait_clocks(self.wr_clk_name, 10)
        await self.deassert_reset()
        await self.wait_clocks(self.wr_clk_name, 10)

        # Generate the packets from the sequence
        packets = sequence.generate_packets()
        count = len(packets)

        self.log.info(f"Running sequence '{sequence.name}' with {count} packets")

        # Send all packets
        for packet in packets:
            await self.write_master.send(packet)

        # Wait for all packets to be transmitted
        while self.write_master.transfer_busy:
            await self.wait_clocks(self.wr_clk_name, 1)

        # Allow time for processing
        await self.wait_clocks(self.wr_clk_name, delay_clks_after*10)

        # Wait for all packets to be received
        timeout_counter = 0
        while len(self.rd_monitor.observed_queue) < count and timeout_counter < self.TIMEOUT_CYCLES:
            await self.wait_clocks(self.wr_clk_name, 1)
            timeout_counter += 1

        if timeout_counter >= self.TIMEOUT_CYCLES:
            self.log.error(f"Timeout waiting for packets! Only received {len(self.rd_monitor.observed_queue)} of {count}")

        # Additional delay for stable results
        await self.wait_clocks(self.wr_clk_name, delay_clks_after)

        # Compare the packets
        self.compare_packets(f"Sequence Test '{sequence.name}'", count)

        # Log results
        if self.total_errors == 0:
            self.log.info(f"Sequence Test '{sequence.name}' PASSED!")
        else:
            self.log.error(f"Sequence Test '{sequence.name}' FAILED with {self.total_errors} errors!")

        # Assert no errors
        assert self.total_errors == 0, f"Sequence Test '{sequence.name}' failed with {self.total_errors} errors"

        # Reset error counter for next test
        self.total_errors = 0

    async def simple_incremental_loops(self, count, delay_key, delay_clks_after):
        """Run simple incremental tests with different packet sizes (legacy method)"""
        # Choose the type of randomizer
        self.log.info(f'simple_incremental_loops({count=}, {delay_key=}, {delay_clks_after=}')
        self.write_master.set_randomizer(FlexRandomizer(RANDOMIZER_CONFIGS[delay_key]['write']))
        self.read_slave.set_randomizer(FlexRandomizer(RANDOMIZER_CONFIGS[delay_key]['read']))

        # Reset and prepare for test
        await self.assert_reset()
        await self.wait_clocks(self.wr_clk_name, 10)
        await self.deassert_reset()
        await self.wait_clocks(self.wr_clk_name, 10)

        # Send packets
        for i in range(count):
            # Create packet
            addr = i & self.MAX_ADDR  # Mask address to avoid overflow
            ctrl = i & self.MAX_CTRL  # Mask control to avoid overflow
            data0 = i & self.MAX_DATA  # Mask data to avoid overflow
            data1 = i*16 & self.MAX_DATA  # Mask data to avoid overflow
            packet = GAXIPacket(self.field_config)
            packet.addr=addr
            packet.ctrl=ctrl
            packet.data0=data0
            packet.data1=data1

            # Queue the packet for transmission
            await self.write_master.send(packet)

        # Wait for all packets to be transmitted
        while self.write_master.transfer_busy:
            await self.wait_clocks(self.wr_clk_name, 1)

        # Read data from the buffer
        await self.wait_clocks(self.wr_clk_name, delay_clks_after*50)

        # Wait for all packets to be received
        timeout_counter = 0
        while len(self.rd_monitor.observed_queue) < count and timeout_counter < self.TIMEOUT_CYCLES:
            await self.wait_clocks(self.wr_clk_name, 1)
            timeout_counter += 1

        if timeout_counter >= self.TIMEOUT_CYCLES:
            self.log.error(f"Timeout waiting for packets! Only received {len(self.rd_monitor.observed_queue)} of {count}")

        # Additional delay for stable results
        await self.wait_clocks(self.wr_clk_name, delay_clks_after)

        # Compare the packets
        self.compare_packets("Simple Incremental Loops", count)

        assert self.total_errors == 0, f'Simple Incremental Loops found {self.total_errors} Errors'
