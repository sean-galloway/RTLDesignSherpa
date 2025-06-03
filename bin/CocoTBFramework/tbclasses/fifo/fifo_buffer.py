"""Testbench for FIFO buffer components with enhanced signal handling and robust error detection"""
import os
import random
import cocotb

from CocoTBFramework.tbclasses.tbbase import TBBase
from CocoTBFramework.components.flex_randomizer import FlexRandomizer
from CocoTBFramework.components.field_config import FieldConfig

from CocoTBFramework.components.fifo.fifo_packet import FIFOPacket
from CocoTBFramework.components.fifo.fifo_master import FIFOMaster
from CocoTBFramework.components.fifo.fifo_slave import FIFOSlave
from CocoTBFramework.components.fifo.fifo_monitor import FIFOMonitor
from CocoTBFramework.components.fifo.fifo_memory_integ import EnhancedMemoryModel
from CocoTBFramework.tbclasses.fifo.fifo_buffer_configs import FIELD_CONFIGS, RANDOMIZER_CONFIGS


class FifoBufferTB(TBBase):
    """Testbench for FIFO buffer components with enhanced error detection and statistics"""

    def __init__(self, dut,
                    wr_clk=None, wr_rstn=None,
                    rd_clk=None, rd_rstn=None):
        super().__init__(dut)

        # Get test parameters from environment
        self.TEST_DEPTH = self.convert_to_int(os.environ.get('TEST_DEPTH', '0'))
        self.TEST_DATA_WIDTH = self.convert_to_int(os.environ.get('TEST_DATA_WIDTH', '0'))
        self.TEST_MODE = os.environ.get('TEST_MODE', 'fifo_mux')
        self.TEST_KIND = os.environ.get('TEST_KIND', 'sync')
        self.TEST_CLK_WR = self.convert_to_int(os.environ.get('TEST_CLK_WR', '10'))
        self.TEST_CLK_RD = self.convert_to_int(os.environ.get('TEST_CLK_RD', '10'))

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

        # Define field configuration
        self.field_config = FieldConfig.from_dict(FIELD_CONFIGS['standard'])
        self.field_config.update_field_width('data', self.DW)

        self.log.debug(f"\n{self.field_config}")

        # Create enhanced memory model
        # self.memory_model = EnhancedMemoryModel(
        #     num_lines=self.TEST_DEPTH,
        #     bytes_per_line=self.DW // 8 or 1,
        #     log=self.log
        # )

        # Set up signal mappings
        # Required signals (valid/ready) for master
        master_signal_map = {
            'm2s_valid': 'i_wr_valid',
            's2m_ready': 'o_wr_ready'
        }

        # Optional signals (data fields) for master
        master_optional_map = {
            'm2s_pkt_data': 'i_wr_data'
        }

        # Required signals (valid/ready) for slave
        slave_signal_map = {
            'm2s_valid': 'o_rd_valid',
            's2m_ready': 'i_rd_ready'
        }

        # Optional signals (data fields) for slave
        slave_optional_map = {
            'm2s_pkt_data': 'o_rd_data'
        }

        # Create BFM components
        self.write_master = FIFOMaster(
            dut, 'write_master', '', self.wr_clk,
            field_config=self.field_config,
            # memory_model=self.memory_model,
            timeout_cycles=self.TIMEOUT_CYCLES,
            signal_map=master_signal_map,
            optional_signal_map=master_optional_map,
            log=self.log
        )

        self.read_slave = FIFOSlave(
            dut, 'read_slave', '', self.rd_clk,
            mode=self.TEST_MODE,
            field_config=self.field_config,
            # memory_model=self.memory_model,
            timeout_cycles=self.TIMEOUT_CYCLES,
            signal_map=slave_signal_map,
            optional_signal_map=slave_optional_map,
            log=self.log
        )

        # Set up monitors
        self.wr_monitor = FIFOMonitor(
            dut, 'Write monitor', '', self.wr_clk,
            field_config=self.field_config,
            is_slave=False,
            signal_map=master_signal_map,
            optional_signal_map=master_optional_map,
            log=self.log
        )

        self.rd_monitor = FIFOMonitor(
            dut, 'Read monitor', '', self.rd_clk,
            mode=self.TEST_MODE,
            field_config=self.field_config,
            is_slave=True,
            signal_map=slave_signal_map,
            optional_signal_map=slave_optional_map,
            log=self.log
        )

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

    def get_component_statistics(self):
        """Get statistics from all components for analysis"""
        stats = {
            'write_master': self.write_master.get_stats(),
            'read_slave': self.read_slave.get_stats() if hasattr(self.read_slave, 'get_stats') else {},
            'write_monitor': self.wr_monitor.get_stats() if hasattr(self.wr_monitor, 'get_stats') else {},
            'read_monitor': self.rd_monitor.get_stats() if hasattr(self.rd_monitor, 'get_stats') else {},
            # 'memory_model': self.memory_model.get_stats() if hasattr(self.memory_model, 'get_stats') else {}
        }
        return stats

    async def simple_incremental_loops(self, count, delay_key, delay_clks_after):
        """Run simple incremental tests with different packet sizes"""
        # Choose the type of randomizer
        self.log.info('='*80)
        self.log.info(f'simple_incremental_loops({count=}, {delay_key=}, {delay_clks_after=}{self.get_time_ns_str()}')
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
            data = i & self.MAX_DATA  # Mask data to avoid overflow
            packet = FIFOPacket(self.field_config)
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
        while len(self.rd_monitor.observed_queue) < count and timeout_counter < self.TIMEOUT_CYCLES:
            await self.wait_clocks(self.wr_clk_name, 1)
            timeout_counter += 1

        if timeout_counter >= self.TIMEOUT_CYCLES:
            self.log.error(f"Timeout waiting for packets! Only received {len(self.rd_monitor.observed_queue)} of {count}{self.get_time_ns_str()}")

        # Additional delay for stable results
        await self.wait_clocks(self.wr_clk_name, delay_clks_after)

        # Compare the packets
        self.compare_packets("Simple Incremental Loops", count)

        # Print statistics
        stats = self.get_component_statistics()
        self.log.info(f"Test Statistics: {stats}")

        assert self.total_errors == 0, f'Simple Incremental Loops found {self.total_errors} Errors{self.get_time_ns_str()}'

    async def stress_test_with_random_patterns(self, count=100, delay_key='constrained'):
        """Run a stress test with more complex patterns to test FIFO buffering"""
        self.log.info('='*80)
        self.log.info(f'Running stress test with {count} packets and delay profile {delay_key}{self.get_time_ns_str()}')

        # Set randomizers for both components
        self.write_master.set_randomizer(FlexRandomizer(RANDOMIZER_CONFIGS[delay_key]['write']))
        self.read_slave.set_randomizer(FlexRandomizer(RANDOMIZER_CONFIGS[delay_key]['read']))

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
            packet = FIFOPacket(self.field_config)
            packet.data = pattern

            # Queue the packet for transmission
            await self.write_master.send(packet)

            # Add occasional delay to prevent overwhelming the FIFO
            if i % 10 == 9:
                await self.wait_clocks(self.wr_clk_name, 5)

        # Wait for all packets to be transmitted
        while self.write_master.transfer_busy:
            await self.wait_clocks(self.wr_clk_name, 1)

        # Allow time for all packets to be received
        await self.wait_clocks(self.wr_clk_name, 50)

        # Wait for all packets to be received
        timeout_counter = 0
        while len(self.rd_monitor.observed_queue) < len(patterns) and timeout_counter < self.TIMEOUT_CYCLES:
            await self.wait_clocks(self.wr_clk_name, 1)
            timeout_counter += 1

        if timeout_counter >= self.TIMEOUT_CYCLES:
            self.log.error(f"Timeout waiting for packets! Only received {len(self.rd_monitor.observed_queue)} of {len(patterns)}{self.get_time_ns_str()}")

        # Compare the packets
        self.compare_packets("Stress Test With Random Patterns", len(patterns))

        # Get and report statistics
        stats = self.get_component_statistics()
        self.log.info(f"Stress Test Statistics: {stats}")

        # Return test result
        return self.total_errors == 0
