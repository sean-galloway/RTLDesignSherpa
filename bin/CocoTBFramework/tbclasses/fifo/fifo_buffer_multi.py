"""Testbench for FIFO buffer components with multiple signals and enhanced error detection"""
import os
import cocotb

from CocoTBFramework.tbclasses.tbbase import TBBase
from CocoTBFramework.components.flex_randomizer import FlexRandomizer
from CocoTBFramework.components.field_config import FieldConfig

from CocoTBFramework.components.fifo.fifo_packet import FIFOPacket
from CocoTBFramework.components.fifo.fifo_master import FIFOMaster
from CocoTBFramework.components.fifo.fifo_slave import FIFOSlave
from CocoTBFramework.components.fifo.fifo_monitor import FIFOMonitor
from CocoTBFramework.components.fifo.fifo_memory_integ import EnhancedMemoryModel
from CocoTBFramework.components.fifo.fifo_command_handler import FIFOCommandHandler
from CocoTBFramework.tbclasses.fifo.fifo_buffer_configs import FIELD_CONFIGS, RANDOMIZER_CONFIGS


class FifoMultiBufferTB(TBBase):
    """Testbench for multi-signal FIFO components like fifo_sync_multi and fifo_skid_buffer_multi with enhanced error detection"""

    def __init__(self, dut,
                    wr_clk=None, wr_rstn=None,
                    rd_clk=None, rd_rstn=None):
        super().__init__(dut)

        # Get test parameters from environment
        self.TEST_DEPTH = self.convert_to_int(os.environ.get('TEST_DEPTH', '0'))
        self.TEST_ADDR_WIDTH = self.convert_to_int(os.environ.get('TEST_ADDR_WIDTH', '0'))
        self.TEST_CTRL_WIDTH = self.convert_to_int(os.environ.get('TEST_CTRL_WIDTH', '0'))
        self.TEST_DATA_WIDTH = self.convert_to_int(os.environ.get('TEST_DATA_WIDTH', '0'))
        self.TEST_MODE = os.environ.get('TEST_MODE', 'fifo_mux')
        self.TEST_KIND = os.environ.get('TEST_KIND', 'sync')
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
        self.rd_clk = self.wr_clk if self.TEST_KIND == 'sync' else rd_clk
        self.rd_clk_name = self.wr_clk_name if self.TEST_KIND == 'sync' else rd_clk.name
        self.rd_rstn = self.wr_rstn if self.TEST_KIND == 'sync' else rd_rstn

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

        # Create field configuration
        self.field_config = FieldConfig.from_dict(FIELD_CONFIGS['field'])
        self.field_config.update_field_width('addr', self.AW)
        self.field_config.update_field_width('ctrl', self.CW)
        self.field_config.update_field_width('data0', self.DW)
        self.field_config.update_field_width('data1', self.DW)

        self.log.debug(f"\n{self.field_config}")

        # Create enhanced memory model
        self.memory_model = EnhancedMemoryModel(
            num_lines=self.TEST_DEPTH,
            bytes_per_line=(self.AW + self.CW + 2*self.DW) // 8 or 1,
            log=self.log
        )

        # Set up signal mappings for multi-signal mode

        # Optional signals (data fields) for master
        master_optional_map = {
            'i_wr_pkt_addr': 'i_wr_addr',
            'i_wr_pkt_ctrl': 'i_wr_ctrl',
            'i_wr_pkt_data0': 'i_wr_data0',
            'i_wr_pkt_data1': 'i_wr_data1'
        }

        # Optional signals (data fields) for slave
        slave_optional_map = {
            'o_rd_pkt_addr': 'o_rd_addr',
            'o_rd_pkt_ctrl': 'o_rd_ctrl',
            'o_rd_pkt_data0': 'o_rd_data0',
            'o_rd_pkt_data1': 'o_rd_data1',
        }

        # For fifo_mux mode, we also need to map to ow_rd_* signals
        if self.TEST_MODE == 'fifo_mux':
            slave_optional_map['m2s_pkt_addr'] = 'ow_rd_addr'
            slave_optional_map['m2s_pkt_ctrl'] = 'ow_rd_ctrl'
            slave_optional_map['m2s_pkt_data0'] = 'ow_rd_data0'
            slave_optional_map['m2s_pkt_data1'] = 'ow_rd_data1'

        # Create BFM components - use multi-signal mode with signal maps
        self.write_master = FIFOMaster(
            dut, 'write_master', '', self.wr_clk,
            field_config=self.field_config,
            memory_model=self.memory_model,
            timeout_cycles=self.TIMEOUT_CYCLES,
            optional_signal_map=master_optional_map,
            log=self.log,
            multi_sig=True
        )

        self.read_slave = FIFOSlave(
            dut, 'read_slave', '', self.rd_clk,
            mode=self.TEST_MODE,
            field_config=self.field_config,
            memory_model=self.memory_model,
            timeout_cycles=self.TIMEOUT_CYCLES,
            optional_signal_map=slave_optional_map,
            log=self.log,
            multi_sig=True
        )

        # Set up monitors
        self.wr_monitor = FIFOMonitor(
            dut, 'Write monitor', '', self.wr_clk,
            field_config=self.field_config,
            is_slave=False,
            optional_signal_map=master_optional_map,
            log=self.log,
            multi_sig=True
        )

        self.rd_monitor = FIFOMonitor(
            dut, 'Read monitor', '', self.rd_clk,
            mode=self.TEST_MODE,
            field_config=self.field_config,
            is_slave=True,
            optional_signal_map=slave_optional_map,
            log=self.log,
            multi_sig=True
        )

        # Create command handler to coordinate transactions
        self.command_handler = FIFOCommandHandler(
            self.write_master,
            self.read_slave,
            memory_model=self.memory_model,
            log=self.log,
            fifo_capacity=self.TEST_DEPTH
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

                # Provide detailed field comparison for debugging
                all_fields = set(wr_pkt.get_all_field_names()) | set(rd_pkt.get_all_field_names())
                for field in all_fields:
                    wr_val = getattr(wr_pkt, field, None)
                    rd_val = getattr(rd_pkt, field, None)
                    if wr_val != rd_val:
                        self.log.error(f"  Field '{field}' mismatch: write={wr_val}, read={rd_val}")

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
            'memory_model': self.memory_model.get_stats() if hasattr(self.memory_model, 'get_stats') else {},
            'command_handler': self.command_handler.get_stats() if hasattr(self.command_handler, 'get_stats') else {}
        }
        return stats

    async def simple_incremental_loops(self, count, delay_key, delay_clks_after):
        """Run simple incremental tests with different packet sizes"""
        # Choose the type of randomizer
        self.log.info(f'simple_incremental_loops({count=}, {delay_key=}, {delay_clks_after=})')
        self.write_master.set_randomizer(FlexRandomizer(RANDOMIZER_CONFIGS[delay_key]['write']))
        self.read_slave.set_randomizer(FlexRandomizer(RANDOMIZER_CONFIGS[delay_key]['read']))

        # Reset and prepare for test
        await self.assert_reset()
        await self.wait_clocks(self.wr_clk_name, 10)
        await self.deassert_reset()
        await self.wait_clocks(self.wr_clk_name, 10)

        # Start the command handler
        await self.command_handler.start()

        # Send packets
        for i in range(count):
            # Create packet
            addr = i & self.MAX_ADDR  # Mask address to avoid overflow
            ctrl = i & self.MAX_CTRL  # Mask control to avoid overflow
            data0 = i & self.MAX_DATA  # Mask data to avoid overflow
            data1 = (i * 2) & self.MAX_DATA  # Mask data to avoid overflow
            packet = FIFOPacket(self.field_config)
            packet.addr = addr
            packet.ctrl = ctrl
            packet.data0 = data0
            packet.data1 = data1

            # Set FIFO metadata for improved debugging
            packet.set_fifo_metadata(
                depth=min(i, self.TEST_DEPTH),
                capacity=self.TEST_DEPTH
            )

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
            self.log.error(f"Timeout waiting for packets! Only received {len(self.rd_monitor.observed_queue)} of {count}")

        # Additional delay for stable results
        await self.wait_clocks(self.wr_clk_name, delay_clks_after)

        # Stop the command handler
        await self.command_handler.stop()

        # Compare the packets
        self.compare_packets("Simple Incremental Loops", count)

        # Print statistics
        stats = self.get_component_statistics()
        self.log.info(f"Test Statistics: {stats}")

        assert self.total_errors == 0, f'Simple Incremental Loops found {self.total_errors} Errors'

    async def run_sequence_test(self, sequence_type='comprehensive', count=20):
        """Run a test using predefined FIFO sequences"""
        from CocoTBFramework.components.fifo.fifo_sequence import FIFOSequence

        self.log.info(f"Running {sequence_type} sequence test with {count} packets")

        # Reset the environment
        await self.assert_reset()
        await self.wait_clocks(self.wr_clk_name, 10)
        await self.deassert_reset()
        await self.wait_clocks(self.wr_clk_name, 10)

        # Start the command handler
        await self.command_handler.start()

        # Create the appropriate sequence
        if sequence_type == 'comprehensive':
            sequence = FIFOSequence.create_comprehensive_test(
                name="comprehensive_test",
                capacity=self.TEST_DEPTH,
                data_width=self.DW
            )
        elif sequence_type == 'stress':
            sequence = FIFOSequence.create_data_stress_test(
                name="stress_test",
                data_width=self.DW,
                delay=1
            )
        elif sequence_type == 'burst':
            sequence = FIFOSequence.create_burst_sequence(
                name="burst_test",
                count=count // 5,
                burst_size=5,
                pattern_type="increment"
            )
        elif sequence_type == 'capacity':
            sequence = FIFOSequence.create_fifo_capacity_test(
                name="capacity_test",
                capacity=self.TEST_DEPTH
            )
        else:
            self.log.error(f"Unknown sequence type: {sequence_type}")
            return False

        # Set field configuration to match our testbench
        sequence.field_config = self.field_config

        # Generate the packets
        packets = sequence.generate_packets(count=count, apply_fifo_metadata=True)
        self.log.info(f"Generated {len(packets)} packets for sequence test")

        # Process the packets through the command handler
        response_map = await self.command_handler.process_sequence(sequence)

        # Wait for all transactions to complete
        await self.wait_clocks(self.wr_clk_name, 50)

        # Stop the command handler
        await self.command_handler.stop()

        # Compare monitored packets
        self.compare_packets(f"{sequence_type.capitalize()} Sequence Test", len(packets))

        # Get and report statistics
        stats = self.get_component_statistics()
        sequence_stats = sequence.get_stats()
        self.log.info(f"Sequence Test Statistics - Components: {stats}")
        self.log.info(f"Sequence Test Statistics - Sequence: {sequence_stats}")

        return self.total_errors == 0

    async def protocol_error_test(self):
        """Test error detection features in the FIFO components"""
        self.log.info("Running protocol error test")

        # Set to faster randomizers for quicker testing
        self.write_master.set_randomizer(FlexRandomizer(RANDOMIZER_CONFIGS['fast']['write']))
        self.read_slave.set_randomizer(FlexRandomizer(RANDOMIZER_CONFIGS['fast']['read']))

        # Reset environment
        await self.assert_reset()
        await self.wait_clocks(self.wr_clk_name, 10)
        await self.deassert_reset()
        await self.wait_clocks(self.wr_clk_name, 10)

        # Start the command handler
        await self.command_handler.start()

        # Test field width violations
        self.log.info("Testing field width violations")

        # Create a packet with field values that exceed their bit widths
        packet_oversized = FIFOPacket(self.field_config)
        packet_oversized.addr = (1 << (self.AW + 2)) - 1  # Value exceeds AW bit width
        packet_oversized.ctrl = (1 << (self.CW + 4)) - 1  # Value exceeds CW bit width
        packet_oversized.data0 = (1 << (self.DW + 8)) - 1  # Value exceeds DW bit width
        packet_oversized.data1 = (1 << (self.DW + 16)) - 1  # Value exceeds DW bit width

        # Send the oversized packet
        await self.write_master.send(packet_oversized)

        # Wait for transmission to complete
        while self.write_master.transfer_busy:
            await self.wait_clocks(self.wr_clk_name, 1)

        # Wait for processing
        await self.wait_clocks(self.wr_clk_name, 20)

        # Check that values were properly masked
        if self.wr_monitor.observed_queue:
            wr_pkt = self.wr_monitor.observed_queue[0]
            self.log.info(f"Field values after masking: {wr_pkt.formatted(compact=True)}")

            # Verify fields were masked correctly
            addr_mask = (1 << self.AW) - 1
            ctrl_mask = (1 << self.CW) - 1
            data_mask = (1 << self.DW) - 1

            masked_addr = packet_oversized.addr & addr_mask
            masked_ctrl = packet_oversized.ctrl & ctrl_mask
            masked_data0 = packet_oversized.data0 & data_mask
            masked_data1 = packet_oversized.data1 & data_mask

            if wr_pkt.addr != masked_addr or wr_pkt.ctrl != masked_ctrl or \
               wr_pkt.data0 != masked_data0 or wr_pkt.data1 != masked_data1:
                self.log.error("Field masking did not work correctly")
                self.total_errors += 1
            else:
                self.log.info("Field masking verification passed")

        # Wait for all processing to complete
        await self.wait_clocks(self.wr_clk_name, 20)

        # Stop the command handler
        await self.command_handler.stop()

        # Get statistics to verify masked values were recorded
        stats = self.get_component_statistics()
        self.log.info(f"Protocol Error Test Statistics: {stats}")

        return self.total_errors == 0
