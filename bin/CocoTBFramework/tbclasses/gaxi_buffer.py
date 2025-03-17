"""AXI style skid buffer Testbench using modular GAXI components"""
import os

from CocoTBFramework.tbclasses.tbbase import TBBase
from CocoTBFramework.components.constrained_random import ConstrainedRandom
from CocoTBFramework.components.flex_randomizer import FlexRandomizer

from CocoTBFramework.components.gaxi.gaxi_packet import GAXIPacket
from CocoTBFramework.components.gaxi.gaxi_components import GAXIMaster, GAXISlave, GAXIMonitor


class GaxiBufferTB(TBBase):
    def __init__(self, dut,
                    wr_clk=None, wr_rstn=None,
                    rd_clk=None, rd_rstn=None):
        super().__init__(dut)
        self.TEST_DEPTH = self.convert_to_int(os.environ.get('TEST_DEPTH', '0'))
        self.TEST_WIDTH = self.convert_to_int(os.environ.get('TEST_WIDTH', '0'))
        self.TEST_MODE = os.environ.get('TEST_MODE', 'skid')
        self.TEST_CLK_WR = self.convert_to_int(os.environ.get('TEST_CLK_WR', '10'))
        self.TEST_CLK_RD = self.convert_to_int(os.environ.get('TEST_CLK_RD', '10'))

        self.DATA_WIDTH = self.TEST_WIDTH
        self.MAX_DATA = (2**self.TEST_WIDTH)-1
        self.TIMEOUT_CYCLES = 1000
        self.total_errors = 0
        self.wr_clk = wr_clk
        self.wr_clk_name = wr_clk.name
        self.wr_rstn = wr_rstn
        self.rd_clk = self.wr_clk           if rd_clk  is None else rd_clk
        self.rd_clk_name = self.wr_clk_name if rd_clk  is None else rd_clk.name
        self.rd_rstn = self.wr_rstn         if rd_rstn is None else rd_rstn

        # log the test values
        msg = '\n'
        msg += '='*80 + "\n"
        msg += ' Settings:\n'
        msg += '-'*80 + "\n"
        msg += f' Depth:  {self.TEST_DEPTH}\n'
        msg += f' Width:  {self.TEST_WIDTH}\n'
        msg += f' Max:    {self.MAX_DATA}\n'
        msg += f' MODE:   {self.TEST_MODE}\n'
        msg += f' clk_wr: {self.TEST_CLK_WR}\n'
        msg += f' clk_rd: {self.TEST_CLK_WR}\n'
        msg += '='*80 + "\n"
        self.log.info(msg)

        # Define field configuration for skid buffer packets
        self.field_config = {
            'data': {
                'bits': self.DATA_WIDTH,
                'default': 0,
                'format': 'hex',
                'display_width': 8,
                'active_bits': (self.DATA_WIDTH-1, 0),
                'description': 'Data value'
            }
        }

        # Create randomizers using the existing ConstrainedRandom classes
        # We'll convert these to FlexRandomizer format for the GAXI components
        read_constraints = [(0, 1), (2, 8), (9, 30)]
        read_weights = [5, 2, 1]
        self.read_crand = ConstrainedRandom(read_constraints, read_weights)

        write_constraints = [(0, 0), (1, 8), (9, 20)]
        write_weights = [5, 2, 1]
        self.write_crand = ConstrainedRandom(write_constraints, write_weights)

        # Create delay randomizers for GAXI components
        self.write_delay_constraints_constrained = {
            'valid_delay': ([[0, 0], [1, 8], [9, 20]], [5, 2, 1])
        }
        self.write_delay_constraints_fast = {
            'valid_delay': ([[0, 0], [1, 8], [9, 20]], [5, 0, 0])
        }
        self.read_delay_constraints_constrained = {
            'ready_delay': ([[0, 1], [2, 8], [9, 30]], [5, 2, 1])
        }
        self.read_delay_constraints_fast = {
            'ready_delay': ([[0, 0], [1, 8], [9, 30]], [5, 0, 0])
        }

        self.write_randomizer = FlexRandomizer(self.write_delay_constraints_fast)
        if not isinstance(self.write_randomizer, FlexRandomizer):
            raise ValueError("self.read_randomizer is not properly initialized!")

        self.read_randomizer = FlexRandomizer(self.read_delay_constraints_fast)
        if not isinstance(self.read_randomizer, FlexRandomizer):
            raise ValueError("self.read_randomizer is not properly initialized!")

        # Create BFM components - add signal_map=None to explicitly use standard mode
        self.write_master = GAXIMaster(
            dut, 'write_master', '', self.wr_clk,
            field_config=self.field_config,
            randomizer=self.write_randomizer,
            timeout_cycles=self.TIMEOUT_CYCLES,
            signal_map=None,  # Explicitly specify standard mode
            log=self.log
        )

        self.read_slave = GAXISlave(
            dut, 'read_slave', '', self.rd_clk,
            mode=self.TEST_MODE,
            field_config=self.field_config,
            randomizer=self.read_randomizer,
            timeout_cycles=self.TIMEOUT_CYCLES,
            signal_map=None,  # Explicitly specify standard mode
            log=self.log
        )

        self.wr_monitor = GAXIMonitor(
            dut, 'Write monitor', '', self.wr_clk,
            field_config=self.field_config,
            is_slave=False,
            signal_map=None,  # Explicitly specify standard mode
            log=self.log
        )

        self.rd_monitor = GAXIMonitor(
            dut, 'Read monitor', '', self.rd_clk,
            mode=self.TEST_MODE,
            field_config=self.field_config,
            is_slave=True,
            signal_map=None,  # Explicitly specify standard mode
            log=self.log
        )

    async def clear_interface(self):
        """Clear the interface signals"""
        await self.write_master.reset_bus()
        await self.read_slave.reset_bus()

    async def assert_reset(self):
        """Assert reset"""
        self.wr_rstn.value = 0
        self.rd_rstn.value = 0
        await self.clear_interface()

    async def deassert_reset(self):
        """Deassert reset"""
        self.wr_rstn.value = 1
        self.rd_rstn.value = 1
        self.log.info("Reset complete.")

    def compare_packets(self, msg, expected_count):
        """
        Compare packets captured by wr_monitor and rd_monitor.
        Logs any mismatches without stopping the test and updates self.total_errors.
        Returns two lists of hex string data for the written and read packets (for logging).
        """
        # 1. Ensure the number of packets in both monitors are the same
        wr_mon_count = len(self.wr_monitor.observed_queue)
        rd_mon_count = len(self.rd_monitor.observed_queue)
        if wr_mon_count != rd_mon_count:
            self.log.error(
                f"Packet count mismatch: "
                f"{len(wr_mon_count)} sent vs "
                f"{len(rd_mon_count)} received"
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

        while self.wr_monitor.observed_queue and self.rd_monitor.observed_queue:
            wr_pkt = self.wr_monitor.observed_queue.popleft()   # next packet from write monitor
            rd_pkt = self.rd_monitor.observed_queue.popleft()   # next packet from read monitor

            # Compare the two packets
            if wr_pkt != rd_pkt:
                self.log.error(
                    f"{msg}: Packet mismatch – WR: {wr_pkt.formatted(compact=True)} "
                    f"vs RD: {rd_pkt.formatted(compact=True)}"
                )
                # 4. Increment the error counter for this mismatch
                self.total_errors += 1

        # If any packets remain in one monitor after the other is exhausted, log them as extra errors
        while self.wr_monitor.observed_queue:
            pkt = self.wr_monitor.observed_queue.popleft()
            self.log.error(f"{msg}: Unmatched extra packet in WR monitor: {pkt.formatted(compact=True)}")
            self.total_errors += 1
        while self.rd_monitor.observed_queue:
            pkt = self.rd_monitor.observed_queue.popleft()
            self.log.error(f"{msg}: Unmatched extra packet in RD monitor: {pkt.formatted(compact=True)}")
            self.total_errors += 1

    async def simple_incremental_loops(self, count, use_fast, delay_clks_after):
        """Run simple incremental tests with different packet sizes"""
        # Choose the type of randomizer
        self.log.info(f'simple_incremental_loops({count=}, {use_fast=}, {delay_clks_after=}')
        if use_fast:
            self.write_randomizer = FlexRandomizer(self.write_delay_constraints_fast)
            self.read_randomizer = FlexRandomizer(self.read_delay_constraints_fast)
        else:
            self.write_randomizer = FlexRandomizer(self.write_delay_constraints_constrained)
            self.read_randomizer = FlexRandomizer(self.read_delay_constraints_constrained)

        self.write_master.set_randomizer(self.write_randomizer)
        self.read_slave.set_randomizer(self.read_randomizer)

        self.assert_reset()
        await self.wait_clocks(self.wr_clk_name, 10)
        self.deassert_reset()
        await self.wait_clocks(self.wr_clk_name, 10)

        for i in range(count):
            # Create packet with data
            data = i & self.MAX_DATA # mask the data so we don't overflow
            packet = GAXIPacket(self.field_config, data=data)

            # Queue the packet - this doesn't wait for transmission
            await self.write_master.send(packet)

        # wait until all is transferred
        while self.write_master.transfer_busy:
            await self.wait_clocks(self.wr_clk_name, 1)

        # Read data from the FIFO
        await self.wait_clocks(self.wr_clk_name, delay_clks_after*5)
        while len(self.rd_monitor._recvQ) < count:
            await self.wait_clocks(self.wr_clk_name, 1)
        await self.wait_clocks(self.wr_clk_name, delay_clks_after)

        self.compare_packets("Simple Incremental Loops", count)

        assert self.total_errors == 0, f'Simple Incremental Loops found {self.total_errors} Errors'
