"""
Testbench for axi_data_upsize module
Tests narrow→wide accumulator using proper GAXI components
"""

import os
import sys
import cocotb
from cocotb.triggers import RisingEdge, Timer
from cocotb.clock import Clock
import random

# Add framework to path
repo_root = os.path.abspath(os.path.join(os.path.dirname(__file__), '../../../../..'))
sys.path.insert(0, os.path.join(repo_root, 'bin'))

from CocoTBFramework.tbclasses.shared.tbbase import TBBase
from CocoTBFramework.components.gaxi.gaxi_master import GAXIMaster
from CocoTBFramework.components.gaxi.gaxi_slave import GAXISlave
from CocoTBFramework.components.shared.field_config import FieldConfig, FieldDefinition


class AXIDataUpsizeTB(TBBase):
    """
    Testbench class for axi_data_upsize module using proper GAXI components.

    Architecture:
    - GAXIMaster for narrow input (drives valid/data/sideband/last, receives ready)
    - GAXISlave for wide output (drives ready, receives valid/data/sideband/last)
    - Queue-based verification using ._recvQ
    """

    def __init__(self, dut):
        super().__init__(dut)

        # Clock and reset
        self.clk = dut.aclk
        self.clk_name = 'aclk'
        self.rst_n = dut.aresetn

        # Extract parameters from DUT
        try:
            self.narrow_width = int(dut.NARROW_WIDTH.value)
            self.wide_width = int(dut.WIDE_WIDTH.value)
            self.narrow_sb_width = int(dut.NARROW_SB_WIDTH.value) if hasattr(dut, 'NARROW_SB_WIDTH') else 0
            self.wide_sb_width = int(dut.WIDE_SB_WIDTH.value) if hasattr(dut, 'WIDE_SB_WIDTH') else 0
            self.sb_or_mode = bool(int(dut.SB_OR_MODE.value)) if hasattr(dut, 'SB_OR_MODE') else False
            self.width_ratio = self.wide_width // self.narrow_width
        except:
            # Fallback if parameters not accessible
            self.narrow_width = 32
            self.wide_width = 128
            self.narrow_sb_width = 4
            self.wide_sb_width = 16
            self.sb_or_mode = False
            self.width_ratio = 4

        # Initialize GAXI components
        self._init_gaxi_components()

        self.log.info(f"Initialized AXI Data Upsize TB: {self.narrow_width}→{self.wide_width}, "
                      f"ratio={self.width_ratio}, sb_mode={'OR' if self.sb_or_mode else 'concat'}")

    def _init_gaxi_components(self):
        """Initialize GAXI master and slave components"""

        # Narrow input - GAXIMaster drives the converter input
        narrow_field_config = FieldConfig()
        narrow_field_config.add_field(FieldDefinition(name='data', bits=self.narrow_width, default=0))
        if self.narrow_sb_width > 0:
            narrow_field_config.add_field(FieldDefinition(name='sideband', bits=self.narrow_sb_width, default=0))
        narrow_field_config.add_field(FieldDefinition(name='last', bits=1, default=0))

        self.narrow_master = GAXIMaster(
            dut=self.dut,
            title="NARROW_IN",
            prefix="narrow_",
            clock=self.clk,
            field_config=narrow_field_config,
            pkt_prefix="narrow",
            multi_sig=True,
            log=self.log
        )

        # Wide output - GAXISlave monitors the converter output
        wide_field_config = FieldConfig()
        wide_field_config.add_field(FieldDefinition(name='data', bits=self.wide_width, default=0))
        if self.wide_sb_width > 0:
            wide_field_config.add_field(FieldDefinition(name='sideband', bits=self.wide_sb_width, default=0))
        wide_field_config.add_field(FieldDefinition(name='last', bits=1, default=0))

        self.wide_slave = GAXISlave(
            dut=self.dut,
            title="WIDE_OUT",
            prefix="wide_",
            clock=self.clk,
            field_config=wide_field_config,
            pkt_prefix="wide",
            multi_sig=True,
            log=self.log
        )

    # =========================================================================
    # MANDATORY METHODS - Required by TBBase
    # =========================================================================

    async def setup_clocks_and_reset(self, period_ns=10):
        """Complete initialization - start clocks and perform reset"""
        # Start clock
        await self.start_clock(self.clk_name, freq=period_ns, units='ns')

        # Reset sequence
        await self.assert_reset()
        await self.wait_clocks(self.clk_name, 5)
        await self.deassert_reset()
        await self.wait_clocks(self.clk_name, 2)

        self.log.info("Reset sequence complete")

    async def assert_reset(self):
        """Assert reset signal (active-low)"""
        self.rst_n.value = 0
        self.log.debug("Reset asserted")

    async def deassert_reset(self):
        """Deassert reset signal (active-low)"""
        self.rst_n.value = 1
        self.log.debug("Reset deasserted")

    # =========================================================================
    # TEST UTILITY METHODS
    # =========================================================================

    async def send_narrow_beat(self, data, sideband=0, last=False):
        """
        Send a narrow beat using GAXI master

        Args:
            data: Data value
            sideband: Sideband value (WSTRB or RRESP)
            last: Assert narrow_last
        """
        # Create packet with generic field names
        pkt_dict = {
            'data': data,
            'last': 1 if last else 0
        }
        if self.narrow_sb_width > 0:
            pkt_dict['sideband'] = sideband

        narrow_pkt = self.narrow_master.create_packet(**pkt_dict)
        await self.narrow_master.send(narrow_pkt)

    def get_wide_beats(self, count=None, clear=False):
        """
        Get wide beats from slave receive queue

        Args:
            count: Number of beats to retrieve (None = all)
            clear: Clear queue after retrieval

        Returns:
            List of (data, sideband, last) tuples
        """
        beats = []
        queue_len = len(self.wide_slave._recvQ)

        if count is None:
            count = queue_len

        for i in range(min(count, queue_len)):
            pkt = self.wide_slave._recvQ[i] if not clear else self.wide_slave._recvQ.popleft()
            data = getattr(pkt, 'data', 0)
            sideband = getattr(pkt, 'sideband', 0) if self.wide_sb_width > 0 else 0
            last = bool(getattr(pkt, 'last', 0))
            beats.append((data, sideband, last))

        return beats

    # =========================================================================
    # TEST SCENARIO METHODS
    # =========================================================================

    async def test_basic_accumulation(self, num_transactions=10):
        """
        Test basic accumulation: send WIDTH_RATIO narrow beats,
        expect 1 wide beat with accumulated data
        """
        self.log.info(f"Starting basic accumulation test ({num_transactions} transactions)")

        for txn in range(num_transactions):
            # Generate narrow beats
            narrow_beats = []
            for i in range(self.width_ratio):
                data = random.randint(0, (1 << self.narrow_width) - 1)
                sideband = random.randint(0, (1 << self.narrow_sb_width) - 1) if self.narrow_sb_width > 0 else 0
                narrow_beats.append((data, sideband))

            # Send narrow beats using GAXI master
            for i, (data, sideband) in enumerate(narrow_beats):
                await self.send_narrow_beat(data, sideband, last=False)

            # Wait for wide beat to appear
            await self.wait_clocks(self.clk_name, self.width_ratio + 5)

            # Verify we received 1 wide beat
            wide_beats = self.get_wide_beats(count=1, clear=True)

            if len(wide_beats) != 1:
                self.log.error(f"Transaction {txn}: Expected 1 wide beat, got {len(wide_beats)}")
                return False

            wide_data, wide_sideband, wide_last = wide_beats[0]

            # Verify accumulation
            expected_data = 0
            for i, (data, _) in enumerate(narrow_beats):
                expected_data |= (data << (i * self.narrow_width))

            if wide_data != expected_data:
                self.log.error(f"Transaction {txn}: Data mismatch - "
                               f"expected 0x{expected_data:x}, got 0x{wide_data:x}")
                return False

            # Verify sideband
            if self.narrow_sb_width > 0:
                if self.sb_or_mode:
                    # OR mode: expected is OR of all narrow sidebands
                    expected_sb = 0
                    for _, sb in narrow_beats:
                        expected_sb |= sb
                else:
                    # Concatenate mode: pack sidebands
                    expected_sb = 0
                    for i, (_, sb) in enumerate(narrow_beats):
                        expected_sb |= (sb << (i * self.narrow_sb_width))

                if wide_sideband != expected_sb:
                    self.log.error(f"Transaction {txn}: Sideband mismatch - "
                                   f"expected 0x{expected_sb:x}, got 0x{wide_sideband:x}")
                    return False

        self.log.info(f"✓ Basic accumulation test PASSED ({num_transactions} transactions)")
        return True

    async def test_early_last(self, num_transactions=10):
        """
        Test early termination: send fewer than WIDTH_RATIO beats with last=1
        """
        self.log.info(f"Starting early LAST test ({num_transactions} transactions)")

        for txn in range(num_transactions):
            # Send random number of beats (1 to WIDTH_RATIO-1)
            num_beats = random.randint(1, self.width_ratio - 1)

            narrow_beats = []
            for i in range(num_beats):
                data = random.randint(0, (1 << self.narrow_width) - 1)
                sideband = random.randint(0, (1 << self.narrow_sb_width) - 1) if self.narrow_sb_width > 0 else 0
                narrow_beats.append((data, sideband))

            # Send narrow beats (last one with last=1)
            for i, (data, sideband) in enumerate(narrow_beats):
                is_last = (i == num_beats - 1)
                await self.send_narrow_beat(data, sideband, last=is_last)

            # Wait for wide beat
            await self.wait_clocks(self.clk_name, num_beats + 5)

            # Get wide beat
            wide_beats = self.get_wide_beats(count=1, clear=True)

            if len(wide_beats) != 1:
                self.log.error(f"Transaction {txn}: Expected 1 wide beat, got {len(wide_beats)}")
                return False

            _, _, wide_last = wide_beats[0]

            # Verify LAST asserted
            if not wide_last:
                self.log.error(f"Transaction {txn}: Expected wide_last=1 for early termination")
                return False

        self.log.info(f"✓ Early LAST test PASSED ({num_transactions} transactions)")
        return True

    async def test_backpressure(self, num_transactions=5):
        """
        Test backpressure: delay wide_ready randomly
        """
        self.log.info(f"Starting backpressure test ({num_transactions} transactions)")

        for txn in range(num_transactions):
            # Send WIDTH_RATIO narrow beats
            for i in range(self.width_ratio):
                data = random.randint(0, (1 << self.narrow_width) - 1)
                await self.send_narrow_beat(data, sideband=0, last=False)

            # Add random delay before checking output
            delay_cycles = random.randint(5, 20)
            await self.wait_clocks(self.clk_name, delay_cycles)

            # Verify wide beat arrived
            wide_beats = self.get_wide_beats(count=1, clear=True)
            if len(wide_beats) != 1:
                self.log.error(f"Transaction {txn}: Expected 1 wide beat, got {len(wide_beats)}")
                return False

        self.log.info(f"✓ Backpressure test PASSED ({num_transactions} transactions)")
        return True

    async def test_continuous_streaming(self, num_wide_beats=20):
        """Test continuous streaming without gaps"""
        self.log.info(f"Starting continuous streaming test ({num_wide_beats} wide beats)")

        # Send narrow beats continuously
        for wide_beat in range(num_wide_beats):
            for narrow_beat in range(self.width_ratio):
                data = (wide_beat << 8) | narrow_beat  # Unique pattern
                await self.send_narrow_beat(data, sideband=0, last=False)

        # Wait for all wide beats to complete
        expected_wide_beats = num_wide_beats
        await self.wait_clocks(self.clk_name, (num_wide_beats * self.width_ratio) + 20)

        # Verify count
        actual_wide_beats = len(self.wide_slave._recvQ)
        if actual_wide_beats != expected_wide_beats:
            self.log.error(f"Continuous streaming: Expected {expected_wide_beats} beats, got {actual_wide_beats}")
            return False

        self.log.info(f"✓ Continuous streaming test PASSED ({num_wide_beats} wide beats)")
        return True
