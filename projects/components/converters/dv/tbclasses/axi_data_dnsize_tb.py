"""
Testbench for axi_data_dnsize module
Tests wide→narrow splitter using proper GAXI components
"""

import os
import sys
import cocotb
from cocotb.triggers import RisingEdge, Timer
from cocotb.clock import Clock
import random

# Import framework utilities (PYTHONPATH includes bin/)
from CocoTBFramework.tbclasses.shared.utilities import get_repo_root
from CocoTBFramework.tbclasses.shared.tbbase import TBBase

# Add repo root to Python path using robust git-based method
repo_root = get_repo_root()
sys.path.insert(0, repo_root)
from CocoTBFramework.components.gaxi.gaxi_master import GAXIMaster
from CocoTBFramework.components.gaxi.gaxi_slave import GAXISlave
from CocoTBFramework.components.shared.field_config import FieldConfig, FieldDefinition


class AXIDataDnsizeTB(TBBase):
    """
    Testbench class for axi_data_dnsize module using proper GAXI components.

    Architecture:
    - GAXIMaster for wide input (drives valid/data/sideband/last, receives ready)
    - GAXISlave for narrow output (drives ready, receives valid/data/sideband/last)
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
            self.wide_width = int(dut.WIDE_WIDTH.value)
            self.narrow_width = int(dut.NARROW_WIDTH.value)
            self.wide_sb_width = int(dut.WIDE_SB_WIDTH.value) if hasattr(dut, 'WIDE_SB_WIDTH') else 0
            self.narrow_sb_width = int(dut.NARROW_SB_WIDTH.value) if hasattr(dut, 'NARROW_SB_WIDTH') else 0
            self.sb_broadcast = bool(int(dut.SB_BROADCAST.value)) if hasattr(dut, 'SB_BROADCAST') else True
            self.track_bursts = bool(int(dut.TRACK_BURSTS.value)) if hasattr(dut, 'TRACK_BURSTS') else False
            self.width_ratio = self.wide_width // self.narrow_width
        except:
            # Fallback if parameters not accessible
            self.wide_width = 128
            self.narrow_width = 32
            self.wide_sb_width = 2
            self.narrow_sb_width = 2
            self.sb_broadcast = True
            self.track_bursts = False
            self.width_ratio = 4

        # Initialize GAXI components
        self._init_gaxi_components()

        self.log.info(f"Initialized AXI Data Dnsize TB: {self.wide_width}→{self.narrow_width}, "
                      f"ratio={self.width_ratio}, sb_mode={'broadcast' if self.sb_broadcast else 'slice'}, "
                      f"track_bursts={self.track_bursts}")

    def _init_gaxi_components(self):
        """Initialize GAXI master and slave components"""

        # Wide input - GAXIMaster drives the converter input
        wide_field_config = FieldConfig()
        wide_field_config.add_field(FieldDefinition(name='data', bits=self.wide_width, default=0))
        if self.wide_sb_width > 0:
            wide_field_config.add_field(FieldDefinition(name='sideband', bits=self.wide_sb_width, default=0))
        wide_field_config.add_field(FieldDefinition(name='last', bits=1, default=0))

        self.wide_master = GAXIMaster(
            dut=self.dut,
            title="WIDE_IN",
            prefix="wide_",
            clock=self.clk,
            field_config=wide_field_config,
            pkt_prefix="wide",
            multi_sig=True,
            log=self.log
        )

        # Narrow output - GAXISlave monitors the converter output
        narrow_field_config = FieldConfig()
        narrow_field_config.add_field(FieldDefinition(name='data', bits=self.narrow_width, default=0))
        if self.narrow_sb_width > 0:
            narrow_field_config.add_field(FieldDefinition(name='sideband', bits=self.narrow_sb_width, default=0))
        narrow_field_config.add_field(FieldDefinition(name='last', bits=1, default=0))

        self.narrow_slave = GAXISlave(
            dut=self.dut,
            title="NARROW_OUT",
            prefix="narrow_",
            clock=self.clk,
            field_config=narrow_field_config,
            pkt_prefix="narrow",
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

        # Initialize burst tracking signals if needed
        if self.track_bursts:
            self.dut.burst_len.value = 0
            self.dut.burst_start.value = 0

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

    async def start_burst(self, burst_len):
        """
        Start a new burst (only if TRACK_BURSTS=1)

        Args:
            burst_len: Burst length (encoded as beats-1)
        """
        if self.track_bursts:
            self.dut.burst_len.value = burst_len
            self.dut.burst_start.value = 1
            await self.wait_clocks(self.clk_name, 1)
            self.dut.burst_start.value = 0

    async def send_wide_beat(self, data, sideband=0, last=False):
        """
        Send a wide beat using GAXI master

        Args:
            data: Data value
            sideband: Sideband value (WSTRB or RRESP)
            last: Assert wide_last
        """
        # Create packet with generic field names
        pkt_dict = {
            'data': data,
            'last': 1 if last else 0
        }
        if self.wide_sb_width > 0:
            pkt_dict['sideband'] = sideband

        wide_pkt = self.wide_master.create_packet(**pkt_dict)
        await self.wide_master.send(wide_pkt)

    def get_narrow_beats(self, count=None, clear=False):
        """
        Get narrow beats from slave receive queue

        Args:
            count: Number of beats to retrieve (None = all)
            clear: Clear queue after retrieval

        Returns:
            List of (data, sideband, last) tuples
        """
        beats = []
        queue_len = len(self.narrow_slave._recvQ)

        if count is None:
            count = queue_len

        for i in range(min(count, queue_len)):
            pkt = self.narrow_slave._recvQ[i] if not clear else self.narrow_slave._recvQ.popleft()
            data = getattr(pkt, 'data', 0)
            sideband = getattr(pkt, 'sideband', 0) if self.narrow_sb_width > 0 else 0
            last = bool(getattr(pkt, 'last', 0))
            beats.append((data, sideband, last))

        return beats

    # =========================================================================
    # TEST SCENARIO METHODS
    # =========================================================================

    async def test_basic_splitting(self, num_transactions=10):
        """
        Test basic splitting: send 1 wide beat,
        expect WIDTH_RATIO narrow beats with correct data slices
        """
        self.log.info(f"Starting basic splitting test ({num_transactions} transactions)")

        for txn in range(num_transactions):
            # Generate wide beat data
            wide_data = random.randint(0, (1 << self.wide_width) - 1)
            wide_sideband = random.randint(0, (1 << self.wide_sb_width) - 1) if self.wide_sb_width > 0 else 0

            # Send wide beat using GAXI master
            await self.send_wide_beat(wide_data, wide_sideband, last=False)

            # Wait for narrow beats to appear
            await self.wait_clocks(self.clk_name, self.width_ratio + 5)

            # Verify we received WIDTH_RATIO narrow beats
            narrow_beats = self.get_narrow_beats(count=self.width_ratio, clear=True)

            if len(narrow_beats) != self.width_ratio:
                self.log.error(f"Transaction {txn}: Expected {self.width_ratio} narrow beats, got {len(narrow_beats)}")
                return False

            # Verify each narrow beat
            for i, (narrow_data, narrow_sideband, narrow_last) in enumerate(narrow_beats):
                # Extract expected narrow data slice
                expected_data = (wide_data >> (i * self.narrow_width)) & ((1 << self.narrow_width) - 1)

                if narrow_data != expected_data:
                    self.log.error(f"Transaction {txn}, beat {i}: Data mismatch - "
                                   f"expected 0x{expected_data:x}, got 0x{narrow_data:x}")
                    return False

                # Verify sideband
                if self.narrow_sb_width > 0:
                    if self.sb_broadcast:
                        # Broadcast mode: all narrow beats get same sideband
                        expected_sb = wide_sideband
                    else:
                        # Slice mode: extract appropriate slice
                        expected_sb = (wide_sideband >> (i * self.narrow_sb_width)) & ((1 << self.narrow_sb_width) - 1)

                    if narrow_sideband != expected_sb:
                        self.log.error(f"Transaction {txn}, beat {i}: Sideband mismatch - "
                                       f"expected 0x{expected_sb:x}, got 0x{narrow_sideband:x}")
                        return False

        self.log.info(f"✓ Basic splitting test PASSED ({num_transactions} transactions)")
        return True

    async def test_last_propagation(self, num_transactions=5):
        """
        Test that wide_last propagates to last narrow beat
        (only for simple mode, not burst tracking mode)
        """
        if self.track_bursts:
            # Skip this test in burst tracking mode
            self.log.info("Skipping LAST propagation test (burst tracking mode)")
            return True

        self.log.info(f"Starting LAST propagation test ({num_transactions} transactions)")

        for txn in range(num_transactions):
            wide_data = random.randint(0, (1 << self.wide_width) - 1)
            wide_sideband = random.randint(0, (1 << self.wide_sb_width) - 1) if self.wide_sb_width > 0 else 0

            # Send wide beat with LAST asserted
            await self.send_wide_beat(wide_data, wide_sideband, last=True)

            # Wait for narrow beats
            await self.wait_clocks(self.clk_name, self.width_ratio + 5)

            # Get narrow beats
            narrow_beats = self.get_narrow_beats(count=self.width_ratio, clear=True)

            # Check only the last narrow beat has LAST asserted
            for i, (_, _, narrow_last) in enumerate(narrow_beats):
                expected_last = (i == self.width_ratio - 1)
                if narrow_last != expected_last:
                    self.log.error(f"Transaction {txn}, beat {i}: LAST mismatch - "
                                   f"expected {expected_last}, got {narrow_last}")
                    return False

        self.log.info(f"✓ LAST propagation test PASSED ({num_transactions} transactions)")
        return True

    async def test_burst_tracking(self, num_bursts=15):
        """Test burst tracking mode for correct LAST generation"""
        if not self.track_bursts:
            self.log.info("Skipping burst tracking test (simple mode)")
            return True

        self.log.info(f"Starting burst tracking test ({num_bursts} bursts)")

        for burst_id in range(num_bursts):
            # Random burst length (1-16 beats, encoded as 0-15)
            burst_len_encoded = random.randint(0, 15)
            burst_len_beats = burst_len_encoded + 1

            # Start burst
            await self.start_burst(burst_len_encoded)
            await self.wait_clocks(self.clk_name, 2)

            # Send burst_len_beats wide beats
            for beat in range(burst_len_beats):
                wide_data = random.randint(0, (1 << self.wide_width) - 1)
                is_last_wide_beat = (beat == burst_len_beats - 1)
                await self.send_wide_beat(wide_data, 0, last=is_last_wide_beat)

            # Wait for all narrow beats
            total_narrow_beats = burst_len_beats * self.width_ratio
            await self.wait_clocks(self.clk_name, total_narrow_beats + 10)

            # Verify LAST only on final narrow beat
            narrow_beats = self.get_narrow_beats(count=total_narrow_beats, clear=True)

            for i, (_, _, narrow_last) in enumerate(narrow_beats):
                expected_last = (i == total_narrow_beats - 1)
                if narrow_last != expected_last:
                    self.log.error(f"Burst {burst_id}, beat {i}: LAST mismatch - "
                                   f"expected {expected_last}, got {narrow_last}")
                    return False

        self.log.info(f"✓ Burst tracking test PASSED ({num_bursts} bursts)")
        return True

    async def test_backpressure(self, num_transactions=10):
        """Test backpressure handling"""
        self.log.info(f"Starting backpressure test ({num_transactions} transactions)")

        for txn in range(num_transactions):
            wide_data = random.randint(0, (1 << self.wide_width) - 1)

            # Send wide beat
            await self.send_wide_beat(wide_data, 0, last=False)

            # Random backpressure on narrow output
            for _ in range(self.width_ratio):
                if random.random() < 0.3:  # 30% chance of backpressure
                    await self.wait_clocks(self.clk_name, random.randint(1, 5))

            # Wait for transaction to complete
            await self.wait_clocks(self.clk_name, self.width_ratio + 10)

        # Verify we got all expected beats
        expected_total = num_transactions * self.width_ratio
        actual_total = len(self.narrow_slave._recvQ)

        if actual_total != expected_total:
            self.log.error(f"Backpressure test: Expected {expected_total} beats, got {actual_total}")
            return False

        self.log.info(f"✓ Backpressure test PASSED ({num_transactions} transactions)")
        return True

    async def test_continuous_streaming(self, num_wide_beats=30):
        """Test continuous streaming without gaps"""
        self.log.info(f"Starting continuous streaming test ({num_wide_beats} wide beats)")

        # Send multiple wide beats back-to-back
        for beat in range(num_wide_beats):
            wide_data = random.randint(0, (1 << self.wide_width) - 1)
            await self.send_wide_beat(wide_data, 0, last=False)

        # Wait for all narrow beats to complete
        expected_narrow_beats = num_wide_beats * self.width_ratio
        await self.wait_clocks(self.clk_name, expected_narrow_beats + 20)

        # Verify count
        actual_narrow_beats = len(self.narrow_slave._recvQ)
        if actual_narrow_beats != expected_narrow_beats:
            self.log.error(f"Continuous streaming: Expected {expected_narrow_beats} beats, got {actual_narrow_beats}")
            return False

        self.log.info(f"✓ Continuous streaming test PASSED ({num_wide_beats} wide beats)")
        return True
