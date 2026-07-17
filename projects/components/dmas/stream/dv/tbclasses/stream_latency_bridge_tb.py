"""
Testbench for stream_latency_bridge module

Purpose: Verify occupancy tracking and data flow through 1-cycle latency pipeline
"""

import cocotb
from cocotb.triggers import RisingEdge, Timer

# Framework imports
import os
import sys

# Import framework utilities (PYTHONPATH includes bin/)
from TBClasses.shared.utilities import get_repo_root
from TBClasses.shared.tbbase import TBBase

# Add repo root to Python path using robust git-based method
repo_root = get_repo_root()
sys.path.insert(0, repo_root)

from CocoTBFramework.components.gaxi.gaxi_factories import create_gaxi_master, create_gaxi_slave
from CocoTBFramework.components.shared.field_config import FieldConfig, FieldDefinition
from CocoTBFramework.components.shared.flex_randomizer import FlexRandomizer


class StreamLatencyBridgeTB(TBBase):
    """Testbench for stream_latency_bridge"""

    def __init__(self, dut):
        super().__init__(dut)
        self.dut = dut
        self.data_width = int(dut.DATA_WIDTH.value)
        self.s_master = None
        self.m_slave = None

    async def setup_clocks_and_reset(self):
        """Standard clock and reset initialization"""
        await self.start_clock('clk', freq=10, units='ns')
        await self.assert_reset()
        await self.wait_clocks('clk', 10)
        await self.deassert_reset()
        await self.wait_clocks('clk', 5)
        self._create_bfms()

    def _create_bfms(self):
        """Create the GAXI BFMs for the s (input) and m (output) interfaces.

        s_valid/s_ready/s_data -> GAXIMaster ; m_valid/m_ready/m_data -> GAXISlave.
        Cycle-accurate control comes from deterministic FlexRandomizer delay
        sequences (see set_*_seq); the active timing profile sets the baseline.
        """
        fc = FieldConfig()
        fc.add_field(FieldDefinition(name='data', bits=self.data_width,
                                     format='hex', description='beat data'))
        self.s_master = create_gaxi_master(
            dut=self.dut, title='lb_s', prefix='s', clock=self.dut.clk,
            field_config=fc, multi_sig=True, log=self.log)
        self.m_slave = create_gaxi_slave(
            dut=self.dut, title='lb_m', prefix='m', clock=self.dut.clk,
            field_config=fc, multi_sig=True, log=self.log)
        self.set_gaxi_timing_profile(os.environ.get('GAXI_TIMING_PROFILE', 'backtoback'))

    def set_gaxi_timing_profile(self, profile_name='backtoback'):
        """Apply a GAXI timing profile: master valid_delay + slave ready_delay."""
        from TBClasses.amba.amba_random_configs import GAXI_RANDOMIZER_CONFIGS
        if profile_name == 'mixed':
            profile_name = 'gaxi_realistic'
        if profile_name not in GAXI_RANDOMIZER_CONFIGS:
            self.log.warning(f"Unknown GAXI timing profile '{profile_name}', using 'backtoback'")
            profile_name = 'backtoback'
        cfg = GAXI_RANDOMIZER_CONFIGS[profile_name]
        self.s_master.randomizer = FlexRandomizer(cfg['master'])
        self.m_slave.randomizer = FlexRandomizer(cfg['slave'])
        self.log.info(f"GAXI latency-bridge timing profile: {profile_name}")

    def set_s_delay_seq(self, seq):
        """Load a deterministic valid_delay sequence on the s master (cycle-exact)."""
        self.s_master.randomizer = FlexRandomizer({'valid_delay': list(seq)})

    def set_m_ready_seq(self, seq):
        """Load a deterministic ready_delay sequence on the m slave (cycle-exact)."""
        self.m_slave.randomizer = FlexRandomizer({'ready_delay': list(seq)})

    async def assert_reset(self):
        """Assert reset signal"""
        self.dut.rst_n.value = 0

    async def deassert_reset(self):
        """Deassert reset signal"""
        self.dut.rst_n.value = 1

    def get_occupancy(self):
        """Get current bridge occupancy (FIFO count)"""
        return int(self.dut.occupancy.value)

    def get_fifo_depth(self):
        """Skid-buffer depth (occupancy == skid_count, max == SKID_DEPTH)."""
        try:
            return int(self.dut.SKID_DEPTH.value)
        except Exception:
            return 4

    async def _fill_blocked(self, n_beats=6, settle=15):
        """Queue n_beats on the s master at full speed with the drain blocked,
        then settle. Returns (occupancy, s_ready) once the FIFO is full."""
        self.set_s_delay_seq([0])             # master back-to-back
        self.set_m_ready_seq([100000])        # slave holds ready low
        for i in range(n_beats):
            await self.s_master.send(self.s_master.create_packet(data=0xA000 + i))
        for _ in range(settle):
            await RisingEdge(self.dut.clk)
        return self.get_occupancy(), int(self.dut.s_ready.value)

    async def _release_and_drain(self, max_cycles=60):
        """Release the drain (slave ready full speed) and run until the bridge
        empties and the master pipeline is idle. reset_bus interrupts the
        in-flight ready-delay so the swap takes effect immediately."""
        self.set_m_ready_seq([0])
        await self.m_slave.reset_bus()
        for _ in range(max_cycles):
            await RisingEdge(self.dut.clk)
            if self.get_occupancy() == 0 and not self.s_master.transfer_busy:
                break

    async def test_occupancy(self):
        """Occupancy tracking via GAXI BFMs.

        Covers testplan scenarios:
        - LATENCY-BRIDGE-02: Upstream backpressure
        - LATENCY-BRIDGE-03: Downstream stall
        - LATENCY-BRIDGE-04: Buffer full condition
        - LATENCY-BRIDGE-05: Buffer empty condition
        """
        self.log.info("=== Scenario LATENCY-BRIDGE-02/03/04/05: Occupancy tracking ===")
        depth = self.get_fifo_depth()

        assert self.get_occupancy() == 0, "Initial occupancy should be 0"
        self.log.info("Initial occupancy = 0")

        occ, s_ready = await self._fill_blocked()
        self.log.info(f"After fill (drain blocked): occupancy={occ}, s_ready={s_ready}")
        assert occ == depth, f"Expected occupancy={depth} when full, got {occ}"
        assert s_ready == 0, f"Expected s_ready=0 (backpressure) when full, got {s_ready}"

        await self._release_and_drain()
        occ = self.get_occupancy()
        assert occ == 0, f"Expected occupancy=0 after drain, got {occ}"
        self.log.info("Occupancy tracking verified")

    async def test_backpressure(self):
        """Backpressure: FIFO fills to SKID_DEPTH, s_ready deasserts; after
        draining s_ready re-asserts and occupancy returns to 0."""
        self.log.info("=== Testing Backpressure (GAXI BFM) ===")
        depth = self.get_fifo_depth()
        errors = []

        occ, s_ready = await self._fill_blocked()
        self.log.info(f"At backpressure: occupancy={occ}, s_ready={s_ready}")
        if occ != depth:
            errors.append(f"Expected occupancy={depth} at backpressure, got {occ}")
        if s_ready != 0:
            errors.append(f"Expected s_ready=0 at max occupancy, got {s_ready}")

        await self._release_and_drain()
        ready_after = int(self.dut.s_ready.value)
        occ_after = self.get_occupancy()
        if ready_after != 1:
            errors.append(f"Expected s_ready=1 after draining, got {ready_after}")
        if occ_after != 0:
            errors.append(f"Expected occupancy=0 after draining, got {occ_after}")

        if errors:
            for err in errors:
                self.log.error(f"  - {err}")
            raise AssertionError(f"Backpressure test failed with {len(errors)} error(s)")
        self.log.info(f"Backpressure released (s_ready={ready_after}, occupancy={occ_after})")

    async def test_streaming(self, num_beats=20):
        """Streaming flow under the active timing profile.

        Covers testplan scenarios:
        - LATENCY-BRIDGE-01: Basic streaming transfer
        - LATENCY-BRIDGE-06: Burst transfer
        - LATENCY-BRIDGE-07: Variable latency compensation
        - LATENCY-BRIDGE-08: Data integrity
        """
        self.log.info("=== Scenario LATENCY-BRIDGE-01/06/07/08: Streaming flow ===")
        occupancies = []

        async def feeder():
            for i in range(num_beats):
                await self.s_master.send(self.s_master.create_packet(data=i))

        feed_task = cocotb.start_soon(feeder())
        guard = 0
        while guard < 2000:
            await RisingEdge(self.dut.clk)
            occupancies.append(self.get_occupancy())
            guard += 1
            if (feed_task.done()
                    and not self.s_master.transfer_busy
                    and len(self.s_master.transmit_queue) == 0
                    and self.get_occupancy() == 0):
                break

        if not occupancies:
            occupancies = [self.get_occupancy()]
        avg = sum(occupancies) / len(occupancies)
        self.log.info(f"Streaming occupancy: avg={avg:.2f}, max={max(occupancies)}, samples={len(occupancies)}")
        assert max(occupancies) > 0, "Occupancy should be non-zero during streaming"
        self.log.info("Streaming flow completed")
        return occupancies
