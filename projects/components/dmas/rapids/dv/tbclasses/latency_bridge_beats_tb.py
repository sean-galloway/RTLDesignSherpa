# SPDX-License-Identifier: MIT
# SPDX-FileCopyrightText: 2024-2025 sean galloway
#
# RTL Design Sherpa - Industry-Standard RTL Design and Verification
# https://github.com/sean-galloway/RTLDesignSherpa
#
# Module: latency_bridge_beats_tb
# Purpose: Testbench for latency_bridge_beats module
#
# Documentation: projects/components/dmas/rapids/PRD.md
# Subsystem: rapids
#
# Author: sean galloway
# Created: 2025-01-10
"""
Testbench for latency_bridge_beats module

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


class LatencyBridgeBeatsTB(TBBase):
    """Testbench for latency_bridge_beats"""

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

        wr_valid/wr_ready/wr_data (FIFO in front of the bridge) -> GAXIMaster ;
        m_valid/m_ready/m_data -> GAXISlave.
        Both carry a 'data' payload. Cycle-accurate control is achieved by loading
        deterministic FlexRandomizer delay sequences (see set_*_delay_seq).
        """
        fc = FieldConfig()
        fc.add_field(FieldDefinition(name='data', bits=self.data_width,
                                     format='hex', description='beat data'))
        # The master feeds the wrapper's REGISTERED=1 gaxi_fifo_sync (wr_*), not
        # the bridge's s_* port: the bridge expects s_data one cycle after the
        # handshake, which no valid/ready BFM produces. See
        # dv/tb/latency_bridge_beats_tb_top.sv.
        self.s_master = create_gaxi_master(
            dut=self.dut, title='lb_wr', prefix='wr', clock=self.dut.clk,
            field_config=fc, multi_sig=True, log=self.log)
        self.m_slave = create_gaxi_slave(
            dut=self.dut, title='lb_m', prefix='m', clock=self.dut.clk,
            field_config=fc, multi_sig=True, log=self.log)
        # Default: back-to-back (full speed) on both sides.
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
        """Skid-buffer depth of the bridge (occupancy == skid_count, max == SKID_DEPTH)."""
        try:
            return int(self.dut.SKID_DEPTH.value)
        except Exception:
            return 4

    async def _fill_blocked(self, n_beats=6, settle=15):
        """Queue n_beats on the s master at full speed with the drain blocked,
        then settle. Returns (occupancy, s_ready) once the FIFO is full."""
        # Master back-to-back, downstream blocked (huge ready delay -> ready held low).
        self.set_s_delay_seq([0])
        self.set_m_ready_seq([100000])
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
        """Occupancy tracking: fill the FIFO with the drain blocked, verify it
        reaches DEPTH and asserts backpressure, then drain to empty."""
        self.log.info("=== Testing Occupancy Tracking (GAXI BFM) ===")
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
        """Backpressure: FIFO fills to DEPTH, s_ready deasserts; after draining
        s_ready re-asserts and occupancy returns to 0. Soft-fail accumulation."""
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
            self.log.error("=" * 80)
            self.log.error(f"BACKPRESSURE TEST FAILED: {len(errors)} error(s)")
            for err in errors:
                self.log.error(f"  - {err}")
            self.log.error("=" * 80)
            raise AssertionError(f"Backpressure test failed with {len(errors)} error(s)")
        self.log.info(f"Backpressure released (s_ready={ready_after}, occupancy={occ_after})")
        self.log.info("Backpressure test passed")

    async def test_streaming(self, num_beats=None):
        """Streaming flow under the active timing profile: continuously feed
        num_beats while the slave drains, sampling occupancy each cycle, and
        check every beat comes out of m_data unchanged and in order."""
        if num_beats is None:
            num_beats = {'gate': 20, 'func': 60, 'full': 200}.get(os.environ.get('TEST_LEVEL', 'gate').lower(), 20)
        self.log.info(f"=== Testing Streaming Flow ({num_beats} beats, profile-driven) ===")
        occupancies = []
        received = []
        self.m_slave.add_callback(lambda pkt: received.append(int(pkt.data)))

        # Feed beats from a background coroutine so we can sample occupancy each
        # cycle while data is in flight (send() queues + yields, so feeding and
        # sampling from the same coroutine would race the beats to completion).
        async def feeder():
            for i in range(num_beats):
                await self.s_master.send(self.s_master.create_packet(data=i))

        feed_task = cocotb.start_soon(feeder())

        # A slow producer profile can spend tens of cycles per beat, so the guard
        # scales with the beat count (200 beats at 'full' overran a fixed 2000
        # cycles and the check counted 119 of 200 -- regression 2026-09-27).
        guard, guard_limit = 0, 60 * num_beats + 500
        while guard < guard_limit:
            await RisingEdge(self.dut.clk)
            occupancies.append(self.get_occupancy())
            guard += 1
            # Drained means: feeder finished, master idle, nothing left in the
            # wrapper FIFO, nothing presented to the bridge, bridge empty and
            # nothing held on m_*. Bridge occupancy alone reads 0 while the last
            # beat still sits in the FIFO under slave backpressure (199 of 200
            # counted -- regression 2026-09-27).
            done = (feed_task.done()
                    and not self.s_master.transfer_busy
                    and len(self.s_master.transmit_queue) == 0
                    and int(self.dut.fifo_count.value) == 0
                    and int(self.dut.s_valid.value) == 0
                    and self.get_occupancy() == 0
                    and int(self.dut.m_valid.value) == 0)
            if done:
                break

        if not occupancies:
            occupancies = [self.get_occupancy()]
        avg = sum(occupancies) / len(occupancies)
        self.log.info(f"Streaming occupancy: avg={avg:.2f}, max={max(occupancies)}, samples={len(occupancies)}")
        assert max(occupancies) > 0, "Occupancy should be non-zero during streaming"
        # The slave monitor reports a beat a cycle or two after its handshake;
        # give the tail a bounded wait rather than a fixed handful of cycles.
        for _ in range(500):
            if len(received) >= num_beats:
                break
            await self.wait_clocks('clk', 1)
        await self.wait_clocks('clk', 5)
        expected = list(range(num_beats))
        assert received == expected, (f"data path: received {len(received)} beats, expected {num_beats}; "
                                      f"first mismatch at {next((i for i, (a, b) in enumerate(zip(received, expected)) if a != b), None)}; "
                                      f"received[:12]={received[:12]}")
        self.log.info(f"Streaming flow completed: {num_beats} beats received in order")
        return occupancies
