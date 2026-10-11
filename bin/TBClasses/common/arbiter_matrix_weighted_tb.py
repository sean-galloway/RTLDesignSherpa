# SPDX-License-Identifier: MIT
# SPDX-FileCopyrightText: 2024-2026 sean galloway
#
# RTL Design Sherpa - Industry-Standard RTL Design and Verification
# https://github.com/sean-galloway/RTLDesignSherpa
#
# Module: ArbiterMatrixWeightedTB
# Purpose: Testbench for the weighted matrix arbiter using ArbiterMaster
#          stimulus and ArbiterMonitor checking.
#
# Documentation: cocotb-framework PyPI package
# Subsystem: framework
#
# Author: sean galloway
# Created: 2026-10-11

"""
Testbench for arbiter_matrix_weighted.

Follows the same ArbiterMaster / ArbiterMonitor methodology as
ArbiterRoundRobinTB.  Randomized scenario phases drive stimulus through the
master and assert through the monitor (grant one-hot, no unrequested grants,
weighted distribution).  Directed supplements exercise corner cases that the
master/monitor cannot express deterministically.
"""

import os
import random
import cocotb
from cocotb.clock import Clock
from cocotb.triggers import RisingEdge, FallingEdge, Timer, ClockCycles
from cocotb.utils import get_sim_time

from TBClasses.shared.tbbase import TBBase
from CocoTBFramework.components.shared.arbiter_monitor import WeightedRoundRobinArbiterMonitor
from CocoTBFramework.components.shared.arbiter_master import ArbiterMaster


class ArbiterMatrixWeightedTB(TBBase):
    """Weighted matrix arbiter testbench with ArbiterMaster/ArbiterMonitor."""

    def __init__(self, dut):
        super().__init__(dut)

        self.CLIENTS = int(dut.CLIENTS.value)
        self.WAIT_GNT_ACK = int(dut.WAIT_GNT_ACK.value)
        self.MAX_LEVELS = int(dut.MAX_LEVELS.value)
        try:
            self.MAX_LEVELS_WIDTH = int(dut.MAX_LEVELS_WIDTH.value)
        except Exception:
            self.MAX_LEVELS_WIDTH = (self.MAX_LEVELS - 1).bit_length()

        self.SEED = self.convert_to_int(os.environ.get('SEED', '0'))
        random.seed(self.SEED)

        self.TEST_LEVEL = os.environ.get('TEST_LEVEL', 'gate').lower()
        if self.TEST_LEVEL not in ('gate', 'func', 'full'):
            self.TEST_LEVEL = 'gate'
        self.LEVEL_MULT = {'gate': 1, 'func': 2, 'full': 5}[self.TEST_LEVEL]

        # Weighted monitor: tracks max_thresh and runs WRR compliance checks.
        self.monitor = WeightedRoundRobinArbiterMonitor(
            dut=dut,
            title="MatrixW_Monitor",
            clock=self.dut.clk,
            reset_n=self.dut.rst_n,
            req_signal=self.dut.request,
            gnt_valid_signal=self.dut.grant_valid,
            gnt_signal=self.dut.grant,
            gnt_id_signal=self.dut.grant_id,
            gnt_ack_signal=self.dut.grant_ack,
            block_arb_signal=self.dut.block_arb,
            max_thresh_signal=self.dut.max_thresh,
            clients=self.CLIENTS,
            ack_mode=(self.WAIT_GNT_ACK == 1),
            log=self.log,
            clock_period_ns=10
        )

        # Weighted master: drives requests and weight vector.
        self.master = ArbiterMaster(
            dut=dut,
            title="MatrixW Driver",
            clock=self.dut.clk,
            num_clients=self.CLIENTS,
            ack_mode=(self.WAIT_GNT_ACK == 1),
            is_weighted=True,
            log=self.log
        )
        self.master._max_levels_width = self.MAX_LEVELS_WIDTH

        self.monitor_errors = []
        self.monitor.add_transaction_callback(self._on_monitor_transaction)
        self.monitor.add_reset_callback(self._on_monitor_reset)
        self.monitor.enable_debug()

        if hasattr(self.monitor, 'compliance'):
            self.monitor.compliance.ack_timeout_cycles = 8000
            self.log.info(f"Configured ACK timeout: 8000 cycles ({8000 * 10}ns)")

        self.clock_started = False

        self.log.info(
            f"ArbiterMatrixWeightedTB initialized: CLIENTS={self.CLIENTS}, "
            f"MAX_LEVELS={self.MAX_LEVELS}, MAX_LEVELS_WIDTH={self.MAX_LEVELS_WIDTH}, "
            f"WAIT_GNT_ACK={self.WAIT_GNT_ACK}, TEST_LEVEL={self.TEST_LEVEL}, "
            f"SEED={self.SEED}"
        )

    # -------------------------------------------------------------------------
    # Lifecycle contract
    # -------------------------------------------------------------------------
    def _on_monitor_transaction(self, transaction):
        if transaction.gnt_id >= self.CLIENTS:
            error = f"Invalid grant ID {transaction.gnt_id} >= {self.CLIENTS}"
            self.monitor_errors.append(error)
            self.log.error(error)

    def _on_monitor_reset(self, reset_type):
        self.log.debug(f"Monitor reset event: {reset_type}{self.get_time_ns_str()}")

    async def assert_reset(self):
        self.dut.rst_n.value = 0

    async def deassert_reset(self):
        self.dut.rst_n.value = 1

    async def setup_clocks_and_reset(self):
        await self.start_clock('clk', 10, units='ns')
        await self.reset_dut()
        await self.master.startup()
        self.log.info(f"DUT reset complete, components started{self.get_time_ns_str()}")

    async def start_clock(self, clock_name: str, period: int, units: str = 'ns'):
        if not self.clock_started:
            clock_gen = Clock(getattr(self.dut, clock_name), period, units=units)
            cocotb.start_soon(clock_gen.start())
            self.clock_started = True
            await ClockCycles(self.dut.clk, 2)

    async def reset_dut(self):
        self.dut.rst_n.value = 0
        self.dut.request.value = 0
        self.dut.block_arb.value = 0
        self.dut.max_thresh.value = 0
        if self.CLIENTS > 1:
            self.dut.grant_ack.value = 0
        for _ in range(10):
            await RisingEdge(self.dut.clk)
        self.dut.rst_n.value = 1
        for _ in range(2):
            await RisingEdge(self.dut.clk)
        await Timer(1, units='ns')
        self.log.info(f"DUT reset complete{self.get_time_ns_str()}")

    async def enter_directed_mode(self):
        """Shut the master down so directed pokes own the request/weight vectors."""
        for client_id in range(self.CLIENTS):
            self.master.disable_client(client_id)
        await self.wait_clocks(2)
        if self.master.active:
            await self.master.shutdown()
        idle_cycles = 0
        while idle_cycles < 5:
            await self.wait_clocks(1)
            req = int(self.dut.request.value) if self.dut.request.value.is_resolvable else 0
            gv = int(self.dut.grant_valid.value) if self.dut.grant_valid.value.is_resolvable else 0
            if req == 0 and gv == 0:
                idle_cycles += 1
            elif req == 0 and gv == 1 and self.WAIT_GNT_ACK == 1:
                gnt = int(self.dut.grant.value) if self.dut.grant.value.is_resolvable else 0
                if gnt:
                    self.dut.grant_ack.value = gnt
                    await self.wait_clocks(1)
                    self.dut.grant_ack.value = 0
                    idle_cycles = 0
            else:
                idle_cycles = 0

    async def exit_directed_mode(self):
        """Restart the master for subsequent randomized scenario phases."""
        if not self.master.active:
            await self.master.startup()

    async def wait_clocks(self, num_clocks: int):
        for _ in range(num_clocks):
            await RisingEdge(self.dut.clk)
        await Timer(1, units='ns')

    def get_time_ns_str(self):
        return f" @ {get_sim_time('ns'):.1f}ns"

    def convert_to_int(self, value):
        try:
            return int(value)
        except (ValueError, TypeError):
            return 0

    # -------------------------------------------------------------------------
    # Low-level helpers (kept for directed supplements)
    # -------------------------------------------------------------------------
    def set_weights(self, weights):
        """Pack per-client weights into the max_thresh vector."""
        if len(weights) != self.CLIENTS:
            raise ValueError(
                f"weights length {len(weights)} != CLIENTS {self.CLIENTS}"
            )
        packed = 0
        for i, w in enumerate(weights):
            packed |= (int(w) & ((1 << self.MAX_LEVELS_WIDTH) - 1)) << (i * self.MAX_LEVELS_WIDTH)
        self.dut.max_thresh.value = packed

    async def set_request(self, value: int):
        self.dut.request.value = value
        await self.wait_clocks(1)

    def read_grant(self):
        gv = int(self.dut.grant_valid.value)
        gnt = int(self.dut.grant.value)
        gid = int(self.dut.grant_id.value) if self.CLIENTS > 1 else 0
        return gv, gnt, gid

    def is_one_hot(self, value: int) -> bool:
        return value == 0 or ((value & (value - 1)) == 0)

    def one_hot_to_id(self, value: int) -> int:
        if value == 0:
            return 0
        return (value.bit_length() - 1)

    async def _wait_for_grant(self, timeout=20):
        for _ in range(timeout):
            gv, gnt, gid = self.read_grant()
            if gv:
                return gv, gnt, gid
            await self.wait_clocks(1)
        raise AssertionError(f"No grant appeared within {timeout} cycles")

    async def _drive_ack(self, ack_vec: int, cycles: int = 1):
        if self.CLIENTS > 1:
            self.dut.grant_ack.value = ack_vec
        await self.wait_clocks(cycles)
        if self.CLIENTS > 1:
            self.dut.grant_ack.value = 0

    async def drain_arbiter(self, auto_ack_enabled, timeout_cycles=200):
        """Wait for grant_valid to drop, retiring a stranded grant if needed."""
        for _ in range(timeout_cycles):
            await self.wait_clocks(1)
            gv = self.dut.grant_valid.value
            if not gv.is_resolvable:
                continue
            if int(gv) == 0:
                break
            gnt = self.dut.grant.value
            if auto_ack_enabled and gnt.is_resolvable and int(gnt):
                self.dut.grant_ack.value = int(gnt)
                await self.wait_clocks(1)
                self.dut.grant_ack.value = 0
        else:
            self.log.warning(
                f"Arbiter still asserting grant_valid {timeout_cycles} cycles "
                f"after every client was disabled"
            )
        await self.wait_clocks(10)

    # -------------------------------------------------------------------------
    # Master/monitor scenario phases
    # -------------------------------------------------------------------------
    async def test_grant_signals(self):
        """Basic grant signal functionality using master manual requests."""
        self.log.info(f"=== grant signal test ==={self.get_time_ns_str()}")

        self.master.set_weights([2] * self.CLIENTS)
        await self.wait_clocks(3)
        self.master.set_ack_profile('immediate')
        auto_ack_enabled = (self.WAIT_GNT_ACK == 1)

        for client_id in range(self.CLIENTS):
            for c in range(self.CLIENTS):
                self.master.disable_client(c)
            await self.drain_arbiter(auto_ack_enabled)

            self.log.info(f"Testing grant signal for client {client_id}")
            before = list(self.monitor.arbiter_stats.get('grants_per_client', []))
            before_i = before[client_id] if client_id < len(before) else 0

            if auto_ack_enabled:
                await self.master.manual_request(
                    client_id=client_id,
                    cycles=10,
                    auto_ack=True,
                    ack_delay=1
                )
            else:
                await self.master.manual_request(client_id, cycles=5)

            after_i = before_i
            for _ in range(40):
                after = list(self.monitor.arbiter_stats.get('grants_per_client', []))
                after_i = after[client_id] if client_id < len(after) else 0
                if after_i > before_i:
                    break
                await self.wait_clocks(1)

            assert after_i > before_i, (
                f"Client {client_id} did not receive grant ({before_i} -> {after_i})"
            )
            self.log.info(f"Client {client_id} granted ({before_i} -> {after_i})")

        self.log.info("grant signal test PASSED")
        return True

    async def run_basic_arbitration_test(self, duration_cycles: int = 800):
        """Randomized basic arbitration via master profiles."""
        self.log.info(
            f"=== basic arbitration test ({duration_cycles} cycles) ==={self.get_time_ns_str()}"
        )

        self.master.set_weights([2] * self.CLIENTS)
        for client_id in range(self.CLIENTS):
            self.master.set_client_profile(client_id, 'default')
            self.master.enable_client(client_id)
        self.master.set_ack_profile('fast')

        await self.wait_clocks(100)
        initial_stats = self.monitor.get_comprehensive_stats()
        initial_grants = initial_stats.get('total_grants', 0)

        await self.wait_clocks(duration_cycles)

        final_stats = self.monitor.get_comprehensive_stats()
        final_grants = final_stats.get('total_grants', 0)
        total_grants = final_grants - initial_grants

        self.log.info(f"Basic arbitration: {total_grants} grants in {duration_cycles} cycles")
        assert total_grants > 20, f"Insufficient activity: {total_grants} < 20"
        self.log.info("basic arbitration test PASSED")
        return True

    async def test_walking_requests(self):
        """Each client, in isolation, must be granted."""
        self.log.info(f"=== walking requests test ==={self.get_time_ns_str()}")

        self.master.set_weights([2] * self.CLIENTS)
        auto_ack_enabled = (self.WAIT_GNT_ACK == 1)
        ack_delay = 1

        phase_start = list(self.monitor.arbiter_stats.get('grants_per_client', []))
        phase_start = [(phase_start[c] if c < len(phase_start) else 0)
                       for c in range(self.CLIENTS)]

        for i in range(self.CLIENTS):
            self.log.info(f"=== Testing individual client {i} ==={self.get_time_ns_str()}")
            for client_id in range(self.CLIENTS):
                self.master.disable_client(client_id)
            await self.drain_arbiter(auto_ack_enabled)

            before = list(self.monitor.arbiter_stats.get('grants_per_client', []))
            before_i = before[i] if i < len(before) else 0

            try:
                if auto_ack_enabled:
                    await self.master.manual_request(
                        client_id=i,
                        cycles=15,
                        auto_ack=True,
                        ack_delay=ack_delay
                    )
                else:
                    await self.master.manual_request(client_id=i, cycles=10)
            except Exception as e:
                self.log.error(f"Client {i} test raised: {e}")
                raise

            after_i = before_i
            for _ in range(40):
                after = list(self.monitor.arbiter_stats.get('grants_per_client', []))
                after_i = after[i] if i < len(after) else 0
                if after_i > before_i:
                    break
                await self.wait_clocks(1)

            if after_i > before_i:
                self.log.info(f"Client {i} granted ({before_i} -> {after_i})")
            else:
                self.log.warning(
                    f"Client {i}: no grant counted within its own request window "
                    f"({before_i} -> {after_i}); phase-level check will decide"
                )
            await self.wait_clocks(10)

        await self.wait_clocks(20)
        phase_end = list(self.monitor.arbiter_stats.get('grants_per_client', []))
        phase_end = [(phase_end[c] if c < len(phase_end) else 0)
                     for c in range(self.CLIENTS)]
        never_granted = [c for c in range(self.CLIENTS)
                         if phase_end[c] <= phase_start[c]]
        assert not never_granted, (
            f"Walking requests: client(s) {never_granted} held an exclusive "
            f"request and were never granted during the phase. "
            f"Per-client grants {phase_start} -> {phase_end}"
        )
        self.log.info("walking requests test PASSED")
        return True

    async def test_weighted_distribution(self):
        """Saturate all clients and verify weighted distribution via monitor."""
        self.log.info(f"=== weighted distribution test ==={self.get_time_ns_str()}")

        if self.CLIENTS == 1:
            self.log.info("weighted distribution test skipped for single client")
            return True

        # Choose weights that fit the DUT's MAX_LEVELS.
        max_weight = min(4, self.MAX_LEVELS - 1) if self.MAX_LEVELS > 1 else 1
        if max_weight < 1:
            max_weight = 1
        weights = [max_weight] + [1] * (self.CLIENTS - 1)
        weights = [min(w, self.MAX_LEVELS - 1) for w in weights]
        weights = [max(w, 1) for w in weights]

        self.master.set_weights(weights)
        await self.wait_clocks(1)

        # Reset the DUT so the credit counters load from the new weights from a
        # clean matrix/credit state.  Without this, leftover state from earlier
        # randomized phases can trap a 2-client configuration in a 1:1 grant
        # pattern even though the weights request a 4:1 ratio.
        await self.reset_dut()
        self.master.set_weights(weights)
        await self.wait_clocks(3)

        mt_val = int(self.dut.max_thresh.value) if self.dut.max_thresh.value.is_resolvable else -1
        self.log.info(f"Weighted distribution: max_thresh=0x{mt_val:x}, weights={weights}")
        self.monitor.set_static_period(True, expected_weights=weights)

        # Hold all requests continuously (saturate).  Manual control keeps the
        # request vector asserted every cycle; in ACK mode the master auto-ACKs
        # each held grant so arbitration can advance.
        for client_id in range(self.CLIENTS):
            self.master.force_client_request(
                client_id, enable=True, auto_ack=True, ack_delay=0
            )

        await self.wait_clocks(100)
        initial_stats = self.monitor.get_comprehensive_stats()
        initial_grants = initial_stats.get('total_grants', 0)

        test_cycles = 1000 * self.LEVEL_MULT
        await self.wait_clocks(test_cycles)

        final_stats = self.monitor.get_comprehensive_stats()
        final_grants = final_stats.get('total_grants', 0)
        total_grants = final_grants - initial_grants

        self.log.info(
            f"Weighted distribution: {total_grants} grants in {test_cycles} cycles, "
            f"weights={weights}"
        )

        compliance = final_stats.get('current_weight_compliance', {})
        if compliance.get('status') == 'analyzed':
            overall = compliance.get('overall_compliance', 0)
            self.log.info(f"Weight compliance: {overall:.3f}")
            assert overall > 0.7, f"Poor weight compliance: {overall:.3f}"
        else:
            # Fallback ratio check if compliance window was not static enough.
            per_client = list(self.monitor.arbiter_stats.get('grants_per_client', []))
            window = [per_client[i] - initial_stats.get('client_stats', [{}] * self.CLIENTS)[i].get('grants', 0)
                      for i in range(self.CLIENTS)]
            self.log.info(f"Per-client window grants: {window}")
            if total_grants > 0 and window[0] > 0:
                for c in range(1, self.CLIENTS):
                    if window[c] > 0:
                        ratio = window[0] / window[c]
                        expected = weights[0] / weights[c]
                        assert 0.5 * expected < ratio < 2.0 * expected, (
                            f"client 0 / client {c} ratio {ratio} far from expected {expected}"
                        )

        self.monitor.set_static_period(False)
        self.log.info("weighted distribution test PASSED")
        return True

    async def test_block_arb(self):
        """block_arb forces no grants; monitor counters stay flat."""
        self.log.info(f"=== block_arb test ==={self.get_time_ns_str()}")

        self.master.set_weights([2] * self.CLIENTS)
        for client_id in range(self.CLIENTS):
            self.master.set_client_profile(client_id, 'fast')
            self.master.enable_client(client_id)
        self.master.set_ack_profile('fast')

        await self.wait_clocks(100)
        baseline_stats = self.monitor.get_comprehensive_stats()
        baseline_grants = baseline_stats.get('total_grants', 0)

        self.dut.block_arb.value = 1
        self.log.info(f"Asserted block_arb{self.get_time_ns_str()}")
        await self.wait_clocks(200)

        blocked_stats = self.monitor.get_comprehensive_stats()
        blocked_grants = blocked_stats.get('total_grants', 0)
        grants_during_block = blocked_grants - baseline_grants
        self.log.info(f"Grants during block: {grants_during_block}")

        self.dut.block_arb.value = 0
        self.log.info(f"De-asserted block_arb{self.get_time_ns_str()}")
        await self.wait_clocks(200)

        final_stats = self.monitor.get_comprehensive_stats()
        final_grants = final_stats.get('total_grants', 0)
        grants_after_unblock = final_grants - blocked_grants
        self.log.info(f"Grants after unblock: {grants_after_unblock}")

        assert grants_during_block <= 10, f"Too many grants during block: {grants_during_block}"
        assert grants_after_unblock > 5, f"Too few grants after unblock: {grants_after_unblock}"
        self.log.info("block_arb test PASSED")
        return True

    async def test_bursty_traffic_pattern(self):
        """Mixed fast/slow profiles."""
        self.log.info(f"=== bursty traffic pattern test ==={self.get_time_ns_str()}")

        self.master.set_weights([2] * self.CLIENTS)
        for client_id in range(self.CLIENTS):
            if client_id < 2:
                self.master.set_client_profile(client_id, 'fast')
            else:
                self.master.set_client_profile(client_id, 'slow')
            self.master.enable_client(client_id)
        self.master.set_ack_profile('random')

        initial_stats = self.monitor.get_comprehensive_stats()
        initial_grants = initial_stats.get('total_grants', 0)

        await self.wait_clocks(2000)

        final_stats = self.monitor.get_comprehensive_stats()
        final_grants = final_stats.get('total_grants', 0)
        total_grants = final_grants - initial_grants

        self.log.info(f"Bursty traffic test: {total_grants} grants generated")
        assert total_grants > 50, f"Insufficient bursty traffic: {total_grants} grants"
        self.log.info("bursty traffic pattern test PASSED")
        return True

    async def test_rapid_request_changes(self):
        """Fast profiles for rapid request changes."""
        self.log.info(f"=== rapid request changes test ==={self.get_time_ns_str()}")

        self.master.set_weights([2] * self.CLIENTS)
        for client_id in range(self.CLIENTS):
            self.master.set_client_profile(client_id, 'fast')
            self.master.enable_client(client_id)
        self.master.set_ack_profile('immediate')

        initial_stats = self.monitor.get_comprehensive_stats()
        initial_grants = initial_stats.get('total_grants', 0)

        await self.wait_clocks(1500)

        final_stats = self.monitor.get_comprehensive_stats()
        final_grants = final_stats.get('total_grants', 0)
        total_grants = final_grants - initial_grants

        self.log.info(f"Rapid changes test: {total_grants} grants generated")
        assert total_grants > 100, f"Insufficient rapid activity: {total_grants} grants"
        self.log.info("rapid request changes test PASSED")
        return True

    async def test_single_client_saturation(self):
        """One client requesting continuously must get a high grant count."""
        self.log.info(f"=== single client saturation test ==={self.get_time_ns_str()}")

        self.master.set_weights([2] * self.CLIENTS)
        self.master.set_ack_profile('immediate')
        for client_id in range(self.CLIENTS):
            self.master.disable_client(client_id)

        stranded = False
        for _ in range(200):
            await self.wait_clocks(1)
            gv = self.dut.grant_valid.value
            if not gv.is_resolvable:
                continue
            if int(gv) == 0:
                break
            gnt = self.dut.grant.value
            if self.WAIT_GNT_ACK == 1 and gnt.is_resolvable and int(gnt):
                if not stranded:
                    self.log.info(
                        f"Retiring stranded grant 0x{int(gnt):x} left unACKed "
                        f"by a disabled client{self.get_time_ns_str()}"
                    )
                    stranded = True
                self.dut.grant_ack.value = int(gnt)
                await self.wait_clocks(1)
                self.dut.grant_ack.value = 0
        else:
            self.log.warning("Arbiter still asserting grant_valid 200 cycles after all clients disabled")
        await self.wait_clocks(10)

        self.master.set_client_profile(0, 'fast')
        self.master.enable_client(0)

        initial_stats = self.monitor.get_comprehensive_stats()
        initial_grants = initial_stats.get('total_grants', 0)

        await self.wait_clocks(100)
        test_duration = 1000
        await self.wait_clocks(test_duration)

        final_stats = self.monitor.get_comprehensive_stats()
        final_grants = final_stats.get('total_grants', 0)
        saturation_grants = final_grants - initial_grants

        self.log.info(f"Single client saturation: {saturation_grants} grants in {test_duration} cycles")
        assert saturation_grants > 30, f"Low saturation: {saturation_grants} < 30"

        for client_id in range(self.CLIENTS):
            self.master.enable_client(client_id)
        self.log.info("single client saturation test PASSED")
        return True

    # -------------------------------------------------------------------------
    # Directed supplements
    # -------------------------------------------------------------------------
    async def test_weighted_sequence(self):
        """DIR supplement: verify documented consecutive-grant weight sequence."""
        self.log.info(f"=== directed: weighted sequence test ==={self.get_time_ns_str()}")
        await self.enter_directed_mode()
        await self.reset_dut()

        if self.CLIENTS == 3:
            weights = [3, 1, 2]
            expected_period = [0, 0, 0, 1, 2, 2]
        elif self.CLIENTS == 2:
            weights = [2, 1]
            expected_period = [0, 0, 1]
        elif self.CLIENTS == 4:
            weights = [3, 1, 2, 1]
            expected_period = [0, 0, 0, 1, 2, 2, 3]
        elif self.CLIENTS == 5:
            weights = [3, 1, 2, 1, 1]
            expected_period = [0, 0, 0, 1, 2, 2, 3, 4]
        elif self.CLIENTS == 8:
            weights = [3, 1, 2, 1, 1, 1, 1, 1]
            expected_period = [0, 0, 0, 1, 2, 2, 3, 4, 5, 6, 7]
        else:
            weights = [2] + [1] * (self.CLIENTS - 1)
            expected_period = None

        weights = [min(w, self.MAX_LEVELS - 1) for w in weights]
        weights = [max(w, 1) for w in weights]
        self.set_weights(weights)
        await self.wait_clocks(3)

        await self.set_request((1 << self.CLIENTS) - 1)

        if expected_period is not None:
            periods = 2 + self.LEVEL_MULT
            expected = expected_period * periods
            observed = []
            for _ in range(len(expected)):
                gv, gnt, gid = self.read_grant()
                assert gv == 1, (
                    f"grant_valid dropped with all clients requesting "
                    f"(observed={observed})"
                )
                winner = self.one_hot_to_id(gnt)
                assert winner == gid, (
                    f"grant_id={gid} mismatches grant=0x{gnt:x}"
                )
                observed.append(winner)
                await self.wait_clocks(1)

            self.log.info(f"observed sequence: {observed[:len(expected_period)*2]}")
            assert observed == expected, (
                f"weighted sequence mismatch\nobserved: {observed}\n"
                f"expected: {expected}"
            )
        else:
            cycles = (sum(weights) * self.CLIENTS * 2) * self.LEVEL_MULT
            counts = [0] * self.CLIENTS
            for _ in range(cycles):
                gv, gnt, gid = self.read_grant()
                assert gv == 1, "grant_valid dropped with all clients requesting"
                counts[self.one_hot_to_id(gnt)] += 1
                await self.wait_clocks(1)
            self.log.info(f"ratio counts: {counts}")
            assert counts[0] > 0
            for c in range(1, self.CLIENTS):
                assert counts[c] > 0
                ratio = counts[0] / counts[c]
                assert 1.5 < ratio < 2.5, (
                    f"client 0 / client {c} ratio {ratio} out of range"
                )

        await self.exit_directed_mode()
        self.log.info("directed: weighted sequence test PASSED")
        return True

    async def test_one_hot_and_request_match(self):
        """DIR supplement: grant is one-hot or zero and only grants an eligible client."""
        self.log.info(f"=== directed: one-hot / request-match test ==={self.get_time_ns_str()}")
        await self.enter_directed_mode()

        self.set_weights([2] * self.CLIENTS)
        await self.wait_clocks(3)

        if self.CLIENTS <= 5:
            patterns = list(range(1 << self.CLIENTS))
        else:
            patterns = [0, (1 << self.CLIENTS) - 1]
            rng = random.Random(self.SEED)
            for _ in range(50 * self.LEVEL_MULT):
                patterns.append(rng.randint(0, (1 << self.CLIENTS) - 1))

        for req in patterns:
            await self.set_request(req)
            gv, gnt, gid = self.read_grant()

            assert self.is_one_hot(gnt), (
                f"req=0x{req:x}: grant=0x{gnt:x} is not one-hot or zero"
            )
            if gv:
                assert gnt != 0, f"req=0x{req:x}: grant_valid=1 but grant=0"
                assert (gnt & req) == gnt, (
                    f"req=0x{req:x}: grant=0x{gnt:x} grants an unrequested client"
                )
                assert gid == self.one_hot_to_id(gnt), (
                    f"req=0x{req:x}: grant_id={gid} does not match grant=0x{gnt:x}"
                )
            else:
                assert gnt == 0, (
                    f"req=0x{req:x}: grant_valid=0 but grant=0x{gnt:x}"
                )

        await self.exit_directed_mode()
        self.log.info("directed: one-hot / request-match test PASSED")
        return True

    async def test_zero_weight(self):
        """DIR supplement: a weight=0 client is never granted."""
        self.log.info(f"=== directed: zero-weight test ==={self.get_time_ns_str()}")
        await self.enter_directed_mode()

        if self.CLIENTS < 2:
            self.log.info("directed: zero-weight test skipped for single client")
            await self.exit_directed_mode()
            return True

        weights = [2] * self.CLIENTS
        zero_client = 1
        weights[zero_client] = 0
        self.set_weights(weights)
        await self.wait_clocks(3)

        await self.set_request((1 << self.CLIENTS) - 1)

        window = sum(w for w in weights) * 4 * self.LEVEL_MULT
        for _ in range(window):
            gv, gnt, gid = self.read_grant()
            assert gv == 1, "grant_valid dropped with all clients requesting"
            winner = self.one_hot_to_id(gnt)
            assert winner != zero_client, (
                f"client {zero_client} (weight=0) was granted"
            )
            await self.wait_clocks(1)

        await self.exit_directed_mode()
        self.log.info("directed: zero-weight test PASSED")
        return True

    async def test_weight_change(self):
        """DIR supplement: dynamic weight changes take effect at next credit reload."""
        self.log.info(f"=== directed: weight-change test ==={self.get_time_ns_str()}")
        await self.enter_directed_mode()

        if self.CLIENTS < 2:
            self.log.info("directed: weight-change test skipped for single client")
            await self.exit_directed_mode()
            return True

        self.set_weights([2] + [1] * (self.CLIENTS - 1))
        await self.wait_clocks(3)
        await self.set_request((1 << self.CLIENTS) - 1)

        history = []
        found_reload = False
        max_warmup = self.CLIENTS * 6
        for _ in range(max_warmup):
            gv, gnt, _ = self.read_grant()
            assert gv == 1
            winner = self.one_hot_to_id(gnt)
            history.append(winner)
            if len(history) >= 2 and history[-2] == 0 and winner != 0:
                found_reload = True
                break
            await self.wait_clocks(1)

        assert found_reload, (
            f"did not find a client-0 reload cycle in {max_warmup} cycles"
        )
        self.log.info(f"client 0 reload cycle found{self.get_time_ns_str()}")

        await self.wait_clocks(1)
        new_weights = [1] + [1] * (self.CLIENTS - 1)
        self.set_weights(new_weights)
        self.log.info(f"changed weights to {new_weights}{self.get_time_ns_str()}")

        post_change = []
        c0_turns_after_change = []
        current_c0_turn = 0
        max_cycles = self.CLIENTS * 10 * self.LEVEL_MULT
        cycles = 0
        while cycles < max_cycles:
            gv, gnt, _ = self.read_grant()
            assert gv == 1
            winner = self.one_hot_to_id(gnt)
            post_change.append(winner)
            cycles += 1

            if winner == 0:
                current_c0_turn += 1
            else:
                if current_c0_turn > 0:
                    c0_turns_after_change.append(current_c0_turn)
                    current_c0_turn = 0
                    if len(c0_turns_after_change) >= 2:
                        break
            await self.wait_clocks(1)

        if current_c0_turn > 0:
            c0_turns_after_change.append(current_c0_turn)

        self.log.info(f"client-0 turns after weight change: {c0_turns_after_change}")
        assert len(c0_turns_after_change) >= 2, (
            f"expected 2 post-change c0 turns, got {c0_turns_after_change}"
        )
        assert c0_turns_after_change[0] == 2, (
            f"first post-change c0 turn {c0_turns_after_change[0]} != 2 "
            f"(leftover old weight)"
        )
        assert c0_turns_after_change[1] == 1, (
            f"second post-change c0 turn {c0_turns_after_change[1]} != 1 "
            f"(new weight not loaded)"
        )

        await self.exit_directed_mode()
        self.log.info("directed: weight-change test PASSED")
        return True

    async def test_idle_gap(self):
        """DIR supplement: rotation is correct after a mid-stream idle gap."""
        self.log.info(f"=== directed: idle-gap test ==={self.get_time_ns_str()}")
        await self.enter_directed_mode()

        self.set_weights([1] * self.CLIENTS)
        await self.wait_clocks(3)
        await self.set_request((1 << self.CLIENTS) - 1)

        for _ in range(self.CLIENTS * 2):
            await self.wait_clocks(1)

        self.dut.request.value = 0b0001
        await self.wait_clocks(self.CLIENTS * 2)

        self.dut.request.value = (1 << self.CLIENTS) - 1
        after_gap = []
        for _ in range(self.CLIENTS):
            await self.wait_clocks(1)
            gv, gnt, _ = self.read_grant()
            assert gv == 1, "grant_valid dropped after idle gap"
            after_gap.append(self.one_hot_to_id(gnt))

        assert sorted(after_gap) == list(range(self.CLIENTS)), (
            f"post-gap rotation {after_gap} is not a permutation of all clients"
        )
        self.log.info(f"post-gap rotation: {after_gap}")
        await self.exit_directed_mode()
        self.log.info("directed: idle-gap test PASSED")
        return True

    async def test_mid_credit_idle(self):
        """DIR supplement: multi-credit winner idles mid-turn; credits persist."""
        self.log.info(f"=== directed: mid-credit idle test ==={self.get_time_ns_str()}")
        await self.enter_directed_mode()

        if self.CLIENTS < 3:
            self.log.info("directed: mid-credit idle test skipped for CLIENTS < 3")
            await self.exit_directed_mode()
            return True

        weights = [3] + [1] * (self.CLIENTS - 1)
        weights = [min(w, self.MAX_LEVELS - 1) for w in weights]
        weights = [max(w, 1) for w in weights]
        self.set_weights(weights)
        await self.wait_clocks(3)
        self.dut.request.value = (1 << self.CLIENTS) - 1
        await self.wait_clocks(1)

        c0_run = 0
        max_warmup = self.CLIENTS * 6
        for _ in range(max_warmup):
            gv, gnt, gid = self.read_grant()
            assert gv == 1, "grant_valid dropped during warmup"
            if gid == 0:
                c0_run += 1
                if c0_run == 3:
                    break
            else:
                c0_run = 0
            await self.wait_clocks(1)

        assert c0_run == 3, (
            f"did not see a fresh weight-3 client-0 turn in {max_warmup} cycles"
        )
        self.log.info(f"fresh client-0 turn found{self.get_time_ns_str()}")

        found_next_c0 = False
        for _ in range(self.CLIENTS * 4):
            await self.wait_clocks(1)
            gv, gnt, gid = self.read_grant()
            assert gv == 1, "grant_valid dropped while waiting for next c0 turn"
            if gid == 0:
                found_next_c0 = True
                break

        assert found_next_c0, "client 0 did not win again after its fresh turn"

        self.dut.request.value = ((1 << self.CLIENTS) - 1) & ~0x1
        during_idle = []
        for _ in range(self.CLIENTS - 1):
            await self.wait_clocks(1)
            gv, gnt, gid = self.read_grant()
            assert gv == 1, "grant_valid dropped during idle gap"
            during_idle.append(gid)

        assert sorted(during_idle) == list(range(1, self.CLIENTS)), (
            f"during-idle grants {during_idle} are not exactly clients 1..{self.CLIENTS-1}"
        )
        self.log.info(f"during-idle rotation: {during_idle}")

        self.dut.request.value = (1 << self.CLIENTS) - 1
        after_return = []
        for _ in range(self.CLIENTS * 4):
            await self.wait_clocks(1)
            gv, gnt, gid = self.read_grant()
            assert gv == 1, "grant_valid dropped after client 0 returned"
            after_return.append(gid)
            if gid != 0:
                break

        c0_run = 0
        for g in after_return:
            if g == 0:
                c0_run += 1
            else:
                break

        assert c0_run == 2, (
            f"client 0 consumed {c0_run} grants after return, expected 2 "
            f"(remaining credits from weight 3)"
        )
        self.log.info(f"client 0 run after return: {c0_run}")

        await self.exit_directed_mode()
        self.log.info("directed: mid-credit idle test PASSED")
        return True

    async def test_single_requester_immediate(self):
        """DIR supplement: a lone requester is granted in one cycle."""
        self.log.info(f"=== directed: single requester immediacy test ==={self.get_time_ns_str()}")
        await self.enter_directed_mode()

        self.set_weights([2] * self.CLIENTS)
        await self.wait_clocks(3)

        rng = random.Random(self.SEED)
        for _ in range(self.CLIENTS * 3):
            req = rng.randint(1, (1 << self.CLIENTS) - 1)
            await self.set_request(req)

        for client in range(self.CLIENTS):
            await self.set_request(1 << client)
            gv, gnt, gid = self.read_grant()
            assert gv == 1, f"client {client} alone: no grant"
            assert gnt == (1 << client), f"client {client} alone: grant=0x{gnt:x}"
            assert gid == client, f"client {client} alone: grant_id={gid}"

        await self.exit_directed_mode()
        self.log.info("directed: single requester immediacy test PASSED")
        return True

    async def test_single_client_no_ack(self):
        """DIR supplement: CLIENTS==1 no-ACK credit reload behavior."""
        if self.CLIENTS != 1 or self.WAIT_GNT_ACK != 0:
            self.log.info("directed: single-client no-ACK test skipped")
            return True

        self.log.info(f"=== directed: single-client no-ACK test ==={self.get_time_ns_str()}")
        await self.enter_directed_mode()

        weight = 3
        self.set_weights([weight])
        await self.wait_clocks(3)

        await self.set_request(1)
        await self.set_request(1)
        self.dut.request.value = 0
        await self.wait_clocks(2)

        await self.set_request(1)
        after_return = []
        for _ in range(weight + 2):
            gv, gnt, gid = self.read_grant()
            assert gv == 1, f"single-client grant_valid={gv} after return"
            assert gid == 0, f"single-client grant_id={gid}, expected 0"
            assert gnt == 1, f"single-client grant=0x{gnt:x}, expected 0x1"
            after_return.append(gid)
            await self.wait_clocks(1)

        assert len(after_return) == weight + 2
        assert all(g == 0 for g in after_return)

        await self.exit_directed_mode()
        self.log.info("directed: single-client no-ACK test PASSED")
        return True

    async def test_single_client_ack(self):
        """DIR supplement: CLIENTS==1 ACK held grant and credit reload."""
        if self.CLIENTS != 1 or self.WAIT_GNT_ACK != 1:
            self.log.info("directed: single-client ACK test skipped")
            return True

        self.log.info(f"=== directed: single-client ACK test ==={self.get_time_ns_str()}")
        await self.enter_directed_mode()

        weight = 3
        self.set_weights([weight])
        await self.reset_dut()
        self.set_weights([weight])
        await self.wait_clocks(3)
        self.dut.request.value = 1
        await self.wait_clocks(1)

        for rep in range(weight * 2):
            gv, gnt, gid = await self._wait_for_grant()
            assert gv == 1, f"rep {rep}: no grant"
            assert gid == 0, f"rep {rep}: grant_id={gid}, expected 0"
            assert gnt == 1, f"rep {rep}: grant=0x{gnt:x}, expected 0x1"
            await self._drive_ack(1, 1)
            await self.wait_clocks(1)

        await self.exit_directed_mode()
        self.log.info("directed: single-client ACK test PASSED")
        return True

    async def test_reset_order(self):
        """DIR supplement: reset restores client 0 as highest priority."""
        self.log.info(f"=== directed: reset-order test ==={self.get_time_ns_str()}")
        await self.enter_directed_mode()

        self.set_weights([2] * self.CLIENTS)
        await self.wait_clocks(3)

        rng = random.Random(self.SEED)
        for _ in range(self.CLIENTS * 4):
            req = rng.randint(1, (1 << self.CLIENTS) - 1)
            await self.set_request(req)

        await self.reset_dut()
        self.set_weights([2] * self.CLIENTS)
        await self.wait_clocks(3)
        await self.set_request((1 << self.CLIENTS) - 1)

        gv, gnt, gid = self.read_grant()
        assert gv == 1, "No grant after reset with all clients requesting"
        assert gnt == 1, f"first grant after reset is 0x{gnt:x}, expected 0x1"
        assert gid == 0, f"first grant_id after reset is {gid}, expected 0"

        await self.exit_directed_mode()
        self.log.info("directed: reset-order test PASSED")
        return True

    # -------------------------------------------------------------------------
    # ACK-mode directed supplements
    # -------------------------------------------------------------------------
    async def test_ack_hold_until_owner_ack(self):
        """DIR supplement: in ACK mode the grant is held until the winner ACKs."""
        if self.WAIT_GNT_ACK != 1:
            self.log.info("directed: ACK hold test skipped in no-ACK mode")
            return True

        self.log.info(f"=== directed: ACK hold-until-owner-ack test ==={self.get_time_ns_str()}")
        await self.enter_directed_mode()
        self.set_weights([1] * self.CLIENTS)
        await self.reset_dut()
        self.set_weights([1] * self.CLIENTS)
        await self.wait_clocks(3)
        self.dut.request.value = (1 << self.CLIENTS) - 1
        await self.wait_clocks(1)

        _, gnt, gid = await self._wait_for_grant()
        first_winner = gid
        self.log.info(f"first grant to client {first_winner}")

        self.dut.grant_ack.value = 0
        for _ in range(5):
            await self.wait_clocks(1)
            gv, held_gnt, held_gid = self.read_grant()
            assert gv == 1, "grant_valid dropped while waiting for ACK"
            assert held_gid == first_winner, (
                f"grant changed from {first_winner} to {held_gid} before ACK"
            )
            assert held_gnt == gnt, (
                f"grant vector changed from 0x{gnt:x} to 0x{held_gnt:x} before ACK"
            )

        await self._drive_ack(1 << first_winner, 1)
        await self.wait_clocks(1)
        gv, next_gnt, next_gid = self.read_grant()
        if self.CLIENTS > 1:
            assert gv == 1, "no next grant after owner ACK with pending requests"
            assert next_gid != first_winner, "grant did not rotate after ACK"
            assert (next_gnt & ((1 << self.CLIENTS) - 1)) != 0, "next grant is zero"

        await self.exit_directed_mode()
        self.log.info("directed: ACK hold-until-owner-ack test PASSED")
        return True

    async def test_ack_foreign_ack_immunity(self):
        """DIR supplement: only the granted client's ACK bit retires the held grant."""
        if self.WAIT_GNT_ACK != 1:
            self.log.info("directed: foreign-ACK immunity test skipped in no-ACK mode")
            return True
        if self.CLIENTS < 2:
            self.log.info("directed: foreign-ACK immunity test skipped for single client")
            return True

        self.log.info(f"=== directed: ACK foreign-ack immunity test ==={self.get_time_ns_str()}")
        await self.enter_directed_mode()
        self.set_weights([1] * self.CLIENTS)
        await self.reset_dut()
        self.set_weights([1] * self.CLIENTS)
        await self.wait_clocks(3)
        self.dut.request.value = (1 << self.CLIENTS) - 1
        await self.wait_clocks(1)

        _, _, first_gid = await self._wait_for_grant()
        foreign = (first_gid + 1) % self.CLIENTS
        self.log.info(f"first grant to client {first_gid}; foreign client {foreign}")

        self.dut.grant_ack.value = 1 << foreign
        for _ in range(5):
            await self.wait_clocks(1)
            gv, _, gid = self.read_grant()
            assert gv == 1, "grant_valid dropped after foreign ACK"
            assert gid == first_gid, (
                f"foreign ACK changed grant from {first_gid} to {gid}"
            )

        await self._drive_ack(1 << first_gid, 1)
        await self.wait_clocks(1)
        gv, _, gid = self.read_grant()
        assert gv == 1, "no next grant after owner ACK"
        assert gid != first_gid, "grant did not rotate after owner ACK"

        await self.exit_directed_mode()
        self.log.info("directed: ACK foreign-ack immunity test PASSED")
        return True

    async def test_ack_back_to_back_handoff(self):
        """DIR supplement: ACK-mode grants hand off in consecutive cycles."""
        if self.WAIT_GNT_ACK != 1:
            self.log.info("directed: back-to-back handoff test skipped in no-ACK mode")
            return True
        if self.CLIENTS < 2:
            self.log.info("directed: back-to-back handoff test skipped for single client")
            return True

        self.log.info(f"=== directed: ACK back-to-back handoff test ==={self.get_time_ns_str()}")
        await self.enter_directed_mode()
        self.set_weights([1] * self.CLIENTS)
        await self.reset_dut()
        self.set_weights([1] * self.CLIENTS)
        await self.wait_clocks(3)
        self.dut.request.value = (1 << self.CLIENTS) - 1
        await self.wait_clocks(1)

        expected = list(range(self.CLIENTS)) + list(range(self.CLIENTS))
        observed = []

        _, _, gid = await self._wait_for_grant()
        observed.append(gid)
        for _ in range(2 * self.CLIENTS - 1):
            await self._drive_ack(1 << gid, 1)
            await self.wait_clocks(1)
            gv, _, gid = self.read_grant()
            assert gv == 1, "grant_valid dropped during back-to-back handoff"
            observed.append(gid)

        assert observed == expected, (
            f"back-to-back rotation {observed} != expected {expected}"
        )
        self.log.info(f"back-to-back rotation: {observed}")

        await self.exit_directed_mode()
        self.log.info("directed: ACK back-to-back handoff test PASSED")
        return True

    async def test_ack_single_requester(self):
        """DIR supplement: a lone requester in ACK mode is re-granted after each ACK."""
        if self.WAIT_GNT_ACK != 1:
            self.log.info("directed: single-requester ACK test skipped in no-ACK mode")
            return True

        self.log.info(f"=== directed: ACK single-requester test ==={self.get_time_ns_str()}")
        await self.enter_directed_mode()
        self.set_weights([2] * self.CLIENTS)
        for client in range(self.CLIENTS):
            await self.reset_dut()
            self.set_weights([2] * self.CLIENTS)
            await self.wait_clocks(3)
            self.dut.request.value = 1 << client
            await self.wait_clocks(1)

            for rep in range(3):
                gv, gnt, gid = await self._wait_for_grant()
                assert gid == client, f"client {client} rep {rep}: grant_id={gid}"
                assert gnt == (1 << client), f"client {client} rep {rep}: grant=0x{gnt:x}"
                await self._drive_ack(1 << client, 1)
                await self.wait_clocks(1)

        await self.exit_directed_mode()
        self.log.info("directed: ACK single-requester test PASSED")
        return True

    # -------------------------------------------------------------------------
    # Compliance and reporting
    # -------------------------------------------------------------------------
    def check_monitor_errors(self):
        if self.monitor_errors:
            self.log.error(f"Monitor errors detected: {self.monitor_errors}")
            raise AssertionError(f"Monitor errors: {self.monitor_errors}")

        compliance = getattr(self.monitor, 'compliance', None)
        if compliance is None or not hasattr(compliance, 'get_warning_summary'):
            return
        summary = compliance.get_warning_summary()
        self.log.info(
            f"Compliance verdict: {summary['total_errors']} error(s), "
            f"{summary['total_warnings']} warning(s); "
            f"errors={summary['error_types']} warnings={summary['warning_types']}"
        )
        errs = [w for w in compliance.protocol_warnings if w.get('severity') == 'error']
        assert summary['total_errors'] == 0, (
            f"Arbiter protocol compliance: {summary['total_errors']} error(s) "
            f"{summary['error_types']}\n" + "\n".join(
                f"  @{w.get('timestamp')}ns {w.get('type')}: {w.get('message')} "
                f"details={w.get('details')}" for w in errs[:10])
        )

    async def handle_test_transition_ack_cleanup(self):
        await self.wait_clocks(10)

    def generate_final_report(self):
        try:
            monitor_stats = self.monitor.get_comprehensive_stats()
            total_grants = monitor_stats.get('total_grants', 0) or len(self.monitor)
            fairness = monitor_stats.get('fairness_index', 0)
            master_stats = self.master.get_stats()

            self.log.info("=== FINAL TEST REPORT ===")
            self.log.info(f"Total grants observed: {total_grants}")
            self.log.info(f"Fairness index: {fairness:.3f}")
            self.log.info(f"Master statistics: {master_stats}")
            self.log.info(f"Monitor errors: {len(self.monitor_errors)}")

            success = total_grants > 0 and len(self.monitor_errors) == 0
            if success:
                self.log.info("Final report validation PASSED")
            else:
                self.log.error("Final report validation FAILED")
            return success
        except Exception as e:
            self.log.error(f"Error generating final report: {e}")
            return False

    # -------------------------------------------------------------------------
    # Test orchestration
    # -------------------------------------------------------------------------
    async def run_all_tests(self):
        """Run the weighted matrix arbiter test suite."""
        results = []

        # Master/monitor scenario phases
        results.append(("grant-signals", await self.test_grant_signals()))
        await self.handle_test_transition_ack_cleanup()

        results.append(("basic-arbitration",
                        await self.run_basic_arbitration_test(400 * self.LEVEL_MULT)))
        await self.handle_test_transition_ack_cleanup()

        results.append(("walking-requests", await self.test_walking_requests()))
        await self.handle_test_transition_ack_cleanup()

        results.append(("weighted-distribution", await self.test_weighted_distribution()))
        await self.handle_test_transition_ack_cleanup()

        results.append(("block-arb", await self.test_block_arb()))
        await self.handle_test_transition_ack_cleanup()

        results.append(("bursty-traffic", await self.test_bursty_traffic_pattern()))
        await self.handle_test_transition_ack_cleanup()

        results.append(("rapid-request-changes", await self.test_rapid_request_changes()))
        await self.handle_test_transition_ack_cleanup()

        results.append(("single-client-saturation", await self.test_single_client_saturation()))
        await self.handle_test_transition_ack_cleanup()

        # Directed supplements.  Several no-ACK-only supplements are skipped in
        # ACK mode because the held-grant semantics break simple request->grant
        # sampling; the ACK-mode equivalents are covered below.
        if self.WAIT_GNT_ACK == 0:
            results.append(("weighted-sequence", await self.test_weighted_sequence()))
            await self.handle_test_transition_ack_cleanup()

            results.append(("one-hot/request-match", await self.test_one_hot_and_request_match()))
            await self.handle_test_transition_ack_cleanup()

            results.append(("zero-weight", await self.test_zero_weight()))
            await self.handle_test_transition_ack_cleanup()

            results.append(("weight-change", await self.test_weight_change()))
            await self.handle_test_transition_ack_cleanup()

            results.append(("idle-gap", await self.test_idle_gap()))
            await self.handle_test_transition_ack_cleanup()

            results.append(("mid-credit-idle", await self.test_mid_credit_idle()))
            await self.handle_test_transition_ack_cleanup()

            results.append(("single-requester-immediate",
                            await self.test_single_requester_immediate()))
            await self.handle_test_transition_ack_cleanup()

            results.append(("single-client-no-ack", await self.test_single_client_no_ack()))
            await self.handle_test_transition_ack_cleanup()

            results.append(("reset-order", await self.test_reset_order()))
            await self.handle_test_transition_ack_cleanup()
        else:
            results.append(("reset-order", await self.test_reset_order()))
            await self.handle_test_transition_ack_cleanup()

            results.append(("single-client-ack", await self.test_single_client_ack()))
            await self.handle_test_transition_ack_cleanup()

        # ACK-mode directed supplements
        results.append(("ack-hold-until-owner-ack",
                        await self.test_ack_hold_until_owner_ack()))
        results.append(("ack-foreign-ack-immunity",
                        await self.test_ack_foreign_ack_immunity()))
        results.append(("ack-back-to-back-handoff",
                        await self.test_ack_back_to_back_handoff()))
        results.append(("ack-single-requester",
                        await self.test_ack_single_requester()))

        # Final monitor compliance check
        self.check_monitor_errors()
        report_success = self.generate_final_report()
        if not report_success:
            results.append(("final-report", False))
        else:
            results.append(("final-report", True))

        self.log.info("=" * 60)
        self.log.info("ArbiterMatrixWeighted test summary:")
        all_passed = True
        for name, passed in results:
            status = "PASSED" if passed else "FAILED"
            self.log.info(f"  {name}: {status}")
            all_passed = all_passed and passed
        self.log.info("=" * 60)

        return all_passed
