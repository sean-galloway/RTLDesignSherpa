# SPDX-License-Identifier: MIT
# SPDX-FileCopyrightText: 2024-2026 sean galloway
#
# RTL Design Sherpa - Industry-Standard RTL Design and Verification
# https://github.com/sean-galloway/RTLDesignSherpa
#
# Module: ArbiterMatrixTB
# Purpose: Testbench for the matrix (distributed-state) fair arbiter using
#          ArbiterMaster stimulus and ArbiterMonitor checking.
#
# Documentation: cocotb-framework PyPI package
# Subsystem: framework
#
# Author: sean galloway
# Created: 2026-10-11

"""
Testbench for arbiter_matrix.

Follows the same ArbiterMaster / ArbiterMonitor methodology as
ArbiterRoundRobinTB.  Randomized scenario phases drive stimulus through the
master and assert through the monitor (grant one-hot, no unrequested grants,
rotation/fairness).  Directed supplements exercise corner cases that the
master/monitor cannot express deterministically.
"""

import os
import random
import cocotb
from cocotb.clock import Clock
from cocotb.triggers import RisingEdge, FallingEdge, Timer, ClockCycles
from cocotb.utils import get_sim_time

from TBClasses.shared.tbbase import TBBase
from CocoTBFramework.components.shared.arbiter_monitor import RoundRobinArbiterMonitor
from CocoTBFramework.components.shared.arbiter_master import ArbiterMaster


class ArbiterMatrixTB(TBBase):
    """Matrix fair arbiter testbench with ArbiterMaster/ArbiterMonitor."""

    def __init__(self, dut):
        super().__init__(dut)

        self.CLIENTS = int(dut.CLIENTS)
        self.WAIT_GNT_ACK = int(dut.WAIT_GNT_ACK)
        self.SEED = self.convert_to_int(os.environ.get('SEED', '0'))
        random.seed(self.SEED)

        self.TEST_LEVEL = os.environ.get('TEST_LEVEL', 'gate').lower()
        if self.TEST_LEVEL not in ('gate', 'func', 'full'):
            self.TEST_LEVEL = 'gate'
        self.LEVEL_MULT = {'gate': 1, 'func': 2, 'full': 5}[self.TEST_LEVEL]

        # Monitor: matrix arbiter is observationally equivalent to RR, so the
        # RR monitor (and its mask-replay compliance model) applies.
        self.monitor = RoundRobinArbiterMonitor(
            dut=dut,
            title="Matrix_Monitor",
            clock=self.dut.clk,
            reset_n=self.dut.rst_n,
            req_signal=self.dut.request,
            gnt_valid_signal=self.dut.grant_valid,
            gnt_signal=self.dut.grant,
            gnt_id_signal=self.dut.grant_id,
            gnt_ack_signal=self.dut.grant_ack,
            block_arb_signal=self.dut.block_arb,
            clients=self.CLIENTS,
            ack_mode=(self.WAIT_GNT_ACK == 1),
            log=self.log,
            clock_period_ns=10
        )

        # Master: drives requests and handles ACKs for enabled clients.
        self.master = ArbiterMaster(
            dut=dut,
            title="Matrix Driver",
            clock=self.dut.clk,
            num_clients=self.CLIENTS,
            ack_mode=(self.WAIT_GNT_ACK == 1),
            log=self.log
        )

        self.monitor_errors = []
        self.monitor.add_transaction_callback(self._on_monitor_transaction)
        self.monitor.add_reset_callback(self._on_monitor_reset)
        self.monitor.enable_debug()

        if hasattr(self.monitor, 'compliance'):
            self.monitor.compliance.ack_timeout_cycles = 8000
            self.log.info(f"Configured ACK timeout: 8000 cycles ({8000 * 10}ns)")

        self.clock_started = False

        self.log.info(
            f"ArbiterMatrixTB initialized: CLIENTS={self.CLIENTS}, "
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
        """Shut the master down so directed pokes own the request vector."""
        # Disable every client first so the request vector actually drops, then
        # stop the master so it cannot re-assert anything while we poke signals.
        for client_id in range(self.CLIENTS):
            self.master.disable_client(client_id)
        await self.wait_clocks(2)
        if self.master.active:
            await self.master.shutdown()
        # Drain until request and grant_valid are both idle for several cycles.
        # In ACK mode a held grant must be retired by the owner's ACK bit.
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
    async def set_request(self, value: int):
        # Directed tests call enter_directed_mode() first, so the master is
        # shut down and request is fully under testbench control.
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

        self.master.set_ack_profile('immediate')
        auto_ack_enabled = (self.WAIT_GNT_ACK == 1)

        for client_id in range(self.CLIENTS):
            # Isolate each client so an ACK-mode grant to the previous client
            # cannot block this one.
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

    async def test_block_arb(self):
        """block_arb forces no grants; monitor counters stay flat."""
        self.log.info(f"=== block_arb test ==={self.get_time_ns_str()}")

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

    async def test_fairness(self):
        """All clients requesting continuously: fairness index must be high."""
        self.log.info(f"=== fairness test ==={self.get_time_ns_str()}")

        # 'saturate' keeps every client re-requesting immediately after grant.
        for client_id in range(self.CLIENTS):
            self.master.set_client_profile(client_id, 'saturate')
            self.master.enable_client(client_id)
        self.master.set_ack_profile('fast')

        initial_grants_per_client = list(
            self.monitor.arbiter_stats.get('grants_per_client', []))

        test_cycles = 1000 * self.LEVEL_MULT
        await self.wait_clocks(test_cycles)

        final_grants_per_client = list(
            self.monitor.arbiter_stats.get('grants_per_client', []))
        window = [b - a for a, b in zip(initial_grants_per_client,
                                        final_grants_per_client)]
        total_new_grants = sum(window)

        if window and total_new_grants > 0:
            n = len(window)
            fairness_index = (sum(window) ** 2) / (n * sum(x * x for x in window))
        else:
            fairness_index = 0

        self.log.info(
            f"Fairness test: {total_new_grants} grants, "
            f"fairness index: {fairness_index:.3f}{self.get_time_ns_str()}"
        )
        self.log.info(f"Per-client window grants: {window}")

        assert total_new_grants > 50, (
            f"Insufficient activity for fairness test: {total_new_grants} grants"
        )
        assert fairness_index > 0.7, f"Poor fairness: {fairness_index:.3f} < 0.7"
        self.log.info("fairness test PASSED")
        return True

    # -------------------------------------------------------------------------
    # Directed supplements
    # -------------------------------------------------------------------------
    async def test_one_hot_and_request_match(self):
        """DIR supplement: grant is one-hot or zero and only grants a requesting client."""
        self.log.info(f"=== directed: one-hot / request-match test ==={self.get_time_ns_str()}")
        await self.enter_directed_mode()

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

    async def test_strong_fairness_continuous(self):
        """DIR supplement: all clients requesting, each grants once per N grants."""
        self.log.info(
            f"=== directed: strong fairness (continuous) test ==={self.get_time_ns_str()}"
        )
        await self.enter_directed_mode()

        await self.set_request((1 << self.CLIENTS) - 1)

        for _ in range(self.CLIENTS + 5):
            gv, _, _ = self.read_grant()
            if gv:
                break
            await self.wait_clocks(1)
        assert gv == 1, "No grant appeared with all clients requesting"

        window = 4 * self.CLIENTS
        counts = [0] * self.CLIENTS
        for _ in range(window):
            await self.wait_clocks(1)
            gv, gnt, gid = self.read_grant()
            assert gv == 1, "grant_valid dropped with all clients requesting"
            winner = self.one_hot_to_id(gnt)
            assert winner == gid, f"grant_id={gid} mismatches grant=0x{gnt:x}"
            counts[winner] += 1

        self.log.info(f"grant counts over {window} cycles: {counts}")
        expected = window // self.CLIENTS
        for c in range(self.CLIENTS):
            assert counts[c] == expected, (
                f"client {c} got {counts[c]} grants, expected {expected}"
            )
        await self.exit_directed_mode()
        self.log.info("directed: strong fairness (continuous) test PASSED")
        return True

    async def test_fairness_cold_start_and_gaps(self):
        """DIR supplement: rotation is correct from reset and after idle gaps."""
        self.log.info(
            f"=== directed: fairness cold-start + gaps test ==={self.get_time_ns_str()}"
        )
        await self.enter_directed_mode()

        await self.reset_dut()
        self.dut.request.value = (1 << self.CLIENTS) - 1

        expected = list(range(self.CLIENTS)) + list(range(self.CLIENTS))
        observed = []
        for _ in range(2 * self.CLIENTS):
            await self.wait_clocks(1)
            gv, gnt, _ = self.read_grant()
            assert gv == 1, "grant_valid dropped during cold-start rotation"
            observed.append(self.one_hot_to_id(gnt))
        assert observed == expected, (
            f"cold-start rotation {observed} != expected {expected}"
        )
        self.log.info(f"cold-start rotation: {observed}")

        self.dut.request.value = 0b0001
        await self.wait_clocks(self.CLIENTS)

        self.dut.request.value = (1 << self.CLIENTS) - 1
        after_gap = []
        for _ in range(self.CLIENTS):
            await self.wait_clocks(1)
            gv, gnt, _ = self.read_grant()
            assert gv == 1, "grant_valid dropped after gap"
            after_gap.append(self.one_hot_to_id(gnt))

        assert sorted(after_gap) == list(range(self.CLIENTS)), (
            f"post-gap rotation {after_gap} is not a permutation of all clients"
        )
        self.log.info(f"post-gap rotation: {after_gap}")
        await self.exit_directed_mode()
        self.log.info("directed: fairness cold-start + gaps test PASSED")
        return True

    async def test_single_requester_immediate(self):
        """DIR supplement: a lone requester is granted in one cycle."""
        self.log.info(
            f"=== directed: single requester immediacy test ==={self.get_time_ns_str()}"
        )
        await self.enter_directed_mode()

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

    async def test_reset_order(self):
        """DIR supplement: reset restores client 0 as highest priority."""
        self.log.info(f"=== directed: reset-order test ==={self.get_time_ns_str()}")
        await self.enter_directed_mode()

        rng = random.Random(self.SEED)
        for _ in range(self.CLIENTS * 4):
            req = rng.randint(1, (1 << self.CLIENTS) - 1)
            await self.set_request(req)

        await self.reset_dut()
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
        await self.reset_dut()
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
        await self.reset_dut()
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
        await self.reset_dut()
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
        for client in range(self.CLIENTS):
            await self.reset_dut()
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
        """Run the matrix arbiter test suite."""
        results = []

        # Master/monitor scenario phases
        results.append(("grant-signals", await self.test_grant_signals()))
        await self.handle_test_transition_ack_cleanup()

        results.append(("basic-arbitration",
                        await self.run_basic_arbitration_test(400 * self.LEVEL_MULT)))
        await self.handle_test_transition_ack_cleanup()

        results.append(("walking-requests", await self.test_walking_requests()))
        await self.handle_test_transition_ack_cleanup()

        results.append(("block-arb", await self.test_block_arb()))
        await self.handle_test_transition_ack_cleanup()

        results.append(("bursty-traffic", await self.test_bursty_traffic_pattern()))
        await self.handle_test_transition_ack_cleanup()

        results.append(("rapid-request-changes", await self.test_rapid_request_changes()))
        await self.handle_test_transition_ack_cleanup()

        results.append(("single-client-saturation", await self.test_single_client_saturation()))
        await self.handle_test_transition_ack_cleanup()

        results.append(("fairness", await self.test_fairness()))
        await self.handle_test_transition_ack_cleanup()

        # Directed supplements.  Several are no-ACK only because the held-grant
        # semantics of ACK mode break the simple request->grant sampling these
        # tests use; the ACK-mode equivalents are covered by the dedicated ACK
        # supplements below.
        if self.WAIT_GNT_ACK == 0:
            results.append(("one-hot/request-match",
                            await self.test_one_hot_and_request_match()))
            await self.handle_test_transition_ack_cleanup()

            results.append(("strong-fairness-continuous",
                            await self.test_strong_fairness_continuous()))
            await self.handle_test_transition_ack_cleanup()

            results.append(("fairness-cold-start-and-gaps",
                            await self.test_fairness_cold_start_and_gaps()))
            await self.handle_test_transition_ack_cleanup()

            results.append(("single-requester-immediate",
                            await self.test_single_requester_immediate()))
            await self.handle_test_transition_ack_cleanup()

            results.append(("reset-order", await self.test_reset_order()))
            await self.handle_test_transition_ack_cleanup()
        else:
            results.append(("reset-order", await self.test_reset_order()))
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
        self.log.info("ArbiterMatrix test summary:")
        all_passed = True
        for name, passed in results:
            status = "PASSED" if passed else "FAILED"
            self.log.info(f"  {name}: {status}")
            all_passed = all_passed and passed
        self.log.info("=" * 60)

        return all_passed
