# SPDX-License-Identifier: MIT
# SPDX-FileCopyrightText: 2026 sean galloway
#
# RTL Design Sherpa - Industry-Standard RTL Design and Verification
# https://github.com/sean-galloway/RTLDesignSherpa
#
# Module: ace_snoop_transport_tb
# Purpose: ACE snoop-channel transport testbench (slave and master orientations)
#
# Subsystem: framework

"""ACE snoop-channel transport testbench.

A single ``AXI4ACESnoopTransportTB`` class tests both DUT orientations:

* ``axi4ace_snoop_slave``  (cache-side):  master on ``m_axi_``, responder on ``fub_``
* ``axi4ace_snoop_master`` (CCU-side):    master on ``fub_``, responder on ``m_axi_``

The TB lifts the deterministic MESI reference model from the BFM acceptance
test and expands it into a reusable testbench with timing profiles, stats,
and level-scaled scenarios.
"""

import os
import random

from CocoTBFramework.components.ace.ace_compliance_checker import ACEComplianceChecker
from CocoTBFramework.components.ace.ace_interfaces import (
    AXI4ACESnoopMaster,
    AXI4ACESnoopSlave,
)
from CocoTBFramework.components.ace.ace_transaction import (
    CRRESP,
    CacheState,
    SnoopType,
)
from CocoTBFramework.components.shared.flex_randomizer import FlexRandomizer

from TBClasses.shared.tbbase import TBBase


class AXI4ACESnoopTransportTB(TBBase):
    """Testbench for the ACE snoop-channel skid-buffer transports.

    Parameters (via constructor or environment):
        TEST_ADDR_WIDTH  - AC address width (default 32)
        TEST_DATA_WIDTH  - CD data width (default 32)
        TEST_SEED        - random seed (default from TBBase)
    """

    # Base cache-line addresses for each MESI state.  These fit comfortably in
    # 32-bit and 64-bit address spaces; the TB masks them to the active width.
    ADDR_INVALID   = 0x0000_0000
    ADDR_SHARED    = 0x0000_1000
    ADDR_EXCLUSIVE = 0x0000_2000
    ADDR_MODIFIED  = 0x0000_3000
    ADDR_OWNED     = 0x0000_4000

    def __init__(self, dut, aclk=None, aresetn=None,
                 master_prefix="m_axi_", slave_prefix="fub_",
                 addr_width=None, data_width=None):
        super().__init__(dut)

        # Configuration: constructor args win, then environment, then defaults.
        self.TEST_ADDR_WIDTH = (
            addr_width if addr_width is not None
            else self.convert_to_int(os.environ.get('TEST_ADDR_WIDTH', '32'))
        )
        self.TEST_DATA_WIDTH = (
            data_width if data_width is not None
            else self.convert_to_int(os.environ.get('TEST_DATA_WIDTH', '32'))
        )
        self.TEST_CLK_PERIOD = self.convert_to_int(os.environ.get('TEST_CLK_PERIOD', '10'))
        self.ACE_COMPLIANCE_CHECK = (
            os.environ.get('ACE_COMPLIANCE_CHECK', '1').lower() in ('1', 'true', 'yes')
        )

        self.addr_mask = (1 << self.TEST_ADDR_WIDTH) - 1
        self.data_mask = (1 << self.TEST_DATA_WIDTH) - 1

        self.aclk = aclk
        self.aclk_name = aclk._name if aclk else 'aclk'
        self.aresetn = aresetn
        self.master_prefix = master_prefix
        self.slave_prefix = slave_prefix

        self.log.info(
            "ACE snoop transport TB config: "
            f"ADDR_WIDTH={self.TEST_ADDR_WIDTH}, DATA_WIDTH={self.TEST_DATA_WIDTH}, "
            f"master_prefix={master_prefix!r}, slave_prefix={slave_prefix!r}"
        )

        # Build the initiator and responder BFMs.
        self.master = AXI4ACESnoopMaster(
            dut=dut,
            clock=self.aclk,
            prefix=self.master_prefix,
            log=self.log,
            ifc_name="init",
            data_width=self.TEST_DATA_WIDTH,
            addr_width=self.TEST_ADDR_WIDTH,
        )
        self.slave = AXI4ACESnoopSlave(
            dut=dut,
            clock=self.aclk,
            prefix=self.slave_prefix,
            log=self.log,
            ifc_name="resp",
            data_width=self.TEST_DATA_WIDTH,
            addr_width=self.TEST_ADDR_WIDTH,
        )

        # Program the responder cache-state map.
        self.state_map = {
            self.ADDR_INVALID:   CacheState.INVALID,
            self.ADDR_SHARED:    CacheState.SHARED,
            self.ADDR_EXCLUSIVE: CacheState.EXCLUSIVE,
            self.ADDR_MODIFIED:  CacheState.MODIFIED,
            self.ADDR_OWNED:     CacheState.OWNED,
        }
        for addr, state in self.state_map.items():
            self.slave.set_line_behavior(addr & self.addr_mask, state)

        self.handler = self._make_snoop_handler()
        self.slave.set_handler(self.handler)

        # ACE compliance checker for CRRESP validity rules.
        if self.ACE_COMPLIANCE_CHECK:
            self.ace_checker = ACEComplianceChecker(log=self.log)
        else:
            self.ace_checker = None

        # Statistics.
        self.stats = {
            'total_snoops': 0,
            'successful_snoops': 0,
            'failed_snoops': 0,
            'crresp_mismatches': 0,
            'data_mismatches': 0,
            'unexpected_data': 0,
            'missing_data': 0,
        }

        # Timing profile randomizers.
        self.randomizer_configs = self._create_randomizer_configs()
        self.set_timing_profile('normal')

        self.log.info("ACE snoop transport TB initialized")

    # -------------------------------------------------------------------------
    # Reference model: deterministic MESI handler.
    # -------------------------------------------------------------------------

    def _make_snoop_handler(self, data_seed: int = 0xDEAD_BEEF):
        """Return a deterministic MESI snoop handler with non-zero data."""

        def handler(addr: int, snoop_type: SnoopType, state: CacheState):
            if state == CacheState.INVALID:
                return CRRESP(0), None

            if state == CacheState.SHARED:
                if snoop_type in (SnoopType.READ_SHARED, SnoopType.READ_ONCE):
                    return CRRESP.from_bits(is_shared=True), None
                return CRRESP(0), None

            if state == CacheState.EXCLUSIVE:
                data = (addr ^ data_seed) & self.data_mask
                if snoop_type in (SnoopType.READ_SHARED, SnoopType.READ_ONCE):
                    return CRRESP.from_bits(
                        data_transfer=True, is_shared=True, was_unique=True
                    ), data
                if snoop_type == SnoopType.READ_UNIQUE:
                    return CRRESP.from_bits(data_transfer=True, was_unique=True), data
                if snoop_type == SnoopType.CLEAN_SHARED:
                    return CRRESP.from_bits(is_shared=True, was_unique=True), None
                return CRRESP(0), None

            if state == CacheState.MODIFIED:
                data = (addr ^ 0xBEEF_CAFE) & self.data_mask
                if snoop_type == SnoopType.READ_SHARED:
                    return CRRESP.from_bits(
                        data_transfer=True, pass_dirty=True, is_shared=True
                    ), data
                if snoop_type == SnoopType.READ_UNIQUE:
                    return CRRESP.from_bits(data_transfer=True, pass_dirty=True), data
                if snoop_type in (SnoopType.CLEAN_SHARED, SnoopType.CLEAN_INVALID):
                    return CRRESP.from_bits(
                        data_transfer=True, pass_dirty=True, is_shared=True
                    ), data
                if snoop_type == SnoopType.MAKE_INVALID:
                    return CRRESP(0), None
                if snoop_type == SnoopType.READ_ONCE:
                    return CRRESP.from_bits(data_transfer=True, pass_dirty=True), data
                return CRRESP(0), None

            if state == CacheState.OWNED:
                data = (addr ^ 0xCAFE_BABE) & self.data_mask
                if snoop_type in (SnoopType.READ_SHARED, SnoopType.READ_ONCE):
                    return CRRESP.from_bits(
                        data_transfer=True, pass_dirty=True, is_shared=True
                    ), data
                if snoop_type == SnoopType.READ_UNIQUE:
                    return CRRESP.from_bits(
                        data_transfer=True, pass_dirty=True, is_shared=True
                    ), data
                if snoop_type in (SnoopType.CLEAN_SHARED, SnoopType.CLEAN_INVALID):
                    return CRRESP.from_bits(
                        data_transfer=True, pass_dirty=True, is_shared=True
                    ), data
                if snoop_type == SnoopType.MAKE_INVALID:
                    return CRRESP(0), None
                return CRRESP(0), None

            return CRRESP(0), None

        return handler

    def expected(self, addr: int, snoop_type: SnoopType):
        """Return the expected (crresp, data) for a snoop using the same model."""
        state = self.slave.line_behaviors.get(addr & self.addr_mask, CacheState.INVALID)
        return self.handler(addr & self.addr_mask, snoop_type, state)

    def _state_for_addr(self, addr: int) -> CacheState:
        return self.slave.line_behaviors.get(addr & self.addr_mask, CacheState.INVALID)

    # -------------------------------------------------------------------------
    # Timing profiles.
    # -------------------------------------------------------------------------

    def _create_randomizer_configs(self):
        """Timing/ready-delay configurations for the snoop channels."""
        return {
            'normal': {
                'ac_valid_delay':  ([(0, 2), (3, 5)], [0.7, 0.3]),
                'cr_valid_delay':  ([(0, 1), (2, 4)], [0.7, 0.3]),
                'cd_valid_delay':  ([(0, 1), (2, 4)], [0.7, 0.3]),
                'cr_ready_delay':  ([(0, 0), (1, 3)], [0.8, 0.2]),
                'cd_ready_delay':  ([(0, 0), (1, 3)], [0.8, 0.2]),
            },
            'fast': {
                'ac_valid_delay':  ([(0, 0)], [1.0]),
                'cr_valid_delay':  ([(0, 0)], [1.0]),
                'cd_valid_delay':  ([(0, 0)], [1.0]),
                'cr_ready_delay':  ([(0, 0)], [1.0]),
                'cd_ready_delay':  ([(0, 0)], [1.0]),
            },
            'slow': {
                'ac_valid_delay':  ([(2, 5), (6, 10)], [0.6, 0.4]),
                'cr_valid_delay':  ([(2, 5), (6, 10)], [0.6, 0.4]),
                'cd_valid_delay':  ([(2, 5), (6, 10)], [0.6, 0.4]),
                'cr_ready_delay':  ([(2, 5), (6, 10)], [0.6, 0.4]),
                'cd_ready_delay':  ([(2, 5), (6, 10)], [0.6, 0.4]),
            },
            'backtoback': {
                'ac_valid_delay':  ([(0, 0)], [1.0]),
                'cr_valid_delay':  ([(0, 0)], [1.0]),
                'cd_valid_delay':  ([(0, 0)], [1.0]),
                'cr_ready_delay':  ([(0, 0)], [1.0]),
                'cd_ready_delay':  ([(0, 0)], [1.0]),
            },
            'stress': {
                'ac_valid_delay':  ([(0, 0), (1, 4), (5, 10)], [0.4, 0.4, 0.2]),
                'cr_valid_delay':  ([(0, 1), (2, 6), (7, 12)], [0.4, 0.4, 0.2]),
                'cd_valid_delay':  ([(0, 1), (2, 6), (7, 12)], [0.4, 0.4, 0.2]),
                'cr_ready_delay':  ([(0, 0), (2, 5), (6, 12)], [0.4, 0.4, 0.2]),
                'cd_ready_delay':  ([(0, 0), (2, 5), (6, 12)], [0.4, 0.4, 0.2]),
            },
        }

    def set_timing_profile(self, profile_name):
        """Apply a named timing profile to all snoop channels."""
        if profile_name not in self.randomizer_configs:
            self.log.warning(f"Unknown timing profile '{profile_name}', using 'normal'")
            profile_name = 'normal'
        cfg = self.randomizer_configs[profile_name]

        applied = []

        def apply(channel, key, rand_key):
            if channel is None:
                return
            delay_cfg = cfg.get(key)
            if delay_cfg is None:
                return
            channel.set_randomizer(FlexRandomizer({rand_key: delay_cfg}))
            applied.append(f"{channel.title}.{rand_key}")

        apply(self.master.ac_channel, 'ac_valid_delay', 'valid_delay')
        apply(self.slave.cr_channel, 'cr_valid_delay', 'valid_delay')
        apply(self.slave.cd_channel, 'cd_valid_delay', 'valid_delay')
        apply(self.master.cr_channel, 'cr_ready_delay', 'ready_delay')
        apply(self.master.cd_channel, 'cd_ready_delay', 'ready_delay')

        self.log.info(f"Set timing profile to '{profile_name}' -> {applied or 'nothing'}")
        return applied

    # -------------------------------------------------------------------------
    # Reset helpers.
    # -------------------------------------------------------------------------

    async def assert_reset(self):
        self.aresetn.value = 0
        await self.wait_clocks(self.aclk_name, 5)
        self.log.info("Reset asserted")

    async def deassert_reset(self):
        self.aresetn.value = 1
        await self.wait_clocks(self.aclk_name, 5)
        self.log.info(f"Reset deasserted{self.get_time_ns_str()}")

    # -------------------------------------------------------------------------
    # Core snoop issuance and checking.
    # -------------------------------------------------------------------------

    async def issue_and_check(self, addr: int, snoop_type: SnoopType,
                              profile: str | None = None) -> bool:
        """Issue one snoop and check the result against the reference model."""
        if profile is not None:
            self.set_timing_profile(profile)

        self.stats['total_snoops'] += 1
        exp_crresp, exp_data = self.expected(addr, snoop_type)

        try:
            result = await self.master.issue_snoop(addr & self.addr_mask, snoop_type)
        except Exception as e:
            self.log.error(
                f"Snoop to 0x{addr & self.addr_mask:08X} {snoop_type.name} raised: {e}"
            )
            self.stats['failed_snoops'] += 1
            raise

        ok = self._check_result(addr, snoop_type, result, exp_crresp, exp_data)
        if ok:
            self.stats['successful_snoops'] += 1
        else:
            self.stats['failed_snoops'] += 1
        return ok

    def _check_result(self, addr: int, snoop_type: SnoopType, result,
                      exp_crresp: CRRESP, exp_data) -> bool:
        """Check one snoop result; return True if it passed."""
        addr &= self.addr_mask
        ok = True

        # CRRESP equality.
        if result.crresp != exp_crresp:
            self.log.error(
                f"addr=0x{addr:08X} {snoop_type.name}: CRRESP mismatch "
                f"got {result.crresp!r}, expected {exp_crresp!r}"
            )
            self.stats['crresp_mismatches'] += 1
            ok = False

        # Data expectation.
        if exp_data is not None:
            if not result.crresp.data_transfer:
                self.log.error(
                    f"addr=0x{addr:08X} {snoop_type.name}: expected DataTransfer"
                )
                self.stats['missing_data'] += 1
                ok = False
            if len(result.data) != 1:
                self.log.error(
                    f"addr=0x{addr:08X} {snoop_type.name}: expected 1 data beat, "
                    f"got {len(result.data)}"
                )
                self.stats['data_mismatches'] += 1
                ok = False
            elif result.data[0] != (exp_data & self.data_mask):
                self.log.error(
                    f"addr=0x{addr:08X} {snoop_type.name}: data mismatch "
                    f"got 0x{result.data[0]:08X}, expected 0x{exp_data & self.data_mask:08X}"
                )
                self.stats['data_mismatches'] += 1
                ok = False
        else:
            if result.crresp.data_transfer:
                self.log.error(
                    f"addr=0x{addr:08X} {snoop_type.name}: unexpected DataTransfer"
                )
                self.stats['unexpected_data'] += 1
                ok = False
            if result.data:
                self.log.error(
                    f"addr=0x{addr:08X} {snoop_type.name}: unexpected data beats"
                )
                self.stats['unexpected_data'] += 1
                ok = False

        # Pass CRRESP through the ACE compliance checker.
        if self.ace_checker is not None:
            self.ace_checker.check_crresp_validity(result.crresp, snoop_type, addr)

        if ok:
            self.log.info(
                f"OK addr=0x{addr:08X} {snoop_type.name} -> {result.crresp} "
                f"data={result.data if result.data else '[]'}"
            )
        return ok

    # -------------------------------------------------------------------------
    # Scenarios.
    # -------------------------------------------------------------------------

    async def scenario_mesi_matrix(self, iterations: int = 1):
        """Exercise every CacheState × SnoopType combination."""
        self.log.info(
            f"Scenario: full MESI × snoop-type matrix ({iterations} iteration(s))"
        )
        states = list(CacheState)
        snoops = list(SnoopType)

        count = 0
        for _ in range(iterations):
            for state in states:
                addr = self._addr_for_state(state)
                for snoop_type in snoops:
                    await self.issue_and_check(addr, snoop_type)
                    count += 1
        self.log.info(f"MESI matrix completed: {count} snoops")

    async def scenario_back_to_back(self, count: int = 10):
        """In-order back-to-back snoops mixing states and snoop types."""
        self.log.info(f"Scenario: back-to-back in-order snoops ({count})")
        states = list(CacheState)
        snoops = list(SnoopType)

        # Deterministic but varied sequence seeded from the current RNG state.
        sequence = []
        for i in range(count):
            state = states[i % len(states)]
            snoop_type = snoops[(i * 3) % len(snoops)]
            addr = self._addr_for_state(state)
            sequence.append((addr, snoop_type))

        results = []
        for addr, snoop_type in sequence:
            results.append((addr, snoop_type, await self.master.issue_snoop(addr, snoop_type)))

        for addr, snoop_type, result in results:
            exp_crresp, exp_data = self.expected(addr, snoop_type)
            self._check_result(addr, snoop_type, result, exp_crresp, exp_data)

        self.log.info(f"Back-to-back sequence completed: {len(results)} snoops")

    async def scenario_backpressure(self, deep: bool = False):
        """Snoops under CR/CD ready backpressure."""
        self.log.info("Scenario: CR/CD backpressure")
        if deep:
            backpressure = FlexRandomizer({
                'ready_delay': ([(0, 0), (3, 8), (9, 16)], [0.3, 0.4, 0.3])
            })
        else:
            backpressure = FlexRandomizer({
                'ready_delay': ([(0, 0), (2, 5)], [1, 2])
            })
        self.master.cr_channel.set_randomizer(backpressure)
        self.master.cd_channel.set_randomizer(backpressure)

        bp_cases = [
            (self.ADDR_MODIFIED,  SnoopType.READ_SHARED),
            (self.ADDR_EXCLUSIVE, SnoopType.READ_SHARED),
            (self.ADDR_SHARED,    SnoopType.READ_SHARED),
            (self.ADDR_MODIFIED,  SnoopType.READ_UNIQUE),
            (self.ADDR_OWNED,     SnoopType.CLEAN_INVALID),
            (self.ADDR_INVALID,   SnoopType.MAKE_INVALID),
        ]
        for addr, snoop_type in bp_cases:
            await self.issue_and_check(addr, snoop_type)

        self.log.info("Backpressure scenario completed")

    async def scenario_stress(self, count: int = 50):
        """Randomized stress mix of states, snoop types, and timing."""
        self.log.info(f"Scenario: stress mix ({count} snoops)")
        self.set_timing_profile('stress')
        states = list(CacheState)
        snoops = list(SnoopType)

        for i in range(count):
            state = random.choice(states)
            snoop_type = random.choice(snoops)
            addr = self._addr_for_state(state)
            await self.issue_and_check(addr, snoop_type)

        self.log.info(f"Stress mix completed: {count} snoops")

    # -------------------------------------------------------------------------
    # High-level run dispatch by TEST_LEVEL.
    # -------------------------------------------------------------------------

    async def run_scenarios(self, test_level: str):
        """Run the scenario suite scaled to the requested test level."""
        test_level = test_level.lower()
        valid = ('gate', 'func', 'full')
        if test_level not in valid:
            self.log.warning(f"Invalid TEST_LEVEL '{test_level}', using 'gate'. Valid: {valid}")
            test_level = 'gate'

        if test_level == 'gate':
            await self.scenario_mesi_matrix(iterations=1)
            await self.scenario_back_to_back(count=5)
        elif test_level == 'func':
            await self.scenario_mesi_matrix(iterations=1)
            await self.scenario_back_to_back(count=12)
            await self.scenario_backpressure(deep=False)
        else:  # full
            await self.scenario_mesi_matrix(iterations=2)
            await self.scenario_back_to_back(count=25)
            await self.scenario_backpressure(deep=True)
            await self.scenario_stress(count=50)

        # Wait for all channel activity to drain, then verify busy is low.
        await self._wait_quiescent()
        if bool(self.dut.busy.value):
            raise AssertionError("DUT busy remained high after quiescence")
        self.log.info("DUT busy is low after quiescence")

        self.log_summary()
        if self.ace_checker is not None:
            self.ace_checker.print_compliance_report()

    # -------------------------------------------------------------------------
    # Utility.
    # -------------------------------------------------------------------------

    def _addr_for_state(self, state: CacheState) -> int:
        mapping = {
            CacheState.INVALID:   self.ADDR_INVALID,
            CacheState.SHARED:    self.ADDR_SHARED,
            CacheState.EXCLUSIVE: self.ADDR_EXCLUSIVE,
            CacheState.MODIFIED:  self.ADDR_MODIFIED,
            CacheState.OWNED:     self.ADDR_OWNED,
        }
        return mapping.get(state, self.ADDR_INVALID) & self.addr_mask

    async def _wait_quiescent(self, max_cycles: int = 200):
        """Wait until all BFM queues are empty and the interface is idle."""
        for _ in range(max_cycles):
            idle = (
                not bool(self.dut.busy.value)
                and not getattr(self.master.ac_channel, '_sendQ', None)
                and not getattr(self.master.cr_channel, '_recvQ', None)
                and not getattr(self.master.cd_channel, '_recvQ', None)
                and not getattr(self.slave.ac_channel, '_recvQ', None)
                and not getattr(self.slave.cr_channel, '_sendQ', None)
                and not getattr(self.slave.cd_channel, '_sendQ', None)
            )
            if idle:
                return
            await self.wait_clocks(self.aclk_name, 1)
        self.log.warning(f"Did not reach quiescence within {max_cycles} cycles")

    def log_summary(self):
        """Log test statistics and any BFM counters that are exposed."""
        total = self.stats['total_snoops']
        success = self.stats['successful_snoops']
        rate = (success / total * 100) if total else 0.0
        self.log.info("=" * 60)
        self.log.info("ACE SNOOP TRANSPORT TEST SUMMARY")
        self.log.info("=" * 60)
        self.log.info(f"Total snoops:        {total}")
        self.log.info(f"Successful snoops:   {success}")
        self.log.info(f"Failed snoops:       {self.stats['failed_snoops']}")
        self.log.info(f"Success rate:        {rate:.1f}%")
        self.log.info(f"CRRESP mismatches:   {self.stats['crresp_mismatches']}")
        self.log.info(f"Data mismatches:     {self.stats['data_mismatches']}")
        self.log.info(f"Missing data:        {self.stats['missing_data']}")
        self.log.info(f"Unexpected data:     {self.stats['unexpected_data']}")

        # Log BFM-exposed counters if present.
        for name, comp in (
            ('master.ac', self.master.ac_channel),
            ('master.cr', self.master.cr_channel),
            ('master.cd', self.master.cd_channel),
            ('slave.ac',  self.slave.ac_channel),
            ('slave.cr',  self.slave.cr_channel),
            ('slave.cd',  self.slave.cd_channel),
        ):
            txn = getattr(comp, 'transactions', None)
            dropped = getattr(comp, 'dropped', None)
            errors = getattr(comp, 'errors', None)
            if txn is not None or dropped is not None or errors is not None:
                self.log.info(
                    f"{name} counters: transactions={txn}, dropped={dropped}, errors={errors}"
                )
        self.log.info("=" * 60)

    def get_test_stats(self):
        """Return a copy of the statistics dictionary."""
        return self.stats.copy()
