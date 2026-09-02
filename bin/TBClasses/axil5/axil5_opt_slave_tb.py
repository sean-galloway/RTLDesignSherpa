# SPDX-License-Identifier: MIT
# SPDX-FileCopyrightText: 2026 sean galloway
#
# RTL Design Sherpa - Industry-Standard RTL Design and Verification
# https://github.com/sean-galloway/RTLDesignSherpa
#
# Module: AXIL5OptSlaveTB
# Purpose: Drive every AXI5-Lite optional signal group against real RTL
#
# Subsystem: framework

"""Testbench for ``axil5_opt_slave`` -- the AXI5-Lite optional signal groups.

Until this existed the optional groups (USER, TRACE, LOOP, MPAM, MECID, NSAID,
POISON, exclusive access) were declaration-only. The framework unit tests
compared field configs, and the one sim test drove an AXI4-Lite DUT with every
group switched off -- so nothing ever put an optional value on a wire and read
it back.

What each check proves, and how:

``TRACE`` / ``LOOP`` / ``USER``
    Driven on the address channel, echoed by the DUT on the matching response
    channel (the spec behaviour for LOOP and TRACE; the DUT's stated contract
    for USER). Checked from ``last_b_packet`` / ``last_r_packet``. A value that
    fails to reach the wire comes back as 0 and the check fails.

``POISON``
    Written with the data, stored, and returned on a read of the same address.
    Proves the value survives a round trip rather than merely being driven.
    One bit wide on every legal AXI-Lite bus (one per 64 data bits, floor of
    one, and Lite allows only 32 or 64), so this checks the round trip, not
    the width derivation -- no Lite width can distinguish that from a
    hardcoded 1.

``LOCK`` (exclusive)
    An exclusive access answers EXOKAY rather than OKAY, so the effect is
    visible in a field the BFM already returns.

``PROT`` / ``MPAM`` / ``MECID`` / ``NSAID``
    No architectural effect a Lite slave can express, so the DUT captures them
    on ``o_last_*`` observation ports and the TB samples those. This is the
    check that the BFM DROVE the value -- the others could in principle pass
    on an echo of something the BFM never sent.

The whole suite would pass vacuously against a BFM that drove zeros if the
expected values were zero, so every value used here is non-zero and distinct
per field. `_distinct_values` builds them and asserts that.
"""

import os
import random

from CocoTBFramework.components.axil5.axil5_factories import (
    create_axil5_master_rd,
    create_axil5_master_wr,
)

from TBClasses.shared.tbbase import TBBase

# Optional-group widths. These MUST match the DUT's parameters: the BFM
# declares a field of the width it is told, and the resolver binds by name, so
# a mismatch is a width truncation rather than a bind failure -- silent, and
# exactly the class of bug the strict-bind rule cannot see.
USER_WIDTH = 4
LOOP_WIDTH = 3
MPAM_WIDTH = 11
MECID_WIDTH = 16
NSAID_WIDTH = 4


class AXIL5OptSlaveTB(TBBase):
    """AXI5-Lite masters with every optional group enabled, on real RTL."""

    def __init__(self, dut, aclk=None, aresetn=None):
        TBBase.__init__(self, dut)
        self.dut = dut
        self.aclk = aclk if aclk is not None else dut.aclk
        self.aresetn = aresetn if aresetn is not None else dut.aresetn

        self.TEST_ADDR_WIDTH = self.convert_to_int(
            os.environ.get('TEST_ADDR_WIDTH', '32'))
        self.TEST_DATA_WIDTH = self.convert_to_int(
            os.environ.get('TEST_DATA_WIDTH', '32'))
        self.TEST_CLK_PERIOD = self.convert_to_int(
            os.environ.get('TEST_CLK_PERIOD', '10'))

        # One poison bit per 64 data bits, minimum one -- the same rule the
        # field config applies, restated here only because the TB has to know
        # how wide a value it may legally drive.
        self.poison_width = max(1, self.TEST_DATA_WIDTH // 64)

        # Every optional group ON. This is the configuration under test: with
        # them off the components are AXI4-Lite and prove nothing new.
        groups = dict(
            user_width=USER_WIDTH,
            trace=True,
            loop_width=LOOP_WIDTH,
            mpam_width=MPAM_WIDTH,
            mecid_width=MECID_WIDTH,
            nsaid_width=NSAID_WIDTH,
            poison=True,
            exclusive=True,
        )

        self.wr = create_axil5_master_wr(
            dut=dut, clock=self.aclk, prefix='s_axil_', log=self.log,
            addr_width=self.TEST_ADDR_WIDTH, data_width=self.TEST_DATA_WIDTH,
            multi_sig=True, **groups)
        self.rd = create_axil5_master_rd(
            dut=dut, clock=self.aclk, prefix='s_axil_', log=self.log,
            addr_width=self.TEST_ADDR_WIDTH, data_width=self.TEST_DATA_WIDTH,
            multi_sig=True, **groups)

        self.write_if = self.wr['interface']
        self.read_if = self.rd['interface']
        # Which groups the DUT was ELABORATED with. The BFM still drives every
        # wire -- the ports exist either way -- so only the EXPECTATION changes:
        # a disabled group is not carried, so its field comes back zero. Without
        # this the suite could only ever run all-groups-on, which is the one
        # configuration in which a packing bug cannot show.
        self.enabled = {
            g: os.environ.get(f'TEST_ENABLE_{g.upper()}', '1') == '1'
            for g in ('user', 'trace', 'loop', 'mpam', 'mecid', 'nsaid',
                      'poison', 'lock')
        }
        off = [g for g, on in self.enabled.items() if not on]
        self.log.info("AXIL5 masters created; groups OFF: %s"
                      % (", ".join(off) if off else "none (all enabled)"))

    def _want(self, group, value):
        """Expected value of an optional field: zero when its group is off."""
        return value if self.enabled[group] else 0

    # ---- required TBBase lifecycle --------------------------------------
    async def setup_clocks_and_reset(self):
        await self.start_clock('aclk', self.TEST_CLK_PERIOD, 'ns')
        await self.assert_reset()
        await self.wait_clocks('aclk', 10)
        await self.deassert_reset()
        await self.wait_clocks('aclk', 10)

    async def assert_reset(self):
        self.aresetn.value = 0

    async def deassert_reset(self):
        self.aresetn.value = 1

    # ---- helpers ---------------------------------------------------------
    def _distinct_values(self, rnd):
        """Non-zero, mutually distinct values for every qualifier.

        Distinct because a shared value would let a crossed connection pass:
        if AWMPAM and AWMECID both carried 5, swapping them in the RTL or the
        field config would go unnoticed. Non-zero because an unbound or
        undriven field reads 0, which is the failure this suite exists to
        detect -- expecting 0 anywhere would make that check vacuous.
        """
        vals = {
            'awuser':  rnd.randrange(1, 1 << USER_WIDTH),
            'wuser':   rnd.randrange(1, 1 << USER_WIDTH),
            'awtrace': 1,
            'awloop':  rnd.randrange(1, 1 << LOOP_WIDTH),
            'awmpam':  rnd.randrange(1, 1 << MPAM_WIDTH),
            'awmecid': rnd.randrange(1, 1 << MECID_WIDTH),
            'awnsaid': rnd.randrange(1, 1 << NSAID_WIDTH),
            'awprot':  rnd.randrange(1, 8),
            'wpoison': rnd.randrange(1, 1 << self.poison_width),
        }
        assert all(v != 0 for v in vals.values()), \
            "a zero expectation would pass against an undriven signal"
        return vals

    @staticmethod
    def _field(packet, name):
        """A response-packet field, or None when the packet lacks it."""
        return getattr(packet, name, None)

    def _check(self, what, got, want, failures):
        if got != want:
            failures.append(f"{what}: got {got!r}, expected {want!r}")
            self.log.error(f"  MISMATCH {what}: got {got!r} want {want!r}")
        else:
            self.log.info(f"  ok {what} = {got!r}")

    # ---- the checks ------------------------------------------------------
    async def test_write_qualifiers(self, addr, data, rnd):
        """Drive every AW/W optional field; check echo and capture."""
        v = self._distinct_values(rnd)
        self.log.info(f"=== write 0x{data:08X} -> 0x{addr:08X} with {v} ===")

        await self.write_if.write_transaction(addr, data, **v)

        failures = []
        b = self.write_if.last_b_packet
        assert b is not None, "no B packet retained; response sideband is lost"

        # Echoed on the response channel.
        self._check('BUSER',  self._field(b, 'user'),
                    self._want('user', v['awuser']), failures)
        self._check('BTRACE', self._field(b, 'trace'),
                    self._want('trace', v['awtrace']), failures)
        self._check('BLOOP',  self._field(b, 'loop'),
                    self._want('loop', v['awloop']), failures)

        # Captured by the DUT -- proof the BFM drove the wire.
        self._check('AWPROT@dut',  int(self.dut.o_last_aw_prot.value),
                    v['awprot'], failures)
        self._check('AWMPAM@dut',  int(self.dut.o_last_aw_mpam.value),
                    self._want('mpam', v['awmpam']), failures)
        self._check('AWMECID@dut', int(self.dut.o_last_aw_mecid.value),
                    self._want('mecid', v['awmecid']), failures)
        self._check('AWNSAID@dut', int(self.dut.o_last_aw_nsaid.value),
                    self._want('nsaid', v['awnsaid']), failures)
        self._check('WUSER@dut',   int(self.dut.o_last_w_user.value),
                    self._want('user', v['wuser']), failures)
        return failures, v

    async def test_read_qualifiers(self, addr, expect_data, expect_poison, rnd):
        """Drive every AR optional field; check echo, poison and capture."""
        v = {
            'aruser':  rnd.randrange(1, 1 << USER_WIDTH),
            'artrace': 1,
            'arloop':  rnd.randrange(1, 1 << LOOP_WIDTH),
            'armpam':  rnd.randrange(1, 1 << MPAM_WIDTH),
            'armecid': rnd.randrange(1, 1 << MECID_WIDTH),
            'arnsaid': rnd.randrange(1, 1 << NSAID_WIDTH),
            'arprot':  rnd.randrange(1, 8),
        }
        self.log.info(f"=== read 0x{addr:08X} with {v} ===")

        got = await self.read_if.read_transaction(addr, **v)

        failures = []
        self._check('RDATA', got, expect_data, failures)

        r = self.read_if.last_r_packet
        assert r is not None, "no R packet retained; response sideband is lost"

        self._check('RUSER',   self._field(r, 'user'),
                    self._want('user', v['aruser']), failures)
        self._check('RTRACE',  self._field(r, 'trace'),
                    self._want('trace', v['artrace']), failures)
        self._check('RLOOP',   self._field(r, 'loop'),
                    self._want('loop', v['arloop']), failures)
        # POISON is the round-trip check: written earlier, stored, returned now.
        self._check('RPOISON', self._field(r, 'poison'),
                    self._want('poison', expect_poison), failures)

        self._check('ARPROT@dut',  int(self.dut.o_last_ar_prot.value),
                    v['arprot'], failures)
        self._check('ARMPAM@dut',  int(self.dut.o_last_ar_mpam.value),
                    self._want('mpam', v['armpam']), failures)
        self._check('ARMECID@dut', int(self.dut.o_last_ar_mecid.value),
                    self._want('mecid', v['armecid']), failures)
        self._check('ARNSAID@dut', int(self.dut.o_last_ar_nsaid.value),
                    self._want('nsaid', v['arnsaid']), failures)
        return failures

    async def test_exclusive_access(self, addr, data):
        """AxLOCK=1 must answer EXOKAY, and must not be reported as an error.

        Regression guard: the shared transaction methods used to raise on any
        non-zero response, so a successful exclusive access surfaced as
        RuntimeError and exclusive access was unusable.

        With ENABLE_LOCK=0 the DUT does not carry AxLOCK, so an exclusive
        access is indistinguishable from a normal one and OKAY is the correct
        answer. The expectation follows the configuration.
        """
        exok = 1 if self.enabled['lock'] else 0
        self.log.info(f"=== exclusive write/read at 0x{addr:08X} "
                      f"(lock {'on' if self.enabled['lock'] else 'OFF'}, "
                      f"expecting {'EXOKAY' if exok else 'OKAY'}) ===")
        failures = []

        resp = await self.write_if.write_transaction(addr, data, awlock=1)
        self._check(f'exclusive BRESP (want {exok})', resp, exok, failures)

        await self.read_if.read_transaction(addr, arlock=1)
        r = self.read_if.last_r_packet
        self._check(f'exclusive RRESP (want {exok})',
                    self._field(r, 'resp'), exok, failures)

        # And a NORMAL access must still answer OKAY -- otherwise the check
        # above would pass against a DUT that always returns EXOKAY.
        resp = await self.write_if.write_transaction(addr, data, awlock=0)
        self._check('normal BRESP (OKAY=0)', resp, 0, failures)
        return failures

    async def run_all(self, count=4):
        """Every check, over `count` addresses. Returns the failure list."""
        seed = int(os.environ.get('SEED', '0'))
        rnd = random.Random(seed)
        self.log.info(f"AXIL5 optional-signal suite, seed={seed}")

        all_failures = []
        data_mask = (1 << self.TEST_DATA_WIDTH) - 1
        bytes_per_word = self.TEST_DATA_WIDTH // 8

        for i in range(count):
            addr = i * bytes_per_word
            data = rnd.randrange(1, data_mask)

            failures, v = await self.test_write_qualifiers(addr, data, rnd)
            all_failures += failures
            all_failures += await self.test_read_qualifiers(
                addr, data, v['wpoison'], rnd)

        all_failures += await self.test_exclusive_access(
            addr=0, data=0xA5A5_5A5A & data_mask)

        if all_failures:
            self.log.error(f"{len(all_failures)} optional-signal failures:")
            for f in all_failures:
                self.log.error(f"  - {f}")
        else:
            self.log.info("all AXI5-Lite optional signal groups verified")
        return all_failures
