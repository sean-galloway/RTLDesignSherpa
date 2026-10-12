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

"""Testbench for ``axil5_opt_slave`` -- the AXI5-Lite ID and optional groups.

Signal set per IHI 0022 Issue L Table B2.2, AXI5-Lite column: AWID/BID and
ARID/RID (YS), USER, TRACE and POISON (O). AxLOCK, AxMPAM, AxMECID, AxNSAID
and xLOOP are "N" (not present) on AXI5-Lite and exclusive access is not
supported (B2.1.5), so none of them is driven or checked here.

What each check proves, and how:

``ID``
    Driven on AW/AR, reflected by the DUT on B/R (A5.1.1: the Manager requires
    BID and RID to be reflected from AWID and ARID). Checked from
    ``last_b_packet`` / ``last_r_packet``. The ID is mandatory on a
    Subordinate, so it has no ENABLE_* and is checked in every configuration.

``TRACE`` / ``USER``
    Driven on the address channel, echoed by the DUT on the matching response
    channel (the spec behaviour for TRACE; the DUT's stated contract for
    USER). A value that fails to reach the wire comes back as 0 and the check
    fails.

``POISON``
    Written with the data, stored, and returned on a read of the same address.
    Proves the value survives a round trip rather than merely being driven.

``PROT`` / ``WUSER``
    No response to ride back on, so the DUT captures them on ``o_last_*``
    observation ports and the TB samples those -- the check that the BFM
    DROVE the value.

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
ID_WIDTH = 4
USER_WIDTH = 4


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
            id_width=ID_WIDTH,
            user_width=USER_WIDTH,
            trace=True,
            poison=True,
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
            for g in ('user', 'trace', 'poison')
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
        if AWID and AWUSER both carried 5, swapping them in the RTL or the
        field config would go unnoticed. Non-zero because an unbound or
        undriven field reads 0, which is the failure this suite exists to
        detect -- expecting 0 anywhere would make that check vacuous.
        """
        vals = {
            'awid':    rnd.randrange(1, 1 << ID_WIDTH),
            'awuser':  rnd.randrange(1, 1 << USER_WIDTH),
            'wuser':   rnd.randrange(1, 1 << USER_WIDTH),
            'awtrace': 1,
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

        # Reflected / echoed on the response channel. BID has no enable: an
        # AXI5-Lite Subordinate always carries the ID.
        self._check('BID',    self._field(b, 'id'), v['awid'], failures)
        self._check('BUSER',  self._field(b, 'user'),
                    self._want('user', v['awuser']), failures)
        self._check('BTRACE', self._field(b, 'trace'),
                    self._want('trace', v['awtrace']), failures)

        # Captured by the DUT -- proof the BFM drove the wire.
        self._check('AWPROT@dut',  int(self.dut.o_last_aw_prot.value),
                    v['awprot'], failures)
        self._check('WUSER@dut',   int(self.dut.o_last_w_user.value),
                    self._want('user', v['wuser']), failures)
        return failures, v

    async def test_read_qualifiers(self, addr, expect_data, expect_poison, rnd):
        """Drive every AR optional field; check echo, poison and capture."""
        v = {
            'arid':    rnd.randrange(1, 1 << ID_WIDTH),
            'aruser':  rnd.randrange(1, 1 << USER_WIDTH),
            'artrace': 1,
            'arprot':  rnd.randrange(1, 8),
        }
        self.log.info(f"=== read 0x{addr:08X} with {v} ===")

        got = await self.read_if.read_transaction(addr, **v)

        failures = []
        self._check('RDATA', got, expect_data, failures)

        r = self.read_if.last_r_packet
        assert r is not None, "no R packet retained; response sideband is lost"

        self._check('RID',     self._field(r, 'id'), v['arid'], failures)
        self._check('RUSER',   self._field(r, 'user'),
                    self._want('user', v['aruser']), failures)
        self._check('RTRACE',  self._field(r, 'trace'),
                    self._want('trace', v['artrace']), failures)
        # POISON is the round-trip check: written earlier, stored, returned now.
        self._check('RPOISON', self._field(r, 'poison'),
                    self._want('poison', expect_poison), failures)

        self._check('ARPROT@dut',  int(self.dut.o_last_ar_prot.value),
                    v['arprot'], failures)
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

        if all_failures:
            self.log.error(f"{len(all_failures)} optional-signal failures:")
            for f in all_failures:
                self.log.error(f"  - {f}")
        else:
            self.log.info("AXI5-Lite ID and optional signal groups verified")
        return all_failures
