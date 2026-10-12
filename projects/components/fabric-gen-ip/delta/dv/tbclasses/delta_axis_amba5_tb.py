# SPDX-License-Identifier: MIT
# SPDX-FileCopyrightText: 2026 sean galloway
#
# RTL Design Sherpa - Industry-Standard RTL Design and Verification
# https://github.com/sean-galloway/RTLDesignSherpa
#
# Module: delta_axis_amba5_tb
# Purpose: TB for a delta AXIS crossbar generated with --amba5: routing plus
#          the IHI 0051B ch. 5 interface check signals (odd parity).
#
# Subsystem: delta (dv)
#
# Author: sean galloway
# Created: 2026-10-12

"""
Delta AXIS crossbar TB, AMBA 5 flavor.

Binds one RDS-DV AXIS5 master BFM to every crossbar master port
(``s<m>_axis_``) and one AXIS5 slave BFM to every slave port
(``m<s>_axis_``) of the flattening harness
``dv/tb/delta_axis_flat_2x4_strb_amba5_th.sv``. All BFMs run with
``enable_parity=True``: masters drive every payload *CHK plus TVALIDCHK /
TWAKEUPCHK, slaves check the payload *CHK they receive and drive TREADYCHK.

What the crossbar itself owns, and what this TB checks it for:

- payload *CHK carried from the granted master to the slave unchanged
  (the slave BFM's odd-parity check on every received beat);
- TVALIDCHK / TWAKEUPCHK generated on every slave port and TREADYCHK on
  every master port, as the inversion of the signal it drives
  (a per-cycle watcher, counted so a silent watcher cannot pass);
- TWAKEUP steered by TDEST before TVALID;
- the sticky ``s<m>_parity_error`` / ``m<s>_parity_error`` flags: clear on
  clean traffic, set by a bad payload *CHK or TVALIDCHK on a master port and
  by a bad TREADYCHK on a slave port.
"""

import os
import random

import cocotb
from cocotb.triggers import FallingEdge, RisingEdge
from CocoTBFramework.components.axis5.axis5_check import odd_parity_chk
from CocoTBFramework.components.axis5.axis5_factories import (
    create_axis5_master,
    create_axis5_slave,
)
from CocoTBFramework.components.axis5.axis5_packet import AXIS5Packet
from CocoTBFramework.components.shared.flex_randomizer import FlexRandomizer
from TBClasses.shared.tbbase import TBBase


class DeltaAxisAmba5TB(TBBase):
    """TB for delta_axis_flat_2x4 (--strb-width 4 --amba5) via its harness."""

    def __init__(self, dut):
        super().__init__(dut)
        self.NUM_MASTERS = self.convert_to_int(os.environ.get('TEST_NUM_MASTERS', '2'))
        self.NUM_SLAVES = self.convert_to_int(os.environ.get('TEST_NUM_SLAVES', '4'))
        self.DATA_WIDTH = self.convert_to_int(os.environ.get('TEST_DATA_WIDTH', '32'))
        self.ID_WIDTH = self.convert_to_int(os.environ.get('TEST_ID_WIDTH', '1'))
        self.DEST_WIDTH = self.convert_to_int(os.environ.get('TEST_DEST_WIDTH', '2'))
        self.USER_WIDTH = self.convert_to_int(os.environ.get('TEST_USER_WIDTH', '1'))
        self.SEED = self.convert_to_int(os.environ.get('SEED', '12345'))
        self.TEST_LEVEL = os.environ.get('TEST_LEVEL', 'gate').lower()
        if self.TEST_LEVEL not in ('gate', 'func', 'full'):
            self.log.warning(f"Invalid TEST_LEVEL '{self.TEST_LEVEL}', using 'gate'")
            self.TEST_LEVEL = 'gate'
        # Frames per (master, slave) pair: the depth knob
        self.FRAMES_PER_PAIR = {'gate': 1, 'func': 3, 'full': 8}[self.TEST_LEVEL]
        random.seed(self.SEED)
        self.log.info(f"delta AMBA5 TB: {self.NUM_MASTERS}x{self.NUM_SLAVES} "
                      f"DW={self.DATA_WIDTH} level={self.TEST_LEVEL} seed={self.SEED}")

        self.aclk = dut.aclk
        self.aresetn = dut.aresetn
        self.masters = []
        self.slaves = []
        self.received = []   # per slave: packets in arrival order
        # Control-check watcher: (port, signal) -> cycles checked / mismatches
        self.ctrl_checked = 0
        self.ctrl_mismatches = []
        self._watch_on = False
        # Handshakes seen on each port (independent of the BFMs' own counts)
        self.s_beats = [0] * self.NUM_MASTERS
        self.m_beats = [0] * self.NUM_SLAVES
        self.m_stalls = 0    # slave-port cycles with TVALID high, TREADY low

    # ------------------------------------------------------------------
    # Mandatory TB methods
    # ------------------------------------------------------------------
    async def setup_clocks_and_reset(self):
        await self.start_clock('aclk', 10, 'ns')
        self._init_inputs()
        self._build_bfms()
        cocotb.start_soon(self._ctrl_chk_watcher())
        await self.assert_reset()
        await self.deassert_reset()

    async def assert_reset(self):
        self._watch_on = False
        self.aresetn.value = 0
        await self.wait_clocks('aclk', 5)

    async def deassert_reset(self):
        self.aresetn.value = 1
        await self.wait_clocks('aclk', 3)
        self._watch_on = True

    # ------------------------------------------------------------------
    # Setup
    # ------------------------------------------------------------------
    def _sig(self, name):
        return getattr(self.dut, name)

    def _init_inputs(self):
        for m in range(self.NUM_MASTERS):
            p = f"s{m}_axis_"
            for n in ('tdata', 'tstrb', 'tlast', 'tid', 'tdest', 'tuser', 'tvalid',
                      'twakeup'):
                self._sig(p + n).value = 0
            # Check bits for the all-zero idle payload: odd parity = all ones
            for n in ('tdatachk', 'tstrbchk', 'tlastchk', 'tidchk', 'tdestchk',
                      'tuserchk', 'tvalidchk', 'twakeupchk'):
                sig = self._sig(p + n)
                sig.value = (1 << len(sig)) - 1
        for s in range(self.NUM_SLAVES):
            self._sig(f"m{s}_axis_tready").value = 0
            self._sig(f"m{s}_axis_treadychk").value = 1

    def _build_bfms(self):
        common = {
            'clock': self.aclk, 'data_width': self.DATA_WIDTH, 'id_width': self.ID_WIDTH,
            'dest_width': self.DEST_WIDTH, 'user_width': self.USER_WIDTH,
            'enable_wakeup': True, 'enable_parity': True,
            # one pin per field (tdata, tdatachk, ...), not one packed bus
            'multi_sig': True,
            # 'parity_error' is the AXIS5 packet's pin-less status field
            # (0 = no error); nothing on the bus to bind it to
            'optional_fields': ('parity_error',),
            'log': self.log,
        }
        # Timing axis: gate runs back-to-back (no valid or ready gaps); func
        # and full take the GAXI defaults -- random VALID gaps on the masters
        # and random READY stalls on the slaves -- so the packet-atomic grant
        # has to hold each beat and its *CHK across stalls.
        def timing(kind):
            if self.TEST_LEVEL != 'gate':
                return None
            return FlexRandomizer({kind: ([(0, 0)], [1])})
        for m in range(self.NUM_MASTERS):
            self.masters.append(create_axis5_master(
                dut=self.dut, prefix=f"s{m}_axis_", randomizer=timing('valid_delay'),
                **common)['master'])
        for s in range(self.NUM_SLAVES):
            slave = create_axis5_slave(
                dut=self.dut, prefix=f"m{s}_axis_", randomizer=timing('ready_delay'),
                **common)['slave']
            # The AXIS slave registers its own frame callback, and a cocotb
            # Monitor with callbacks does not also fill _recvQ -- collect here.
            got = []
            slave.add_callback(got.append)
            self.received.append(got)
            self.slaves.append(slave)

    # ------------------------------------------------------------------
    # Checkers
    # ------------------------------------------------------------------
    async def _ctrl_chk_watcher(self):
        """Every cycle out of reset: each single-bit control check the
        crossbar DRIVES is the inversion of its signal (IHI 0051B 5.3).

        Sampled on the falling edge, after the rising-edge drivers settle.
        """
        driven = [(f"m{s}_axis_", 'tvalid') for s in range(self.NUM_SLAVES)]
        driven += [(f"m{s}_axis_", 'twakeup') for s in range(self.NUM_SLAVES)]
        driven += [(f"s{m}_axis_", 'tready') for m in range(self.NUM_MASTERS)]
        while True:
            await FallingEdge(self.aclk)
            if not self._watch_on:
                continue
            for m in range(self.NUM_MASTERS):
                if int(self._sig(f"s{m}_axis_tvalid").value) and \
                        int(self._sig(f"s{m}_axis_tready").value):
                    self.s_beats[m] += 1
            for s in range(self.NUM_SLAVES):
                if int(self._sig(f"m{s}_axis_tvalid").value):
                    if int(self._sig(f"m{s}_axis_tready").value):
                        self.m_beats[s] += 1
                    else:
                        self.m_stalls += 1
            for prefix, sig in driven:
                val = int(self._sig(prefix + sig).value)
                chk = int(self._sig(prefix + sig + 'chk').value)
                self.ctrl_checked += 1
                if chk != (val ^ 1):
                    self.ctrl_mismatches.append((prefix + sig, val, chk))

    def parity_error_flags(self):
        s_flags = [int(self._sig(f"s{m}_parity_error").value) for m in range(self.NUM_MASTERS)]
        m_flags = [int(self._sig(f"m{s}_parity_error").value) for s in range(self.NUM_SLAVES)]
        return s_flags, m_flags

    def slave_parity_stats(self):
        passed = sum(s.parity_checks_passed for s in self.slaves)
        failed = sum(s.parity_errors_detected for s in self.slaves)
        return passed, failed

    # ------------------------------------------------------------------
    # Stimulus
    # ------------------------------------------------------------------
    def _beat(self, master, data, dest, last, tid):
        pkt = AXIS5Packet(field_config=master.field_config, data_width=self.DATA_WIDTH,
                          enable_wakeup=True, enable_parity=True)
        pkt.data = data
        pkt.strb = random.randrange(1, 1 << (self.DATA_WIDTH // 8))
        pkt.last = last
        pkt.id = tid
        pkt.dest = dest
        pkt.user = random.randrange(0, 1 << self.USER_WIDTH)
        return pkt

    async def _send_frames(self, m, plan):
        """Send master m's frames: plan is a list of (dest, [data...])."""
        master = self.masters[m]
        for dest, beats in plan:
            for i, data in enumerate(beats):
                pkt = self._beat(master, data, dest, int(i == len(beats) - 1),
                                 m & ((1 << self.ID_WIDTH) - 1))
                ok = await master.send_packet(pkt)
                assert ok, f"master {m} timed out sending to dest {dest}"

    async def run_routing_with_checks(self):
        """Every master sends frames to every slave concurrently; each slave
        must receive exactly its frames, every beat odd-parity clean, and no
        error flag may set."""
        expected = {s: [] for s in range(self.NUM_SLAVES)}
        plans = []
        for m in range(self.NUM_MASTERS):
            plan = []
            for _ in range(self.FRAMES_PER_PAIR):
                for s in range(self.NUM_SLAVES):
                    beats = [random.getrandbits(self.DATA_WIDTH)
                             for _ in range(random.randint(1, 4))]
                    plan.append((s, beats))
                    expected[s].extend(beats)
            random.shuffle(plan)
            plans.append(plan)
        senders = [cocotb.start_soon(self._send_frames(m, plans[m]))
                   for m in range(self.NUM_MASTERS)]
        for t in senders:
            await t
        total = sum(len(v) for v in expected.values())
        for _ in range(2000):
            await RisingEdge(self.aclk)
            if sum(len(r) for r in self.received) >= total:
                break
        await self.wait_clocks('aclk', 10)

        if self.TEST_LEVEL != 'gate':
            assert self.m_stalls > 0, "no slave stall seen: the timing axis is not armed"
        self.log.info(f"handshakes: masters={self.s_beats} slaves={self.m_beats} "
                      f"stalls={self.m_stalls} "
                      f"expected per slave={[len(expected[s]) for s in range(self.NUM_SLAVES)]}")
        for s in range(self.NUM_SLAVES):
            got = [int(p.data) for p in self.received[s]]
            assert sorted(got) == sorted(expected[s]), (
                f"slave {s}: received {len(got)} beats, expected {len(expected[s])}; "
                f"missing={sorted(set(expected[s]) - set(got))[:4]} "
                f"extra={sorted(set(got) - set(expected[s]))[:4]}")
            dests = {int(p.dest) for p in self.received[s]}
            assert dests <= {s}, f"slave {s} saw TDEST {dests}"
        passed, failed = self.slave_parity_stats()
        assert failed == 0, f"slave BFMs saw {failed} bad payload *CHK beats"
        assert passed == total, f"parity checked on {passed} of {total} beats"
        s_flags, m_flags = self.parity_error_flags()
        assert not any(s_flags) and not any(m_flags), \
            f"parity_error set on clean traffic: s={s_flags} m={m_flags}"
        assert self.ctrl_checked > 0 and not self.ctrl_mismatches, (
            f"control *CHK mismatches ({len(self.ctrl_mismatches)} of "
            f"{self.ctrl_checked} checks): {self.ctrl_mismatches[:4]}")
        self.log.info(f"routing: {total} beats, {passed} odd-parity checks, "
                      f"{self.ctrl_checked} control-check samples, flags clear")
        for got in self.received:
            got.clear()
        return total

    async def run_wakeup_steering(self):
        """TWAKEUP with no TVALID reaches only the TDEST-selected slave, and
        that slave port's TWAKEUPCHK is its inversion.

        TWAKEUP is driven here directly (it is a hint with no handshake), so
        the masters' TVALIDCHK/TWAKEUPCHK mirrors are stopped and both check
        bits are driven in the same delta as their signals."""
        for master in self.masters:
            for t in master._chk_tasks:
                t.kill()
        for m in range(self.NUM_MASTERS):
            for dest in range(self.NUM_SLAVES):
                await FallingEdge(self.aclk)
                self._sig(f"s{m}_axis_tdest").value = dest
                self._sig(f"s{m}_axis_tdestchk").value = odd_parity_chk(dest, self.DEST_WIDTH)
                self._sig(f"s{m}_axis_twakeup").value = 1
                self._sig(f"s{m}_axis_twakeupchk").value = 0
                await RisingEdge(self.aclk)
                await FallingEdge(self.aclk)
                woke = [int(self._sig(f"m{s}_axis_twakeup").value)
                        for s in range(self.NUM_SLAVES)]
                assert woke == [int(s == dest) for s in range(self.NUM_SLAVES)], \
                    f"TWAKEUP from master {m} tdest={dest}: slaves woke {woke}"
                assert int(self._sig(f"m{dest}_axis_twakeupchk").value) == 0, \
                    f"m{dest}_axis_twakeupchk is not ~TWAKEUP"
                self._sig(f"s{m}_axis_twakeup").value = 0
                self._sig(f"s{m}_axis_twakeupchk").value = 1
        await self.wait_clocks('aclk', 3)
        s_flags, m_flags = self.parity_error_flags()
        assert not any(s_flags) and not any(m_flags), \
            f"parity_error set by clean wakeup: s={s_flags} m={m_flags}"

    async def run_error_injection(self):
        """Each class of bad check sets the right sticky flag and only it.

        1. bad TDATACHK on master 0's beat -> s0_parity_error, and the slave
           BFM sees the same bad bit (carried, not regenerated);
        2. bad TVALIDCHK on master 1      -> s1_parity_error;
        3. bad TREADYCHK on slave 2        -> m2_parity_error.
        A reset between cases proves each flag clears.
        """
        # 1. payload check
        self.masters[0]._inject_parity_error = True
        await self._send_frames(0, [(1, [0x5A5A_0001])])
        self.masters[0]._inject_parity_error = False
        await self.wait_clocks('aclk', 10)
        s_flags, m_flags = self.parity_error_flags()
        _, failed = self.slave_parity_stats()
        assert s_flags == [1] + [0] * (self.NUM_MASTERS - 1) and not any(m_flags), \
            f"bad TDATACHK on m0: flags s={s_flags} m={m_flags}"
        assert failed == 1, f"slave BFM saw {failed} bad beats, expected the 1 injected"
        await self._reset_and_expect_clear()

        # 2. TVALIDCHK on master 1: stop its mirror, drive the wrong value
        mirror = self.masters[1]._chk_tasks
        for t in mirror:
            t.kill()
        await FallingEdge(self.aclk)
        self._sig("s1_axis_tvalidchk").value = int(self._sig("s1_axis_tvalid").value)
        await self.wait_clocks('aclk', 2)
        s_flags, m_flags = self.parity_error_flags()
        assert s_flags[1] == 1 and s_flags[0] == 0 and not any(m_flags), \
            f"bad TVALIDCHK on m1: flags s={s_flags} m={m_flags}"
        self._sig("s1_axis_tvalidchk").value = int(self._sig("s1_axis_tvalid").value) ^ 1
        await self._reset_and_expect_clear()

        # 3. TREADYCHK on slave 2
        for t in self.slaves[2]._chk_tasks:
            t.kill()
        await FallingEdge(self.aclk)
        self._sig("m2_axis_treadychk").value = int(self._sig("m2_axis_tready").value)
        await self.wait_clocks('aclk', 2)
        s_flags, m_flags = self.parity_error_flags()
        expect_m = [int(s == 2) for s in range(self.NUM_SLAVES)]
        assert m_flags == expect_m and not any(s_flags), \
            f"bad TREADYCHK on s2: flags s={s_flags} m={m_flags}"
        self._sig("m2_axis_treadychk").value = int(self._sig("m2_axis_tready").value) ^ 1
        await self._reset_and_expect_clear()

    async def _reset_and_expect_clear(self):
        await self.assert_reset()
        await self.deassert_reset()
        s_flags, m_flags = self.parity_error_flags()
        assert not any(s_flags) and not any(m_flags), \
            f"parity_error did not clear on reset: s={s_flags} m={m_flags}"

