# SPDX-License-Identifier: MIT
# SPDX-FileCopyrightText: 2024-2025 sean galloway
#
# RTL Design Sherpa - Industry-Standard RTL Design and Verification
# https://github.com/sean-galloway/RTLDesignSherpa
#
# Module: test_mon_cg_gating
# Purpose: Structural clock-gating test for all 16 *_mon_cg monitor wrappers, BFM-driven
#
# Documentation: PRD.md
# Subsystem: tests
#
# Author: sean galloway
# Created: 2026-07-20

"""
Clock gating behaviour test for the 16 ``*_mon_cg`` monitor wrappers.

This test exists because the pre-existing ``test_*_mon_cg.py`` suites all passed
while none of the twelve wrappers of the day actually gated a clock (GitHub
issue #41, "Clock gating" section).  Those suites exercise monitor *function*;
they never looked at the clock.  This one looks at nothing else.

STIMULUS IS THE FRAMEWORK'S.  Every valid/ready pair on the DUT is driven by
the CocoTBFramework BFMs the family's own monitor TB class already builds:
the upstream request comes from the master BFM, the downstream response from
the slave BFM's memory model, and every stall in the phases below is a BFM
``ready_policy`` ('stall' / 'always'), not a pin poke.  The test reads DUT
pins to OBSERVE handshakes and gating; it drives only the config pins
(cfg_*, cam_clear).  Sean, 2026-09-26: "Never hand roll BFMs".  The previous
version of this file drove valid/ready by hand and delivered every response
beat twice for as long as it existed (see the handbook, dv/bfm-usage.md,
"A hand-rolled driver has a write-timing hazard a BFM does not").

What is asserted, per DUT:

  Phase 1 - idle, consumer response-ready LOW (upstream response BFM: 'stall')
      ``cg_gating`` rises and the internal gated clock STOPS TOGGLING.

  Phase 2 - idle, consumer response-ready HIGH ('always')
      A consumer that parks R/B-ready high while idle is behaving correctly and
      must NOT defeat gating.  Activity must be derived from VALID signals and
      outstanding work only, never from a peer's READY.

  Phase 3 - wake
      The master BFM's request valid restores the gated clock and drops
      ``cg_gating``.

  Phase 4 - transfer integrity across gate/ungate
      Every request starts from a fully gated block.  Exactly one upstream
      and one downstream request handshake per transaction - no drops, no
      duplicates - observed on the pins at falling edges.

  Phase 5 - beat held inside the block under downstream back-pressure
      The downstream request BFM stalls; the accepted request sits in the
      wrapper.  The block must stay awake until the BFM releases it.

  Phase 6 - monitor-bus liveness (TASK-070)
      The MonbusSlave stalls; one transaction completes; its completion packet
      parks on ``monbus_valid``.  The block must not gate under it, and when
      the MonbusSlave releases, the slave receives exactly one packet.

The gated clock is observed directly at ``dut.gated_aclk``; cocotb-test compiles
Verilator with ``--public-flat-rw``, so wrapper-internal nets are visible.
"""

import os
import pytest
import cocotb
from cocotb.triggers import RisingEdge, FallingEdge, Edge, with_timeout

from cocotb_test.simulator import run
from TBClasses.shared.utilities import get_paths, sim_build_path
from TBClasses.shared.filelist_utils import get_sources_from_filelist
from TBClasses.amba.amba_random_configs import AXI_RANDOMIZER_CONFIGS
from CocoTBFramework.components.shared.flex_randomizer import FlexRandomizer
from TBClasses.axi4.monitor.axi4_master_monitor_tb import AXI4MasterMonitorTB
from TBClasses.axi4.monitor.axi4_slave_monitor_tb import AXI4SlaveMonitorTB
from TBClasses.axi5.monitor.axi5_master_monitor_tb import AXI5MasterMonitorTB
from TBClasses.axi5.monitor.axi5_slave_monitor_tb import AXI5SlaveMonitorTB
from TBClasses.axil4.monitor.axil4_master_monitor_tb import AXIL4MasterMonitorTB
from TBClasses.axil4.monitor.axil4_slave_monitor_tb import AXIL4SlaveMonitorTB
from TBClasses.axil5.monitor.axil5_master_monitor_tb import AXIL5MasterMonitorTB
from TBClasses.axil5.monitor.axil5_slave_monitor_tb import AXIL5SlaveMonitorTB

CLK_PERIOD_NS = 10
CG_IDLE_COUNT_WIDTH = 4

# cfg_cg_idle_count values to sweep.  0 is the aggressive case: the block gates
# the cycle after activity drops, which is what exposes a beat stranded inside
# the stopped clock domain.  Correctness must not depend on the idle count being
# long enough to cover the wrapper's internal pipeline latency, so both an
# aggressive and a relaxed setting are covered.
IDLE_COUNTS = (0, 4)

# BFM timing comes from the repo's shared profile table, never from numbers
# typed here (bin/TBClasses/amba/amba_random_configs.py). 'backtoback' is the
# deterministic zero-gap case; 'constrained' puts 0-10 cycle gaps on every
# valid and ready so the gate/ungate boundaries land at varied points of a
# transaction. The stalls the phases need are still ready_policy, which is
# deterministic backpressure and overrides the profile while set.
BFM_PROFILES = ('backtoback', 'constrained')

WRAPPER_SUFFIX = 'mon_cg'


# ---------------------------------------------------------------------------
# DUT table
# ---------------------------------------------------------------------------
# Port naming is fully symmetric across all sixteen wrappers:
#   masters: upstream = fub_ax*   downstream = m_ax*
#   slaves:  upstream = s_ax*     downstream = fub_ax*
# The test reads these pins to observe handshakes; it never drives them.

AXI4_PARAMS = {
    'AXI_ID_WIDTH': '8', 'AXI_ADDR_WIDTH': '32', 'AXI_DATA_WIDTH': '32',
    'AXI_USER_WIDTH': '1', 'MAX_TRANSACTIONS': '8',
    'CG_IDLE_COUNT_WIDTH': str(CG_IDLE_COUNT_WIDTH),
}
AXI5_PARAMS = dict(AXI4_PARAMS)
AXIL_PARAMS = {
    'AXIL_ADDR_WIDTH': '32', 'AXIL_DATA_WIDTH': '32', 'MAX_TRANSACTIONS': '8',
    'CG_IDLE_COUNT_WIDTH': str(CG_IDLE_COUNT_WIDTH),
}

TB_CLASSES = {
    ('axi4', 'master'): AXI4MasterMonitorTB, ('axi4', 'slave'): AXI4SlaveMonitorTB,
    ('axi5', 'master'): AXI5MasterMonitorTB, ('axi5', 'slave'): AXI5SlaveMonitorTB,
    ('axil4', 'master'): AXIL4MasterMonitorTB, ('axil4', 'slave'): AXIL4SlaveMonitorTB,
    ('axil5', 'master'): AXIL5MasterMonitorTB, ('axil5', 'slave'): AXIL5SlaveMonitorTB,
}


def _dut_table():
    table = {}
    for family, bus, params in (('axi4', 'axi', AXI4_PARAMS),
                                ('axil4', 'axil', AXIL_PARAMS),
                                ('axi5', 'axi', AXI5_PARAMS),
                                ('axil5', 'axil', AXIL_PARAMS)):
        for role in ('master', 'slave'):
            for direction in ('rd', 'wr'):
                name = f'{family}_{role}_{direction}_{WRAPPER_SUFFIX}'
                up = f'fub_{bus}' if role == 'master' else f's_{bus}'
                down = f'm_{bus}' if role == 'master' else f'fub_{bus}'
                table[name] = dict(
                    name=name, family=family, bus=bus, role=role,
                    direction=direction, up=up, down=down,
                    params=params,
                    filelist=f'rtl/amba/filelists/{name}.f',
                )
    return table


DUTS = _dut_table()


# ---------------------------------------------------------------------------
# cocotb side
# ---------------------------------------------------------------------------

def _cfg():
    """Rebuild the DUT descriptor inside the simulator from env."""
    return DUTS[os.environ['DUT']]


def _get(dut, name):
    handle = getattr(dut, name, None)
    return int(handle.value) if handle is not None else 0


def _set_cfg(dut, name, value):
    """Drive a CONFIG pin if the DUT has it. Config pins are not a protocol
    interface; every valid/ready in this test is a BFM's."""
    handle = getattr(dut, name, None)
    if handle is not None:
        handle.value = value


async def _gated_clock_running(dut, window_cycles=8):
    """True if dut.gated_aclk toggles within window_cycles of aclk."""
    try:
        await with_timeout(Edge(dut.gated_aclk),
                           window_cycles * CLK_PERIOD_NS, 'ns')
        return True
    except Exception:      # cocotb.result.SimTimeoutError
        return False


class GatingHarness:
    """The family's monitor TB (framework BFMs on both sides of the wrapper
    plus a MonbusSlave) with the three controls the gating phases need:
    the upstream response BFM's ready policy, the downstream request BFM's
    ready policy, and one BFM-driven transaction."""

    def __init__(self, dut):
        self.dut = dut
        self.cfg = _cfg()
        self.is_rd = self.cfg['direction'] == 'rd'
        self.is_axil = self.cfg['bus'] == 'axil'
        up, down = self.cfg['up'], self.cfg['down']
        req = 'ar' if self.is_rd else 'aw'
        # Pins the test OBSERVES.
        self.up_req_valid = f'{up}_{req}valid'
        self.up_req_ready = f'{up}_{req}ready'
        self.down_req_valid = f'{down}_{req}valid'
        self.down_req_ready = f'{down}_{req}ready'
        cls = TB_CLASSES[(self.cfg['family'], self.cfg['role'])]
        self.tb = cls(dut, is_write=not self.is_rd, aclk=dut.aclk, aresetn=dut.aresetn)
        self.log = dut._log
        self.txn = 0

    async def initialize(self):
        await self.tb.initialize()
        d = self.dut
        # The monitor TB enables timeouts at 1000 us; a stopped clock makes
        # that meaningless, and a timeout packet would confuse phase 6's
        # exactly-one accounting. Completion on, everything else off.
        _set_cfg(d, 'cfg_timeout_enable', 0)
        _set_cfg(d, 'cfg_perf_enable', 0)
        _set_cfg(d, 'cfg_debug_enable', 0)
        _set_cfg(d, 'cfg_threshold_enable', 0)
        _set_cfg(d, 'cfg_compl_enable', 1)
        _set_cfg(d, 'cfg_error_enable', 1)
        _set_cfg(d, 'cfg_addr_check_enable', 0)
        _set_cfg(d, 'cfg_cg_enable', 1)
        _set_cfg(d, 'cfg_cg_idle_count', int(os.environ['CG_IDLE_COUNT']))
        # BFM handles, from the factory component dicts every family's TB
        # keeps (the per-channel attribute names differ between the base TB
        # classes; the dict keys do not). The upstream master BFM's response
        # receiver is a GAXISlave whose ready is the consumer's response-ready;
        # the downstream slave BFM's request receivers are GAXISlaves whose
        # ready is the downstream request-ready.
        owner = self.tb if self.is_axil else self.tb.base_tb
        mc = next(getattr(owner, a) for a in ('master_components', 'write_master', 'read_master')
                  if getattr(owner, a, None) is not None)
        sc = next(getattr(owner, a) for a in ('slave_components', 'write_slave', 'read_slave')
                  if getattr(owner, a, None) is not None)
        self.up_rsp = mc['R'] if self.is_rd else mc['B']
        self.down_req = [sc['AR']] if self.is_rd else [sc['AW'], sc['W']]
        self.mon = self.tb.mon_slave
        # Shared delay profile on every BFM channel: request drivers and
        # response drivers take the 'master' (valid_delay) section, request and
        # response receivers the 'slave' (ready_delay) section.
        prof = AXI_RANDOMIZER_CONFIGS[os.environ['BFM_PROFILE']]
        req_keys = ('AR',) if self.is_rd else ('AW', 'W')
        rsp_key = 'R' if self.is_rd else 'B'
        for k in req_keys:
            mc[k].set_randomizer(FlexRandomizer(dict(prof['master'])))
            sc[k].set_randomizer(FlexRandomizer(dict(prof['slave'])))
        sc[rsp_key].set_randomizer(FlexRandomizer(dict(prof['master'])))
        mc[rsp_key].set_randomizer(FlexRandomizer(dict(prof['slave'])))
        # Phase 1 starts with the consumer's response-ready LOW; the downstream
        # request receivers follow the profile ('valid_first' + ready_delay).
        self.up_rsp.set_ready_policy('stall')
        for c in self.down_req:
            c.set_ready_policy('valid_first')
        self.mon.set_ready_policy('always')

    # -- stimulus: ONE transaction through the framework BFMs ---------------
    async def one_transaction(self):
        self.txn += 1
        addr = 0x1000 + 0x40 * self.txn
        data = 0xA5A50000 + self.txn
        tag = self.txn
        tb, fam, role = self.tb, self.cfg['family'], self.cfg['role']
        if self.is_axil:
            if self.is_rd:
                return await tb.single_read_test(addr)
            return await tb.single_write_test(addr, data)
        b = tb.base_tb
        if fam == 'axi4':
            if role == 'master':
                return await (b.single_read_test(addr, arid=tag) if self.is_rd
                              else b.single_write_test(addr, data, transaction_id=tag))
            return await (b.single_read_response_test(addr, arid=tag) if self.is_rd
                          else b.single_write_response_test(addr, data, transaction_id=tag))
        # axi5: master and slave TBs share the signature
        return await (b.single_read_test(addr, arid=tag) if self.is_rd
                      else b.single_write_test(addr, data, awid=tag))

    # -- observation ---------------------------------------------------------
    def start_handshake_counter(self, cycles):
        """Count request handshakes on both sides of the wrapper, sampling the
        pins at falling edges (valid/ready are stable there: the BFMs write
        at falling edges and the DUT's registers move at rising edges)."""
        dut = self
        class _Counter:
            up = 0
            down = 0
            async def _run(self):
                for _ in range(cycles):
                    await FallingEdge(dut.dut.aclk)
                    if _get(dut.dut, dut.up_req_valid) and _get(dut.dut, dut.up_req_ready):
                        self.up += 1
                    if _get(dut.dut, dut.down_req_valid) and _get(dut.dut, dut.down_req_ready):
                        self.down += 1
        c = _Counter()
        c.task = cocotb.start_soon(c._run())
        return c

    async def settle_to_gated(self, cycles=40):
        for _ in range(cycles):
            await RisingEdge(self.dut.aclk)

    async def await_delivery(self, count, timeout_cycles=200):
        """Wait until the MonbusSlave has received `count` packets since the
        last clear. Housekeeping (cam_clear) must not land inside the
        reporter's emission window: on the full monitor at idle-count 0 the
        CAM going empty drops the last liveness term a few cycles before the
        packet reaches monbus_valid, and the clock stops with the packet
        mid-reporter. Measured on the axi4/axil4/axil5 slave wrappers when
        this test cleared right after the transaction (amba ISSUE, see
        TASK-001 section 15). So: deliver first, then clear."""
        for _ in range(timeout_cycles):
            if len(self.mon.received_packets) >= count:
                return
            await RisingEdge(self.dut.aclk)
        raise AssertionError(
            f"{self.cfg['name']}: {len(self.mon.received_packets)} monbus packet(s) "
            f"received, expected {count} within {timeout_cycles} cycles")

    async def cam_clear_pulse(self):
        _set_cfg(self.dut, 'cam_clear', 1)
        await RisingEdge(self.dut.aclk)
        _set_cfg(self.dut, 'cam_clear', 0)


async def _run_txn_and_count(h, cycles=600):
    """One BFM transaction with the pin-level handshake counter running
    alongside it. Returns (up_handshakes, down_handshakes)."""
    counter = h.start_handshake_counter(cycles)
    await with_timeout(h.one_transaction(), cycles * CLK_PERIOD_NS, 'ns')
    await counter.task
    return counter.up, counter.down


@cocotb.test(timeout_time=20, timeout_unit='ms')
async def mon_cg_gating_test(dut):
    h = GatingHarness(dut)
    name = h.cfg['name']

    for port in ('cfg_cg_enable', 'cfg_cg_idle_count', 'cg_gating', 'cg_idle'):
        assert getattr(dut, port, None) is not None, (
            f'{name}: port {port} missing -- the converged clock-gating '
            f'interface is not implemented on this wrapper')

    await h.initialize()

    # ---------------------------------------------------------------- P1 ---
    # Idle bus, consumer response-ready LOW -> must gate, clock must stop.
    await h.settle_to_gated()
    assert _get(dut, 'cg_gating') == 1, (
        f'{name} [phase 1]: cg_gating never asserted after '
        f'{os.environ["CG_IDLE_COUNT"]} idle cycles on a completely quiet bus')
    assert not await _gated_clock_running(dut), (
        f'{name} [phase 1]: cg_gating=1 but the gated clock is STILL TOGGLING - '
        f'the wrapper reports gating it does not perform')
    assert _get(dut, h.up_req_ready) == 0, (
        f'{name} [phase 1]: {h.up_req_ready} is high while gated - a transfer '
        f'could be accepted with the clock stopped')

    # ---------------------------------------------------------------- P2 ---
    # Same, but the consumer parks its response-ready HIGH.  This is legal and
    # common and must not defeat gating.
    h.up_rsp.set_ready_policy('always')
    await h.settle_to_gated()
    assert _get(dut, 'cg_gating') == 1, (
        f'{name} [phase 2]: consumer holding response-ready high on an idle bus '
        f'defeats clock gating - activity is being derived from a peer READY '
        f'rather than from VALIDs and outstanding work')
    assert not await _gated_clock_running(dut), (
        f'{name} [phase 2]: gated clock still toggling with response-ready '
        f'parked high on an idle bus')

    # ------------------------------------------------------------- P3/P4 ---
    # Phase 3 (wake) and phase 4 (transfer integrity) are one loop: every
    # transaction starts from a fully gated block, so each straddles an ungate
    # boundary, and each completes before the next so the block returns to a
    # genuinely idle state.
    # From here the consumer's response-ready follows the profile again.
    h.up_rsp.set_ready_policy('valid_first')
    n_req = 3
    for i in range(n_req):
        assert _get(dut, 'cg_gating') == 1, (
            f'{name} [phase 4, req {i}]: block did not re-gate between requests')
        assert _get(dut, h.up_req_ready) == 0, (
            f'{name} [phase 4, req {i}]: {h.up_req_ready} high while gated')
        counter = h.start_handshake_counter(cycles=600)
        txn = cocotb.start_soon(h.one_transaction())
        if i == 0:
            # Phase 3: the BFM's request valid alone must restart the clock.
            for _ in range(60):
                await FallingEdge(dut.aclk)
                if _get(dut, h.up_req_valid):
                    break
            assert _get(dut, h.up_req_valid) == 1, (
                f'{name} [phase 3]: the master BFM never raised {h.up_req_valid}')
            await RisingEdge(dut.aclk)
            await RisingEdge(dut.aclk)
            assert _get(dut, 'cg_gating') == 0, (
                f'{name} [phase 3]: cg_gating still asserted two cycles after a '
                f'request valid went high - the block never wakes')
            assert await _gated_clock_running(dut), (
                f'{name} [phase 3]: gated clock did not restart on activity')
        await with_timeout(txn, 600 * CLK_PERIOD_NS, 'ns')
        await counter.task
        assert counter.up == 1, (
            f'{name} [phase 4, req {i}]: {counter.up} upstream request handshakes '
            f'across the gate/ungate boundary, expected exactly 1')
        assert counter.down == 1, (
            f'{name} [phase 4, req {i}]: {counter.down} downstream request '
            f'handshakes, expected exactly 1 (request dropped or duplicated)')
        # The completion packet must be delivered before any housekeeping.
        await h.await_delivery(i + 1)
        # Clear any residual monitor state so `busy` cannot pin us awake.
        await h.cam_clear_pulse()
        await h.settle_to_gated(cycles=60)

    # ---------------------------------------------------------------- P5 ---
    # A beat held INSIDE the block.  The downstream request BFM stalls, so an
    # accepted request sits in the wrapper's datapath.  While it is in there
    # the block must stay awake: if the activity term went quiet here the clock
    # would stop with the beat trapped, and nothing would ever restart it.
    for c in h.down_req:
        c.set_ready_policy('stall')
    await h.settle_to_gated(cycles=20)
    assert _get(dut, 'cg_gating') == 1, (
        f'{name} [phase 5]: block did not gate before the back-pressure case')
    counter = h.start_handshake_counter(cycles=800)
    txn = cocotb.start_soon(h.one_transaction())
    for _ in range(60):
        await FallingEdge(dut.aclk)
        if _get(dut, h.up_req_valid) and _get(dut, h.up_req_ready):
            break
    await RisingEdge(dut.aclk)    # documented 1-clock wakeup latency
    await RisingEdge(dut.aclk)
    for _ in range(30):
        await RisingEdge(dut.aclk)
        assert _get(dut, 'cg_gating') == 0, (
            f'{name} [phase 5]: clock gated while a request was still inside the '
            f'block waiting on downstream back-pressure - the beat is stranded '
            f'in a stopped clock domain with nothing left to wake it')
    for c in h.down_req:
        c.set_ready_policy('valid_first')
    await with_timeout(txn, 800 * CLK_PERIOD_NS, 'ns')
    await counter.task
    assert counter.up == 1 and counter.down == 1, (
        f'{name} [phase 5]: {counter.up} upstream / {counter.down} downstream '
        f'handshakes after releasing back-pressure, expected 1 and 1')
    await h.await_delivery(n_req + 1)
    await h.cam_clear_pulse()
    await h.settle_to_gated(cycles=60)

    # ---------------------------------------------------------------- P6 ---
    # Monitor-bus liveness (TASK-070).  The MonbusSlave stalls, one transaction
    # completes, and its completion packet parks on ``monbus_valid``.  The
    # pending packet is outstanding work and must hold the block awake.  A
    # wrapper whose activity term ignores it gates with the packet parked: the
    # reporter's clock stops with valid frozen high, and a consumer that later
    # raises ready sees valid&&ready on every ungated cycle - the SAME packet
    # accepted over and over until unrelated traffic happens to wake the block.
    h.mon.set_ready_policy('stall')
    h.mon.clear_received_packets()
    await with_timeout(h.one_transaction(), 600 * CLK_PERIOD_NS, 'ns')
    # No cam_clear here: the completion frees the CAM entry itself, and a
    # clear inside the reporter's emission window is exactly the race that
    # strands the packet (see await_delivery). The parked packet is what
    # holds the block awake now.
    # The completion packet must now be parked on the output register.  If it
    # never appears the packet was stranded mid-reporter by the clock stopping
    # before valid could assert - the freeze variant of the same defect.
    for _ in range(100):
        if _get(dut, 'monbus_valid'):
            break
        await RisingEdge(dut.aclk)
    assert _get(dut, 'monbus_valid') == 1, (
        f'{name} [phase 6]: no completion packet parked on monbus_valid with '
        f'the MonbusSlave stalled - the packet was emitted into a stopping '
        f'clock domain and stranded (or never emitted at all)')
    # Idle the bus with the packet still parked; the block must not gate.
    gated_while_parked = 0
    for _ in range(60):
        await RisingEdge(dut.aclk)
        if _get(dut, 'cg_gating') and _get(dut, 'monbus_valid'):
            gated_while_parked += 1
    # Release the consumer: the MonbusSlave records every packet it accepts on
    # the ungated clock.  The defect signature is the same packet accepted on
    # consecutive cycles off a frozen valid, which shows up here as more than
    # one received packet.
    h.mon.set_ready_policy('always')
    for _ in range(30):
        await RisingEdge(dut.aclk)
    delivered = h.mon.get_received_packets_sync()
    for pkt in delivered:
        dut._log.info(f'P6 delivery: {pkt}')
    assert len(delivered) == 1, (
        f'{name} [phase 6]: {len(delivered)} monbus deliveries for the one '
        f'packet this phase generated (0 = packet lost; 2+ = a packet was '
        f're-delivered off a frozen valid, or an EARLIER phase\'s packet was '
        f'stranded mid-reporter by the clock stopping and only surfaced now)')
    assert gated_while_parked == 0, (
        f'{name} [phase 6]: clock gated for {gated_while_parked} cycles with '
        f'a packet parked on monbus_valid - pending monitor packets are '
        f'outstanding work and must hold the block awake')

    # Let the delivered packet's idle window expire so the block ends gated.
    await h.settle_to_gated(cycles=60)

    dut._log.info(f'{name}: clock gating verified (stops when idle, survives a '
                  f'parked response-ready, wakes on activity, loses no '
                  f'transfers, exactly-once monbus delivery)')


# ---------------------------------------------------------------------------
# pytest side
# ---------------------------------------------------------------------------

@pytest.mark.parametrize('profile', BFM_PROFILES)
@pytest.mark.parametrize('idle_count', IDLE_COUNTS)
@pytest.mark.parametrize('dut_key', sorted(DUTS.keys()))
def test_mon_cg_gating(dut_key, idle_count, profile):
    """Clock gating actually gates a clock, for every *_mon_cg wrapper."""
    cfg = DUTS[dut_key]
    worker_id = os.environ.get('PYTEST_XDIST_WORKER', 'gw0')

    module, repo_root, tests_dir, log_dir, rtl_dict = get_paths({
        'rtl_common': 'rtl/common',
        'rtl_includes': 'rtl/amba/includes',
        'rtl_monitor': 'rtl/amba/monitor',
        'rtl_shared': 'rtl/amba/shared',
    })

    test_name = f'test_{worker_id}_mon_cg_gating_{dut_key}_ic{idle_count}_{profile}'
    log_path = os.path.join(log_dir, f'{test_name}.log')
    sim_build = sim_build_path(tests_dir, test_name)
    os.makedirs(sim_build, exist_ok=True)
    os.makedirs(log_dir, exist_ok=True)

    verilog_sources, includes = get_sources_from_filelist(
        repo_root=repo_root, filelist_path=cfg['filelist'])

    run(
        python_search=[tests_dir],
        verilog_sources=verilog_sources,
        includes=includes + [rtl_dict['rtl_common'], sim_build],
        toplevel=dut_key,
        module='test_mon_cg_gating',
        parameters=dict(cfg['params']),
        sim_build=sim_build,
        extra_env={
            'DUT': dut_key,
            'CG_IDLE_COUNT': str(idle_count),
            'BFM_PROFILE': profile,
            'LOG_PATH': log_path,
            'COCOTB_LOG_LEVEL': 'INFO',
        },
        waves=bool(int(os.environ.get('WAVES', '0'))),
        keep_files=True,
        compile_args=[
            '-Wall', '-Wno-SYNCASYNCNET', '-Wno-UNUSED', '-Wno-DECLFILENAME',
            '-Wno-PINMISSING', '-Wno-UNDRIVEN', '-Wno-WIDTHEXPAND',
            '-Wno-WIDTHTRUNC', '-Wno-SELRANGE', '-Wno-CASEINCOMPLETE',
            '-Wno-TIMESCALEMOD',
        ],
        simulator='verilator',
    )
