# SPDX-License-Identifier: MIT
# SPDX-FileCopyrightText: 2024-2025 sean galloway
#
# RTL Design Sherpa - Industry-Standard RTL Design and Verification
# https://github.com/sean-galloway/RTLDesignSherpa
#
# Module: test_mon_cg_gating
# Purpose: Structural clock-gating test for all 12 *_mon_cg monitor wrappers
#
# Documentation: PRD.md
# Subsystem: tests
#
# Author: sean galloway
# Created: 2026-07-20

"""
Clock gating behaviour test for the 12 ``*_mon_cg`` monitor wrappers.

This test exists because the pre-existing ``test_*_mon_cg.py`` suites all passed
while none of the twelve wrappers actually gated a clock (GitHub issue #41,
"Clock gating" section).  Those suites exercise monitor *function*; they never
looked at the clock.  This one looks at nothing else.

What is asserted, per DUT:

  Phase 1 - idle, consumer response-ready LOW
      ``cg_gating`` rises and the internal gated clock STOPS TOGGLING.
      A wrapper that only reports gating (AXI4 today) or that disables the
      monitor instead of gating it (AXIL4 today) fails here.

  Phase 2 - idle, consumer response-ready HIGH
      A consumer that parks R/B-ready high while idle is behaving correctly and
      must NOT defeat gating.  This is the exact condition that pins the AXI5
      wrappers permanently awake today, because they fold ``*_rready`` /
      ``*_bready`` (a peer's READY) into the activity term.  Activity must be
      derived from VALID signals and outstanding work only.

  Phase 3 - wake
      Asserting a request valid restores the gated clock and drops ``cg_gating``.

  Phase 4 - transfer integrity across gate/ungate
      The request-side ready is masked to 0 while gated, so no transfer may be
      accepted with the clock stopped.  Driving requests that each straddle a
      gate/ungate boundary must produce exactly one upstream handshake and
      exactly one downstream handshake per request - no drops, no duplicates.

  Phase 5 - beat held inside the block under downstream back-pressure
      While an accepted beat waits on downstream ready the block must stay
      awake; gating here would strand the beat in a stopped clock domain.

  Phase 6 - monitor-bus liveness (TASK-070)
      A completion packet parked on ``monbus_valid`` behind a low
      ``monbus_ready`` is outstanding work: the block must not gate under it,
      and when the consumer raises ready each pending packet must be
      delivered exactly once.  The un-fixed wrappers gated with valid frozen
      high and re-delivered the same packet on every ungated cycle (measured:
      30 accepts of one packet in 30 cycles).

The gated clock is observed directly at ``dut.gated_aclk``; cocotb-test compiles
Verilator with ``--public-flat-rw``, so wrapper-internal nets are visible.
"""

import os
import pytest
import cocotb
from cocotb.triggers import RisingEdge, FallingEdge, Timer, Edge, with_timeout
from cocotb_test.simulator import run

from TBClasses.monbus import parse
from TBClasses.shared.utilities import get_paths
from TBClasses.shared.filelist_utils import get_sources_from_filelist


CLK_PERIOD_NS = 10
CG_IDLE_COUNT_WIDTH = 4

# cfg_cg_idle_count values to sweep.  0 is the aggressive case: the block gates
# the cycle after activity drops, which is what exposes a beat stranded inside
# the stopped clock domain.  Correctness must not depend on the idle count being
# long enough to cover the wrapper's internal pipeline latency, so both an
# aggressive and a relaxed setting are covered.
IDLE_COUNTS = (0, 4)


# ---------------------------------------------------------------------------
# DUT table
# ---------------------------------------------------------------------------
# Port naming is fully symmetric across all twelve wrappers:
#   masters: upstream = fub_ax*   downstream = m_ax*
#   slaves:  upstream = s_ax*     downstream = fub_ax*
# and in both cases the upstream request valid, the upstream response ready,
# the downstream request ready and the downstream response valid are INPUTS.

AXI4_PARAMS = {
    'AXI_ID_WIDTH': '8', 'AXI_ADDR_WIDTH': '32', 'AXI_DATA_WIDTH': '32',
    'AXI_USER_WIDTH': '1', 'MAX_TRANSACTIONS': '8',
    'CG_IDLE_COUNT_WIDTH': str(CG_IDLE_COUNT_WIDTH),
}
AXI5_PARAMS = dict(AXI4_PARAMS)
AXIL4_PARAMS = {
    'AXIL_ADDR_WIDTH': '32', 'AXIL_DATA_WIDTH': '32', 'MAX_TRANSACTIONS': '8',
    'CG_IDLE_COUNT_WIDTH': str(CG_IDLE_COUNT_WIDTH),
}


def _dut_table():
    table = {}
    for family, bus, params in (('axi4', 'axi', AXI4_PARAMS),
                                ('axil4', 'axil', AXIL4_PARAMS),
                                ('axi5', 'axi', AXI5_PARAMS)):
        for role in ('master', 'slave'):
            for direction in ('rd', 'wr'):
                name = f'{family}_{role}_{direction}_mon_cg'
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


def _set(dut, name, value):
    """Drive a port if the DUT has it (AXIL has no id/len/last)."""
    handle = getattr(dut, name, None)
    if handle is not None:
        handle.value = value
        return True
    return False


def _get(dut, name):
    handle = getattr(dut, name, None)
    return int(handle.value) if handle is not None else 0


async def _gated_clock_running(dut, window_cycles=8):
    """True if dut.gated_aclk toggles within window_cycles of aclk."""
    try:
        await with_timeout(Edge(dut.gated_aclk),
                           window_cycles * CLK_PERIOD_NS, 'ns')
        return True
    except Exception:      # cocotb.result.SimTimeoutError
        return False


class MonCgGatingTB:
    """Minimal, protocol-shape-agnostic driver for the *_mon_cg wrappers."""

    def __init__(self, dut):
        self.dut = dut
        self.cfg = _cfg()
        self.up = self.cfg['up']
        self.down = self.cfg['down']
        self.is_rd = self.cfg['direction'] == 'rd'
        self.log = dut._log

        if self.is_rd:
            self.req_valid = f'{self.up}_arvalid'      # input
            self.req_ready = f'{self.up}_arready'      # output (masked)
            self.rsp_ready = f'{self.up}_rready'       # input  (peer READY)
            self.d_req_valid = f'{self.down}_arvalid'  # output
            self.d_req_ready = f'{self.down}_arready'  # input
            self.d_rsp_valid = f'{self.down}_rvalid'   # input
            self.d_rsp_ready = f'{self.down}_rready'   # output
        else:
            self.req_valid = f'{self.up}_awvalid'
            self.req_ready = f'{self.up}_awready'
            self.rsp_ready = f'{self.up}_bready'
            self.d_req_valid = f'{self.down}_awvalid'
            self.d_req_ready = f'{self.down}_awready'
            self.d_rsp_valid = f'{self.down}_bvalid'
            self.d_rsp_ready = f'{self.down}_bready'

    # -- setup -------------------------------------------------------------
    async def start_clock(self):
        async def _clk():
            while True:
                self.dut.aclk.value = 0
                await Timer(CLK_PERIOD_NS // 2, units='ns')
                self.dut.aclk.value = 1
                await Timer(CLK_PERIOD_NS // 2, units='ns')
        cocotb.start_soon(_clk())

    def quiesce(self):
        """All request valids low, all downstream readys high, no responses."""
        d = self.dut
        _set(d, 'cam_clear', 0)
        _set(d, 'monbus_ready', 1)
        _set(d, 'cfg_monitor_enable', 1)
        _set(d, 'cfg_error_enable', 1)
        _set(d, 'cfg_compl_enable', 1)
        _set(d, 'cfg_timeout_enable', 0)
        _set(d, 'cfg_perf_enable', 0)
        _set(d, 'cfg_debug_enable', 0)
        _set(d, 'cfg_threshold_enable', 0)
        _set(d, 'cfg_timeout_cycles', 0xFFFF)
        _set(d, 'cfg_addr_check_enable', 0)
        _set(d, 'cfg_cg_enable', 1)
        _set(d, 'cfg_cg_idle_count', int(os.environ['CG_IDLE_COUNT']))

        _set(d, self.req_valid, 0)
        _set(d, self.rsp_ready, 0)
        _set(d, self.d_req_ready, 1)
        _set(d, self.d_rsp_valid, 0)
        if not self.is_rd:
            _set(d, f'{self.up}_wvalid', 0)
            _set(d, f'{self.down}_wready', 1)

    async def reset(self):
        self.dut.aresetn.value = 0
        self.quiesce()
        for _ in range(5):
            await RisingEdge(self.dut.aclk)
        self.dut.aresetn.value = 1
        for _ in range(5):
            await RisingEdge(self.dut.aclk)

    async def settle_to_gated(self, cycles=40):
        for _ in range(cycles):
            await RisingEdge(self.dut.aclk)

    # -- stimulus ----------------------------------------------------------
    def drive_request(self, addr, tag):
        d, up = self.dut, self.up
        if self.is_rd:
            _set(d, f'{up}_araddr', addr)
            _set(d, f'{up}_arid', tag)
            _set(d, f'{up}_arlen', 0)
            _set(d, f'{up}_arsize', 2)
            _set(d, f'{up}_arburst', 1)
            _set(d, f'{up}_arprot', 0)
            _set(d, f'{up}_arvalid', 1)
        else:
            _set(d, f'{up}_awaddr', addr)
            _set(d, f'{up}_awid', tag)
            _set(d, f'{up}_awlen', 0)
            _set(d, f'{up}_awsize', 2)
            _set(d, f'{up}_awburst', 1)
            _set(d, f'{up}_awprot', 0)
            _set(d, f'{up}_awvalid', 1)
            _set(d, f'{up}_wdata', 0xA5A5A5A5)
            _set(d, f'{up}_wstrb', 0xF)
            _set(d, f'{up}_wlast', 1)
            _set(d, f'{up}_wvalid', 1)

    def clear_request(self):
        self.clear_req()
        self.clear_data()

    def clear_req(self):
        _set(self.dut, self.req_valid, 0)

    def clear_data(self):
        if not self.is_rd:
            _set(self.dut, f'{self.up}_wvalid', 0)

    def drive_response(self, tag, enable):
        d, down = self.dut, self.down
        if self.is_rd:
            _set(d, f'{down}_rid', tag)
            _set(d, f'{down}_rdata', 0xDEADBEEF)
            _set(d, f'{down}_rresp', 0)
            _set(d, f'{down}_rlast', 1)
            _set(d, f'{down}_rvalid', 1 if enable else 0)
        else:
            _set(d, f'{down}_bid', tag)
            _set(d, f'{down}_bresp', 0)
            _set(d, f'{down}_bvalid', 1 if enable else 0)

    # -- observation -------------------------------------------------------
    def up_handshake(self):
        return _get(self.dut, self.req_valid) and _get(self.dut, self.req_ready)

    def down_handshake(self):
        return _get(self.dut, self.d_req_valid) and _get(self.dut, self.d_req_ready)

    def data_handshake(self):
        if self.is_rd:
            return False
        return (_get(self.dut, f'{self.up}_wvalid')
                and _get(self.dut, f'{self.up}_wready'))

    def start_handshake_counter(self, cycles=200):
        """Count request handshakes on both sides, every cycle, in background.

        Runs concurrently with the stimulus so no handshake can slip past while
        the test is busy checking something else.

        Sampling is on the falling edge, which shows the valid/ready state that
        the *next* rising edge will consummate.  A channel's valid is therefore
        dropped one falling edge later - dropping it immediately would pull it
        low before the rising edge that completes the transfer, so the handshake
        the test counted would never actually happen in the RTL.  Dropping it
        after exactly one rising edge is what makes a re-accept across a
        gate/ungate boundary show up as a duplicate.
        """
        tb = self

        class _Counter:
            up = 0
            down = 0

            async def _run(self):
                pend_req = False
                pend_data = False
                for _ in range(cycles):
                    await FallingEdge(tb.dut.aclk)
                    # `elif`, not `if`: a signal written this delta still reads
                    # back with its old value, so re-testing the channel on the
                    # cycle we drop its valid would double-count the handshake
                    # we already counted.
                    if pend_req:
                        tb.clear_req()
                        pend_req = False
                    elif tb.up_handshake():
                        self.up += 1
                        pend_req = True
                    if pend_data:
                        tb.clear_data()
                        pend_data = False
                    elif tb.data_handshake():
                        pend_data = True
                    if tb.down_handshake():
                        self.down += 1
                    if self.up and self.down:
                        # Keep watching a little longer to catch duplicates.
                        for _ in range(10):
                            await FallingEdge(tb.dut.aclk)
                            if pend_req:
                                tb.clear_req()
                                pend_req = False
                            elif tb.up_handshake():
                                self.up += 1
                                pend_req = True
                            if pend_data:
                                tb.clear_data()
                                pend_data = False
                            if tb.down_handshake():
                                self.down += 1
                        return

            async def join(self):
                await self._task

        c = _Counter()
        c._task = cocotb.start_soon(c._run())
        return c


@cocotb.test(timeout_time=60, timeout_unit='sec')
async def mon_cg_gating_test(dut):
    tb = MonCgGatingTB(dut)
    name = tb.cfg['name']
    dut._log.info(f'=== clock-gating test: {name} ===')

    # The converged interface must exist.  A wrapper that never gated has no
    # gated clock to look at, and that is itself the defect.
    assert hasattr(dut, 'gated_aclk'), (
        f'{name}: no internal `gated_aclk` net - the wrapper does not generate '
        f'a gated clock at all')
    for port in ('cfg_cg_enable', 'cfg_cg_idle_count', 'cg_gating', 'cg_idle'):
        assert hasattr(dut, port), f'{name}: missing converged CG port `{port}`'

    await tb.start_clock()
    await tb.reset()

    # ---------------------------------------------------------------- P1 ---
    # Idle bus, consumer response-ready LOW -> must gate, clock must stop.
    await tb.settle_to_gated()
    assert _get(dut, 'cg_gating') == 1, (
        f'{name} [phase 1]: cg_gating never asserted after '
        f'{os.environ["CG_IDLE_COUNT"]} idle cycles on a completely quiet bus')
    running = await _gated_clock_running(dut)
    assert not running, (
        f'{name} [phase 1]: cg_gating=1 but the gated clock is STILL TOGGLING - '
        f'the wrapper reports gating it does not perform')
    assert _get(dut, tb.req_ready) == 0, (
        f'{name} [phase 1]: {tb.req_ready} is high while gated - a transfer '
        f'could be accepted with the clock stopped')

    # ---------------------------------------------------------------- P2 ---
    # Same, but the consumer parks its response-ready HIGH.  This is legal and
    # common and must not defeat gating.
    _set(dut, tb.rsp_ready, 1)
    await tb.settle_to_gated()
    assert _get(dut, 'cg_gating') == 1, (
        f'{name} [phase 2]: consumer holding {tb.rsp_ready} high on an idle bus '
        f'defeats clock gating - activity is being derived from a peer READY '
        f'rather than from VALIDs and outstanding work')
    running = await _gated_clock_running(dut)
    assert not running, (
        f'{name} [phase 2]: gated clock still toggling with {tb.rsp_ready} '
        f'parked high on an idle bus')
    _set(dut, tb.rsp_ready, 0)
    await tb.settle_to_gated(cycles=10)

    # ------------------------------------------------------------- P3/P4 ---
    # Phase 3 (wake) and phase 4 (transfer integrity) are one loop: every
    # request starts from a fully gated block, so each straddles an ungate
    # boundary, and each is retired before the next so the block returns to a
    # genuinely idle state rather than accumulating outstanding transactions.
    n_req = 3
    up_hs = 0
    down_hs = 0
    for i in range(n_req):
        # Confirm we really are gated and really are masking ready.
        assert _get(dut, 'cg_gating') == 1, (
            f'{name} [phase 4, req {i}]: block did not re-gate between requests')
        assert _get(dut, tb.req_ready) == 0, (
            f'{name} [phase 4, req {i}]: {tb.req_ready} high while gated')

        tag = i + 1

        # Count upstream and downstream request handshakes concurrently with
        # the stimulus, sampling every cycle on the ungated clock so a dropped
        # or duplicated accept cannot hide between checks.
        counter = tb.start_handshake_counter(cycles=200)
        tb.drive_request(0x2000 + 0x40 * i, tag)

        # Phase 3: the request valid alone must restart the clock.
        if i == 0:
            await RisingEdge(dut.aclk)
            await RisingEdge(dut.aclk)
            assert _get(dut, 'cg_gating') == 0, (
                f'{name} [phase 3]: cg_gating still asserted two cycles after a '
                f'request valid went high - the block never wakes')
            assert await _gated_clock_running(dut), (
                f'{name} [phase 3]: gated clock did not restart on activity')

        await counter.join()
        seen_up, seen_down = counter.up, counter.down
        tb.clear_request()

        assert seen_up == 1, (
            f'{name} [phase 4, req {i}]: {seen_up} upstream handshakes across '
            f'the gate/ungate boundary, expected exactly 1')
        assert seen_down == 1, (
            f'{name} [phase 4, req {i}]: {seen_down} downstream handshakes, '
            f'expected exactly 1 (request dropped or duplicated)')
        up_hs += seen_up
        down_hs += seen_down

        # Retire the transaction so the block can go idle and re-gate.
        # Exactly ONE response beat: holding the response valid high would keep
        # injecting beats for as long as it is asserted, which would leave the
        # datapath permanently non-empty and the block permanently awake.
        _set(dut, tb.rsp_ready, 1)
        tb.drive_response(tag, True)
        for _ in range(200):
            await FallingEdge(dut.aclk)
            if _get(dut, tb.d_rsp_valid) and _get(dut, tb.d_rsp_ready):
                break
        await FallingEdge(dut.aclk)   # let the rising edge consummate it
        tb.drive_response(tag, False)
        for _ in range(40):           # drain it out of the upstream port
            await RisingEdge(dut.aclk)
        _set(dut, tb.rsp_ready, 0)

        # Clear any residual monitor state so `busy` cannot pin us awake.
        _set(dut, 'cam_clear', 1)
        await RisingEdge(dut.aclk)
        _set(dut, 'cam_clear', 0)
        await tb.settle_to_gated(cycles=60)

    # ---------------------------------------------------------------- P5 ---
    # A beat held INSIDE the block.  Back-pressure the downstream request port
    # so an accepted beat sits in the wrapper's datapath.  While it is in there
    # the block must stay awake: if the activity term went quiet here the clock
    # would stop with the beat trapped, and nothing would ever restart it to
    # drain the beat.  This is the condition an activity term built only from
    # port valids has to cover, so it is asserted rather than assumed.
    _set(dut, tb.d_req_ready, 0)
    await tb.settle_to_gated(cycles=20)
    assert _get(dut, 'cg_gating') == 1, (
        f'{name} [phase 5]: block did not gate before the back-pressure case')

    tb.drive_request(0x8000, 4)
    held = tb.start_handshake_counter(cycles=400)
    await RisingEdge(dut.aclk)    # documented 1-clock wakeup latency
    await RisingEdge(dut.aclk)
    for _ in range(30):
        await RisingEdge(dut.aclk)
        assert _get(dut, 'cg_gating') == 0, (
            f'{name} [phase 5]: clock gated while a beat was still inside the '
            f'block waiting on downstream back-pressure - the beat is stranded '
            f'in a stopped clock domain with nothing left to wake it')

    _set(dut, tb.d_req_ready, 1)
    await held.join()
    tb.clear_request()
    assert held.up == 1 and held.down == 1, (
        f'{name} [phase 5]: {held.up} upstream / {held.down} downstream '
        f'handshakes after releasing back-pressure, expected 1 and 1')

    assert up_hs == n_req and down_hs == n_req, (
        f'{name} [phase 4]: {up_hs} upstream / {down_hs} downstream handshakes '
        f'for {n_req} requests')

    # ---------------------------------------------------------------- P6 ---
    # Monitor-bus liveness (TASK-070).  Park a completion packet on
    # ``monbus_valid`` by holding ``monbus_ready`` low, then let the AXI side
    # go idle.  The pending packet is outstanding work and must hold the block
    # awake.  A wrapper whose activity term ignores it gates with the packet
    # parked: the reporter's clock stops with valid frozen high, and a
    # consumer that later raises ready sees valid&&ready on every ungated
    # cycle - the SAME packet accepted over and over until unrelated traffic
    # happens to wake the block.

    # Retire the phase-5 transaction so the block can genuinely idle.
    _set(dut, tb.rsp_ready, 1)
    tb.drive_response(4, True)
    for _ in range(200):
        await FallingEdge(dut.aclk)
        if _get(dut, tb.d_rsp_valid) and _get(dut, tb.d_rsp_ready):
            break
    await FallingEdge(dut.aclk)
    tb.drive_response(4, False)
    for _ in range(40):
        await RisingEdge(dut.aclk)
    _set(dut, tb.rsp_ready, 0)
    _set(dut, 'cam_clear', 1)
    await RisingEdge(dut.aclk)
    _set(dut, 'cam_clear', 0)
    await tb.settle_to_gated(cycles=60)

    # Back-pressure the monitor bus, then run one transaction to completion so
    # the reporter emits exactly one completion packet it cannot deliver.
    _set(dut, 'monbus_ready', 0)
    counter = tb.start_handshake_counter(cycles=300)
    tb.drive_request(0xA000, 5)
    await counter.join()
    tb.clear_request()
    _set(dut, tb.rsp_ready, 1)
    tb.drive_response(5, True)
    for _ in range(200):
        await FallingEdge(dut.aclk)
        if _get(dut, tb.d_rsp_valid) and _get(dut, tb.d_rsp_ready):
            break
    await FallingEdge(dut.aclk)
    tb.drive_response(5, False)
    for _ in range(40):
        await RisingEdge(dut.aclk)
    _set(dut, tb.rsp_ready, 0)
    _set(dut, 'cam_clear', 1)
    await RisingEdge(dut.aclk)
    _set(dut, 'cam_clear', 0)

    # The completion packet must now be parked on the output register.  If it
    # never appears the packet was stranded mid-reporter by the clock stopping
    # before valid could assert - the freeze variant of the same defect.
    for _ in range(100):
        if _get(dut, 'monbus_valid'):
            break
        await RisingEdge(dut.aclk)
    assert _get(dut, 'monbus_valid') == 1, (
        f'{name} [phase 6]: no completion packet parked on monbus_valid with '
        f'monbus_ready held low - the packet was emitted into a stopping clock '
        f'domain and stranded (or never emitted at all)')

    # Idle the bus with the packet still parked; the block must not gate.
    gated_while_parked = 0
    for _ in range(60):
        await RisingEdge(dut.aclk)
        if _get(dut, 'cg_gating') and _get(dut, 'monbus_valid'):
            gated_while_parked += 1

    # Release the consumer and record every delivery on the ungated clock.
    # Sampling starts ON the falling edge where ready rises: valid&&ready seen
    # at a falling edge is consummated by the following rising edge, so
    # waiting a cycle before the first sample would miss the first delivery.
    # Packet VALUES are recorded, not just a count: the defect signature is
    # the same packet accepted on consecutive cycles off a frozen valid, and
    # a plain count cannot tell one packet re-delivered N times from N
    # distinct packets draining out of the reporter FIFO.
    await FallingEdge(dut.aclk)
    _set(dut, 'monbus_ready', 1)
    delivered = []
    for _ in range(30):
        if _get(dut, 'monbus_valid'):
            delivered.append(int(dut.monbus_packet.value))
        await FallingEdge(dut.aclk)

    for pkt in delivered:
        dut._log.info(f'P6 delivery: {parse(pkt).get_packet_type_name()} '
                      f'raw=0x{pkt:032x}')

    duplicates = sum(1 for a, b in zip(delivered, delivered[1:]) if a == b)
    assert duplicates == 0, (
        f'{name} [phase 6]: the same monbus packet was accepted on '
        f'{duplicates + 1} consecutive cycles - a frozen monbus_valid is '
        f're-delivering one packet to the ungated consumer')
    assert len(delivered) == 1, (
        f'{name} [phase 6]: {len(delivered)} monbus deliveries for the one '
        f'packet this phase generated (0 = packet lost; 2+ = an EARLIER '
        f'phase\'s packet was stranded mid-reporter by the clock stopping '
        f'inside the emission window and only surfaced now - the monitor\'s '
        f'CAM occupancy must hold the block awake until the packet reaches '
        f'monbus_valid)')
    assert gated_while_parked == 0, (
        f'{name} [phase 6]: clock gated for {gated_while_parked} cycles with '
        f'a packet parked on monbus_valid - pending monitor packets are '
        f'outstanding work and must hold the block awake')

    # Let the delivered packet's idle window expire so the block ends gated.
    await tb.settle_to_gated(cycles=60)

    dut._log.info(f'{name}: clock gating verified (stops when idle, survives a '
                  f'parked response-ready, wakes on activity, loses no '
                  f'transfers, exactly-once monbus delivery)')


# ---------------------------------------------------------------------------
# pytest side
# ---------------------------------------------------------------------------

@pytest.mark.parametrize('idle_count', IDLE_COUNTS)
@pytest.mark.parametrize('dut_key', sorted(DUTS.keys()))
def test_mon_cg_gating(dut_key, idle_count):
    """Clock gating actually gates a clock, for every *_mon_cg wrapper."""
    cfg = DUTS[dut_key]
    worker_id = os.environ.get('PYTEST_XDIST_WORKER', 'gw0')

    module, repo_root, tests_dir, log_dir, rtl_dict = get_paths({
        'rtl_common': 'rtl/common',
        'rtl_includes': 'rtl/amba/includes',
        'rtl_monitor': 'rtl/amba/monitor',
        'rtl_shared': 'rtl/amba/shared',
    })

    test_name = f'test_{worker_id}_mon_cg_gating_{dut_key}_ic{idle_count}'
    log_path = os.path.join(log_dir, f'{test_name}.log')
    sim_build = os.path.join(tests_dir, 'local_sim_build', test_name)
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
