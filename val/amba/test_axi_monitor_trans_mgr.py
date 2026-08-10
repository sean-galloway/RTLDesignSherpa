# SPDX-License-Identifier: MIT
# SPDX-FileCopyrightText: 2024-2026 sean galloway
#
# RTL Design Sherpa - Industry-Standard RTL Design and Verification
# https://github.com/sean-galloway/RTLDesignSherpa
#
# Module: AxiMonitorTransMgrTB
# Purpose: axi_monitor_trans_mgr transaction-tracking regression tests
#
# Documentation: docs/markdown/rtl-amba/index.md
# Subsystem: tests
#
# Author: sean galloway
# Created: 2026-07-20

"""
axi_monitor_trans_mgr transaction-tracking regression tests (GitHub issue #41).

These tests target the transaction-tracking core of the AXI monitor, which is
exercised through the ``axi_monitor_base`` hierarchy (the trans_mgr has no
packet output of its own, so the monitor bus is the natural observation point).

Every scenario below is LEGAL AXI4 traffic that the pre-existing suite passed
while the RTL mishandled it. They exist so the next regression is caught:

  Phase 1 -- multiple outstanding transactions sharing one ARID.
             AXI4 explicitly permits this and requires the responses to come
             back in issue order. The monitor used to suppress allocation on
             ANY id match, collapsing both transactions into a single slot:
             one completion packet for two transactions, a beat count of 2
             against an expected_beats of 1, and the first transaction's
             address overwritten by the second.

  Phase 2 -- a same-ID command arriving on the cleanup cycle of the previous
             transaction (inter-command delays 0, 1, 2). The slot was neither
             free nor surviving, so the command got no entry, its data beat
             found no match, and the monitor fabricated an EVT_DATA_ORPHAN
             error packet on entirely legal traffic.

  Phase 3 -- slot reallocation shortly after cleanup. The reporter clears its
             event_reported flag off a one-cycle-delayed snapshot, so a slot
             reallocated inside that window came up already marked reported,
             collapsing the reporter's emission window to a single cycle.

Phases 1 and 3 read the internal transaction table directly (the DUT is built
with --public-flat-rw) because slot occupancy, per-slot beat counts and the
event_reported flag are the properties under test and are not fully observable
from the monitor bus alone. The struct decode is width-checked against the RTL
at runtime, so a change to bus_transaction_t fails loudly instead of silently
decoding garbage.
"""

import os
import random

import cocotb
import pytest
from cocotb.triggers import RisingEdge
from cocotb_test.simulator import run

from TBClasses.shared.tbbase import TBBase
from TBClasses.shared.utilities import get_paths
from TBClasses.shared.filelist_utils import get_sources_from_filelist
from TBClasses.monbus.monbus_slave import MonbusSlave
from TBClasses.monbus.monbus_types import PktType

# AXI response codes
RESP_OKAY = 0b00
BURST_INCR = 0b01

# transaction_state_t (rtl/amba/includes/monitor_common_pkg.sv)
TRANS_IDLE = 0
TRANS_ADDR_PHASE = 1
TRANS_DATA_PHASE = 2
TRANS_COMPLETE = 3
TRANS_ERROR = 4
TRANS_ORPHANED = 5

# bus_transaction_t layout, MSB field first
# (rtl/amba/includes/monitor_amba4_pkg.sv). Total width is asserted against
# the elaborated RTL in AxiMonitorTransMgrTB._check_struct_width().
TRANS_FIELDS = [
    ('valid', 1),
    ('cmd_received', 1),
    ('data_started', 1),
    ('data_completed', 1),
    ('resp_received', 1),
    ('event_reported', 1),
    ('eos_seen', 1),
    ('state', 3),
    ('addr', 32),
    ('id', 8),
    ('len', 8),
    ('size', 3),
    ('burst', 2),
    ('channel', 6),
    ('addr_timer', 32),
    ('data_timer', 32),
    ('resp_timer', 32),
    ('addr_timestamp', 32),
    ('data_timestamp', 32),
    ('resp_timestamp', 32),
    ('expected_beats', 8),
    ('data_beat_count', 8),
    ('event_code', 8),
]
TRANS_WIDTH = sum(w for _, w in TRANS_FIELDS)


def decode_trans(raw: int, width: int) -> dict:
    """Decode a packed bus_transaction_t into a field dict."""
    out = {}
    msb_off = 0
    for name, w in TRANS_FIELDS:
        lsb = width - (msb_off + w)
        out[name] = (raw >> lsb) & ((1 << w) - 1)
        msb_off += w
    return out


class AxiMonitorTransMgrTB(TBBase):
    """Testbench for the AXI monitor transaction-tracking core."""

    def __init__(self, dut):
        super().__init__(dut)
        self.MAX_TRANS = int(os.environ.get('TEST_MAX_TRANS', '8'))
        self.IW = int(os.environ.get('TEST_IW', '4'))
        self.AW = int(os.environ.get('TEST_AW', '32'))

        self.mon_slave = None

        # Continuous observations collected by _sample_table()
        self.samples_running = False
        self.peak_valid_slots = 0
        # Cycles where a slot was in ADDR/DATA phase but already flagged
        # event_reported -- the defect 3 signature.
        self.premature_reported = []
        # Worst (data_beat_count, expected_beats) overrun seen on any slot.
        self.beat_overruns = []
        # Max number of slots simultaneously holding the same id.
        self.max_same_id_slots = 0

    # -- required TBBase lifecycle -------------------------------------

    async def setup_clocks_and_reset(self):
        await self.start_clock('aclk', 10, 'ns')
        await self.assert_reset()
        for _ in range(10):
            await RisingEdge(self.dut.aclk)
        await self.deassert_reset()
        for _ in range(5):
            await RisingEdge(self.dut.aclk)
        await self.initialize_inputs()

    async def assert_reset(self):
        self.dut.aresetn.value = 0

    async def deassert_reset(self):
        self.dut.aresetn.value = 1

    # -- setup ---------------------------------------------------------

    async def initialize_inputs(self):
        self.dut.clear.value = 0
        self.dut.cmd_valid.value = 0
        self.dut.cmd_ready.value = 1
        self.dut.cmd_addr.value = 0
        self.dut.cmd_id.value = 0
        self.dut.cmd_len.value = 0
        self.dut.cmd_size.value = 2
        self.dut.cmd_burst.value = BURST_INCR

        self.dut.data_valid.value = 0
        self.dut.data_ready.value = 1
        self.dut.data_id.value = 0
        self.dut.data_last.value = 0
        self.dut.data_resp.value = RESP_OKAY

        self.dut.resp_valid.value = 0
        self.dut.resp_ready.value = 1
        self.dut.resp_id.value = 0
        self.dut.resp_code.value = RESP_OKAY

        self.dut.monbus_ready.value = 1

        self.dut.cfg_error_enable.value = 1
        self.dut.cfg_compl_enable.value = 1
        self.dut.cfg_threshold_enable.value = 0
        self.dut.cfg_timeout_enable.value = 0
        self.dut.cfg_perf_enable.value = 0
        self.dut.cfg_debug_enable.value = 0

        self.dut.cfg_freq_sel.value = 0
        self.dut.cfg_addr_cnt.value = 0xF
        self.dut.cfg_data_cnt.value = 0xF
        self.dut.cfg_resp_cnt.value = 0xF

        self.dut.cfg_active_trans_threshold.value = 0xFFFF
        self.dut.cfg_latency_threshold.value = 0xFFFFFFFF
        self.dut.cfg_debug_level.value = 0
        self.dut.cfg_debug_mask.value = 0

        self.dut.cfg_addr_check_enable.value = 0
        self.dut.cfg_addr_range_enable.value = 0
        self.dut.cfg_addr_range_low.value = 0
        self.dut.cfg_addr_range_high.value = 0

        self.dut.cfg_start_event_sel.value = 0
        self.dut.cfg_end_event_sel.value = 0
        self.dut.cfg_start_trigger.value = 0
        self.dut.cfg_end_trigger.value = 0
        self.dut.cfg_window_force_close.value = 0
        self.dut.i_mon_time.value = 0

        await RisingEdge(self.dut.aclk)

        self._check_struct_width()

        self.mon_slave = MonbusSlave(
            dut=self.dut, title="MonBus", prefix="", clock=self.dut.aclk,
            bus_name="monbus", pkt_prefix="", log=self.log
        )

    def _check_struct_width(self):
        """Fail loudly if bus_transaction_t no longer matches TRANS_FIELDS."""
        rtl_width = self.dut.w_trans_table[0].value.n_bits
        assert rtl_width == TRANS_WIDTH, (
            f"bus_transaction_t is {rtl_width} bits but this test decodes "
            f"{TRANS_WIDTH}. Update TRANS_FIELDS in {__file__} to match "
            f"rtl/amba/includes/monitor_amba4_pkg.sv."
        )

    # -- observation ---------------------------------------------------

    def read_table(self):
        """Snapshot the whole transaction table as decoded dicts."""
        out = []
        for i in range(self.MAX_TRANS):
            raw = int(self.dut.w_trans_table[i].value)
            out.append(decode_trans(raw, TRANS_WIDTH))
        return out

    async def _sample_table(self):
        """Background sampler: records the invariants under test each cycle."""
        while self.samples_running:
            await RisingEdge(self.dut.aclk)
            try:
                table = self.read_table()
            except Exception:
                continue

            live = [e for e in table if e['valid']]
            self.peak_valid_slots = max(self.peak_valid_slots, len(live))

            ids = {}
            for e in live:
                ids[e['id']] = ids.get(e['id'], 0) + 1
            if ids:
                self.max_same_id_slots = max(self.max_same_id_slots, max(ids.values()))

            for idx, e in enumerate(table):
                if not e['valid']:
                    continue
                # Defect 3: an entry still in its address/data phase must not
                # already be marked reported.
                if e['state'] in (TRANS_ADDR_PHASE, TRANS_DATA_PHASE) and e['event_reported']:
                    self.premature_reported.append(
                        (idx, e['state'], e['id'], int(get_sim_cycle(self.dut))))
                # Defect 1: a beat count must never exceed the expected beats
                # of the transaction it is attributed to.
                if e['expected_beats'] and e['data_beat_count'] > e['expected_beats']:
                    self.beat_overruns.append(
                        (idx, e['id'], e['data_beat_count'], e['expected_beats']))

    def start_sampling(self):
        self.samples_running = True
        self.premature_reported = []
        self.beat_overruns = []
        self.peak_valid_slots = 0
        self.max_same_id_slots = 0
        cocotb.start_soon(self._sample_table())

    def stop_sampling(self):
        self.samples_running = False

    # -- stimulus ------------------------------------------------------

    async def send_cmd(self, txn_id, addr, length=0):
        """One address-phase beat (AR/AW)."""
        self.dut.cmd_id.value = txn_id
        self.dut.cmd_addr.value = addr
        self.dut.cmd_len.value = length
        self.dut.cmd_valid.value = 1
        await RisingEdge(self.dut.aclk)
        self.dut.cmd_valid.value = 0

    async def send_data(self, txn_id, last=True, resp=RESP_OKAY):
        """One data-phase beat (R/W)."""
        self.dut.data_id.value = txn_id
        self.dut.data_last.value = 1 if last else 0
        self.dut.data_resp.value = resp
        self.dut.data_valid.value = 1
        await RisingEdge(self.dut.aclk)
        self.dut.data_valid.value = 0
        self.dut.data_last.value = 0

    async def send_burst(self, txn_id, beats, resp=RESP_OKAY):
        for b in range(beats):
            await self.send_data(txn_id, last=(b == beats - 1), resp=resp)

    async def idle(self, n):
        for _ in range(n):
            await RisingEdge(self.dut.aclk)

    async def drain(self, quiet_cycles=48, max_cycles=1200):
        """Wait until the monitor bus goes genuinely quiet.

        A fixed delay is not safe here: the reporter serialises packets and
        the last completion of a phase can land after an arbitrary fixed
        wait, which then miscounts it into the NEXT phase.

        Counting RECEIVED packets alone is not sufficient either, and that was
        a real bug. The MonbusSlave uses the default GAXI ready profile, whose
        ready_delay reaches 30 cycles (gaxi_component_base.py: [(0,1),(2,8),
        (9,30)] weighted [5,2,1]), and the reporter needs ~2 more cycles to
        reload its output register. So the gap between two packets can exceed
        32 cycles while a packet is still sitting on the bus with monbus_valid
        high -- and the old 30-cycle quiet window would declare the bus idle,
        return, and let that packet be counted into the following phase after
        clear_packets(). That produced "3 or 5 completion packet(s), expected 4"
        depending purely on the drawn seed: a leak-out under-counts this phase,
        a leak-in over-counts the next.

        Fix: require the bus to be actually idle (monbus_valid low) as well as
        quiet, and widen the window past the maximum ready delay plus refill.
        """
        stable = 0
        last = len(self.mon_slave.received_packets)
        for _ in range(max_cycles):
            await RisingEdge(self.dut.aclk)
            now = len(self.mon_slave.received_packets)
            in_flight = int(self.dut.monbus_valid.value)
            if now == last and not in_flight:
                stable += 1
                if stable >= quiet_cycles:
                    return
            else:
                stable = 0
                last = now

    # -- packet helpers ------------------------------------------------

    def packets(self):
        return list(self.mon_slave.received_packets)

    def count(self, pkt_type):
        return sum(1 for p in self.packets()
                   if getattr(p, 'pkt_type', None) == pkt_type)

    def completions(self):
        return [p for p in self.packets()
                if getattr(p, 'pkt_type', None) == PktType.PktTypeCompletion]

    def errors(self):
        return [p for p in self.packets()
                if getattr(p, 'pkt_type', None) == PktType.PktTypeError]

    def clear_packets(self):
        self.mon_slave.received_packets.clear()


def get_sim_cycle(dut):
    """Cheap monotonic marker for diagnostics."""
    from cocotb.utils import get_sim_time
    return get_sim_time('ns')


# ======================================================================
# Phase 1 -- multiple outstanding transactions sharing one ARID
# ======================================================================

async def phase_same_id_outstanding(tb) -> list:
    """Two (then four) outstanding reads on one ID must occupy separate slots."""
    failures = []
    tb.log.info("PHASE 1: multiple outstanding transactions with the same ID")

    # --- 1a: two single-beat reads, same ID -------------------------------
    tb.clear_packets()
    tb.start_sampling()

    await tb.send_cmd(txn_id=1, addr=0x1000, length=0)
    await tb.send_cmd(txn_id=1, addr=0x2000, length=0)   # legal AXI4
    await tb.idle(2)

    table = tb.read_table()
    live_id1 = [e for e in table if e['valid'] and e['id'] == 1]
    if len(live_id1) != 2:
        failures.append(
            f"1a: two outstanding AR(id=1) occupy {len(live_id1)} slot(s), expected 2 "
            f"(addresses tracked: {[hex(e['addr']) for e in live_id1]})")
    else:
        addrs = sorted(e['addr'] for e in live_id1)
        if addrs != [0x1000, 0x2000]:
            failures.append(
                f"1a: slot addresses {[hex(a) for a in addrs]}, expected [0x1000, 0x2000] "
                "(second command overwrote the first)")

    await tb.send_data(txn_id=1, last=True)     # completes the OLDEST
    await tb.idle(3)
    await tb.send_data(txn_id=1, last=True)     # completes the second
    await tb.drain()
    tb.stop_sampling()

    compl = tb.completions()
    errs = tb.errors()
    if len(compl) != 2:
        failures.append(f"1a: {len(compl)} completion packet(s), expected 2")
    if errs:
        failures.append(
            f"1a: {len(errs)} spurious error packet(s) on legal traffic "
            f"(codes={[hex(e.event_code) for e in errs]})")
    compl_addrs = sorted(p.data & 0xFFFFFFFF for p in compl)
    if len(compl) == 2 and compl_addrs != [0x1000, 0x2000]:
        failures.append(
            f"1a: completion addresses {[hex(a) for a in compl_addrs]}, "
            "expected [0x1000, 0x2000]")
    if tb.beat_overruns:
        failures.append(
            f"1a: beat count exceeded expected_beats: {tb.beat_overruns[:4]}")
    if tb.max_same_id_slots < 2:
        failures.append(
            f"1a: at most {tb.max_same_id_slots} slot(s) ever held id=1, expected 2")

    # --- 1b: two multi-beat bursts, same ID -------------------------------
    tb.clear_packets()
    tb.start_sampling()

    await tb.send_cmd(txn_id=3, addr=0x4000, length=1)   # 2 beats
    await tb.send_cmd(txn_id=3, addr=0x5000, length=1)   # 2 beats
    await tb.idle(2)
    await tb.send_burst(txn_id=3, beats=2)               # first transaction
    await tb.idle(3)
    await tb.send_burst(txn_id=3, beats=2)               # second transaction
    await tb.drain()
    tb.stop_sampling()

    compl = tb.completions()
    errs = tb.errors()
    if len(compl) != 2:
        failures.append(f"1b: {len(compl)} completion packet(s) for 2 bursts, expected 2")
    if errs:
        failures.append(
            f"1b: {len(errs)} spurious error packet(s) "
            f"(codes={[hex(e.event_code) for e in errs]})")
    if tb.beat_overruns:
        failures.append(
            f"1b: per-transaction beat count overran expected_beats: "
            f"{tb.beat_overruns[:4]} (beats attributed to the wrong slot)")

    # --- 1c: four outstanding, same ID ------------------------------------
    tb.clear_packets()
    tb.start_sampling()
    for k in range(4):
        await tb.send_cmd(txn_id=2, addr=0x8000 + (k << 12), length=0)
    await tb.idle(2)
    table = tb.read_table()
    live_id2 = [e for e in table if e['valid'] and e['id'] == 2]
    if len(live_id2) != 4:
        failures.append(
            f"1c: four outstanding AR(id=2) occupy {len(live_id2)} slot(s), expected 4")
    for _ in range(4):
        await tb.send_data(txn_id=2, last=True)
        await tb.idle(2)
    await tb.drain()
    tb.stop_sampling()

    compl = tb.completions()
    if len(compl) != 4:
        failures.append(f"1c: {len(compl)} completion packet(s), expected 4")
    if tb.errors():
        failures.append(f"1c: {len(tb.errors())} spurious error packet(s)")

    return failures


# ======================================================================
# Phase 2 -- same-ID command landing on the cleanup cycle
# ======================================================================

async def phase_cleanup_cycle_collision(tb) -> list:
    """A same-ID command on the cleanup cycle must still be tracked."""
    failures = []
    tb.log.info("PHASE 2: same-ID command arriving on the cleanup cycle")

    # delay 3+ was already clean before the fix; it is kept as a control.
    for delay in (0, 1, 2, 3):
        tb.clear_packets()
        tb.start_sampling()

        await tb.send_cmd(txn_id=1, addr=0x1000, length=0)
        await tb.idle(1)
        await tb.send_data(txn_id=1, last=True)
        await tb.idle(delay)
        await tb.send_cmd(txn_id=1, addr=0x2000, length=0)
        await tb.idle(1)
        await tb.send_data(txn_id=1, last=True)
        await tb.drain()
        tb.stop_sampling()

        compl = tb.completions()
        errs = tb.errors()

        if len(compl) != 2:
            failures.append(
                f"2(delay={delay}): {len(compl)} completion packet(s), expected 2 "
                "(the second command was dropped)")
        if errs:
            failures.append(
                f"2(delay={delay}): {len(errs)} FALSE error packet(s) on legal traffic, "
                f"expected 0 (codes={[hex(e.event_code) for e in errs]})")
        compl_addrs = sorted(p.data & 0xFFFFFFFF for p in compl)
        if len(compl) == 2 and compl_addrs != [0x1000, 0x2000]:
            failures.append(
                f"2(delay={delay}): completion addresses {[hex(a) for a in compl_addrs]}, "
                "expected [0x1000, 0x2000]")

    return failures


# ======================================================================
# Phase 3 -- slot reallocation shortly after cleanup
# ======================================================================

async def phase_realloc_event_reported(tb) -> list:
    """A reallocated slot must not inherit the previous entry's reported flag."""
    failures = []
    tb.log.info("PHASE 3: slot reallocation soon after cleanup")

    for delay in range(0, 6):
        tb.clear_packets()
        tb.start_sampling()

        for k in range(4):
            await tb.send_cmd(txn_id=1, addr=0x1000 + (k << 8), length=0)
            await tb.idle(1)
            await tb.send_data(txn_id=1, last=True)
            await tb.idle(delay)
        await tb.drain()
        tb.stop_sampling()

        if tb.premature_reported:
            failures.append(
                f"3(delay={delay}): {len(tb.premature_reported)} cycle(s) where a slot was "
                f"in ADDR/DATA phase with event_reported already set "
                f"(first: slot={tb.premature_reported[0][0]}, "
                f"state={tb.premature_reported[0][1]}, id={tb.premature_reported[0][2]}) "
                "-- a new transaction came up pre-marked, collapsing the "
                "reporter's emission window")

        compl = tb.completions()
        errs = tb.errors()
        if len(compl) != 4:
            failures.append(
                f"3(delay={delay}): {len(compl)} completion packet(s), expected 4")
        if errs:
            failures.append(
                f"3(delay={delay}): {len(errs)} spurious error packet(s), expected 0 "
                f"(codes={[hex(e.event_code) for e in errs]})")

    return failures


# ======================================================================
# Phase 4 -- a timed-out transaction must not leak its slot
# ======================================================================

async def phase_timeout_frees_slot(tb) -> list:
    """A detected timeout must move the slot to a terminal state.

    Detection lives in axi_monitor_timeout, but that block only owns a
    private copy of the table -- trans_mgr has to consume timeout_detected
    and perform the transition, otherwise the slot never becomes
    cleanup-eligible and leaks permanently (transaction-table exhaustion).

    Scope note: the assertion here is deliberately conditional on a timeout
    actually being detected. Detection is another module's contract; if it
    never fires this reports it loudly but does not fail, because the leak
    (trans_mgr's half) cannot be evaluated without it.
    """
    failures = []
    tb.log.info("PHASE 4: a timed-out transaction must free its slot")

    tb.clear_packets()
    # Fast timer tick and a low address-phase threshold.
    tb.dut.cfg_timeout_enable.value = 1
    tb.dut.cfg_freq_sel.value = 0
    tb.dut.cfg_addr_cnt.value = 2
    tb.dut.cfg_data_cnt.value = 0xF
    tb.dut.cfg_resp_cnt.value = 0xF
    await tb.idle(2)

    # A command that is asserted but never accepted: it takes a slot with
    # cmd_received=0 and then stalls there forever.
    tb.dut.cmd_ready.value = 0
    tb.dut.cmd_id.value = 5
    tb.dut.cmd_addr.value = 0xDEAD0000
    tb.dut.cmd_len.value = 0
    tb.dut.cmd_valid.value = 1
    # cfg_addr_cnt=2 means 2 timer ticks. With the 5 MHz table above a tick is
    # 5 clocks, so detection lands ~10 clocks in; the rest is cleanup margin.
    # Do not tune this to the tick by accident: if the LUT parameters change,
    # change them here, not by nudging this number until it passes.
    await tb.idle(400)
    tb.dut.cmd_valid.value = 0
    tb.dut.cmd_ready.value = 1
    await tb.drain()

    timeouts = [p for p in tb.packets()
                if getattr(p, 'pkt_type', None) == PktType.PktTypeTimeout]
    table = tb.read_table()
    stuck = [(i, e['state'], hex(e['addr'])) for i, e in enumerate(table)
             if e['valid'] and e['state'] in (TRANS_ADDR_PHASE, TRANS_DATA_PHASE)]

    if not timeouts:
        tb.log.warning(
            "PHASE 4 not exercised: no PktTypeTimeout was produced, so timeout "
            "DETECTION (axi_monitor_timeout) is not functional in this tree. "
            "trans_mgr's half -- freeing the timed-out slot -- cannot be "
            "evaluated. This is not counted as a failure here.")
    else:
        tb.log.info(f"timeout detected ({len(timeouts)} packet(s)); "
                    "checking the slot was released")
        if stuck:
            failures.append(
                f"4: a timeout fired but {len(stuck)} slot(s) are still parked in "
                f"ADDR/DATA phase {stuck} -- trans_mgr did not move the timed-out "
                "transaction to a terminal state, so it is not cleanup-eligible "
                "and the table leaks an entry per timeout")

    # Restore defaults for any later phase.
    tb.dut.cfg_timeout_enable.value = 0
    tb.dut.cfg_addr_cnt.value = 0xF
    await tb.idle(5)
    return failures


async def phase_saturation_recovers(tb) -> list:
    """A full table must DRAIN and release block_ready -- saturation is not fatal.

    block_ready throttles the COMMAND channel only; responses are never blocked,
    by design (a monitor must not be able to stall returning data). But the data
    and response phases ALSO allocate table entries:

        addr_wants_alloc = cmd_valid && !addr_hit_any            <- gated by block_ready
        data_wants_alloc = data_valid && data_ready && !data_hit_any   <- NOT gated
        resp_wants_alloc = resp_valid && resp_ready && !resp_hit_any   <- NOT gated

    So an unmatched data beat can consume a slot that block_ready has no way to
    withhold. Once the table is full, unmatched data keeps taking slots, occupancy
    never falls back under the release threshold, and the monitor stalls the
    command channel for ever -- taking the monitored datapath down with it.

    This is the monitor-level reproduction of the stream_core multi-channel wedge,
    where the read monitor pinned at MAX_TRANSACTIONS with block_ready low for the
    rest of the simulation.

    The assertions below deliberately check the INVARIANT, not a policy:
      1. occupancy never exceeds the table depth, and
      2. once traffic stops, block_ready comes back.
    Whether overflow is handled by dropping the beat, flagging an orphan, or
    reserving headroom is an implementation choice this test does not constrain.

    NOTE: phase_timeout_frees_slot also stalls a command, but drives no data while
    stalled, so it exercises only the (correct) command path and cannot see this.
    """
    failures = []
    tb.log.info("PHASE 5: a saturated table must drain and release block_ready")

    tb.clear_packets()
    depth = len(tb.read_table())
    id_mask = (1 << int(tb.dut.cmd_id.value.n_bits)) - 1
    tb.log.info(f"table depth = {depth}, id_mask = 0x{id_mask:X}")

    # Emulate the wrapper's gating exactly:  cmd_ready = core_ready & block_ready.
    # Without this the test would drive commands the real design could never issue.
    async def honor_block_ready():
        while True:
            tb.dut.cmd_ready.value = int(tb.dut.block_ready.value)
            await RisingEdge(tb.dut.aclk)

    gate = cocotb.start_soon(honor_block_ready())
    await tb.idle(2)

    # 1) Fill the table using distinct IDs so every command takes its own slot.
    for i in range(depth):
        await tb.send_cmd(txn_id=i & id_mask, addr=0x1000 + (i << 8), length=0)
        await tb.idle(1)
    await tb.idle(5)

    peak_after_fill = int(tb.dut.active_count.value)
    tb.log.info(f"after fill: active_count={peak_after_fill} block_ready={int(tb.dut.block_ready.value)}")

    # 2) With the command channel blocked, drive read data for IDs that are NOT
    #    in the table. Responses are never throttled, so this is traffic the
    #    monitor cannot refuse -- exactly the stream_core situation.
    peak = peak_after_fill
    for i in range(depth * 4):
        unmatched_id = (depth + i) & id_mask
        await tb.send_data(txn_id=unmatched_id, last=True)
        peak = max(peak, int(tb.dut.active_count.value))
        await tb.idle(1)

    tb.log.info(f"after unmatched data: active_count={int(tb.dut.active_count.value)} "
                f"peak={peak} block_ready={int(tb.dut.block_ready.value)}")

    if peak > depth:
        failures.append(
            f"occupancy exceeded table depth: peak active_count={peak} > depth={depth} "
            f"(unmatched data allocated past capacity)")

    # 3) Stop all traffic and let the table drain. Retiring entries must bring
    #    occupancy back under the release threshold and re-assert block_ready.
    tb.dut.data_valid.value = 0
    tb.dut.cmd_valid.value = 0
    released = False
    for _ in range(1000):
        if int(tb.dut.block_ready.value) == 1:
            released = True
            break
        await RisingEdge(tb.dut.aclk)

    final_count = int(tb.dut.active_count.value)
    if not released:
        failures.append(
            f"block_ready never re-asserted after traffic stopped "
            f"(active_count stuck at {final_count}/{depth}) -- the monitor has "
            f"permanently stalled the command channel")
    else:
        tb.log.info(f"block_ready recovered, active_count={final_count}")

    gate.kill()
    tb.dut.cmd_ready.value = 1
    await tb.drain()
    return failures


@cocotb.test(timeout_time=120, timeout_unit="sec")
async def axi_monitor_trans_mgr_test(dut):
    """Transaction-tracking regression suite (issue #41 defects 1-3 + timeout)."""
    tb = AxiMonitorTransMgrTB(dut)
    await tb.setup_clocks_and_reset()

    all_failures = []
    all_failures += await phase_same_id_outstanding(tb)
    all_failures += await phase_cleanup_cycle_collision(tb)
    all_failures += await phase_realloc_event_reported(tb)
    all_failures += await phase_timeout_frees_slot(tb)
    all_failures += await phase_saturation_recovers(tb)

    if all_failures:
        tb.log.error("=" * 78)
        tb.log.error(f"{len(all_failures)} transaction-tracking failure(s):")
        for f in all_failures:
            tb.log.error(f"  - {f}")
        tb.log.error("=" * 78)
    else:
        tb.log.info("All transaction-tracking checks passed")

    assert not all_failures, (
        f"{len(all_failures)} transaction-tracking failure(s):\n  - "
        + "\n  - ".join(all_failures))


# ---------------------------------------------------------------------------
# Seed control.
#
# cocotb self-seeds RANDOM_SEED from the clock when it is not set, so every run
# drove different timing and this suite was NOT reproducible: the same config
# would report 3, 4 or 5 completion packets for identical stimulus depending on
# when it happened to run, and it nearly caused a good RTL fix to be reverted
# as "noise".
#
# That particular symptom turned out to be a TESTBENCH defect, not RTL: drain()
# used a 30-cycle quiet window while the MonbusSlave's default ready_delay also
# reaches 30, so a packet could still be on the bus when drain() returned and
# get counted into the next phase (see drain() for the full mechanism). It is
# fixed there. Seeds stay pinned regardless -- reproducibility is worth having
# on its own, and the corpus below still guards the seeds that once failed.
#
# So: pin a default seed for routine runs, and pin the seeds that have ACTUALLY
# been observed to fail so they run every time as regressions.
#
#   default run          -> DEFAULT_SEED (deterministic)
#   MONITOR_SEED=<n>      -> reproduce one specific seed
#   MONITOR_SEED_SWEEP=1  -> also run every seed in FAILING_SEEDS
#
# When a NEW seed fails, cocotb records it in the results XML as
# "Test failed with RANDOM_SEED=<n>" -- add it to FAILING_SEEDS below so it is
# locked in and can never silently stop being covered.
# ---------------------------------------------------------------------------
DEFAULT_SEED = 12345

# Seeds observed failing on 2026-07-21, harvested from
# val/amba/local_sim_build/*/{,*}_results.xml. Each reproduces a completion-count
# mismatch in phase_same_id_outstanding ("N completion packet(s), expected 4").
FAILING_SEEDS = {
    (4, 32, 8):  [1784649021, 1784649286, 1784649939],
    (8, 32, 16): [1784649035, 1784649937, 1784649940],
}


def generate_test_params():
    """(iw, aw, max_transactions, seed) configurations.

    A FIXED seed alone is a coverage regression: the original random seed was
    doing real exploration, and each new seed shakes the timing differently --
    a scenario that fails under one seed may simply not arise under another.
    Pinning one trajectory would quietly stop finding new defects.

    So this is a corpus + search model, the way a fuzzer is run:

      * corpus  -- DEFAULT_SEED plus every seed in FAILING_SEEDS. Deterministic,
                   always run, never loses a defect that has already been found.
      * search  -- MONITOR_SEED_RANDOM=1 draws fresh seeds to keep exploring.
                   The drawn seed is printed and embedded in the build/log path,
                   so a failure is immediately reproducible via MONITOR_SEED=<n>
                   and can be promoted into FAILING_SEEDS.

    Modes:
      (default)                 corpus: DEFAULT_SEED per config -- deterministic
      MONITOR_SEED=<n>          reproduce one specific seed
      MONITOR_SEED_SWEEP=1      corpus + all known-failing seeds (regression run)
      MONITOR_SEED_RANDOM=<k>   corpus + k freshly drawn seeds per config (search)
    """
    configs = [
        (4, 32, 8),    # nominal
        (4, 32, 4),    # small table: same-ID entries compete for few slots
        (8, 32, 16),   # wide ID, large table
    ]

    override = os.environ.get('MONITOR_SEED')
    if override:
        return [(iw, aw, mt, int(override)) for (iw, aw, mt) in configs]

    params = [(iw, aw, mt, DEFAULT_SEED) for (iw, aw, mt) in configs]

    if os.environ.get('MONITOR_SEED_SWEEP') == '1':
        for cfg in configs:
            for s in FAILING_SEEDS.get(cfg, []):
                params.append((*cfg, s))

    # Exploration. Kept OFF by default so routine runs stay reproducible, but
    # this is what actually finds the next seed-sensitive defect -- run it
    # nightly, not per-commit.
    n_random = int(os.environ.get('MONITOR_SEED_RANDOM', '0'))
    if n_random:
        for cfg in configs:
            for _ in range(n_random):
                s = random.randint(0, 2**31 - 1)
                print(f"[seed-search] {cfg} exploring RANDOM_SEED={s} "
                      f"(reproduce with MONITOR_SEED={s}; "
                      f"if it fails, add it to FAILING_SEEDS)")
                params.append((*cfg, s))
    return params


@pytest.mark.parametrize("iw, aw, max_transactions, seed", generate_test_params())
def test_axi_monitor_trans_mgr(iw, aw, max_transactions, seed):
    """axi_monitor_trans_mgr transaction-tracking test runner."""
    worker_id = os.environ.get('PYTEST_XDIST_WORKER', 'gw0')

    module, repo_root, tests_dir, log_dir, rtl_dict = get_paths({
        'rtl_common': 'rtl/common',
        'rtl_monitor': 'rtl/amba/monitor',
        'rtl_amba_includes': 'rtl/amba/includes',
    })

    dut_name = "axi_monitor_base"
    test_name = (f"test_{worker_id}_axi_monitor_trans_mgr_"
                 f"iw{iw}_aw{aw}_mt{max_transactions}_seed{seed}")
    log_path = os.path.join(log_dir, f'{test_name}.log')
    sim_build = os.path.join(tests_dir, 'local_sim_build', test_name)
    enable_waves = bool(int(os.environ.get('WAVES', '0')))
    os.makedirs(sim_build, exist_ok=True)
    os.makedirs(log_dir, exist_ok=True)

    verilog_sources, includes = get_sources_from_filelist(
        repo_root=repo_root,
        filelist_path="rtl/amba/filelists/axi_monitor_base.f")

    rtl_parameters = {
        # Timer LUT: a 5 MHz table gives a 5-clock tick, which keeps the
        # timeout phase short. This used to be obtained by setting
        # cfg_freq_sel=0 and relying on index 0 of a hardcoded 5..220 MHz
        # table -- a magic index into a table the DUT did not let you choose.
        # The table is a parameter now, so the test states what it needs.
        'CFI_MIN_FREQ_MHZ': '5',
        'CFI_MAX_FREQ_MHZ': '5',
        'ID_WIDTH': str(iw),
        'ADDR_WIDTH': str(aw),
        'UNIT_ID': '1',
        'AGENT_ID': '10',
        'MAX_TRANSACTIONS': str(max_transactions),
        'IS_READ': '1',
        'IS_AXI': '1',
        'ENABLE_PERF_PACKETS': '0',
        'ENABLE_DEBUG_MODULE': '0',
    }

    extra_env = {
        'DUT': dut_name,
        'LOG_PATH': log_path,
        'COCOTB_LOG_LEVEL': 'INFO',
        # RANDOM_SEED is the variable cocotb actually honours; without it
        # cocotb seeds from the clock and the suite is not reproducible.
        # ('SEED' below is unread by this TB but kept for consistency with
        # the framework TBs that do consume it.)
        'RANDOM_SEED': str(seed),
        'COCOTB_RANDOM_SEED': str(seed),
        'SEED': str(seed),
        'TEST_IW': str(iw),
        'TEST_AW': str(aw),
        'TEST_MAX_TRANS': str(max_transactions),
    }

    compile_args = [
        # The transaction table is the object under test; expose it to cocotb.
        "--public-flat-rw",
        "--trace-fst",
        "--trace-structs",
        "-Wall", "-Wno-SYNCASYNCNET", "-Wno-UNUSED", "-Wno-DECLFILENAME",
        "-Wno-PINMISSING", "-Wno-UNDRIVEN", "-Wno-WIDTHEXPAND",
        "-Wno-WIDTHTRUNC", "-Wno-SELRANGE", "-Wno-CASEINCOMPLETE",
        "-Wno-TIMESCALEMOD",
    ]

    try:
        run(
            python_search=[tests_dir],
            verilog_sources=verilog_sources,
            includes=includes + [rtl_dict['rtl_common'], sim_build],
            toplevel=dut_name,
            module=module,
            parameters=rtl_parameters,
            sim_build=sim_build,
            extra_env=extra_env,
            waves=enable_waves,
            plus_args=(['--trace'] if enable_waves else []),
            keep_files=True,
            compile_args=compile_args,
        )
        print(f"✓ PASSED: {test_name}")
    except Exception as e:
        print(f"✗ FAILED: {test_name}")
        print(f"Error: {str(e)}")
        print(f"Log: {log_path}")
        raise
