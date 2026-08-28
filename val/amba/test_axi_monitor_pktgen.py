# SPDX-License-Identifier: MIT
# SPDX-FileCopyrightText: 2024-2026 sean galloway
#
# RTL Design Sherpa - Industry-Standard RTL Design and Verification
# https://github.com/sean-galloway/RTLDesignSherpa
#
# Module: test_axi_monitor_pktgen
# Purpose: Intent-level regression tests for the monitor packet-generation and
#          timeout path (axi_monitor_reporter + axi_monitor_timeout).
#
# BACKGROUND -- why these tests exist (GitHub issue #41)
# -----------------------------------------------------
# The whole AMBA suite was green while:
#   * the reporter marked EVERY eligible slot reported on a single FIFO write,
#     so three slots completing in one cycle emitted one packet and trans_mgr
#     freed all three -- most error and completion packets were discarded;
#   * marking ignored cfg_*_enable, so a disabled packet class was marked
#     reported (and freed) by another class's write;
#   * the FIFO was popped on (monbus_ready && monbus_valid) but loaded on
#     (!monbus_valid && rd_valid), so a queued packet was consumed without
#     ever being latched whenever a bypass packet held the output register;
#   * axi_monitor_timeout re-copied the whole transaction struct every cycle,
#     clobbering its own timer accumulators -- timers pinned at 1 and no
#     threshold above 1 could ever fire.
#
# None of that was visible to the existing full-stack monitor tests, because
# driving AXI traffic at a monitor wrapper cannot reliably construct the exact
# table states and backpressure phasing that expose them. These tests drive the
# transaction table directly through val/amba/axi_monitor_pktgen_dut.sv, with
# the test playing the role of axi_monitor_trans_mgr.
#
# Each test below asserts INTENT, and each was confirmed to FAIL against the
# pre-fix RTL before the fix was written.

import os
import random

import pytest
import cocotb
from cocotb_test.simulator import run
from cocotb.clock import Clock
from cocotb.triggers import RisingEdge, ReadOnly

from TBClasses.shared.utilities import get_paths, sim_build_path
from TBClasses.shared.filelist_utils import get_sources_from_filelist


# ============================================================================
# Constants mirrored from monitor_common_pkg.sv
# ============================================================================
PKT_ERROR      = 0x0
PKT_COMPLETION = 0x1
PKT_THRESHOLD  = 0x2
PKT_TIMEOUT    = 0x3
PKT_PERF       = 0x4

TRANS_IDLE       = 0
TRANS_ADDR_PHASE = 1
TRANS_DATA_PHASE = 2
TRANS_COMPLETE   = 3
TRANS_ERROR      = 4
TRANS_ORPHANED   = 5

N_SLOTS = 4


def decode_monbus(pkt):
    """Decode a 128-bit monbus packet (layout per monitor_common_pkg)."""
    # Header fields decode via the house chokepoint (TBClasses.monbus.parse):
    # one field-layout source of truth + feeds MONBUS_COVERAGE. The
    # event_data sub-field splits below are test-specific and stay local.
    from TBClasses.monbus import parse as _monbus_parse
    _mp = _monbus_parse(pkt)
    return {
        'packet_type': int(_mp.packet_type),
        'protocol': int(_mp.protocol),
        'event_code': int(_mp.event_code),
        'channel_id': int(_mp.channel_id),
        'agent_id': int(_mp.agent_id),
        'unit_id': int(_mp.unit_id),
        'event_data':   pkt         & ((1 << 64) - 1),
        'addr':         pkt         & 0xFFFFFFFF,
    }


# ============================================================================
# Transaction-table model. Stands in for axi_monitor_trans_mgr: the test owns
# the table and pushes it into the DUT's flattened drive vectors.
# ============================================================================
class TransTable:
    FIELDS_1BIT = ('valid', 'cmd_received', 'data_started',
                   'data_completed', 'resp_received')

    def __init__(self, dut, n=N_SLOTS):
        self.dut = dut
        self.n = n
        self.slots = [self._blank() for _ in range(n)]

    @staticmethod
    def _blank():
        return {
            'valid': 0, 'state': TRANS_IDLE, 'cmd_received': 0,
            'data_started': 0, 'data_completed': 0, 'resp_received': 0,
            'addr': 0, 'event_code': 0, 'channel': 0,
            'addr_timestamp': 0, 'data_timestamp': 0,
        }

    def clear(self):
        self.slots = [self._blank() for _ in range(self.n)]
        self.push()

    def set(self, idx, **kwargs):
        self.slots[idx].update(kwargs)

    def free(self, idx):
        """Model trans_mgr cleanup: release the slot."""
        self.slots[idx] = self._blank()

    def push(self):
        """Drive the flattened vectors from the model."""
        def pack(field, width):
            v = 0
            for i, s in enumerate(self.slots):
                v |= (s[field] & ((1 << width) - 1)) << (i * width)
            return v

        for f in self.FIELDS_1BIT:
            getattr(self.dut, f'slot_{f}').value = pack(f, 1)
        self.dut.slot_state.value          = pack('state', 3)
        self.dut.slot_addr.value           = pack('addr', 32)
        self.dut.slot_event_code.value     = pack('event_code', 8)
        self.dut.slot_channel.value        = pack('channel', 6)
        self.dut.slot_addr_timestamp.value = pack('addr_timestamp', 32)
        self.dut.slot_data_timestamp.value = pack('data_timestamp', 32)


# ============================================================================
# Shared harness setup
# ============================================================================
async def setup_dut(dut, *, error_en=1, compl_en=1, timeout_en=1,
                    threshold_en=0, perf_en=0, ready=1,
                    active_thresh=0xFFFF, latency_thresh=0xFFFFFFFF,
                    addr_cnt=0, data_cnt=0, resp_cnt=0):
    """Clock, reset, quiet configuration. Returns the table model."""
    cocotb.start_soon(Clock(dut.aclk, 10, units="ns").start())

    tbl = TransTable(dut)
    tbl.push()

    dut.aresetn.value = 0
    dut.timer_tick.value = 0
    dut.cfg_addr_cnt.value = addr_cnt
    dut.cfg_data_cnt.value = data_cnt
    dut.cfg_resp_cnt.value = resp_cnt
    dut.cfg_error_enable.value = error_en
    dut.cfg_compl_enable.value = compl_en
    dut.cfg_timeout_enable.value = timeout_en
    dut.cfg_threshold_enable.value = threshold_en
    dut.cfg_perf_enable.value = perf_en
    dut.cfg_debug_enable.value = 0
    dut.active_trans_threshold.value = active_thresh
    dut.latency_threshold.value = latency_thresh
    dut.monbus_ready.value = ready

    for _ in range(6):
        await RisingEdge(dut.aclk)
    dut.aresetn.value = 1
    for _ in range(3):
        await RisingEdge(dut.aclk)
    return tbl


def start_capture(dut, captured):
    """Background monbus sampler: records every accepted packet."""
    async def _cap():
        while True:
            await RisingEdge(dut.aclk)
            await ReadOnly()
            if int(dut.monbus_valid.value) and int(dut.monbus_ready.value):
                captured.append(decode_monbus(int(dut.monbus_packet.value)))
    cocotb.start_soon(_cap())


async def idle(dut, cycles):
    for _ in range(cycles):
        await RisingEdge(dut.aclk)


# ============================================================================
# DEFECT 1 -- marking must be per-index
# ============================================================================
@cocotb.test(timeout_time=20, timeout_unit="ms")
async def cocotb_test_per_index_marking(dut):
    """Three slots reach a terminal state in the SAME cycle.

    Intent: one packet is emitted per slot, and each FIFO write marks exactly
    the slot whose packet was written. Nothing is marked reported (and so
    freed by trans_mgr) on behalf of a packet that was never emitted.

    Pre-fix behaviour: the mark loop set every eligible slot on any accepted
    FIFO write -- one packet out, all three slots marked and freed.
    """
    tbl = await setup_dut(dut, compl_en=1, error_en=1)
    captured = []
    start_capture(dut, captured)

    addrs = {0: 0xC0000000, 1: 0xC0000001, 2: 0xC0000002}
    for i, a in addrs.items():
        tbl.set(i, valid=1, state=TRANS_COMPLETE, addr=a, channel=i)
    tbl.push()

    # Watch the marking flags advance one slot at a time. Slots stay in the
    # table until reported, exactly as trans_mgr holds them.
    await idle(dut, 40)

    flags = int(dut.event_reported_flags.value)
    compl = [p for p in captured if p['packet_type'] == PKT_COMPLETION]
    got_addrs = sorted(p['addr'] for p in compl)

    dut._log.info(f"completion packets={len(compl)} addrs={[hex(a) for a in got_addrs]} "
                  f"event_reported_flags={flags:#06b} event_count={int(dut.event_count.value)}")

    assert len(compl) == 3, (
        f"Expected 3 completion packets (one per completed slot), got {len(compl)}. "
        f"Marking is not per-index: a single FIFO write marked multiple slots "
        f"reported, so trans_mgr would free transactions that never produced a "
        f"packet. Captured: {captured}")
    assert got_addrs == sorted(addrs.values()), (
        f"Completion packets must carry each slot's own address. "
        f"Expected {[hex(a) for a in sorted(addrs.values())]}, got {[hex(a) for a in got_addrs]}")
    assert flags == 0b0111, (
        f"All three reported slots should be marked, got {flags:#06b}")
    assert int(dut.event_count.value) == 3, (
        f"event_count must count every marked event, got "
        f"{int(dut.event_count.value)} (a non-blocking increment inside the "
        f"mark for-loop collapses N marks into 1)")


# ============================================================================
# DEFECT 1b -- one packet per cycle, losers stay pending
# ============================================================================
@cocotb.test(timeout_time=20, timeout_unit="ms")
async def cocotb_test_single_mark_per_write(dut):
    """After the FIRST accepted FIFO write, exactly one slot is marked.

    Tighter than the test above: it pins the cycle-level behaviour rather than
    the drained total, so a fix that merely re-emits later still fails here if
    it marks more than one slot per write.
    """
    tbl = await setup_dut(dut, compl_en=1, error_en=1, ready=0)
    for i, a in ((0, 0xA0), (1, 0xA1), (2, 0xA2)):
        tbl.set(i, valid=1, state=TRANS_COMPLETE, addr=a, channel=i)
    tbl.push()

    # Wait for the first mark to land, then check how many slots it marked.
    marked = 0
    for _ in range(20):
        await RisingEdge(dut.aclk)
        await ReadOnly()
        marked = bin(int(dut.event_reported_flags.value)).count('1')
        if marked:
            break

    dut._log.info(f"slots marked on first FIFO write: {marked} "
                  f"(flags={int(dut.event_reported_flags.value):#06b})")
    assert marked == 1, (
        f"A single accepted FIFO write carries a single packet and must mark a "
        f"single slot; {marked} slots were marked. The other {marked - 1} would "
        f"be freed by trans_mgr with no packet ever emitted.")


# ============================================================================
# DEFECT 2 -- marking must honour cfg_*_enable
# ============================================================================
@cocotb.test(timeout_time=20, timeout_unit="ms")
async def cocotb_test_disabled_class_not_marked(dut):
    """A runtime-disabled packet class emits nothing and never counts -- but
    its terminal slots MUST still retire.

    Configuration: errors OFF, completions ON (the mirror of the
    "performance analysis" configuration recommended in rtl/amba/CLAUDE.md).

    CONTRACT CHANGE (E1, runtime-disable leak fix): this test originally
    asserted that a disabled class's slot must stay UNREPORTED. That
    guaranteed the slot was never freed, which is precisely the leak that
    wedged the monitor after ~MAX_TRANSACTIONS runtime-disabled events
    (table pins at MAX, block_ready low forever). The owner-decided contract
    is now: auto-retire is CONTINUOUS over both compiled-out and
    runtime-disabled classes -- the slot is marked reported (freed by
    trans_mgr) with no packet emitted, and the emission counters must NOT
    count these silent retires.

    What is still forbidden, and still checked here:
      * a disabled class must emit zero packets, and
      * event_count must count only packets actually emitted (an
        auto-retired slot bumps nothing).
    """
    tbl = await setup_dut(dut, error_en=0, compl_en=1)
    captured = []
    start_capture(dut, captured)

    tbl.set(0, valid=1, state=TRANS_ERROR,    addr=0xE0000000, channel=0, event_code=0x02)
    tbl.set(1, valid=1, state=TRANS_COMPLETE, addr=0xC0000001, channel=1)
    tbl.push()
    await idle(dut, 40)

    flags = int(dut.event_reported_flags.value)
    types = [p['packet_type'] for p in captured]
    events = int(dut.event_count.value)
    dut._log.info(f"packets={[hex(t) for t in types]} flags={flags:#06b} events={events}")

    assert PKT_ERROR not in types, (
        f"cfg_error_enable=0 must suppress error packets, saw {captured}")
    assert types.count(PKT_COMPLETION) == 1, (
        f"Expected exactly 1 completion packet, got {types.count(PKT_COMPLETION)}")
    assert (flags & 0b0001) != 0, (
        f"Slot 0 is a terminal ERROR slot with cfg_error_enable=0 (and "
        f"timeouts disabled). Auto-retire must mark it reported so trans_mgr "
        f"can free it (flags={flags:#06b}); leaving it unmarked leaks the "
        f"slot and wedges block_ready at saturation (E1).")
    assert (flags & 0b0010) != 0, "Slot 1's completion was emitted, so it must be marked"
    assert events == 1, (
        f"event_count={events}, expected 1: only the emitted completion may "
        f"count -- the auto-retired error slot must not bump the counter")

    # --- mirror case: completions OFF, errors ON -------------------------
    dut.cfg_error_enable.value = 1
    dut.cfg_compl_enable.value = 0
    tbl.clear()
    await idle(dut, 6)
    captured.clear()

    tbl.set(0, valid=1, state=TRANS_ERROR,    addr=0xE0000010, channel=0, event_code=0x02)
    tbl.set(1, valid=1, state=TRANS_COMPLETE, addr=0xC0000011, channel=1)
    tbl.push()
    await idle(dut, 40)

    flags = int(dut.event_reported_flags.value)
    types = [p['packet_type'] for p in captured]
    events = int(dut.event_count.value)
    dut._log.info(f"mirror: packets={[hex(t) for t in types]} flags={flags:#06b} events={events}")

    assert types.count(PKT_ERROR) == 1, (
        f"Expected exactly 1 error packet, got {types.count(PKT_ERROR)}: {captured}")
    assert PKT_COMPLETION not in types, (
        f"cfg_compl_enable=0 must suppress completion packets, saw {captured}")
    assert (flags & 0b0010) != 0, (
        f"Slot 1 is a terminal COMPLETE slot with cfg_compl_enable=0; "
        f"auto-retire must mark it reported (silently, no packet) so it "
        f"cannot leak (flags={flags:#06b})")
    assert events == 2, (
        f"event_count={events}, expected 2 cumulative (1 compl + 1 error "
        f"emitted): auto-retired slots must not bump the counter")


# ============================================================================
# DEFECT 3 -- FIFO pop and output-register load must agree
# ============================================================================
@cocotb.test(timeout_time=20, timeout_unit="ms")
async def cocotb_test_no_packet_lost_under_backpressure(dut):
    """A queued packet must not be popped while a bypass packet occupies the
    output register.

    Threshold/perf/debug packets bypass the FIFO and load the output register
    directly. Pre-fix, the FIFO pop condition was (monbus_ready && monbus_valid)
    while the load condition was (!monbus_valid && rd_valid): accepting the
    bypass packet popped a queued entry that nothing latched.

    Exactly one completion is queued here, so this isolates the pop/load
    disagreement from the per-index marking defect.
    """
    tbl = await setup_dut(dut, threshold_en=1, active_thresh=0,
                          compl_en=1, error_en=1, ready=0)
    captured = []
    start_capture(dut, captured)

    # 1. One active transaction -> active_count(1) > threshold(0) -> a
    #    THRESHOLD packet bypasses the FIFO into the output register.
    tbl.set(0, valid=1, state=TRANS_ADDR_PHASE, addr=0x1000, channel=0)
    tbl.push()
    await idle(dut, 6)
    assert int(dut.monbus_valid.value) == 1, "expected a threshold packet in the output register"

    # 2. A completion lands in the FIFO behind it.
    tbl.set(1, valid=1, state=TRANS_COMPLETE, addr=0xBEEF0001, channel=1)
    tbl.push()
    await idle(dut, 6)

    # 3. Single-cycle ready pulse: accepts the bypass packet. Pre-fix this
    #    also popped the queued completion, which was never latched.
    dut.monbus_ready.value = 1
    await RisingEdge(dut.aclk)
    dut.monbus_ready.value = 0
    await idle(dut, 6)

    # 4. Open the bus and drain.
    dut.monbus_ready.value = 1
    await idle(dut, 30)

    types = [p['packet_type'] for p in captured]
    compl = [p for p in captured if p['packet_type'] == PKT_COMPLETION]
    dut._log.info(f"packets={[hex(t) for t in types]} "
                  f"compl_addrs={[hex(p['addr']) for p in compl]}")

    assert any(p['packet_type'] == PKT_THRESHOLD for p in captured), (
        f"threshold packet should have been emitted: {captured}")
    assert len(compl) == 1, (
        f"The queued completion packet was lost: expected 1 completion, got "
        f"{len(compl)}. The FIFO was popped while the output register held a "
        f"bypass packet, so the entry was consumed without being latched. "
        f"Captured: {captured}")
    assert compl[0]['addr'] == 0xBEEF0001, (
        f"wrong completion address: {compl[0]['addr']:#x}")


# ============================================================================
# DEFECT 4 -- timeouts must actually fire
# ============================================================================
@cocotb.test(timeout_time=20, timeout_unit="ms")
async def cocotb_test_timeout_fires(dut):
    """Program a threshold ABOVE 1, stall a transaction, and require the
    timeout to fire, produce a PktTypeTimeout, and leave the slot eligible
    for cleanup.

    Pre-fix behaviour: axi_monitor_timeout re-copied the whole transaction
    struct from trans_table every cycle, overwriting the timer accumulators it
    incremented only on a timer tick. Every timer sat at 1 forever, so any
    cfg_*_cnt above 1 could never be reached and no timeout ever fired.

    NOTE ON SCOPE: the transition of the timed-out slot to TRANS_ERROR is
    axi_monitor_trans_mgr's job -- see the report attached to issue #41. The
    real trans_mgr does not consume timeout_detected yet, so this test performs
    that transition itself, which is exactly the contract trans_mgr must
    implement. Everything downstream of it (timeout packet generation, marking,
    cleanup eligibility) is the code under test here.
    """
    ADDR_CNT = 5          # deliberately > 1: the pre-fix pinned timer cannot reach it
    tbl = await setup_dut(dut, timeout_en=1, error_en=1, compl_en=1,
                          addr_cnt=ADDR_CNT, data_cnt=0xF, resp_cnt=0xF)
    captured = []
    start_capture(dut, captured)

    # Free-running timer tick, one every 4 cycles.
    async def ticker():
        while True:
            for _ in range(3):
                await RisingEdge(dut.aclk)
                dut.timer_tick.value = 0
            await RisingEdge(dut.aclk)
            dut.timer_tick.value = 1
    cocotb.start_soon(ticker())

    # A command stuck in address phase: issued, never accepted.
    tbl.set(0, valid=1, state=TRANS_ADDR_PHASE, cmd_received=0,
            addr=0xDEAD0000, channel=0)
    tbl.push()

    # Give it well over ADDR_CNT ticks.
    fired = 0
    for _ in range(30 * 4):
        await RisingEdge(dut.aclk)
        await ReadOnly()
        if int(dut.timeout_detected.value) & 1:
            fired = 1
            break

    assert fired, (
        f"timeout_detected never asserted for a transaction stalled in address "
        f"phase with cfg_addr_cnt={ADDR_CNT} over ~30 timer ticks. The phase "
        f"timers are not accumulating.")
    dut._log.info("timeout_detected asserted for slot 0")

    # Leave the ReadOnly phase the poll loop above ended in before driving.
    await RisingEdge(dut.aclk)

    # Act as trans_mgr: a detected timeout moves the slot to TRANS_ERROR.
    tbl.set(0, state=TRANS_ERROR)
    tbl.push()
    await idle(dut, 30)

    to_pkts = [p for p in captured if p['packet_type'] == PKT_TIMEOUT]
    dut._log.info(f"timeout packets={len(to_pkts)} "
                  f"flags={int(dut.event_reported_flags.value):#06b}")

    assert len(to_pkts) >= 1, (
        f"No PktTypeTimeout packet was generated for a timed-out transaction. "
        f"Captured: {captured}")
    assert to_pkts[0]['addr'] == 0xDEAD0000, (
        f"timeout packet address wrong: {to_pkts[0]['addr']:#x}")

    # Slot must now be eligible for cleanup: trans_mgr frees a TRANS_ERROR
    # entry once event_reported is set.
    assert int(dut.event_reported_flags.value) & 1, (
        "The timed-out slot was never marked reported, so trans_mgr can never "
        "free it -- this is the transaction-table exhaustion path.")

    # And once trans_mgr frees it, the slot rearms for its next occupant.
    tbl.free(0)
    tbl.push()
    await idle(dut, 6)
    assert (int(dut.event_reported_flags.value) & 1) == 0, (
        "event_reported must clear when the slot is released for reuse")
    assert (int(dut.timeout_detected.value) & 1) == 0, (
        "timeout_detected must clear when the slot is released for reuse")


# ============================================================================
# DEFECT 4b -- cfg_timeout_enable is not dead configuration
# ============================================================================
@cocotb.test(timeout_time=20, timeout_unit="ms")
async def cocotb_test_timeout_enable_gates_detection(dut):
    """cfg_timeout_enable=0 must suppress timeout detection.

    It was declared on axi_monitor_timeout and never referenced -- detection
    ran unconditionally.
    """
    tbl = await setup_dut(dut, timeout_en=0, addr_cnt=2,
                          data_cnt=0xF, resp_cnt=0xF)

    async def ticker():
        while True:
            for _ in range(3):
                await RisingEdge(dut.aclk)
                dut.timer_tick.value = 0
            await RisingEdge(dut.aclk)
            dut.timer_tick.value = 1
    cocotb.start_soon(ticker())

    tbl.set(0, valid=1, state=TRANS_ADDR_PHASE, cmd_received=0,
            addr=0xDEAD1000, channel=0)
    tbl.push()
    await idle(dut, 30 * 4)

    assert int(dut.timeout_detected.value) == 0, (
        f"cfg_timeout_enable=0 must suppress detection, got "
        f"timeout_detected={int(dut.timeout_detected.value):#06b}")

    # Turn it on: the same stalled transaction must now time out.
    dut.cfg_timeout_enable.value = 1
    fired = 0
    for _ in range(30 * 4):
        await RisingEdge(dut.aclk)
        await ReadOnly()
        if int(dut.timeout_detected.value) & 1:
            fired = 1
            break
    assert fired, "timeout must fire once cfg_timeout_enable is set"


# ============================================================================
# PyTest runners
# ============================================================================
def _run_pktgen(request, testcase):
    """Shared cocotb-test invocation for the packet-generation harness."""
    worker_id = os.environ.get('PYTEST_XDIST_WORKER', 'gw0')

    module, repo_root, tests_dir, log_dir, rtl_dict = get_paths({
        'rtl_gaxi':          'rtl/amba/gaxi',
        'rtl_includes':      'rtl/amba/includes',
        'rtl_common':        'rtl/common',
        'rtl_monitor':       'rtl/amba/monitor',
        'rtl_amba_includes': 'rtl/amba/includes',
    })

    dut_name  = "axi_monitor_pktgen_dut"
    test_name = f"test_{worker_id}_{testcase}"

    log_path  = os.path.join(log_dir, f'{test_name}.log')
    sim_build = sim_build_path(tests_dir, test_name)
    os.makedirs(sim_build, exist_ok=True)
    os.makedirs(log_dir, exist_ok=True)

    verilog_sources, includes = get_sources_from_filelist(
        repo_root=repo_root,
        filelist_path="rtl/amba/filelists/axi_monitor_pktgen_dut.f")
    for src in verilog_sources:
        if not os.path.exists(src):
            raise FileNotFoundError(f"RTL source not found: {src}")

    rtl_parameters = {
        'MAX_TRANSACTIONS': str(N_SLOTS),
        'INTR_FIFO_DEPTH':  '8',
        'IS_READ':          '1',
    }

    extra_env = {
        'DUT':              dut_name,
        'LOG_PATH':         log_path,
        'COCOTB_LOG_LEVEL': 'INFO',
        'TEST_CLK_PERIOD':  '10',
        'SEED':             os.environ.get('SEED', str(random.randint(0, 100000))),
    }

    compile_args = [
        "--trace-fst", "--trace-structs",
        "-Wall", "-Wno-SYNCASYNCNET", "-Wno-UNUSED", "-Wno-DECLFILENAME",
        "-Wno-PINMISSING", "-Wno-UNDRIVEN", "-Wno-WIDTHEXPAND",
        "-Wno-WIDTHTRUNC", "-Wno-SELRANGE", "-Wno-CASEINCOMPLETE",
        "-Wno-TIMESCALEMOD",
    ]

    run(
        python_search=[tests_dir],
        verilog_sources=verilog_sources,
        includes=includes + [rtl_dict['rtl_common'], sim_build],
        toplevel=dut_name,
        module="test_axi_monitor_pktgen",
        testcase=testcase,
        parameters=rtl_parameters,
        extra_env=extra_env,
        sim_build=sim_build,
        compile_args=compile_args,
        waves=bool(int(os.environ.get('WAVES', '0'))),
        keep_files=True,
    )


def test_axi_monitor_pktgen_per_index_marking(request):
    """Issue #41: one packet per slot, one mark per FIFO write."""
    _run_pktgen(request, "cocotb_test_per_index_marking")


def test_axi_monitor_pktgen_single_mark_per_write(request):
    """Issue #41: a single FIFO write marks exactly one slot."""
    _run_pktgen(request, "cocotb_test_single_mark_per_write")


def test_axi_monitor_pktgen_cfg_enable_gating(request):
    """Issue #41: a disabled packet class is neither reported nor freed."""
    _run_pktgen(request, "cocotb_test_disabled_class_not_marked")


def test_axi_monitor_pktgen_backpressure_no_loss(request):
    """Issue #41: FIFO pop and output-register load agree under backpressure."""
    _run_pktgen(request, "cocotb_test_no_packet_lost_under_backpressure")


def test_axi_monitor_pktgen_timeout_fires(request):
    """Issue #41: timeouts fire, emit PktTypeTimeout, and free the slot."""
    _run_pktgen(request, "cocotb_test_timeout_fires")


def test_axi_monitor_pktgen_timeout_enable(request):
    """Issue #41: cfg_timeout_enable actually gates detection."""
    _run_pktgen(request, "cocotb_test_timeout_enable_gates_detection")
