# SPDX-License-Identifier: MIT
# SPDX-FileCopyrightText: 2026 sean galloway
#
# RTL Design Sherpa - Industry-Standard RTL Design and Verification
# https://github.com/sean-galloway/RTLDesignSherpa
#
# Module: test_axi_monitor_soak
# Purpose: Millions-of-cycles soak of the monitor packet-generation path
#          (axi_monitor_reporter + axi_monitor_timeout, via the pktgen DUT).
#          Drives randomized terminal states, timeouts, and monbus backpressure
#          continuously, captures every emitted packet, and builds the
#          {protocol, pkt_type, event_code} coverage matrix -- the same bins the
#          on-chip monbus_pkt_tally histogram would count on silicon.
#
# Documentation: val/amba/axi_monitor_pktgen_dut.sv (the driven DUT)
#                projects/components/misc/rtl/monbus_pkt_tally.sv (the silicon coverage twin)
# Subsystem: tests
#
# Author: sean galloway

"""
This is the pre-silicon soak: run the real monitor packet-gen logic for
SOAK_CYCLES clock cycles (default 2,000,000) under randomized stimulus, prove it
never wedges, and enumerate every packet type / event code it emits.

It answers "millions of cycles against the monitor code" in simulation, and the
coverage matrix it prints is exactly what one AXIL readback of monbus_pkt_tally
would dump on the Genesys board.
"""

import os
import random
from collections import Counter

import pytest
import cocotb
from cocotb.clock import Clock
from cocotb.triggers import RisingEdge, ReadOnly

from cocotb_test.simulator import run

from TBClasses.shared.utilities import get_paths, create_view_cmd, sim_build_path
from TBClasses.shared.filelist_utils import get_sources_from_filelist

# Transaction states (mirror axi_monitor pkg encodings used by the DUT)
TRANS_IDLE, TRANS_ADDR, TRANS_ACTIVE, TRANS_COMPLETE, TRANS_ERROR, TRANS_ORPHANED = range(6)
N_SLOTS = 4

PKT_ERROR, PKT_COMPLETION, PKT_THRESHOLD, PKT_TIMEOUT, PKT_PERF = 0, 1, 2, 3, 4


def decode_monbus(pkt: int) -> tuple:
    """(protocol, pkt_type, event_code) via the house chokepoint."""
    from TBClasses.monbus import parse as _parse
    mp = _parse(pkt)
    return (int(mp.protocol), int(mp.packet_type), int(mp.event_code))


def bin_of(protocol: int, pkt_type: int, event_code: int) -> int:
    """The monbus_pkt_tally bin address: {protocol[3:0], pkt_type[3:0], evcode[7:0]}."""
    return ((protocol & 0xF) << 12) | ((pkt_type & 0xF) << 8) | (event_code & 0xFF)


class TransTable:
    """Stands in for axi_monitor_trans_mgr: owns the table, drives flat vectors."""
    FIELDS_1BIT = ('valid', 'cmd_received', 'data_started', 'data_completed', 'resp_received')

    def __init__(self, dut, n=N_SLOTS):
        self.dut, self.n = dut, n
        self.slots = [self._blank() for _ in range(n)]

    @staticmethod
    def _blank():
        return {'valid': 0, 'state': TRANS_IDLE, 'cmd_received': 0, 'data_started': 0,
                'data_completed': 0, 'resp_received': 0, 'addr': 0, 'event_code': 0,
                'channel': 0, 'addr_timestamp': 0, 'data_timestamp': 0}

    def set(self, idx, **kw):
        self.slots[idx].update(kw)

    def free(self, idx):
        self.slots[idx] = self._blank()

    def push(self):
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


@cocotb.test()
async def monitor_soak(dut):
    soak_cycles = int(os.environ.get('SOAK_CYCLES', '2000000'))
    rng = random.Random(int(os.environ.get('SEED', '1')))
    cocotb.start_soon(Clock(dut.aclk, 10, units="ns").start())

    tbl = TransTable(dut)
    tbl.push()
    dut.aresetn.value = 0
    dut.timer_tick.value = 0
    dut.cfg_addr_cnt.value = 3
    dut.cfg_data_cnt.value = 3
    dut.cfg_resp_cnt.value = 3
    dut.cfg_error_enable.value = 1
    dut.cfg_compl_enable.value = 1
    dut.cfg_timeout_enable.value = 1
    dut.cfg_threshold_enable.value = 0
    dut.cfg_perf_enable.value = 0
    dut.cfg_debug_enable.value = 0
    dut.active_trans_threshold.value = 0xFFFF
    dut.latency_threshold.value = 0xFFFFFFFF
    dut.monbus_ready.value = 1
    for _ in range(6):
        await RisingEdge(dut.aclk)
    dut.aresetn.value = 1
    for _ in range(3):
        await RisingEdge(dut.aclk)

    # Coverage: emitted-packet histogram, exactly the tally's bins.
    tally: Counter = Counter()
    type_counts: Counter = Counter()
    n_packets = 0
    cycles = 0

    # Background monbus sampler.
    async def _cap():
        nonlocal n_packets
        while True:
            await RisingEdge(dut.aclk)
            await ReadOnly()
            if int(dut.monbus_valid.value) and int(dut.monbus_ready.value):
                proto, ptype, ecode = decode_monbus(int(dut.monbus_packet.value))
                tally[bin_of(proto, ptype, ecode)] += 1
                type_counts[ptype] += 1
                n_packets += 1
    cocotb.start_soon(_cap())

    async def tick(k):
        nonlocal cycles
        for _ in range(k):
            await RisingEdge(dut.aclk)
        cycles += k

    # AXI error event codes worth spreading over (raw 8-bit codes).
    err_codes = [0x01, 0x02, 0x03, 0x04, 0x08, 0x10, 0x20]
    last_report = 0

    while cycles < soak_cycles:
        mode = rng.randrange(4)
        n = rng.randint(1, N_SLOTS)
        idxs = rng.sample(range(N_SLOTS), n)

        # Random monbus backpressure to stress the reporter FIFO.
        dut.monbus_ready.value = 0 if rng.random() < 0.15 else 1

        if mode == 0:  # completions
            dut.cfg_compl_enable.value = 1
            for i in idxs:
                tbl.set(i, valid=1, state=TRANS_COMPLETE,
                        addr=rng.getrandbits(32), channel=rng.randrange(64),
                        event_code=0x00)
        elif mode == 1:  # errors, spread over event codes
            dut.cfg_error_enable.value = 1
            for i in idxs:
                tbl.set(i, valid=1, state=TRANS_ERROR,
                        addr=rng.getrandbits(32), channel=rng.randrange(64),
                        event_code=rng.choice(err_codes))
        elif mode == 2:  # timeouts: stall a slot, then age it with ticks
            dut.cfg_timeout_enable.value = 1
            for i in idxs:
                tbl.set(i, valid=1, state=TRANS_ACTIVE, cmd_received=1,
                        addr=rng.getrandbits(32), channel=rng.randrange(64),
                        event_code=0x00)
            tbl.push()
            for _ in range(rng.randint(4, 8)):
                dut.timer_tick.value = 1
                await tick(1)
                dut.timer_tick.value = 0
                await tick(1)
        else:  # mixed completion+error in one push
            for i in idxs:
                st = rng.choice((TRANS_COMPLETE, TRANS_ERROR))
                tbl.set(i, valid=1, state=st, addr=rng.getrandbits(32),
                        channel=rng.randrange(64),
                        event_code=(rng.choice(err_codes) if st == TRANS_ERROR else 0))

        tbl.push()
        await tick(rng.randint(3, 10))     # let packets drain
        dut.monbus_ready.value = 1          # release any backpressure
        await tick(2)
        for i in idxs:                      # trans_mgr cleanup
            tbl.free(i)
        tbl.push()
        await tick(rng.randint(1, 4))

        if cycles - last_report >= 200_000:
            last_report = cycles
            dut._log.info(f"[soak] {cycles:>9,}/{soak_cycles:,} cyc  "
                          f"packets={n_packets:,}  distinct_bins={len(tally)}  "
                          f"types={dict(type_counts)}")

    # -------- results --------
    dut._log.info("=" * 70)
    dut._log.info(f"SOAK COMPLETE: {cycles:,} cycles, {n_packets:,} packets emitted")
    dut._log.info(f"distinct coverage bins {{proto,type,evcode}}: {len(tally)}")
    names = {PKT_ERROR: 'ERROR', PKT_COMPLETION: 'COMPLETION',
             PKT_THRESHOLD: 'THRESHOLD', PKT_TIMEOUT: 'TIMEOUT', PKT_PERF: 'PERF'}
    for t, c in sorted(type_counts.items()):
        dut._log.info(f"  pkt_type {t} ({names.get(t, '?'):10}): {c:,} packets")
    top = sorted(tally.items(), key=lambda kv: -kv[1])[:12]
    dut._log.info("  top bins (bin=0xPTE): " +
                  ", ".join(f"0x{b:04x}={c:,}" for b, c in top))
    dut._log.info("=" * 70)

    # -------- liveness / no-wedge assertions --------
    assert n_packets > 0, "monitor emitted nothing over the whole soak"
    assert type_counts[PKT_COMPLETION] > 0, "no completion packets emitted"
    assert type_counts[PKT_ERROR] > 0, "no error packets emitted"
    # No X on the emission counter after millions of cycles.
    ev = dut.event_count.value
    assert ev.is_resolvable, "event_count went X -- monitor state corrupted"
    # The monitor kept up: a healthy run emits on the order of one packet per
    # completed/errored slot, so packet count should scale with the workload.
    assert n_packets > (cycles // 2000), (
        f"suspiciously few packets ({n_packets}) for {cycles} cycles -- "
        f"the reporter path may have wedged mid-soak")


# ----------------------------------------------------------------------------
# Pytest wrapper (Pattern A)
# ----------------------------------------------------------------------------
def test_axi_monitor_soak(request):
    module, repo_root, tests_dir, log_dir, rtl_dict = get_paths({
        'rtl_shared':   'rtl/amba/shared',
        'rtl_monitor':  'rtl/amba/monitor',
        'rtl_includes': 'rtl/amba/includes',
    })
    dut_name = "axi_monitor_pktgen_dut"
    worker_id = os.environ.get('PYTEST_XDIST_WORKER', 'gw0')
    soak = os.environ.get('SOAK_CYCLES', '2000000')
    test_name = f"test_{worker_id}_{dut_name}_soak{soak}"
    log_path  = os.path.join(log_dir, f'{test_name}.log')
    sim_build = sim_build_path(tests_dir, test_name)
    os.makedirs(sim_build, exist_ok=True)
    os.makedirs(log_dir, exist_ok=True)

    verilog_sources, includes = get_sources_from_filelist(
        repo_root=repo_root,
        module='axi_monitor_pktgen_dut')
    for src in verilog_sources:
        if not os.path.exists(src):
            raise FileNotFoundError(f"RTL source not found: {src}")

    rtl_parameters = {'MAX_TRANSACTIONS': str(N_SLOTS), 'INTR_FIFO_DEPTH': '8', 'IS_READ': '1'}
    extra_env = {
        'DUT': dut_name, 'LOG_PATH': log_path, 'COCOTB_LOG_LEVEL': 'INFO',
        'COCOTB_RESULTS_FILE': os.path.join(log_dir, f'results_{test_name}.xml'),
        'SEED': os.environ.get('SEED', str(random.randint(0, 100000))),
        'SOAK_CYCLES': soak,
    }
    compile_args = [
        '+define+SIMULATION', '-Wno-DECLFILENAME', '-Wno-WIDTHEXPAND',
        '-Wno-WIDTHTRUNC', '-Wno-UNUSEDPARAM', '-Wno-TIMESCALEMOD', '-Wno-UNUSEDSIGNAL',
    ]
    create_view_cmd(log_dir, log_path, sim_build, module, test_name)
    run(
        python_search=[tests_dir], verilog_sources=verilog_sources,
        includes=includes + [rtl_dict['rtl_shared'], sim_build],
        toplevel=dut_name, module=module, parameters=rtl_parameters,
        sim_build=sim_build, extra_env=extra_env, keep_files=True,
        compile_args=compile_args, testcase='monitor_soak',
    )


# ---------------------------------------------------------------------------
# The lite (amba/monitor-lite TASK-002). axi_monitor_pktgen_dut is the full
# monitor's reporter + timeout FUBs fed from a hand-built table; the lite is
# one module with no separable reporter, so its soak drives the CORE's own
# command/data handshakes with random legal read traffic and checks the
# accounting the lite promises instead of a bin count:
#
#     completions + errors + timeouts GENERATED
#         == packets DELIVERED by class + drops REPORTED + drops still PENDING
#     perf_completed_count == clean transactions, perf_error_count == errored
#     refused_count == 0 (the traffic never exceeds the table), no X.
#
# Events are predictable from the stimulus: a transaction with an erroring
# beat yields one Error and no Completion; a clean one yields one Completion;
# a gap of >= 100 clocks in a transaction's progress yields one Timeout (the
# lite ages an entry since its last beat, in microseconds at the 5 MHz LUT
# entry = 5 clocks/us, and latches one timeout per entry). Ordinary gaps are
# <= 10 clocks (2 us) against an 8 us threshold, so no gap is near the edge.
# ---------------------------------------------------------------------------
LITE_N_SLOTS = 4
LITE_TIMEOUT_US = 8
LITE_TICK_CLKS = 5            # cfg_freq_sel=0 -> the 5 MHz LUT entry: 1 us = 5 clocks
LITE_STALL_CLKS = 100         # 20 us >> 8 us: a guaranteed timeout
LITE_ERR_EVENT_DROPPED = 0xE  # AXI_ERR_EVENT_DROPPED: the lite's drop report
PKT_ERROR, PKT_COMPLETION, PKT_TIMEOUT = 0, 1, 3


def _lite_drive(dut, pin, value):
    if hasattr(dut, pin):
        getattr(dut, pin).value = value


async def _lite_init(dut):
    """Quiesce every input of axi_monitor_lite and program the soak config."""
    for pin, v in (('clear', 0), ('i_mon_time', 0),
                   ('cmd_addr', 0), ('cmd_id', 0), ('cmd_len', 0), ('cmd_valid', 0), ('cmd_ready', 1),
                   ('data_id', 0), ('data_last', 0), ('data_resp', 0), ('data_valid', 0), ('data_ready', 1),
                   ('resp_id', 0), ('resp_code', 0), ('resp_valid', 0), ('resp_ready', 1),
                   ('cfg_freq_sel', 0), ('cfg_timeout_cnt', LITE_TIMEOUT_US),
                   ('cfg_error_enable', 1), ('cfg_compl_enable', 1), ('cfg_timeout_enable', 1),
                   ('cfg_threshold_enable', 0), ('cfg_active_trans_threshold', 0xFFFF),
                   ('cfg_latency_threshold', 0xFFFFFFFF), ('cfg_axi_pkt_mask', 0),
                   ('cfg_addr_check_enable', 0), ('cfg_addr_match_enable', 0),
                   ('cfg_addr_range_enable', 0), ('cfg_addr_range_low', 0), ('cfg_addr_range_high', 0),
                   ('monbus_ready', 1)):
        _lite_drive(dut, pin, v)


@cocotb.test()
async def monitor_soak_monlite(dut):
    soak_cycles = int(os.environ.get('SOAK_CYCLES', '200000'))
    rng = random.Random(int(os.environ.get('SEED', '1')))
    cocotb.start_soon(Clock(dut.aclk, 10, units="ns").start())
    await _lite_init(dut)
    dut.aresetn.value = 0
    for _ in range(6):
        await RisingEdge(dut.aclk)
    dut.aresetn.value = 1
    for _ in range(3):
        await RisingEdge(dut.aclk)

    delivered: Counter = Counter()      # by pkt_type, drop reports excluded
    drop_reported = 0
    n_packets = 0

    async def _cap():
        nonlocal n_packets, drop_reported
        while True:
            await RisingEdge(dut.aclk)
            await ReadOnly()
            if int(dut.monbus_valid.value) and int(dut.monbus_ready.value):
                raw = int(dut.monbus_packet.value)
                proto, ptype, ecode = decode_monbus(raw)
                n_packets += 1
                if ptype == PKT_ERROR and ecode == LITE_ERR_EVENT_DROPPED:
                    drop_reported += (raw & 0xFFFF)          # count rides in the addr field
                else:
                    delivered[ptype] += 1
    cocotb.start_soon(_cap())

    # ---- the traffic model: reads with distinct IDs, one data beat a cycle ----
    exp_compl = exp_err = exp_tmo = 0
    active = {}          # id -> dict(beats_left, err_beat, ready_at, saw_stall)
    cycles = 0
    last_report = 0

    def _free_id():
        ids = [i for i in range(LITE_N_SLOTS) if i not in active]
        return rng.choice(ids) if ids else None

    while cycles < soak_cycles or active:
        issuing = cycles < soak_cycles
        # consumer backpressure, 15% of cycles
        dut.monbus_ready.value = 0 if rng.random() < 0.15 else 1
        # at most one command this cycle
        tid = _free_id() if issuing else None
        if tid is not None and rng.random() < 0.35:
            length = rng.choice((0, 0, 1, 3))
            beats = length + 1
            err_beat = rng.randrange(beats) if rng.random() < 0.20 else None
            stall = rng.random() < 0.10
            active[tid] = dict(beats_left=beats, err_beat=err_beat, beat_idx=0,
                               ready_at=cycles + (LITE_STALL_CLKS if stall else rng.randint(1, 10)),
                               stall_done=not stall)
            dut.cmd_id.value = tid
            dut.cmd_addr.value = rng.getrandbits(32) & ~0x3
            dut.cmd_len.value = length
            dut.cmd_valid.value = 1
            if err_beat is None:
                exp_compl += 1
            else:
                exp_err += 1
            if stall:
                exp_tmo += 1
        else:
            dut.cmd_valid.value = 0
        # at most one data beat this cycle, on a transaction whose time has come
        due = [i for i, t in active.items() if t['ready_at'] <= cycles]
        if due:
            i = rng.choice(due)
            t = active[i]
            last = (t['beats_left'] == 1)
            dut.data_id.value = i
            dut.data_last.value = 1 if last else 0
            dut.data_resp.value = 0b10 if t['err_beat'] == t['beat_idx'] else 0b00
            dut.data_valid.value = 1
            t['beats_left'] -= 1
            t['beat_idx'] += 1
            t['ready_at'] = cycles + rng.randint(1, 10)
            if last:
                del active[i]
        else:
            dut.data_valid.value = 0
        await RisingEdge(dut.aclk)
        cycles += 1
        if cycles - last_report >= 50_000:
            last_report = cycles
            dut._log.info(f"[soak-lite] {cycles:>8,}/{soak_cycles:,} cyc  packets={n_packets:,}  "
                          f"delivered={dict(delivered)}  drop_reported={drop_reported}  "
                          f"generated: compl={exp_compl} err={exp_err} tmo={exp_tmo}")
    dut.cmd_valid.value = 0
    dut.data_valid.value = 0
    dut.monbus_ready.value = 1
    for _ in range(600):                       # last timeouts age out, queue drains
        await RisingEdge(dut.aclk)

    pending = int(dut.dropped_count.value)
    completed = int(dut.perf_completed_count.value)
    errored = int(dut.perf_error_count.value)
    refused = int(dut.refused_count.value)
    live = int(dut.active_count.value)
    generated = exp_compl + exp_err + exp_tmo
    accounted = sum(delivered.values()) + drop_reported + pending
    dut._log.info("=" * 70)
    dut._log.info(f"SOAK-LITE COMPLETE: {cycles:,} cycles, {n_packets:,} packets on the bus")
    dut._log.info(f"  generated: {exp_compl} completions + {exp_err} errors + {exp_tmo} timeouts = {generated}")
    dut._log.info(f"  delivered: {dict(delivered)}  drop reports: {drop_reported}  pending drops: {pending}  -> {accounted}")
    dut._log.info(f"  ports: perf_completed={completed} perf_error={errored} refused={refused} active={live}")
    dut._log.info("=" * 70)
    for sig in (dut.dropped_count, dut.perf_completed_count, dut.perf_error_count, dut.refused_count, dut.active_count):
        assert sig.value.is_resolvable, f"{sig._name} went X -- monitor state corrupted"
    assert n_packets > 0, "the lite emitted nothing over the whole soak"
    assert delivered[PKT_COMPLETION] > 0 and delivered[PKT_ERROR] > 0 and delivered[PKT_TIMEOUT] > 0, (
        f"a class never reached the bus: {dict(delivered)}")
    assert refused == 0, f"refused_count={refused}: the traffic never exceeds {LITE_N_SLOTS} outstanding"
    assert live == 0, f"{live} entries still live after the drain"
    assert completed == (exp_compl & 0xFFFF), f"perf_completed_count={completed}, model={exp_compl}"
    assert errored == (exp_err & 0xFFFF), f"perf_error_count={errored}, model={exp_err}"
    assert accounted == generated, (
        f"{generated} events generated but {sum(delivered.values())} delivered + "
        f"{drop_reported} reported dropped + {pending} pending = {accounted}: the lite "
        + ("LOST events it never counted" if accounted < generated else "counted events that did not happen"))


def test_axi_monitor_soak_monlite(request):
    module, repo_root, tests_dir, log_dir, rtl_dict = get_paths({
        'rtl_monitor':  'rtl/amba/monitor',
        'rtl_includes': 'rtl/amba/includes',
    })
    dut_name = "axi_monitor_lite"
    worker_id = os.environ.get('PYTEST_XDIST_WORKER', 'gw0')
    soak = os.environ.get('SOAK_CYCLES', '200000')
    test_name = f"test_{worker_id}_{dut_name}_soak{soak}"
    log_path  = os.path.join(log_dir, f'{test_name}.log')
    sim_build = sim_build_path(tests_dir, test_name)
    os.makedirs(sim_build, exist_ok=True)
    os.makedirs(log_dir, exist_ok=True)
    verilog_sources, includes = get_sources_from_filelist(repo_root=repo_root, module=dut_name)
    rtl_parameters = {'MAX_TRANSACTIONS': str(LITE_N_SLOTS), 'ID_WIDTH': '4', 'ADDR_WIDTH': '32',
                      'IS_READ': '1', 'IS_AXI': '1', 'UNIT_ID': '1', 'AGENT_ID': '10'}
    extra_env = {
        'DUT': dut_name, 'LOG_PATH': log_path, 'COCOTB_LOG_LEVEL': 'INFO',
        'COCOTB_RESULTS_FILE': os.path.join(log_dir, f'results_{test_name}.xml'),
        'SEED': os.environ.get('SEED', str(random.randint(0, 100000))),
        'SOAK_CYCLES': soak,
    }
    compile_args = [
        '+define+SIMULATION', '-Wno-DECLFILENAME', '-Wno-WIDTHEXPAND',
        '-Wno-WIDTHTRUNC', '-Wno-UNUSEDPARAM', '-Wno-TIMESCALEMOD', '-Wno-UNUSEDSIGNAL',
    ]
    create_view_cmd(log_dir, log_path, sim_build, module, test_name)
    run(
        python_search=[tests_dir], verilog_sources=verilog_sources,
        includes=includes + [sim_build],
        toplevel=dut_name, module=module, parameters=rtl_parameters,
        sim_build=sim_build, extra_env=extra_env, keep_files=True,
        compile_args=compile_args, testcase='monitor_soak_monlite',
    )
