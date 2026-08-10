# SPDX-License-Identifier: MIT
# SPDX-FileCopyrightText: 2026 sean galloway
#
# Module: test_stream_core_mon_classes
# Purpose: Prove that each AXI-monitor packet class, CONFIGURED BY REGISTER NAME
#          over APB, actually produces its own packet type on monbus -- and does
#          not produce it when disabled.
#
# WHY THIS FILE EXISTS
# --------------------
# The monitor packet classes were validated at exactly one level: the monitor
# FUB (val/amba/test_axi4_master_rd_mon_fault_classes.py), which drives
# cfg_timeout_cycles / cfg_*_enable straight at the wrapper's ports. Above that,
# nothing checked that a NAMED REGISTER FIELD reaches the port it is supposed to
# drive. Grepping all of stream's dv/ for RDMON_TIMEOUT / WRMON_TIMEOUT /
# DAXMON_TIMEOUT returned nothing at all.
#
# STREAM was believed to cover this because it does test a "timeout" -- but that
# is SCHED_TIMEOUT_CYCLES, the scheduler's write-completion watchdog: different
# register, different RTL, different packet. Two mechanisms sharing a word, and
# the shared word hid the gap until silicon.
#
# The gap is not theoretical. Three config-plumbing defects were found by hand
# in this area, every one of them invisible to both the FUB tests and a board
# coverage run:
#   * cfg_compl_enable     was wired to int_cfg_*_mon_enable   (aliased)
#   * cfg_threshold_enable was wired to *_mon_perf_enable      (aliased)
#   * cfg_timeout_cycles   was squashed 16 -> 4 bits in twelve wrappers, so any
#     value >= 16 became 15 and the whole configurable range collapsed
#
# THE SPLIT, and why there are two files
# --------------------------------------
# stream_core has NO APB interface -- its monitor config arrives on direct
# cfg_*_mon_* PORTS; the register block lives one level up in stream_top_ch8.
# So the plumbing is two hops, and each needs its own check:
#
#   THIS FILE (macro):  cfg_* port  ->  packet type on monbus
#                       i.e. is the cone wired to the signal that names it?
#                       (the two aliasing defects lived exactly here)
#
#   test_stream_top_mon_cfg.py:  register field by name -> cfg_* port
#                       i.e. does APB actually reach the port?
#
# Together they span register name -> packet type. Neither half alone would have
# caught both defect classes.
#
# UNITS (the trap that made the board probe silently useless)
# -----------------------------------------------------------
#   *_TIMEOUT.TIMEOUT_CYCLES  counts the monitor's 1 us frequency-invariant tick
#   *_LATENCY_THRESH          counts raw aclk clocks (r_timestamp is per-cycle)
# They are NOT the same unit. At 100 MHz, TIMEOUT=2 means 200 clocks.

import os
import sys

import pytest
import cocotb
from cocotb.triggers import RisingEdge
from cocotb_test.simulator import run

from TBClasses.shared.utilities import get_paths, get_repo_root
from TBClasses.shared.filelist_utils import get_sources_from_filelist

repo_root = get_repo_root()
sys.path.insert(0, repo_root)

from projects.components.dmas.stream.dv.tbclasses.stream_core_tb import StreamCoreTB
from TBClasses.monbus.monbus_types import PktType

STREAM_TEST_SEED = os.environ.get('RANDOM_SEED', '12345')

# aclk is 100 MHz in this TB, so 1 us == 100 clocks.
ACLK_MHZ = 100


# ===========================================================================
# Config helpers -- everything BY NAME, never by offset
# ===========================================================================
# stream_core takes DIRECT cfg ports (no APB at this level).
_CFG_PREFIX = {'RDMON': 'cfg_rdeng_mon', 'WRMON': 'cfg_wreng_mon'}


def _compose(reg_name, **fields):
    """Build a register value from FIELD NAMES using the generated regmap.

    Field positions come from stream_regmap.py, never from a remembered bit
    number. Hand-assembled masks are exactly how the enable-aliasing defects
    survived review: the write looked right and set the wrong bit.
    """
    import importlib.util
    spec = importlib.util.spec_from_file_location(
        'stream_regmap',
        os.path.join(repo_root, 'projects/components/dmas/stream/rtl/stream_regmap.py'))
    m = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(m)
    # Find the register in whichever top-level dict holds it. The generated
    # module currently exposes 'top_block'; searching rather than hardcoding that
    # name means a regenerate that renames the container does not break this.
    reg = None
    for attr in dir(m):
        if attr.startswith('_'):
            continue
        cand = getattr(m, attr)
        if isinstance(cand, dict) and reg_name in cand:
            reg = cand[reg_name]
            break
    if reg is None:
        raise KeyError(f"{reg_name} not found in stream_regmap.py")
    val = 0
    for fname, fval in fields.items():
        if fname not in reg:
            raise KeyError(f"{reg_name} has no field {fname} (has: "
                           f"{[k for k, v in reg.items() if isinstance(v, dict)]})")
        val |= (int(fval) & 1) << int(reg[fname]['offset'])
    return val


# cfg PORT per class, mirroring the register FIELD of the same meaning. The
# pairing is the thing under test at stream_top; here we drive the port.
_CFG_FOR = {
    'timeout':   'timeout_enable',
    'threshold': 'thresh_enable',
    'compl':     'compl_enable',
    'perf':      'perf_enable',
}


def _enable_only(tb, mon, cls=None, also=None):
    """Drive this monitor's cfg enables: master on, one class on (+ any
    prerequisite named in `also`, for classes that are derived from another)."""
    also = also or {}
    pfx = _CFG_PREFIX[mon]
    getattr(tb.dut, f"{pfx}_enable").value = 1
    for name, port in _CFG_FOR.items():
        on = (name == cls) or bool(also.get(name))
        getattr(tb.dut, f"{pfx}_{port}").value = 1 if on else 0


def _allow_all_packet_types(tb, mon):
    """The *_mask ports are DROP masks (1 = drop that type/event). Clear them so
    nothing is discarded at the monbus entry -- a set mask silently drops every
    packet the cone produces, which reads exactly like 'the cone never fired'.
    """
    pfx = _CFG_PREFIX[mon]
    cleared, missing = [], []
    for m in ('pkt_mask', 'err_mask', 'timeout_mask', 'compl_mask',
              'thresh_mask', 'perf_mask', 'addr_mask', 'debug_mask'):
        sig = getattr(tb.dut, f"{pfx}_{m}", None)
        if sig is None:
            missing.append(m)
        else:
            sig.value = 0
            cleared.append(m)
    tb.log.info(f"  masks cleared on {pfx}: {cleared}"
                + (f"  MISSING: {missing}" if missing else ""))
    if missing:
        raise RuntimeError(
            f"{pfx} has no {missing} port(s) -- masks not fully cleared, so a "
            f"'no packets' result could just be a drop mask")


# ===========================================================================
# The test: one packet class per invocation, positive AND negative
# ===========================================================================
@cocotb.test(timeout_time=int(os.environ.get('COCOTB_TIMEOUT_US', '4000')),
             timeout_unit="us")
async def cocotb_test_mon_class(dut):
    """A named enable + threshold must produce its OWN packet type, and only it."""
    mon_class = os.environ.get('MON_CLASS', 'timeout').lower()
    mon = os.environ.get('MON_BLOCK', 'RDMON').upper()

    tb = StreamCoreTB(dut)
    await tb.setup_clocks_and_reset()

    tb.log.info(f"=== monitor class '{mon_class}' on {mon} (by register name) ===")

    # ---- NEGATIVE first: class disabled, its packet must NOT appear ---------
    # Ordering is deliberate. Running the positive case first and then
    # disabling proves nothing: a packet already in flight, or a sticky flag,
    # can carry into the second phase and read as a pass.
    _allow_all_packet_types(tb, mon)
    _enable_only(tb, mon, cls=None)                  # master on, no class cones
    _arm(tb, mon, 'idle')                            # windows closed, thresholds quiet
    await _provoke(tb, mon_class)
    tb.mon_clear()
    await _provoke(tb, mon_class)
    neg = _count(tb, mon, mon_class)
    assert neg == 0, (
        f"{mon_class}: {neg} {_PKT_FOR[mon_class].name} packets with the cone "
        f"DISABLED -- the enable field does not gate this class. "
        f"types seen: {tb.mon_types_seen()}")

    # ---- POSITIVE: enable that class by name, provoke, expect its type ------
    # PERF is a DERIVED class and cannot be tested one-hot. The legacy
    # PktTypePerf packet reports a COUNT OF COMPLETIONS
    # (axi_monitor_reporter_perf.sv:79 -- w_gen_completed requires
    # r_completed_count > 0, and that counter increments off compl_marked_mask).
    # With completions suppressed there is nothing to count and nothing to
    # report, which is correct behaviour that looks identical to a dead cone.
    #
    # So hold the prerequisite ON and vary only PERF_EN. The negative phase
    # already ran with PERF_EN=0 under the same traffic, so the comparison still
    # isolates PERF_EN -- it just does not pretend perf is independent of compl.
    extra = {'compl': 1} if mon_class == 'perf' else {}
    _enable_only(tb, mon, cls=mon_class, also=extra)
    _arm(tb, mon, mon_class)
    tb.mon_clear()
    await _provoke(tb, mon_class)
    sl = getattr(tb, 'monbus_slave', None)
    if sl is not None:
        tb.log.info(f"  BFM: recvQ={len(getattr(sl, '_recvQ', []))} "
                    f"received={len(sl.received_packets)} "
                    f"stats={getattr(sl, 'monbus_stats', {})}")
        tb.log.info(f"  BFM: mon_valid={int(tb.dut.mon_valid.value)} "
                    f"mon_ready={tb.dut.mon_ready.value}")
    tb.log.info(f"  CROSSCHECK len(tb.mon_decoded)={len(tb.mon_decoded)} "
                f"len(sl.received_packets)={len(sl.received_packets) if sl else 'n/a'} "
                f"type0={type(sl.received_packets[0]).__name__ if sl and sl.received_packets else 'n/a'}")
    from collections import Counter
    by_agent = Counter((tb.mon_type_name(p), int(p.agent_id))
                       for p in tb.mon_decoded)
    tb.log.info(f"  captured by (type, agent_id): {dict(by_agent)}")
    pos = _count(tb, mon, mon_class)
    assert pos > 0, (
        f"{mon_class}: cone ENABLED via {mon}_ENABLE.{list(_EN_FIELD[mon_class])[0]} "
        f"and armed, but ZERO {_PKT_FOR[mon_class].name} packets. This is the "
        f"register->port plumbing, not the monitor: val/amba proves the cone "
        f"fires when driven at the wrapper. types seen: {tb.mon_types_seen()}")

    tb.log.info(f"{mon_class} on {mon}: disabled={neg} enabled={pos} PASS")


# ---- per-class enable field, packet type, arming and provocation -----------
_EN_FIELD = {
    'timeout':   {'TIMEOUT_EN': 1},
    'threshold': {'THRESH_EN': 1},
    'compl':     {'COMPL_EN': 1},
    'perf':      {'PERF_EN': 1},
}

# stream_core.sv:150-151. Counting by packet TYPE alone is wrong: the
# descriptor engines (16+) and scheduler groups (48+) put PktTypeCompletion on
# the SAME monbus, so a 'completions must not appear when disabled' check sees
# theirs and fails on a monitor that is behaving perfectly.
_AGENT_FOR = {'RDMON': 9, 'WRMON': 10}

_PKT_FOR = {
    'timeout':   PktType.PktTypeTimeout,
    'threshold': PktType.PktTypeThreshold,
    'compl':     PktType.PktTypeCompletion,
    'perf':      PktType.PktTypePerf,
}



def _count(tb, mon, mon_class):
    """Packets of this class FROM THE MONITOR UNDER TEST.

    Filtering by agent is essential, not tidiness: stream_core arbitrates one
    monbus across the data monitors (9/10), the descriptor engines (16+) and the
    scheduler groups (48+). An unfiltered count of PktTypeCompletion picks up
    the descriptor engines' completions and reports them as the read monitor's.
    """
    want_type = int(_PKT_FOR[mon_class])
    want_agent = _AGENT_FOR[mon]
    return sum(1 for p in tb.mon_decoded
               if int(p.pkt_type) == want_type and int(p.agent_id) == want_agent)


def _arm(tb, mon, mon_class):
    """Drive the threshold cfg port that makes this class fire under stimulus."""
    pfx = _CFG_PREFIX[mon]

    def _set(port, val):
        sig = getattr(tb.dut, f"{pfx}_{port}", None)
        if sig is None:
            raise RuntimeError(
                f"stream_core has no port {pfx}_{port} -- arming silently did "
                f"nothing, so a 'no packets' result would be meaningless")
        sig.value = val
        tb.log.info(f"  armed {pfx}_{port} = {val}")

    if mon_class == 'timeout':
        # MICROSECONDS. 2 us == 200 clocks @100MHz, comfortably under the stall
        # the slow timing profile produces. Keep the latency threshold high so
        # the threshold cone cannot muddy the result.
        _set('timeout_cycles', 2)              # us: 2 us == 200 clk @100MHz
        _set('latency_thresh', 0x0FFF_FFFF)    # clocks: high -> threshold quiet
    elif mon_class == 'threshold':
        # CLOCKS, and low, so ordinary latency crosses it. Timeout pushed far
        # out so a timeout cannot retire the entry before threshold sees it.
        _set('timeout_cycles', 60_000)         # us: far beyond the run
        _set('latency_thresh', 20)             # CLOCKS: low -> trips
    elif mon_class == 'perf':
        # PERF needs its measurement WINDOW armed, which is a separate port from
        # the class enable: cfg_*_mon_perf_enable says "this class may emit",
        # cfg_*_mon_perf_run opens the window that produces something to emit.
        # Setting only the enable yields zero packets and looks exactly like a
        # dead cone.
        _set('timeout_cycles', 60_000)
        _set('latency_thresh', 0x0FFF_FFFF)
        _set('perf_run', 1)
    else:                                   # 'idle' / compl: nothing armed
        _set('timeout_cycles', 60_000)
        _set('latency_thresh', 0x0FFF_FFFF)
        _set('perf_run', 0)


async def _provoke(tb, mon_class):
    """Run traffic shaped to make this class's condition occur."""
    if mon_class in ('timeout', 'threshold'):
        # Stall the RESPONSE channels: a long AR->R gap is what both the timeout
        # window and the latency threshold measure.
        #
        # 'slow_producer' is a REAL profile name. An earlier version passed
        # 'slow', which does not exist -- set_axi_timing_per_channel logs
        # "Unknown AXI timing profile ... using 'fixed'" at WARNING and carries
        # on, so the provocation silently became no provocation. Any new profile
        # name here must appear in AXI_RANDOMIZER_CONFIGS:
        #   backtoback constrained burst_pause fast fixed high_throughput
        #   slow_producer
        # The named profiles are ALL far too gentle for a microsecond window:
        # the harshest, 'slow_producer', is valid_delay 8..20 clocks == 80..200 ns,
        # against a 2 us (2000 ns) timeout. Using it and seeing zero timeouts
        # would say nothing about the RTL -- the stall never reaches the window.
        #
        # Same recipe as the FUB test that PROVES this cone fires
        # (val/amba/test_axi4_master_rd_mon_fault_classes.py:135): a 300-400
        # clock R-channel stall against a 200-clock window.
        tb.set_axi_timing_profile('fast')
        _stall_read_response(tb, lo=300, hi=400)
    else:
        tb.set_axi_timing_profile('fast')

    await _one_transfer(tb, channel=0,
                        desc_count=int(os.environ.get('DESC_COUNT', '2')))
    # Let late packets (threshold/timeout fire after the data phase) reach monbus
    # before the caller counts them.
    await tb.wait_clocks('clk', 2000)



def _stall_read_response(tb, lo, hi):
    """Hold the read-data channel off for lo..hi clocks per beat.

    Bigger than any named profile on purpose -- see the comment at the call
    site. Reaches the responders the same way set_axi_timing_per_channel does:
    self.<x>_axi_slave['interface'].<ch>_channel.randomizer.
    """
    from CocoTBFramework.components.shared.flex_randomizer import FlexRandomizer
    rnd = FlexRandomizer({'valid_delay': ([(lo, hi)], [1.0])})
    applied = []
    for slave_attr, ch_attr in (('rd_axi_slave', 'r_channel'),
                                ('wr_axi_slave', 'b_channel')):
        slave = getattr(tb, slave_attr, None)
        if not slave:
            continue
        ch = getattr(slave['interface'], ch_attr, None)
        if ch is not None:
            ch.randomizer = rnd
            applied.append(f"{slave_attr}.{ch_attr}")
    tb.log.info(f"_stall_read_response: {lo}-{hi} clk on {applied}")
    if not applied:
        raise RuntimeError(
            "no AXI responder reached -- the stall was NOT applied, so a "
            "'no packets' result would be meaningless. Fix the attribute walk "
            "in _stall_read_response before trusting this test.")


async def _one_transfer(tb, channel, desc_count):
    """Build a short descriptor chain and run it -- the house sequence."""
    transfer_beats = 16
    for i in range(desc_count):
        desc_addr = tb.desc_mem_base + i * 64
        src_addr = tb.src_mem_base + i * transfer_beats * tb.data_bytes
        dst_addr = tb.dst_mem_base + i * transfer_beats * tb.data_bytes
        for b in range(transfer_beats):
            tb.write_source_data(src_addr + b * tb.data_bytes,
                                 (0xA5A5_0000 + i * 256 + b), tb.data_bytes)
        is_last = (i == desc_count - 1)
        tb.write_descriptor(addr=desc_addr, src_addr=src_addr, dst_addr=dst_addr,
                            length=transfer_beats,
                            next_ptr=0 if is_last else (desc_addr + 64),
                            priority=0, last=is_last, channel_id=channel)
    await tb.kick_off_channel(channel, tb.desc_mem_base)
    # Completion is NOT asserted here: the stalled profiles used to provoke
    # timeout deliberately make the transfer slow, and whether it finishes is
    # not what this file measures. The packet type is.
    await tb.wait_for_channel_idle(channel, timeout_us=3000)


# ===========================================================================
# Pytest wrappers -- one per (class, monitor block)
# ===========================================================================
def _run_mon_class(request, mon_class, mon_block):
    module, repo_root_path, tests_dir, log_dir, rtl_dict = get_paths({
        'rtl_stream_macro': '../../../../rtl/stream_macro',
        'rtl_stream_fub': '../../../../rtl/stream_fub',
        'rtl_amba': '../../../../../rtl/amba',
    })

    verilog_sources, includes = get_sources_from_filelist(
        repo_root=repo_root_path,
        filelist_path='projects/components/dmas/stream/rtl/filelists/macro/stream_core.f')

    dut_name = "stream_core"
    rtl_parameters = {
        'NUM_CHANNELS': 4,
        'DATA_WIDTH': 128,
        'AXI_ID_WIDTH': 8,
        'ADDR_WIDTH': 64,
        # Monitors ON: this file exists to test them.
        'USE_AXI_MONITORS': 1,
        # Compile the cones this file asserts on. Mirrors the monitor bitstream's
        # all-except-error flavor.
        'DATA_MON_ENABLE_TIMEOUT_LOGIC': 1,
        'DATA_MON_ENABLE_COMPL_LOGIC': 1,
        'DATA_MON_ENABLE_THRESHOLD_LOGIC': 1,
        'DATA_MON_ENABLE_PERF_LOGIC': 1,
    }

    test_name = f"test_stream_core_mon_{mon_class}_{mon_block.lower()}"
    worker_id = os.environ.get('PYTEST_XDIST_WORKER', '')
    if worker_id:
        test_name = f"{test_name}_{worker_id}"

    log_path = os.path.join(log_dir, f'{test_name}.log')
    sim_build = os.path.join(tests_dir, 'local_sim_build', test_name)
    os.makedirs(sim_build, exist_ok=True)
    os.makedirs(log_dir, exist_ok=True)

    extra_env = {
        'DUT': dut_name,
        'MON_CLASS': mon_class,
        'MON_BLOCK': mon_block,
        'NUM_CHANNELS': '4',
        'DATA_WIDTH': '128',
        'LOG_PATH': log_path,
        'COCOTB_LOG_LEVEL': 'INFO',
        'COCOTB_RESULTS_FILE': os.path.join(log_dir, f'results_{test_name}.xml'),
        'RANDOM_SEED': STREAM_TEST_SEED,
        'COCOTB_RANDOM_SEED': STREAM_TEST_SEED,
    }

    run(
        python_search=[tests_dir],
        verilog_sources=verilog_sources,
        includes=includes,
        toplevel=dut_name,
        module=os.path.splitext(os.path.basename(__file__))[0],
        testcase="cocotb_test_mon_class",
        parameters=rtl_parameters,
        sim_build=sim_build,
        extra_env=extra_env,
        keep_files=True,
        compile_args=["-Wno-fatal", "--timescale", "1ns/1ps",
                      "--unroll-count", "4096", "--unroll-stmts", "20000"],
    )


@pytest.mark.parametrize("mon_block", ["RDMON", "WRMON"])
def test_stream_core_mon_timeout(request, mon_block):
    """TIMEOUT_EN + *_TIMEOUT (microseconds) must yield PktTypeTimeout."""
    _run_mon_class(request, 'timeout', mon_block)


@pytest.mark.parametrize("mon_block", ["RDMON", "WRMON"])
def test_stream_core_mon_threshold(request, mon_block):
    """THRESH_EN + *_LATENCY_THRESH (clocks) must yield PktTypeThreshold."""
    _run_mon_class(request, 'threshold', mon_block)


@pytest.mark.parametrize("mon_block", ["RDMON", "WRMON"])
def test_stream_core_mon_compl(request, mon_block):
    """COMPL_EN must yield PktTypeCompletion -- the field that was ALIASED to
    int_cfg_*_mon_enable, so 'disable completions' silently disabled the whole
    monitor instead."""
    _run_mon_class(request, 'compl', mon_block)


@pytest.mark.parametrize("mon_block", ["RDMON", "WRMON"])
def test_stream_core_mon_perf(request, mon_block):
    """PERF_EN must yield PktTypePerf -- and note THRESH_EN used to be wired to
    this same signal, so the two classes were indistinguishable."""
    _run_mon_class(request, 'perf', mon_block)
