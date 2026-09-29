# SPDX-License-Identifier: MIT
# SPDX-FileCopyrightText: 2026 sean galloway
"""Component-level test for axis4_intf_observer.

Same shape as test_axi4_intf_observer.py, because the block is the same shape:
one obs_regs window, one monbus egress, one telemetry select/data pair. What is
asserted here that the AXI test cannot:

  1. OBS_CAPS0[5:0] pairs bit-for-bit with MON_CTRL[5:0], but the CLASS each
     bit names is AXIS (Credit/Stream/Channel where AXI has
     Threshold/Perf/Debug). Software reads CAPS to decide what a silent cone
     means, so the mapping is asserted against the build parameters.
  2. The AXIS-native counters (METRIC 11..16: bytes, beats, packets, and the
     tap's own packet and drop counts) must agree with the stimulus EXACTLY --
     not merely be non-zero -- and the tap must agree with the meter.
  3. Every PROTOCOL_AXIS packet class the block can emit comes out with the
     event code the header table promises, decoded by the SHARED monbus
     decoder. There is no AXIS monitor in rtl/amba to have been tested
     elsewhere; this tap has no other DV.
"""

import hashlib
import os
import sys

import pytest
import cocotb
from cocotb_test.simulator import run

from TBClasses.shared.utilities import get_paths, get_repo_root, sim_build_path
from TBClasses.shared.filelist_utils import get_sources_from_filelist
from TBClasses.shared.test_levels import current_level, level_env, reg_level_grid

repo_root = get_repo_root()
sys.path.insert(0, repo_root)

from projects.components.utility_ip.misc.dv.tbclasses.axis4_intf_observer_tb import AXIS4IntfObserverTB  # noqa: E402
from TBClasses.monbus.monbus_types import AXISErrorCode  # noqa: E402

# monitor_amba4_pkg event codes this block emits, by class. The Python
# decoder carries AXISErrorCode; the other five AXIS classes are asserted
# against the package's numbering here so a renumbering breaks this test
# rather than silently reinterpreting a packet.
AXIS_TIMEOUT_HANDSHAKE = 0x0
AXIS_TIMEOUT_PACKET = 0x2
AXIS_COMPL_STREAM_END = 0x0
AXIS_CREDIT_BACKPRESSURE = 0x5
AXIS_CHAN_ID_CHANGE = 0x5
AXIS_CHAN_DEST_CHANGE = 0x6
AXIS_STREAM_START = 0x0
AXIS_STREAM_PAUSE = 0x2
AXIS_STREAM_RESUME = 0x3

# OBS_STAT_SEL.METRIC ids, per the module's telemetry mux
M_PRODUCTIVE, M_BACKPRESSURE, M_STARVATION, M_IDLE = 0, 1, 2, 3
M_BYTES_LO, M_BYTES_HI, M_BEATS, M_PACKETS = 11, 12, 13, 14
M_TAP_DROPPED, M_TAP_PACKETS = 15, 16


def _p(name, default):
    return int(os.environ.get(name, default))


async def _arm(tb):
    """Flush every record immediately and open the dump window."""
    await tb.start_egress_sink()
    await tb.write_reg("OBS_CTRL", 0)
    await tb.write_reg("OBS_BASE_ADDR", 0x0000_0000)
    await tb.write_reg("OBS_LIMIT_ADDR", 0x0000_FFFF)


@cocotb.test(timeout_time=200, timeout_unit="us")
async def cocotb_test_observer_regs(dut):
    """Capability reporting, reset values, config round-trip."""
    _lvl = current_level()
    tb = AXIS4IntfObserverTB(dut)
    await tb.setup_clocks_and_reset()

    base = await tb.read_reg("OBS_BASE_ADDR")
    assert base == 0x0004_0000, (
        f"OBS_BASE_ADDR reads 0x{base:08X}, expected its reset 0x00040000: the "
        f"observer APB window is not responding")

    caps0 = await tb.read_reg("OBS_CAPS0")
    caps1 = await tb.read_reg("OBS_CAPS1")
    caps2 = await tb.read_reg("OBS_CAPS2")
    tb.log.info(f"caps0=0x{caps0:08X} caps1=0x{caps1:08X} caps2=0x{caps2:08X}")

    exp = {"ERROR": (0, _p("P_TAP_ERROR", 0)), "TIMEOUT": (1, _p("P_TAP_TIMEOUT", 0)),
           "COMPL": (2, _p("P_TAP_COMPL", 0)), "CREDIT": (3, _p("P_TAP_CREDIT", 0)),
           "STREAM": (4, _p("P_TAP_STREAM", 0)), "CHANNEL": (5, _p("P_TAP_CHANNEL", 0)),
           "MON_TAPS": (6, _p("P_MON_TAPS", 1))}
    for name, (bit, want) in exp.items():
        got = (caps0 >> bit) & 1
        assert got == want, (
            f"OBS_CAPS0[{bit}] ({name}_CONE)={got} but the build set {want}. A "
            f"capability bit that disagrees with its parameter is a confident "
            f"wrong answer -- software reads it to tell 'quiet' from 'not built'.")
    assert (caps0 >> 12) & 0xF == 0, "a stream has no address ranges; N_ADDR_RANGES must read 0"
    assert (caps0 >> 10) & 1 == 0, "ID_SLICE is not offered on the AXIS observer"
    assert caps1 & 0xFF == _p("P_NUM_PORTS", 1), "OBS_CAPS1 port count disagrees with the build"
    assert (caps1 >> 8) & 0xFF == 0, "OBS_CAPS1 NUM_WR_PORTS byte must read 0 on a one-direction bus"
    assert (caps1 >> 16) & 0xFF == _p("P_NUM_CHANNELS", 1), "OBS_CAPS1 NUM_CHANNELS disagrees"
    assert caps2 & 0xFFFF == _p("P_DATA_WIDTH", 64), (
        f"OBS_CAPS2[15:0] must carry DATA_WIDTH (got {caps2 & 0xFFFF}); software "
        f"needs it to turn the meter's byte count into a bandwidth")

    mon_ctrl = await tb.read_reg("MON_CTRL")
    assert mon_ctrl & 0x7 == 0x7, "MON_CTRL ERROR/TIMEOUT/COMPL_EN must reset 1 (shared map)"
    assert (mon_ctrl >> 7) & 1 == 1, "MON_CTRL.MONITOR_EN must reset 1"
    tmo = await tb.read_reg("MON_TIMEOUT")
    assert tmo & 0xFFFF == 1024, f"MON_TIMEOUT reset {tmo & 0xFFFF} != 1024"

    if _lvl == "gate":
        tb.log.info("gate: capability contract + reset values only")
        return

    for name, value in (("MON_CTRL", 0x0000_00FF), ("MON_TIMEOUT", 0x0000_0020),
                        ("MON_LATENCY", 0x1234_5678), ("AXIS_PKT_MASK", 0x00FF_0080),
                        ("AXIS_MASK1", 0xAAAA_5555), ("OBS_BASE_ADDR", 0x0002_0000),
                        ("OBS_LIMIT_ADDR", 0x0002_FFFF)):
        await tb.write_reg(name, value)
        got = await tb.read_reg(name)
        assert got == value, f"{name} round-trip: wrote 0x{value:08X}, read 0x{got:08X}"

    if _lvl != "full":
        return
    await tb.write_reg("OBS_CAPS0", 0xFFFF_FFFF)
    assert await tb.read_reg("OBS_CAPS0") == caps0, "OBS_CAPS0 must be read-only"
    tb.log.info("observer register layer OK")


@cocotb.test(timeout_time=500, timeout_unit="us")
async def cocotb_test_observer_traffic(dut):
    """Meters and tap counters must agree with the stimulus EXACTLY."""
    tb = AXIS4IntfObserverTB(dut)
    await tb.setup_clocks_and_reset()
    await _arm(tb)
    caps0 = await tb.read_reg("OBS_CAPS0")

    n_pkts = {'gate': 4, 'func': 8, 'full': 24}[current_level()]
    beats = 4
    for i in range(n_pkts):
        await tb.send_packet(beats=beats, tid=i % 2, tdest=0, seed=i)
    await tb.wait_clocks("aclk", 300)

    prod = await tb.read_stat(metric=M_PRODUCTIVE)
    got_beats = await tb.read_stat(metric=M_BEATS)
    got_pkts = await tb.read_stat(metric=M_PACKETS)
    got_bytes = await tb.read_stat(metric=M_BYTES_LO)
    tap_pkts = await tb.read_stat(metric=M_TAP_PACKETS)
    tap_drop = await tb.read_stat(metric=M_TAP_DROPPED)
    tb.log.info(f"meter: productive={prod} beats={got_beats} packets={got_pkts} "
                f"bytes={got_bytes}; tap: packets={tap_pkts} dropped={tap_drop}")

    assert got_beats == n_pkts * beats, (
        f"meter beats={got_beats}, drove {n_pkts * beats}: the meter is not on the wire")
    assert got_pkts == n_pkts, f"meter packets={got_pkts}, drove {n_pkts}"
    assert got_bytes == n_pkts * beats * (tb.data_width // 8), (
        f"meter bytes={got_bytes}, all-ones strobes on {n_pkts * beats} beats of "
        f"{tb.data_width // 8} bytes should give {n_pkts * beats * (tb.data_width // 8)}")
    assert prod == got_beats, (
        f"productive cycles={prod} != beats={got_beats}: with an always-ready sink "
        f"every productive cycle is exactly one beat")
    # Per-channel buckets: tid alternated 0/1, so each channel saw half.
    ch0 = await tb.read_stat(metric=4, channel=0)
    ch1 = await tb.read_stat(metric=4, channel=1)
    assert ch0 + ch1 == prod and ch0 == ch1, (
        f"per-tid buckets ch0={ch0} ch1={ch1} do not split the {prod} productive cycles evenly")

    if (caps0 >> 6) & 1:
        assert tap_pkts == n_pkts, (
            f"tap closed {tap_pkts} packets, the meter counted {got_pkts}: the "
            f"tap and the meter disagree about the same wire")
        assert tap_drop == 0, f"tap dropped {tap_drop} events on an unloaded monbus"
        if (caps0 >> 2) & 1:
            assert tb.egress_beats > 0, (
                "COMPL cone built and packets completed, but the monbus group "
                "emitted nothing")
    # The write side does not exist here and must read 0, not alias the read side.
    assert await tb.read_stat(metric=M_BEATS, is_write=1) == 0, (
        "IS_WRITE=1 must read 0 on a one-direction bus")
    tb.log.info("observer traffic path OK")


@cocotb.test(timeout_time=2, timeout_unit="ms")
async def cocotb_test_observer_packet_coverage(dut):
    """Completion per packet, and both injectable errors, by event code."""
    tb = AXIS4IntfObserverTB(dut)
    await tb.setup_clocks_and_reset()
    await _arm(tb)
    caps0 = await tb.read_reg("OBS_CAPS0")
    built_err, built_compl = caps0 & 1, (caps0 >> 2) & 1

    n_pkts = {'gate': 2, 'func': 4, 'full': 8}[current_level()]
    for i in range(n_pkts):
        await tb.send_packet(beats=3, tid=i, tdest=i & 1, seed=i)
        await tb.wait_clocks("aclk", 20)
    await tb.wait_clocks("aclk", 300)
    clean = tb.log_tally("clean traffic")
    if built_compl:
        n_compl = clean.get(("Completion", AXIS_COMPL_STREAM_END), 0)
        assert n_compl == n_pkts, (
            f"{n_pkts} packets closed with TLAST, {n_compl} Completion/STREAM_END "
            f"packets came out. Tally: {clean}")
    assert "Error" not in tb.types_seen(), f"clean traffic raised an Error: {clean}"

    # A beat with no payload byte, then TVALID withdrawn before the handshake.
    await tb.send_beat(last=1, strb=0)
    await tb.wait_clocks("aclk", 40)
    await tb.inject_valid_drop()
    await tb.wait_clocks("aclk", 300)
    injected = tb.log_tally("after error injection")
    if built_err:
        errs = tb.codes_seen("Error")
        for want in (int(AXISErrorCode.AXIS_ERR_STRB_INVALID),
                     int(AXISErrorCode.AXIS_ERR_VALID_TIMING)):
            assert want in errs, (
                f"injected {AXISErrorCode(want).name}, never reported; Error codes "
                f"seen: {sorted(errs)}. Tally: {injected}")
    tb.check_record_framing()


@cocotb.test(timeout_time=4, timeout_unit="ms")
async def cocotb_test_observer_all_classes(dut):
    """Every PROTOCOL_AXIS class, on a build with every cone, by event code."""
    tb = AXIS4IntfObserverTB(dut)
    await tb.setup_clocks_and_reset()
    await _arm(tb)
    caps0 = await tb.read_reg("OBS_CAPS0")

    # every runtime cone on; MON_TIMEOUT in MICROSECONDS (100 cycles each at
    # the 100 MHz this is built for); MON_LATENCY is the stall length in
    # cycles above which Credit/BACKPRESSURE fires
    await tb.write_reg("MON_CTRL", 0xFF)
    await tb.write_reg("MON_TIMEOUT", 2)
    await tb.write_reg("MON_LATENCY", 16)
    tmo_wait = 350          # > 2 us + one tick of phase

    n = {'gate': 2, 'func': 4, 'full': 8}[current_level()]
    # Completion + Stream/START: clean packets
    for i in range(n):
        await tb.send_packet(beats=3, tid=i % 2, seed=i)
        await tb.wait_clocks("aclk", 10)
    # Stream/PAUSE + RESUME: a bubble inside a packet
    await tb.send_packet(beats=2, tid=0, gap=12)
    # Channel/ID_CHANGE and DEST_CHANGE: tid / tdest move mid-packet, each on
    # its own NON-last beat. On a TLAST beat Completion outranks Channel and
    # the change would be a counted loser, not a packet.
    await tb.send_beat(last=0, tid=1, tdest=0)
    await tb.send_beat(last=0, tid=2, tdest=0)
    await tb.send_beat(last=0, tid=2, tdest=3)
    await tb.send_beat(last=1, tid=2, tdest=3)
    await tb.wait_clocks("aclk", 10)
    # Credit/BACKPRESSURE then Timeout/HANDSHAKE: one long stall
    await tb.stalled_beat(stall_cycles=tmo_wait, last=1, tid=0)
    # Timeout/PACKET: a packet left open with nothing following
    await tb.send_beat(last=0, tid=0)
    await tb.wait_clocks("aclk", tmo_wait)
    await tb.send_beat(last=1, tid=0)
    # Errors
    await tb.send_beat(last=1, strb=0)
    await tb.wait_clocks("aclk", 20)
    await tb.inject_valid_drop()
    await tb.wait_clocks("aclk", 400)

    tally = tb.log_tally("all classes")
    seen = tb.types_seen()
    tb.check_record_framing()

    want = {"Error": caps0 & 1, "Timeout": (caps0 >> 1) & 1, "Completion": (caps0 >> 2) & 1,
            "Credit": (caps0 >> 3) & 1, "Stream": (caps0 >> 4) & 1, "Channel": (caps0 >> 5) & 1}
    missing = [k for k, built in want.items() if built and k not in seen]
    assert not missing, (
        f"cones built but these classes never came out: {missing}. Tally: {tally}")

    expect_codes = {
        "Error": {int(AXISErrorCode.AXIS_ERR_STRB_INVALID), int(AXISErrorCode.AXIS_ERR_VALID_TIMING)},
        "Timeout": {AXIS_TIMEOUT_HANDSHAKE, AXIS_TIMEOUT_PACKET},
        "Completion": {AXIS_COMPL_STREAM_END},
        "Credit": {AXIS_CREDIT_BACKPRESSURE},
        "Channel": {AXIS_CHAN_ID_CHANGE, AXIS_CHAN_DEST_CHANGE},
        "Stream": {AXIS_STREAM_START, AXIS_STREAM_PAUSE, AXIS_STREAM_RESUME},
    }
    for cls, codes in expect_codes.items():
        if not want[cls]:
            continue
        got = tb.codes_seen(cls)
        assert codes <= got, (
            f"{cls}: stimulus for codes {sorted(codes)} was driven, saw {sorted(got)}. "
            f"Tally: {tally}")
    # Every packet must be PROTOCOL_AXIS: the decoder's protocol field is the
    # group filter's routing key, so a wrong value silently misroutes.
    protos = {int(pk.protocol) for pk in tb.packets}
    assert protos == {1}, f"expected every packet PROTOCOL_AXIS (1); saw protocols {sorted(protos)}"
    tap_drop = await tb.read_stat(metric=M_TAP_DROPPED)
    tb.log.info(f"classes seen={sorted(seen)}; tap dropped={tap_drop} (simultaneous losers)")


def _run_observer(request, params, testcase="cocotb_test_observer_regs", test_level="gate"):
    dut_name = 'axis4_intf_observer'
    module, repo_root_, tests_dir, log_dir, rtl_dict = get_paths({
        'misc_rtl': '../../../rtl',
    })
    verilog_sources, includes = get_sources_from_filelist(
        repo_root=repo_root_,
        filelist_path=f'projects/components/utility-ip/misc/rtl/filelists/{dut_name}.f')

    # Build key = toplevel + parameters + xdist worker (see the AXI observer
    # test for why testcase/level are NOT part of it).
    p_digest = hashlib.md5(repr(sorted(params.items())).encode()).hexdigest()[:6]
    worker = os.environ.get('PYTEST_XDIST_WORKER', '')
    sim_build = sim_build_path(
        tests_dir, f"{dut_name}_p{p_digest}" + (f"_{worker}" if worker else ""))
    tag = f"{dut_name}_{testcase}_{test_level}" + (f"_{worker}" if worker else "")
    os.makedirs(log_dir, exist_ok=True)
    env = os.environ.copy()
    env.update({'LOG_PATH': os.path.join(log_dir, f"{tag}.log"),
                'COCOTB_RESULTS_FILE': os.path.join(log_dir, f"results_{tag}.xml"),
                'COCOTB_LOG_LEVEL': 'INFO'})
    env.update(level_env(test_level))
    env.update({f"P_{k}": str(v) for k, v in {
        'TAP_ERROR': params['TAP_ENABLE_ERROR_LOGIC'],
        'TAP_TIMEOUT': params['TAP_ENABLE_TIMEOUT_LOGIC'],
        'TAP_COMPL': params['TAP_ENABLE_COMPL_LOGIC'],
        'TAP_CREDIT': params.get('TAP_ENABLE_CREDIT_LOGIC', 0),
        'TAP_STREAM': params.get('TAP_ENABLE_STREAM_LOGIC', 0),
        'TAP_CHANNEL': params.get('TAP_ENABLE_CHANNEL_LOGIC', 0),
        'MON_TAPS': params['ENABLE_MON_TAPS'],
        'NUM_PORTS': params['NUM_PORTS'],
        'NUM_CHANNELS': params['NUM_CHANNELS'],
        'DATA_WIDTH': params['DATA_WIDTH'],
    }.items()})

    enable_waves = bool(int(os.environ.get('WAVES', '0')))
    wave_args = (["--trace-fst", "--trace-structs", "--trace-depth", "99"]
                 if enable_waves else [])
    run(
        python_search=[tests_dir],
        verilog_sources=verilog_sources,
        includes=includes,
        toplevel=dut_name,
        module=os.path.splitext(os.path.basename(__file__))[0],
        testcase=testcase,
        parameters=params,
        sim_build=sim_build,
        extra_env=env,
        timescale="1ns/1ps",
        compile_args=["--unroll-count", "16384", "--unroll-stmts", "200000",
                      "-Wno-WIDTHEXPAND", "-Wno-WIDTHTRUNC", "-Wno-SELRANGE",
                      "-Wno-PINMISSING", "-Wno-PINCONNECTEMPTY",
                      # Same waivers as the AXI observer test: the monbus group
                      # and arbiter it shares trip UNOPTFLAT/MULTIDRIVEN on
                      # proven-false-positive paths documented there.
                      "-Wno-UNOPTFLAT", "-Wno-MULTIDRIVEN"] + wave_args,
        waves=enable_waves,
        sim_args=(["--trace", "--trace-structs", "--trace-depth", "99"]
                  if enable_waves else []),
        plus_args=['--trace'] if enable_waves else [],
    )


# The lean build mirrors how a harness would wrap a DMA stream: the three
# classes a perf run wants (errors, timeouts, completions), 2 tid buckets.
_PARAMS = {
    'NUM_PORTS': 1, 'DATA_WIDTH': 64, 'NUM_CHANNELS': 2,
    'ENABLE_MON_TAPS': 1, 'EGRESS_AXIL': 1,
    'TAP_ENABLE_ERROR_LOGIC': 1, 'TAP_ENABLE_TIMEOUT_LOGIC': 1,
    'TAP_ENABLE_COMPL_LOGIC': 1,
}

# Every cone, so the all-classes test can reach each one.
_PARAMS_ALL = dict(_PARAMS, TAP_ENABLE_CREDIT_LOGIC=1, TAP_ENABLE_STREAM_LOGIC=1,
                   TAP_ENABLE_CHANNEL_LOGIC=1)


@pytest.mark.parametrize("test_level", reg_level_grid())
def test_axis4_intf_observer(request, test_level):
    """Register layer: capabilities, reset values, round-trip."""
    _run_observer(request, dict(_PARAMS), test_level=test_level)


@pytest.mark.parametrize("test_level", reg_level_grid())
def test_axis4_intf_observer_traffic(request, test_level):
    """Meters and tap counters against exact stimulus counts."""
    _run_observer(request, dict(_PARAMS), testcase="cocotb_test_observer_traffic",
                  test_level=test_level)


@pytest.mark.parametrize("test_level", reg_level_grid())
def test_axis4_intf_observer_packets(request, test_level):
    """Completion per packet and both injectable errors, by event code."""
    _run_observer(request, dict(_PARAMS), testcase="cocotb_test_observer_packet_coverage",
                  test_level=test_level)


@pytest.mark.parametrize("test_level", reg_level_grid())
def test_axis4_intf_observer_all_classes(request, test_level):
    """Every PROTOCOL_AXIS class on a build with every cone."""
    _run_observer(request, dict(_PARAMS_ALL), testcase="cocotb_test_observer_all_classes",
                  test_level=test_level)
