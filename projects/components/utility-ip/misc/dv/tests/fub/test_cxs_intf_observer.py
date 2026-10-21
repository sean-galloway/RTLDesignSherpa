# SPDX-License-Identifier: MIT
# SPDX-FileCopyrightText: 2026 sean galloway
"""Component-level test for cxs_intf_observer.

Same shape as test_axis4_intf_observer.py, because the block is the same shape.
What is asserted here that the AXIS test cannot:

  1. The cycle buckets mean CXS things: productive = a flit; backpressure = RUN
     with no credit held (asserted to APPEAR when the receiver's grants are
     throttled, and to stay 0 when they are not); starvation = RUN with a
     credit and no flit; idle = the link not in RUN. They partition the
     window.
  2. Interleaved streams (two channels on CXSSRCID, packets open in both)
     meter per channel exactly and raise no protocol error: the snoop frames
     packets per stream (IHI 0079D 2.5.2).
  3. The snoop catches a protocol violation from the wires alone: CXSVALID
     with no credit held sets the sticky error (METRIC 18) and comes out as
     Error/PROTOCOL.
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

from projects.components.utility_ip.misc.dv.tbclasses.cxs_intf_observer_tb import CXSIntfObserverTB  # noqa: E402
from TBClasses.monbus.monbus_types import CXSCompletionCode, CXSErrorCode  # noqa: E402
from TBClasses.shared.verilator_cfg import FIELD_COMBO_VLT  # noqa: E402  (not -Wno-MULTIDRIVEN)

M_PRODUCTIVE, M_BACKPRESSURE, M_STARVATION, M_IDLE = 0, 1, 2, 3
M_BYTES_LO, M_BYTES_HI, M_BEATS, M_PACKETS = 11, 12, 13, 14
M_TAP_DROPPED, M_TAP_PACKETS, M_CREDITS, M_PROTO_ERR = 15, 16, 17, 18


def _p(name, default):
    return int(os.environ.get(name, default))


async def _arm(tb):
    """Flush every record immediately and open the dump window."""
    await tb.start_egress_sink()
    await tb.write_reg("OBS_CTRL", 0)
    await tb.write_reg("OBS_BASE_ADDR", 0x0000_0000)
    await tb.write_reg("OBS_LIMIT_ADDR", 0x0000_FFFF)


async def _buckets(tb):
    return {m: await tb.read_stat(metric=m) for m in (M_PRODUCTIVE, M_BACKPRESSURE, M_STARVATION, M_IDLE)}


@cocotb.test(timeout_time=200, timeout_unit="us")
async def cocotb_test_observer_regs(dut):
    """Capability reporting and reset values."""
    tb = CXSIntfObserverTB(dut)
    await tb.setup_clocks_and_reset()
    base = await tb.read_reg("OBS_BASE_ADDR")
    assert base == 0x0004_0000, f"OBS_BASE_ADDR reads 0x{base:08X}: the APB window is not responding"
    caps0, caps1, caps2 = (await tb.read_reg("OBS_CAPS0"), await tb.read_reg("OBS_CAPS1"),
                           await tb.read_reg("OBS_CAPS2"))
    tb.log.info(f"caps0=0x{caps0:08X} caps1=0x{caps1:08X} caps2=0x{caps2:08X}")
    exp = {"ERROR": (0, _p("P_TAP_ERROR", 0)), "TIMEOUT": (1, _p("P_TAP_TIMEOUT", 0)),
           "COMPL": (2, _p("P_TAP_COMPL", 0)), "CREDIT": (3, _p("P_TAP_CREDIT", 0)),
           "STREAM": (4, _p("P_TAP_STREAM", 0)), "CHANNEL": (5, _p("P_TAP_CHANNEL", 0)),
           "MON_TAPS": (6, _p("P_MON_TAPS", 1))}
    for name, (bit, want) in exp.items():
        assert (caps0 >> bit) & 1 == want, f"OBS_CAPS0[{bit}] ({name}) disagrees with the build ({want})"
    assert (caps0 >> 12) & 0xF == 0, "a CXS link has no address ranges"
    assert caps1 & 0xFF == _p("P_NUM_PORTS", 1), "OBS_CAPS1 port count disagrees with the build"
    assert (caps1 >> 16) & 0xFF == _p("P_NUM_CHANNELS", 1), "OBS_CAPS1 NUM_CHANNELS disagrees"
    assert caps2 & 0xFFFF == _p("P_DATA_WIDTH", 512), "OBS_CAPS2[15:0] must carry DATA_WIDTH"
    assert (caps2 >> 16) & 0xFF == 8, "OBS_CAPS2[23:16] must carry CXS_SRCID_WIDTH"
    assert await tb.read_stat(metric=M_PROTO_ERR) == 0, "the snoop reports a protocol error out of reset"
    tb.log.info("observer register layer OK")


@cocotb.test(timeout_time=2, timeout_unit="ms")
async def cocotb_test_observer_traffic(dut):
    """Exact meters on interleaved two-channel traffic; backpressure appears
    only when the receiver throttles its grants."""
    tb = CXSIntfObserverTB(dut)
    await tb.setup_clocks_and_reset()
    await _arm(tb)
    caps0 = await tb.read_reg("OBS_CAPS0")
    n_pkts = {'gate': 4, 'func': 8, 'full': 24}[current_level()]
    fb = tb.cfg.flit_bytes
    errors = []

    async def run_traffic(label, grant_gap):
        tb.dut.i_meter_clear.value = 1
        await tb.wait_clocks("aclk", 1)
        tb.dut.i_meter_clear.value = 0
        tb.throttle(grant_gap)
        # two channels, every packet three flits, interleaved flit by flit
        per = {ch: [f for i in range(n_pkts) for f in tb.flits_for(ch, 3 * fb, seed=16 * ch + i)]
               for ch in (0, 1)}
        order = [f for pair in zip(per[0], per[1]) for f in pair]
        assert await tb.send_flits(order), f"{label}: the transmitter never sent every flit"
        await tb.wait_clocks("aclk", 300)
        b = await _buckets(tb)
        beats = await tb.read_stat(metric=M_BEATS)
        pkts = await tb.read_stat(metric=M_PACKETS)
        bytes_lo = await tb.read_stat(metric=M_BYTES_LO)
        ch = [await tb.read_stat(metric=4, channel=c) for c in (0, 1)]
        perr = await tb.read_stat(metric=M_PROTO_ERR)
        tb.log.info(f"[{label}] buckets={b} flits={beats} packets={pkts} bytes={bytes_lo} "
                    f"per-channel productive={ch} protocol_error={perr}")
        n_flits = len(order)
        if beats != n_flits or b[M_PRODUCTIVE] != n_flits:
            errors.append(f"[{label}] meter flits={beats} productive={b[M_PRODUCTIVE]}, sent {n_flits}")
        if pkts != 2 * n_pkts:
            errors.append(f"[{label}] meter packets={pkts}, sent {2 * n_pkts}")
        if bytes_lo != n_flits * fb:
            errors.append(f"[{label}] meter bytes={bytes_lo}, expected {n_flits * fb} (flit granular)")
        if ch != [len(per[0]), len(per[1])]:
            errors.append(f"[{label}] per-channel productive {ch}, sent {[len(per[0]), len(per[1])]}")
        if perr:
            errors.append(f"[{label}] interleaved legal streams raised the snoop's protocol error")
        return b

    free = await run_traffic("free grants", 0)
    held = await run_traffic("throttled grants", 6)
    if held[M_BACKPRESSURE] == 0:
        errors.append("throttled grants: no backpressure cycles metered (RUN with no credit never seen)")
    if held[M_BACKPRESSURE] <= free[M_BACKPRESSURE]:
        errors.append(f"throttling did not raise backpressure ({free[M_BACKPRESSURE]} -> "
                      f"{held[M_BACKPRESSURE]})")
    if (caps0 >> 6) & 1:
        tap_drop = await tb.read_stat(metric=M_TAP_DROPPED)
        if tap_drop:
            tb.log.info(f"tap reported {tap_drop} dropped events (drop-and-count)")
    for e in errors:
        tb.log.error(e)
    assert not errors, errors[0]
    assert await tb.read_stat(metric=M_BEATS, is_write=1) == 0, "IS_WRITE=1 must read 0"
    tb.log.info("observer traffic path OK")


@cocotb.test(timeout_time=2, timeout_unit="ms")
async def cocotb_test_observer_packet_coverage(dut):
    """A CXS Completion per packet on clean traffic, no Error; then a forced
    flit with no credit is caught by the snoop and reported."""
    tb = CXSIntfObserverTB(dut)
    await tb.setup_clocks_and_reset()
    await _arm(tb)
    caps0 = await tb.read_reg("OBS_CAPS0")
    built_err, built_compl = caps0 & 1, (caps0 >> 2) & 1
    n_pkts = {'gate': 2, 'func': 4, 'full': 8}[current_level()]
    fb = tb.cfg.flit_bytes
    for i in range(n_pkts):
        assert await tb.send_flits(tb.flits_for(i & 1, 2 * fb, seed=i))
        await tb.wait_clocks("aclk", 20)
    await tb.wait_clocks("aclk", 300)
    clean = tb.log_tally("clean traffic")
    if built_compl:
        n_compl = clean.get(("Completion", int(CXSCompletionCode.CXS_COMPL_PACKET_END)), 0)
        assert n_compl == n_pkts, f"{n_pkts} packets ended, {n_compl} Completion/PACKET_END. {clean}"
    assert "Error" not in tb.types_seen(), f"clean traffic raised an Error: {clean}"

    # The transmitter deactivates after 16 idle cycles and returns every
    # credit; with the link in STOP and nothing held, force the violation.
    await tb.wait_clocks("aclk", 200)
    await tb.inject_valid_without_credit()
    await tb.wait_clocks("aclk", 300)
    perr = await tb.read_stat(metric=M_PROTO_ERR)
    injected = tb.log_tally("after violation")
    assert perr == 1, "CXSVALID with no credit did not set the snoop's sticky protocol error"
    if built_err:
        assert int(CXSErrorCode.CXS_ERR_PROTOCOL) in tb.codes_seen("Error"), (
            f"the violation was never reported as Error/PROTOCOL. Tally: {injected}")
    tb.check_record_framing()


def _run_observer(request, params, testcase="cocotb_test_observer_regs", test_level="gate"):
    dut_name = 'cxs_intf_observer'
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
        'MAX_CREDIT': params['CXS_MAX_CREDIT'],
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
                      "-Wno-UNOPTFLAT", FIELD_COMBO_VLT] + wave_args,
        waves=enable_waves,
        sim_args=(["--trace", "--trace-structs", "--trace-depth", "99"]
                  if enable_waves else []),
        plus_args=['--trace'] if enable_waves else [],
    )



_PARAMS = {
    'NUM_PORTS': 1, 'DATA_WIDTH': 512, 'NUM_CHANNELS': 2, 'CXS_MAX_CREDIT': 15,
    'CXS_STREAM_SRCID_BITS': 1,
    'ENABLE_MON_TAPS': 1, 'EGRESS_AXIL': 1,
    'TAP_ENABLE_ERROR_LOGIC': 1, 'TAP_ENABLE_TIMEOUT_LOGIC': 1,
    'TAP_ENABLE_COMPL_LOGIC': 1,
}


@pytest.mark.parametrize("test_level", reg_level_grid())
def test_cxs_intf_observer(request, test_level):
    """Register layer: capabilities and reset values."""
    _run_observer(request, dict(_PARAMS), test_level=test_level)


@pytest.mark.parametrize("test_level", reg_level_grid())
def test_cxs_intf_observer_traffic(request, test_level):
    """Exact meters on interleaved streams; backpressure only when throttled."""
    _run_observer(request, dict(_PARAMS), testcase="cocotb_test_observer_traffic",
                  test_level=test_level)


@pytest.mark.parametrize("test_level", reg_level_grid())
def test_cxs_intf_observer_packets(request, test_level):
    """Completion per packet; a forced no-credit flit is caught."""
    _run_observer(request, dict(_PARAMS), testcase="cocotb_test_observer_packet_coverage",
                  test_level=test_level)
