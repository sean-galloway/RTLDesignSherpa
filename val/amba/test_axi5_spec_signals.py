# SPDX-License-Identifier: MIT
# SPDX-FileCopyrightText: 2024-2026 sean galloway
#
# RTL Design Sherpa - Industry-Standard RTL Design and Verification
# https://github.com/sean-galloway/RTLDesignSherpa
#
# Module: test_axi5_spec_signals
# Purpose: Directed pin-level checks of the AXI5 spec signal set (GitHub #102 item 5)
#
# Documentation: docs/markdown/rtl-amba/axi5/README.md
# Subsystem: amba
#
# Author: sean galloway
# Created: 2026-10-12

"""
Directed checks that every rtl/amba/axi5 wrapper carries the IHI 0022 Issue L
signal set for the three groups GitHub #102 item 5 corrected:

- MTE (L A12.2.2, Table A12.9): no RTAGMATCH, no BTAG, no AWTAG (none exist in
  the spec); BTAGMATCH is 2 bits and carries the Table A12.14 encodings
  (0b00 None, 0b01 Separate, 0b10 Fail, 0b11 Pass) end to end.
- Unique ID (L A5.2, Table A5.4): AWIDUNQ/ARIDUNQ on the requests and
  BIDUNQ/RIDUNQ on the responses, carried behind ENABLE_UNIQUE.
- AWAKEUP (L A14.1.1): passed through behind ENABLE_WAKEUP and held while a
  request the wrapper has accepted is still waiting for AxREADY downstream;
  in a _cg wrapper it is an activity term, so it wakes the gated clock with
  no VALID present and the first request after idle is accepted on the
  cycle it is presented.

Pin-level on purpose: the BFM binds by name, so a wrong name or width shows up
here as a missing handle rather than as a silent pass.

REG_LEVEL selects the DUT grid (GATE: two wrappers; FUNC: every wrapper plus
the feature-OFF builds of the four base modules; FULL: FUNC plus a 256-bit
data build). TEST_LEVEL sets the number of randomized passes per check.
"""

import os
import random

import pytest
import cocotb
from cocotb.clock import Clock
from cocotb.triggers import RisingEdge, FallingEdge, ReadOnly, ClockCycles
from cocotb_test.simulator import run

from TBClasses.shared.filelist_utils import get_sources_from_filelist
from TBClasses.shared.utilities import get_paths, sim_build_path

_ITERS = {'gate': 4, 'func': 32, 'full': 256}


def _cfg(dut):
    """Read the role/prefix configuration the pytest wrapper passed."""
    kind = os.environ['SPEC_KIND']          # 'wr' or 'rd'
    role = os.environ['SPEC_ROLE']          # 'master' or 'slave'
    up = 'fub_axi_' if role == 'master' else 's_axi_'
    dn = 'm_axi_' if role == 'master' else 'fub_axi_'
    feats_on = os.environ.get('SPEC_FEATS', '1') == '1'
    iters = _ITERS.get(os.environ.get('TEST_LEVEL', 'func').lower(), 32)
    return kind, up, dn, feats_on, iters


def _sig(dut, name):
    return getattr(dut, name)


def _has(dut, name):
    try:
        getattr(dut, name)
        return True
    except AttributeError:
        return False


async def _reset(dut):
    cocotb.start_soon(Clock(dut.aclk, 10, units="ns").start())
    dut.aresetn.value = 0
    await ClockCycles(dut.aclk, 5)
    dut.aresetn.value = 1
    await ClockCycles(dut.aclk, 2)


def _check_port_shape(dut, kind, up, dn):
    """The spec signal set, by name and width (L Tables A5.4, A12.9, A14.1)."""
    bad = []
    for p in (up, dn):
        # Not AXI5 signals at all: Table A12.9 lists AWTAGOP, ARTAGOP, WTAG,
        # RTAG, WTAGUPDATE, BTAGMATCH, BCOMP -- there is no AWTAG, BTAG or
        # RTAGMATCH, and AxUNIQUE is not the unique-ID indicator.
        for gone in (('awtag', 'btag', 'awunique') if kind == 'wr'
                     else ('rtagmatch', 'arunique')):
            if _has(dut, p + gone):
                bad.append(f"non-spec port {p + gone} still present")
        need = (('awidunq', 'bidunq', 'btagmatch', 'awtagop', 'wtag',
                 'wtagupdate', 'awakeup') if kind == 'wr'
                else ('aridunq', 'ridunq', 'rtag', 'artagop', 'awakeup'))
        for n in need:
            if not _has(dut, p + n):
                bad.append(f"spec port {p + n} missing")
    if kind == 'wr':
        for p in (up, dn):
            if _has(dut, p + 'btagmatch') and len(_sig(dut, p + 'btagmatch')) != 2:
                bad.append(f"{p}btagmatch is {len(_sig(dut, p + 'btagmatch'))} "
                           f"bits; Table A12.9 makes BTAGMATCH 2 bits")
    assert not bad, "AXI5 port set does not match IHI 0022L:\n  " + "\n  ".join(bad)


async def _wait_handshake(dut, valid, ready, limit=200):
    for _ in range(limit):
        await RisingEdge(dut.aclk)
        if int(valid.value) and int(ready.value):
            return
    raise AssertionError(f"no handshake on {valid._name} within {limit} cycles")


async def _req_passthrough(dut, kind, up, dn, feats_on, rng):
    ch = 'aw' if kind == 'wr' else 'ar'
    val = rng.randint(0, 1)
    tagop = rng.randint(0, 3)
    _sig(dut, f'{up}{ch}id').value = rng.randint(0, 15)
    _sig(dut, f'{up}{ch}idunq').value = val
    _sig(dut, f'{up}{ch}tagop').value = tagop
    _sig(dut, f'{dn}{ch}ready').value = 1
    _sig(dut, f'{up}{ch}valid').value = 1
    seen = None
    for _ in range(50):
        await RisingEdge(dut.aclk)
        if int(_sig(dut, f'{up}{ch}ready').value):
            _sig(dut, f'{up}{ch}valid').value = 0
        if int(_sig(dut, f'{dn}{ch}valid').value):
            seen = (int(_sig(dut, f'{dn}{ch}idunq').value),
                    int(_sig(dut, f'{dn}{ch}tagop').value))
            break
    _sig(dut, f'{up}{ch}valid').value = 0
    assert seen is not None, f"{ch.upper()} request never reached {dn}"
    exp = (val, tagop) if feats_on else (0, 0)
    assert seen == exp, (f"{ch.upper()}IDUNQ/{ch.upper()}TAGOP {exp} driven, "
                         f"{seen} delivered (ENABLE_UNIQUE/ENABLE_MTE="
                         f"{int(feats_on)})")
    await ClockCycles(dut.aclk, 2)


async def _resp_passthrough(dut, kind, up, dn, feats_on, rng):
    ch = 'b' if kind == 'wr' else 'r'
    idunq = rng.randint(0, 1)
    _sig(dut, f'{dn}{ch}id').value = rng.randint(0, 15)
    _sig(dut, f'{dn}{ch}idunq').value = idunq
    if kind == 'wr':
        # Table A12.14: 0b00 None, 0b01 Separate, 0b10 Fail, 0b11 Pass.
        extra_name, extra = 'btagmatch', rng.randint(0, 3)
    else:
        _sig(dut, f'{dn}rlast').value = 1
        extra_name, extra = 'rtag', rng.randint(0, (1 << len(_sig(dut, f'{dn}rtag'))) - 1)
    _sig(dut, f'{dn}{extra_name}').value = extra
    _sig(dut, f'{up}{ch}ready').value = 1
    _sig(dut, f'{dn}{ch}valid').value = 1
    seen = None
    for _ in range(50):
        await RisingEdge(dut.aclk)
        if int(_sig(dut, f'{dn}{ch}ready').value):
            _sig(dut, f'{dn}{ch}valid').value = 0
        if int(_sig(dut, f'{up}{ch}valid').value):
            seen = (int(_sig(dut, f'{up}{ch}idunq').value),
                    int(_sig(dut, f'{up}{extra_name}').value))
            break
    _sig(dut, f'{dn}{ch}valid').value = 0
    assert seen is not None, f"{ch.upper()} response never reached {up}"
    exp = (idunq, extra) if feats_on else (0, 0)
    assert seen == exp, (f"{ch.upper()}IDUNQ/{extra_name.upper()} {exp} driven, "
                         f"{seen} delivered (ENABLE_UNIQUE/ENABLE_MTE="
                         f"{int(feats_on)})")
    await ClockCycles(dut.aclk, 2)


async def _awakeup_hold(dut, kind, up, dn, feats_on, rng):
    """L A14.1.1: AWAKEUP passes through, and once a request is presented
    downstream with AxREADY low it stays asserted until AxREADY -- even after
    the upstream side, whose request the wrapper has already accepted, lets
    its own AWAKEUP fall."""
    ch = 'aw' if kind == 'wr' else 'ar'
    wake_up, wake_dn = _sig(dut, f'{up}awakeup'), _sig(dut, f'{dn}awakeup')
    _sig(dut, f'{dn}{ch}ready').value = 0
    wake_up.value = 1
    await RisingEdge(dut.aclk)
    await ReadOnly()
    got = int(wake_dn.value)
    await FallingEdge(dut.aclk)
    assert got == (1 if feats_on else 0), (
        f"{up}awakeup=1 gave {dn}awakeup={got} (ENABLE_WAKEUP={int(feats_on)})")
    _sig(dut, f'{up}{ch}valid').value = 1
    await _wait_handshake(dut, _sig(dut, f'{up}{ch}valid'), _sig(dut, f'{up}{ch}ready'))
    await FallingEdge(dut.aclk)
    _sig(dut, f'{up}{ch}valid').value = 0
    wake_up.value = 0
    hold = rng.randint(2, 8)
    for cyc in range(hold):
        await RisingEdge(dut.aclk)
        await ReadOnly()
        if int(_sig(dut, f'{dn}{ch}valid').value):
            assert int(wake_dn.value) == (1 if feats_on else 0), (
                f"{dn}awakeup fell at cycle {cyc} while {dn}{ch}valid was "
                f"waiting on {ch}ready; A14.1.1 requires it held until "
                f"{ch.upper()}READY")
    await FallingEdge(dut.aclk)
    _sig(dut, f'{dn}{ch}ready').value = 1
    await ClockCycles(dut.aclk, 10)
    await ReadOnly()
    assert int(wake_dn.value) == 0, (
        f"{dn}awakeup still high with nothing pending and {up}awakeup low")
    await FallingEdge(dut.aclk)


@cocotb.test(timeout_time=5, timeout_unit="ms")
async def cocotb_test_spec_signals(dut):
    """Port shape, IDUNQ/BTAGMATCH/RTAG passthrough, AWAKEUP hold."""
    kind, up, dn, feats_on, iters = _cfg(dut)
    _check_port_shape(dut, kind, up, dn)
    rng = random.Random(int(os.environ.get('SEED', '1')))
    if _has(dut, 'cfg_cg_enable'):
        dut.cfg_cg_enable.value = 0
    await _reset(dut)
    for _ in range(iters):
        await _req_passthrough(dut, kind, up, dn, feats_on, rng)
        await _resp_passthrough(dut, kind, up, dn, feats_on, rng)
    for _ in range(max(1, iters // 4)):
        await _awakeup_hold(dut, kind, up, dn, feats_on, rng)


@cocotb.test(timeout_time=5, timeout_unit="ms")
async def cocotb_test_cg_awakeup_wake(dut):
    """A _cg wrapper wakes its gated clock on AWAKEUP with no VALID present,
    so a request presented after the wake is accepted on the same cycle.

    The negative control holds the wrapper idle with AWAKEUP low and checks it
    STAYS gated, so the wake is attributable to AWAKEUP and nothing else.
    """
    kind, up, dn, feats_on, iters = _cfg(dut)
    ch = 'aw' if kind == 'wr' else 'ar'
    assert _has(dut, f'{up}awakeup'), (
        f"{up}awakeup missing: a _cg wrapper with no AWAKEUP input can only "
        f"wake on an observed VALID (IHI 0022L A14.1.1)")
    dut.cfg_cg_enable.value = 1
    dut.cfg_cg_idle_count.value = 2
    await _reset(dut)
    wake = _sig(dut, f'{up}awakeup')
    valid, ready = _sig(dut, f'{up}{ch}valid'), _sig(dut, f'{up}{ch}ready')
    _sig(dut, f'{dn}{ch}ready').value = 1
    rng = random.Random(int(os.environ.get('SEED', '1')))

    for it in range(max(2, iters // 4)):
        wake.value = 0
        valid.value = 0
        for _ in range(64):
            await RisingEdge(dut.aclk)
            if int(dut.cg_gating.value):
                break
        assert int(dut.cg_gating.value), "wrapper never gated while idle"
        # Negative control: idle, AWAKEUP low -> must stay gated.
        for _ in range(rng.randint(4, 12)):
            await RisingEdge(dut.aclk)
            assert int(dut.cg_gating.value), "woke with no activity at all"
        await FallingEdge(dut.aclk)
        wake.value = 1
        woke_after = None
        for cyc in range(8):
            await RisingEdge(dut.aclk)
            await ReadOnly()
            if not int(dut.cg_gating.value):
                woke_after = cyc
                break
        assert woke_after is not None, (
            "AWAKEUP asserted with no VALID did not wake the gated clock "
            "within 8 cycles; it must be counted as activity")
        await FallingEdge(dut.aclk)
        # The request follows AWAKEUP (A14.1.1 recommends at least a cycle):
        # it must be accepted on the cycle it is presented.
        valid.value = 1
        await ReadOnly()
        assert int(ready.value), (
            f"{up}{ch}ready low on the first cycle of a request presented "
            f"after AWAKEUP woke the clock (iteration {it})")
        await RisingEdge(dut.aclk)
        await FallingEdge(dut.aclk)
        valid.value = 0
        wake.value = 0
        await ClockCycles(dut.aclk, 8)


# -----------------------------------------------------------------------------
# pytest wrapper
# -----------------------------------------------------------------------------

_FLAVOURS = ('', '_cg', '_mon', '_mon_cg', '_monlite', '_monlite_cg')
_BASES = (('master', 'wr'), ('master', 'rd'), ('slave', 'wr'), ('slave', 'rd'))


def _dut_name(role, kind, flav):
    return f"axi5_{role}_{kind}{flav}"


def generate_params():
    reg_level = os.environ.get('REG_LEVEL', 'FUNC').upper()
    if reg_level == 'GATE':
        return [('master', 'wr', '', 1, 32, 'gate'),
                ('slave', 'rd', '_cg', 1, 32, 'gate')]
    params = [(r, k, f, 1, 32, 'func') for (r, k) in _BASES for f in _FLAVOURS]
    # Feature-OFF builds: every optional output must tie to 0.
    params += [(r, k, '', 0, 32, 'func') for (r, k) in _BASES]
    if reg_level == 'FULL':
        params = [p[:5] + ('full',) for p in params]
        params += [(r, k, '', 1, 256, 'full') for (r, k) in _BASES]
    return params


@pytest.mark.parametrize("role, kind, flav, feats, data_width, test_level",
                         generate_params())
def test_axi5_spec_signals(role, kind, flav, feats, data_width, test_level):
    module, repo_root, tests_dir, log_dir, rtl_dict = get_paths({
        'rtl_cmn': 'rtl/common',
    })
    dut_name = _dut_name(role, kind, flav)
    reg_level = os.environ.get('REG_LEVEL', 'FUNC').upper()
    worker_id = os.environ.get('PYTEST_XDIST_WORKER', 'gw0')
    test_name = (f"test_{worker_id}_axi5_spec_{dut_name}_f{feats}_d{data_width}_"
                 f"{test_level}_{reg_level}")
    sim_build = sim_build_path(tests_dir, test_name)
    os.makedirs(sim_build, exist_ok=True)
    os.makedirs(log_dir, exist_ok=True)

    verilog_sources, includes = get_sources_from_filelist(
        repo_root=repo_root, module=dut_name)

    parameters = {'AXI_DATA_WIDTH': str(data_width)}
    if not feats:
        parameters.update({'ENABLE_UNIQUE': '0', 'ENABLE_MTE': '0',
                           'ENABLE_WAKEUP': '0'})

    testcases = ['cocotb_test_spec_signals']
    if flav.endswith('_cg'):
        testcases.append('cocotb_test_cg_awakeup_wake')

    run(
        python_search=[tests_dir],
        verilog_sources=verilog_sources,
        includes=includes + [rtl_dict['rtl_cmn'], sim_build],
        toplevel=dut_name,
        module=module,
        parameters=parameters,
        sim_build=sim_build,
        extra_env={
            # Selection via the raw filter: the repo conftest anchors
            # testcase= as ONE exact name, so a list cannot go through it.
            'COCOTB_TEST_FILTER': r'\b(?:' + '|'.join(testcases) + ')$',
            'SPEC_KIND': kind,
            'SPEC_ROLE': role,
            'SPEC_FEATS': str(feats),
            'TEST_LEVEL': test_level,
            'SEED': os.environ.get('SEED', str(random.randint(0, 100000))),
            'COCOTB_LOG_LEVEL': 'INFO',
            'LOG_PATH': os.path.join(log_dir, f'{test_name}.log'),
            'COCOTB_RESULTS_FILE': os.path.join(log_dir, f'results_{test_name}.xml'),
        },
        compile_args=[
            "-Wall", "-Wno-SYNCASYNCNET", "-Wno-UNUSED", "-Wno-DECLFILENAME",
            "-Wno-PINMISSING", "-Wno-UNDRIVEN", "-Wno-WIDTHEXPAND",
            "-Wno-WIDTHTRUNC", "-Wno-SELRANGE", "-Wno-CASEINCOMPLETE",
            "-Wno-TIMESCALEMOD",
        ],
        keep_files=True,
        simulator="verilator",
    )
