#!/usr/bin/env python3
# SPDX-License-Identifier: MIT
# SPDX-FileCopyrightText: 2024-2026 sean galloway
#
# APB5 interface parity and PWAKEUP through a generated crossbar
# (issue #102 items 1 and 7).
#
# No shipped variant enables parity (apbx_xbar_2to2_mixed is APB5 without
# it), so the generator's enable_parity path had no simulation at all. This
# test GENERATES an all-APB5 2x2 crossbar with enable_parity=True into its
# own sim_build directory -- a build artifact, never committed -- and checks
# the generated RTL against IHI 0024E chapter 5:
#
#   - every *CHK output the crossbar drives is ODD parity over its covered
#     signal, one check bit per 8 bits (Table 5-1), sampled under that
#     check's Check Enable term:
#       completer side: PADDRCHK, PCTRLCHK (PPROT+PWRITE), PSELCHK,
#         PENABLECHK, PWDATACHK, PSTRBCHK, PAUSERCHK, PWUSERCHK, PWAKEUPCHK
#       requester side: PRDATACHK, PREADYCHK, PSLVERRCHK, PRUSERCHK,
#         PBUSERCHK
#   - with correct parity driven in, no parity_error_* output fires;
#   - a corrupted PWDATACHK from a requester raises that port's
#     parity_error_wdata, and a corrupted PRDATACHK from a completer raises
#     that port's parity_error_rdata;
#   - PWAKEUP (a Requester output, 3.7.2) from EITHER requester reaches
#     BOTH completers, with PWAKEUPCHK its inversion.
#
# The external requesters/completers are driven directly, as in
# test_apbx_xbar_2to2_mixed.py: the point is to control the check bits
# independently of the payload, including deliberately wrong ones.

import os
import sys

import cocotb
import pytest
from cocotb.clock import Clock
from cocotb.triggers import RisingEdge, ClockCycles, Timer
from cocotb_test.simulator import run

from TBClasses.shared.utilities import get_paths, get_wave_config, sim_build_path
from TBClasses.shared.filelist_utils import get_sources_from_filelist
from TBClasses.shared.test_levels import current_level, level_env, reg_level_grid
from cov_utils.conftest_coverage import get_coverage_compile_args

DUT_NAME = "apbx_xbar_2to2_par5"
AW, DW = 32, 32
S_BASE = (0x1000_0000, 0x1001_0000)   # 64KB windows

# Transfers per requester per completer; the parity checks run on every one.
_ROUNDS = {"gate": 2, "func": 8, "full": 32}[current_level()]


# ---------------------------------------------------------------------------
# Odd parity helpers (IHI 0024E 5.3): payload + check bit hold an odd count
# of ones, so the check bit is the inverted XOR of its group.
# ---------------------------------------------------------------------------
def _xor(v):
    return bin(v).count("1") & 1


def odd_chk(value, width):
    """Check vector for `width` bits of `value`, one bit per 8."""
    chk = 0
    for n in range((width + 7) // 8):
        group = (value >> (8 * n)) & 0xFF
        chk |= (1 ^ _xor(group)) << n
    return chk


def odd_ok(value, width, chk):
    return odd_chk(value, width) == chk


def _v(sig):
    return int(sig.value)


# ---------------------------------------------------------------------------
# Completer model: always ready, correct response parity unless told to
# corrupt PRDATACHK. Checks every request-side check bit it receives.
# ---------------------------------------------------------------------------
async def _completer(dut, s, state):
    p = f"s{s}_apb_"
    sig = lambda n: getattr(dut, p + n)  # noqa: E731
    rdata = 0x5A00_0000 | (s << 16)
    sig("PREADY").value = 1
    sig("PSLVERR").value = 0
    sig("PRUSER").value = s & 1
    sig("PBUSER").value = 1
    sig("PREADYCHK").value = 0            # PREADY=1 -> chk 0
    sig("PSLVERRCHK").value = 1           # PSLVERR=0 -> chk 1
    sig("PRUSERCHK").value = odd_chk(s & 1, 1)
    sig("PBUSERCHK").value = odd_chk(1, 1)
    while True:
        bad = state['corrupt_prdata'][s]
        sig("PRDATA").value = rdata
        sig("PRDATACHK").value = odd_chk(rdata, DW) ^ (0x1 if bad else 0)
        await RisingEdge(dut.pclk)
        if not _v(dut.presetn):
            continue
        errs = state['errs']
        psel = _v(sig("PSEL"))
        # PSELxCHK and PWAKEUPCHK: Check Enable is PRESETn (always checked).
        if not odd_ok(psel, 1, _v(sig("PSELCHK"))):
            errs.append(f"s{s} PSELCHK")
        if not odd_ok(_v(sig("PWAKEUP")), 1, _v(sig("PWAKEUPCHK"))):
            errs.append(f"s{s} PWAKEUPCHK")
        if not psel:
            continue
        state['checked'][s] += 1
        if not odd_ok(_v(sig("PADDR")), AW, _v(sig("PADDRCHK"))):
            errs.append(f"s{s} PADDRCHK")
        ctrl = (_v(sig("PPROT")) << 1) | _v(sig("PWRITE"))
        if not odd_ok(ctrl, 4, _v(sig("PCTRLCHK"))):
            errs.append(f"s{s} PCTRLCHK")
        if not odd_ok(_v(sig("PENABLE")), 1, _v(sig("PENABLECHK"))):
            errs.append(f"s{s} PENABLECHK")
        if not odd_ok(_v(sig("PAUSER")), 1, _v(sig("PAUSERCHK"))):
            errs.append(f"s{s} PAUSERCHK")
        if _v(sig("PWRITE")):
            if not odd_ok(_v(sig("PWDATA")), DW, _v(sig("PWDATACHK"))):
                errs.append(f"s{s} PWDATACHK")
            if not odd_ok(_v(sig("PSTRB")), 4, _v(sig("PSTRBCHK"))):
                errs.append(f"s{s} PSTRBCHK")
            if not odd_ok(_v(sig("PWUSER")), 1, _v(sig("PWUSERCHK"))):
                errs.append(f"s{s} PWUSERCHK")
        if _v(sig("PENABLE")):
            state['beats'][s] += 1
        if _v(getattr(dut, f"s{s}_parity_error_rdata")) and not bad:
            errs.append(f"s{s} parity_error_rdata with clean PRDATACHK")
        if _v(getattr(dut, f"s{s}_parity_error_ctrl")):
            errs.append(f"s{s} parity_error_ctrl with clean response")
        if bad and _v(getattr(dut, f"s{s}_parity_error_rdata")):
            state['rdata_err_seen'][s] = True


# ---------------------------------------------------------------------------
# One requester transfer with correct (or deliberately bad PWDATACHK) parity.
# Checks the response-side check bits at the PREADY edge.
# ---------------------------------------------------------------------------
async def _xfer(dut, m, addr, write, wdata, pauser, pwuser, state,
                bad_pwdatachk=False):
    p = f"m{m}_apb_"
    sig = lambda n: getattr(dut, p + n)  # noqa: E731
    strb = 0xF if write else 0
    sig("PADDR").value = addr
    sig("PADDRCHK").value = odd_chk(addr, AW)
    sig("PWRITE").value = int(write)
    sig("PPROT").value = 0b010
    sig("PCTRLCHK").value = odd_chk((0b010 << 1) | int(write), 4)
    sig("PWDATA").value = wdata
    sig("PWDATACHK").value = odd_chk(wdata, DW) ^ (0x2 if bad_pwdatachk else 0)
    sig("PSTRB").value = strb
    sig("PSTRBCHK").value = odd_chk(strb, 4)
    sig("PAUSER").value = pauser
    sig("PAUSERCHK").value = odd_chk(pauser, 1)
    sig("PWUSER").value = pwuser
    sig("PWUSERCHK").value = odd_chk(pwuser, 1)
    sig("PSEL").value = 1
    sig("PSELCHK").value = 0
    sig("PENABLE").value = 0
    sig("PENABLECHK").value = 1
    await RisingEdge(dut.pclk)
    wdata_err = _v(getattr(dut, f"m{m}_parity_error_wdata"))
    sig("PENABLE").value = 1
    sig("PENABLECHK").value = 0
    got = None
    for _ in range(300):
        await RisingEdge(dut.pclk)
        wdata_err |= _v(getattr(dut, f"m{m}_parity_error_wdata"))
        if _v(getattr(dut, f"m{m}_parity_error_ctrl")):
            state['errs'].append(f"m{m} parity_error_ctrl with clean request")
        # PREADYCHK: Check Enable PSEL & PENABLE
        if not odd_ok(_v(sig("PREADY")), 1, _v(sig("PREADYCHK"))):
            state['errs'].append(f"m{m} PREADYCHK")
        if _v(sig("PREADY")):
            prdata, pruser = _v(sig("PRDATA")), _v(sig("PRUSER"))
            pslverr, pbuser = _v(sig("PSLVERR")), _v(sig("PBUSER"))
            if not odd_ok(pslverr, 1, _v(sig("PSLVERRCHK"))):
                state['errs'].append(f"m{m} PSLVERRCHK")
            if not odd_ok(pbuser, 1, _v(sig("PBUSERCHK"))):
                state['errs'].append(f"m{m} PBUSERCHK")
            if not write:
                if not odd_ok(prdata, DW, _v(sig("PRDATACHK"))):
                    state['errs'].append(f"m{m} PRDATACHK")
                if not odd_ok(pruser, 1, _v(sig("PRUSERCHK"))):
                    state['errs'].append(f"m{m} PRUSERCHK")
            got = dict(prdata=prdata, pslverr=pslverr, pruser=pruser,
                       pbuser=pbuser)
            break
    assert got is not None, f"m{m} transfer to 0x{addr:08X} timed out"
    sig("PSEL").value = 0
    sig("PSELCHK").value = 1
    sig("PENABLE").value = 0
    sig("PENABLECHK").value = 1
    await ClockCycles(dut.pclk, 2)
    got['wdata_err'] = wdata_err
    return got


def _idle_requester(dut, m):
    p = f"m{m}_apb_"
    for n, v in (("PSEL", 0), ("PSELCHK", 1), ("PENABLE", 0),
                 ("PENABLECHK", 1), ("PADDR", 0), ("PADDRCHK", 0xF),
                 ("PWRITE", 0), ("PPROT", 0), ("PCTRLCHK", 1),
                 ("PWDATA", 0), ("PWDATACHK", 0xF), ("PSTRB", 0),
                 ("PSTRBCHK", 1), ("PAUSER", 0), ("PAUSERCHK", 1),
                 ("PWUSER", 0), ("PWUSERCHK", 1), ("PWAKEUP", 0),
                 ("PWAKEUPCHK", 1)):
        getattr(dut, p + n).value = v


async def _set_wake(dut, m, value):
    getattr(dut, f"m{m}_apb_PWAKEUP").value = value
    getattr(dut, f"m{m}_apb_PWAKEUPCHK").value = 1 ^ value
    await Timer(1, units="ns")


@cocotb.test(timeout_time=50, timeout_unit="ms")
async def cocotb_test_parity_and_wake(dut):
    cocotb.start_soon(Clock(dut.pclk, 10, units="ns").start())
    for m in range(2):
        _idle_requester(dut, m)
    state = dict(errs=[], checked=[0, 0], beats=[0, 0],
                 corrupt_prdata=[False, False], rdata_err_seen=[False, False])
    for s in range(2):
        cocotb.start_soon(_completer(dut, s, state))

    dut.presetn.value = 0
    await ClockCycles(dut.pclk, 5)
    dut.presetn.value = 1
    await ClockCycles(dut.pclk, 3)

    # 1. Clean traffic: every pairing, reads and writes, varied payloads.
    n = 0
    for r in range(_ROUNDS):
        for m in range(2):
            for s in range(2):
                wdata = (0x1357_9BDF * (n + 1) + r) & 0xFFFF_FFFF
                addr = S_BASE[s] + ((n * 0x44) & 0xFFFC)
                n += 1
                got = await _xfer(dut, m, addr, write=True, wdata=wdata,
                                  pauser=n & 1, pwuser=(n >> 1) & 1,
                                  state=state)
                assert got['pslverr'] == 0 and not got['wdata_err'], got
                got = await _xfer(dut, m, addr, write=False, wdata=0,
                                  pauser=(n >> 2) & 1, pwuser=0, state=state)
                assert got['prdata'] == (0x5A00_0000 | (s << 16)), got
                assert not got['wdata_err'], got
    assert not state['errs'], f"parity violations: {state['errs'][:10]}"
    assert all(state['beats']), f"a completer saw no access phase: {state}"

    # 2. A requester sends a wrong PWDATACHK: its port flags it.
    got = await _xfer(dut, 1, S_BASE[0] + 0x100, write=True,
                      wdata=0xDEAD_BEEF, pauser=0, pwuser=0, state=state,
                      bad_pwdatachk=True)
    assert got['wdata_err'], "corrupt PWDATACHK on m1 not flagged"
    assert not state['errs'], f"collateral errors: {state['errs'][:10]}"

    # 3. A completer returns a wrong PRDATACHK: its port flags it.
    state['corrupt_prdata'][1] = True
    await RisingEdge(dut.pclk)
    await _xfer(dut, 0, S_BASE[1] + 0x200, write=False, wdata=0,
                pauser=0, pwuser=0, state=state)
    state['corrupt_prdata'][1] = False
    assert state['rdata_err_seen'][1], "corrupt PRDATACHK from s1 not flagged"
    # The crossbar regenerates PRDATACHK toward the requester from the
    # payload, so m0 itself saw CLEAN parity -- the fault stops at s1's port.
    assert not [e for e in state['errs'] if not e.startswith("s1 parity_error_rdata")], \
        f"unexpected errors: {state['errs'][:10]}"
    state['errs'].clear()

    # 4. PWAKEUP from either requester wakes both completers; PWAKEUPCHK is
    #    the inversion (checked continuously by the completer models).
    await ClockCycles(dut.pclk, 4)
    for s in range(2):
        assert _v(getattr(dut, f"s{s}_apb_PWAKEUP")) == 0, f"s{s} awake idle"
    for m in range(2):
        await _set_wake(dut, m, 1)
        for s in range(2):
            assert _v(getattr(dut, f"s{s}_apb_PWAKEUP")) == 1, \
                f"m{m} PWAKEUP not forwarded to s{s}"
            assert _v(getattr(dut, f"s{s}_apb_PWAKEUPCHK")) == 0
        await ClockCycles(dut.pclk, 2)
        await _set_wake(dut, m, 0)
        for s in range(2):
            assert _v(getattr(dut, f"s{s}_apb_PWAKEUP")) == 0, \
                f"s{s} PWAKEUP stuck after m{m} dropped"
            assert _v(getattr(dut, f"s{s}_apb_PWAKEUPCHK")) == 1
    await ClockCycles(dut.pclk, 2)
    assert not state['errs'], f"parity violations: {state['errs'][:10]}"
    dut._log.info(f"{DUT_NAME}: parity + wake OK, checked cycles "
                  f"s0={state['checked'][0]} s1={state['checked'][1]}")


def _generate(out_dir):
    """Emit the parity-enabled variant into the test's own build dir."""
    _, repo_root, _, _, _ = get_paths({})
    gen_dir = os.path.join(repo_root, 'projects/components/fabric-gen-ip/apbx-xbar/bin')
    if gen_dir not in sys.path:
        sys.path.insert(0, gen_dir)
    from apbx_xbar_generator import generate_apbx_xbar
    code = generate_apbx_xbar(
        num_masters=2, num_slaves=2, base_addr=0x1000_0000,
        addr_width=AW, data_width=DW, slave_size=0x10000,
        master_versions=['apb5', 'apb5'], slave_versions=['apb5', 'apb5'],
        name_suffix='_par5', enable_parity=True)
    os.makedirs(out_dir, exist_ok=True)
    path = os.path.join(out_dir, f"{DUT_NAME}.sv")
    with open(path, 'w') as f:
        f.write(code)
    return path


@pytest.mark.parametrize("test_level", reg_level_grid())
def test_apbx_xbar_parity(request, test_level):
    module, repo_root, tests_dir, log_dir, rtl_dict = get_paths({
        'rtl_xbar': 'projects/components/fabric-gen-ip/apbx-xbar/rtl',
    })

    # Compile closure of the shipped mixed variant (apb4 + apb5 boundary IP,
    # arbiters, parity) minus the shipped crossbar itself.
    verilog_sources, includes = get_sources_from_filelist(
        repo_root=repo_root,
        filelist_path='projects/components/fabric-gen-ip/apbx-xbar/rtl/filelists/core/apbx_xbar_2to2_mixed.f'
    )
    verilog_sources = [v for v in verilog_sources
                       if not v.endswith('apbx_xbar_2to2_mixed.sv')]

    worker_id = os.environ.get('PYTEST_XDIST_WORKER', '')
    worker_suffix = f"_{worker_id}" if worker_id else ""
    sim_build_name = f"test_{DUT_NAME}_{test_level}{worker_suffix}"

    log_path = os.path.join(log_dir, f'{sim_build_name}.log')
    results_path = os.path.join(log_dir, f'results_{sim_build_name}.xml')
    sim_build = sim_build_path(tests_dir, sim_build_name)
    os.makedirs(sim_build, exist_ok=True)
    os.makedirs(log_dir, exist_ok=True)
    verilog_sources.append(_generate(os.path.join(sim_build, 'generated')))

    waves = get_wave_config(sim_build)
    extra_args = ['--assert'] + waves['extra_args']
    extra_args.extend(get_coverage_compile_args())

    run(
        python_search=[tests_dir],
        verilog_sources=verilog_sources,
        includes=includes,
        toplevel=DUT_NAME,
        module=module,
        testcase="cocotb_test_parity_and_wake",
        sim_build=sim_build,
        waves=False,
        extra_args=extra_args,
        plus_args=waves['sim_args'],
        extra_env={
            'COCOTB_LOG_LEVEL': 'INFO',
            'LOG_PATH': log_path,
            'COCOTB_RESULTS_FILE': results_path,
            **level_env(test_level),
            **waves['extra_env'],
        },
    )
