# SPDX-License-Identifier: MIT
# SPDX-FileCopyrightText: 2026 sean galloway
#
# Module: test_stream_top_regs
# Purpose: Walk EVERY register in stream_regmap.py -- reset value, write/readback
#          per writable field, read-only fields immovable -- in BOTH monitor
#          configurations.
#
# WHY: if the registers do not work, nothing above them can.
#
# The existing coverage (test_stream_top_advanced.py::cocotb_test_register_access)
# checks a HAND-PICKED list -- VERSION, GLOBAL_CTRL, CHANNEL_ENABLE,
# AXI_XFER_CONFIG, DESCENG_ADDR -- against hardcoded StreamRegisterMap
# constants. The regmap has 139 registers and 86 of them are MONITOR registers,
# so roughly 62% of the address map has never been read or written by a test.
# It also runs at the default 12-bit APB window, which cannot reach the MON
# block at 0x1000+ even in principle.
#
# THE TWO CONFIGURATIONS ARE BOTH REAL BUILDS
# --------------------------------------------
#   USE_AXI_MONITORS=1  build-mon      monitors exist; their registers must work
#   USE_AXI_MONITORS=0  build-perf     monitors do NOT exist
#
# For the second, "the register accepts a write and reads it back" is the WRONG
# answer. Read-back success is the strongest evidence a host has that config
# took effect; returning it for a monitor that was never built is affirmatively
# misleading, and build-perf ships that way today. See [[STREAM-MONREGS]].
#
# So the monitors-absent case asserts the MON window does NOT respond. That is
# expected to FAIL until STREAM-MONREGS lands -- it is the regression gate for
# that fix, and it is marked xfail(strict=False) so the suite stays honest
# without going red for a defect that is already filed.

import os
import sys

import pytest
import cocotb
from cocotb.triggers import ClockCycles
from cocotb_test.simulator import run

from TBClasses.shared.utilities import get_paths, get_repo_root
from TBClasses.shared.filelist_utils import get_sources_from_filelist

repo_root = get_repo_root()
sys.path.insert(0, repo_root)

from projects.components.dmas.stream.dv.tbclasses.stream_core_tb import StreamCoreTB

STREAM_TEST_SEED = os.environ.get('RANDOM_SEED', '12345')

# The APB no-response sentinel. Detect it EXPLICITLY: its bit pattern (0xEF in
# the low byte) satisfies plenty of naive per-bit checks, which is exactly how
# an unreachable register can masquerade as a working one.
NO_RESPONSE = 0xDEADBEEF

# Patterns chosen to catch stuck bits, and deliberately including values > 0xF:
# a field silently truncated to 4 bits (as cfg_timeout_cycles was, in twelve
# wrappers) passes any test that only ever writes small numbers.
PATTERNS = [0x0000_0000, 0xFFFF_FFFF, 0xA5A5_A5A5, 0x5A5A_5A5A, 0x0001_2345]

MON_PREFIXES = ('RDMON', 'WRMON', 'DAXMON', 'MON_')


def _regmap():
    import importlib.util
    spec = importlib.util.spec_from_file_location(
        'stream_regmap',
        os.path.join(repo_root, 'projects/components/dmas/stream/rtl/stream_regmap.py'))
    m = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(m)
    for attr in dir(m):
        if attr.startswith('_'):
            continue
        cand = getattr(m, attr)
        if isinstance(cand, dict) and 'RDMON_ENABLE' in cand:
            return cand
    raise KeyError("no register dict found in stream_regmap.py")


def _is_mon(name):
    return name.startswith(MON_PREFIXES)


def _fields(reg):
    return {k: v for k, v in reg.items() if isinstance(v, dict) and v.get('type') == 'field'}


def _writable_mask(reg):
    """Bit mask of everything software may change, from the FIELD sw attrs.

    Built from the regmap rather than assumed: a register marked rw at the top
    can still contain ro fields, and comparing a full-word readback against the
    full-word write then fails on correct hardware.
    """
    mask = 0
    flds = _fields(reg)
    if not flds:
        return 0xFFFF_FFFF if reg.get('sw') == 'rw' else 0
    for f in flds.values():
        if f.get('sw') != 'rw':
            continue
        off = f.get('offset', '0')
        if ':' in str(off):
            hi, lo = (int(x) for x in str(off).split(':'))
        else:
            hi = lo = int(off)
        mask |= ((1 << (hi - lo + 1)) - 1) << lo
    return mask


def _default(reg):
    try:
        return int(str(reg.get('default', '0')), 0)
    except ValueError:
        return 0


@cocotb.test(timeout_time=4000, timeout_unit="us")
async def cocotb_test_reg_walk(dut):
    """Every register: reset value, writable bits take, read-only bits do not."""
    monitors = os.environ.get('USE_AXI_MONITORS', '1') == '1'

    # apb_addr_width is a CONSTRUCTOR kwarg (default 12) and is NOT read from the
    # environment. At 12 bits every MON address (0x1000+) truncates back into the
    # functional block -- RDMON_ENABLE 0x10E0 -> 0x0E0, WRMON_ENABLE 0x1100 ->
    # 0x100 which is GLOBAL_CTRL -- so the walk would silently rewrite the DMA's
    # control registers while reporting monitor results.
    tb = StreamCoreTB(dut)   # width auto-sized from the register map
    await tb.setup_clocks_and_reset()
    await tb.init_apb_master()

    regs = _regmap()
    fails, checked, skipped = [], 0, 0

    # ---- 1. reset values, before anything is written ------------------------
    for name, reg in sorted(regs.items()):
        if _is_mon(name) and not monitors:
            continue                     # covered by the absence check below
        got = int(await tb.read_reg(name))
        if got == NO_RESPONSE:
            fails.append(f"{name} @ {reg.get('address')}: reset read returned "
                         f"the NO-RESPONSE sentinel -- register unreachable")
            continue

        # Compare ONLY the bits software owns. The RDL `default` is the reset
        # value of a STORAGE element; fields marked sw='r' have no storage and
        # mirror live hardware, so their "default" describes nothing. At reset
        # CHANNEL_IDLE reads 0xF because all four channels ARE idle, and
        # GLOBAL_STATUS reads 1 because the system IS idle -- both correct, both
        # flagged by a naive full-word comparison.
        #
        # NOTE the reg-level sw is not the authority: CHANNEL_IDLE is sw='rw' at
        # register level while every field inside it is sw='r'.
        smask = _writable_mask(reg)
        if smask == 0:
            continue                     # nothing software owns; hw decides
        want = _default(reg) & smask
        if (got & smask) != want:
            fails.append(f"{name} @ {reg.get('address')}: reset value "
                         f"0x{got & smask:08X} != RDL default 0x{want:08X} "
                         f"(sw-owned mask 0x{smask:08X})")
    tb.log.info(f"reset-value sweep done over {len(regs)} registers")

    # ---- 2. write / readback, masked to the writable bits -------------------
    for name, reg in sorted(regs.items()):
        if _is_mon(name) and not monitors:
            continue
        wmask = _writable_mask(reg)
        if wmask == 0:
            # read-only: a write must NOT move it
            before = int(await tb.read_reg(name))
            await tb.write_reg(name, 0xFFFF_FFFF)
            await ClockCycles(dut.aclk, 3)
            after = int(await tb.read_reg(name))
            if after != before:
                fails.append(f"{name}: READ-ONLY but a write changed it "
                             f"0x{before:08X} -> 0x{after:08X}")
            skipped += 1
            continue

        default = _default(reg)
        for pat in PATTERNS:
            await tb.write_reg(name, pat)
            await ClockCycles(dut.aclk, 3)
            got = int(await tb.read_reg(name))
            expect = (pat & wmask) | (default & ~wmask & 0xFFFF_FFFF)
            if got == NO_RESPONSE:
                fails.append(f"{name}: no response after writing 0x{pat:08X}")
                break
            if got != expect:
                fails.append(
                    f"{name} @ {reg.get('address')}: wrote 0x{pat:08X} "
                    f"(wmask 0x{wmask:08X}) read 0x{got:08X}, expected "
                    f"0x{expect:08X}")
                break
            checked += 1
        # leave it at the reset value so later registers see a clean machine
        await tb.write_reg(name, default)

    # ---- 3. monitors ABSENT: the MON window must not answer -----------------
    if not monitors:
        responded = []
        for name, reg in sorted(regs.items()):
            if not _is_mon(name):
                continue
            got = int(await tb.read_reg(name))
            if got != NO_RESPONSE:
                responded.append(f"{name} @ {reg.get('address')} -> 0x{got:08X}")
        if responded:
            fails.append(
                f"USE_AXI_MONITORS=0 but {len(responded)} monitor registers "
                f"still respond, e.g. {responded[:3]}. A host cannot tell a "
                f"configured monitor from an absent one: it writes, reads back "
                f"what it wrote, and concludes the monitor is armed. "
                f"See [[STREAM-MONREGS]].")

    tb.log.info(f"register walk: {checked} write/readback checks, "
                f"{skipped} read-only registers, {len(fails)} failures")
    assert not fails, (
        f"register defects ({len(fails)}):\n  " + "\n  ".join(fails[:25])
        + ("\n  ..." if len(fails) > 25 else ""))


def _run_regs(request, use_monitors):
    module, repo_root_path, tests_dir, log_dir, rtl_dict = get_paths({
        'rtl_stream_top': '../../../../rtl/top',
        'rtl_stream_macro': '../../../../rtl/macro',
        'rtl_stream_fub': '../../../../rtl/fub',
        'rtl_amba': '../../../../../rtl/amba',
    })
    verilog_sources, includes = get_sources_from_filelist(
        repo_root=repo_root_path,
        filelist_path='projects/components/dmas/stream/rtl/filelists/top/stream_top_ch8.f')

    dut_name = "stream_top_ch8"
    test_name = f"test_stream_top_regs_mon{use_monitors}"
    worker_id = os.environ.get('PYTEST_XDIST_WORKER', '')
    if worker_id:
        test_name = f"{test_name}_{worker_id}"

    log_path = os.path.join(log_dir, f'{test_name}.log')
    sim_build = os.path.join(tests_dir, 'local_sim_build', test_name)
    os.makedirs(sim_build, exist_ok=True)
    os.makedirs(log_dir, exist_ok=True)

    run(
        python_search=[tests_dir],
        verilog_sources=verilog_sources,
        includes=includes,
        toplevel=dut_name,
        module=os.path.splitext(os.path.basename(__file__))[0],
        testcase="cocotb_test_reg_walk",
        parameters={
            'NUM_CHANNELS': 4,
            'DATA_WIDTH': 128,
            'AXI_ID_WIDTH': 8,
            'USE_AXI_MONITORS': use_monitors,
            'APB_ADDR_WIDTH': 13,     # 8 KB: the MON block lives at 0x1000+
        },
        sim_build=sim_build,
        extra_env={
            'DUT': dut_name,
            'NUM_CHANNELS': '4',
            'DATA_WIDTH': '128',
            'APB_ADDR_WIDTH': '13',
            'USE_AXI_MONITORS': str(use_monitors),
            'LOG_PATH': log_path,
            'COCOTB_LOG_LEVEL': 'INFO',
            'COCOTB_RESULTS_FILE': os.path.join(log_dir, f'results_{test_name}.xml'),
            'RANDOM_SEED': STREAM_TEST_SEED,
            'COCOTB_RANDOM_SEED': STREAM_TEST_SEED,
        },
        keep_files=True,
        compile_args=["-Wno-fatal", "--timescale", "1ns/1ps",
                      "--unroll-count", "4096", "--unroll-stmts", "20000"],
    )


def test_stream_top_regs_monitors_present(request):
    """All 139 registers, monitors built. The 86 MON registers must work."""
    _run_regs(request, 1)


@pytest.mark.xfail(
    strict=False,
    reason="STREAM-MONREGS: the monitor regfile is instantiated unconditionally "
           "(stream_regs.rdl:758), so it answers even when USE_AXI_MONITORS=0. "
           "This test is the regression gate for gating it.")
def test_stream_top_regs_monitors_absent(request):
    """Monitors NOT built: the MON window must not answer."""
    _run_regs(request, 0)
