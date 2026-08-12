# SPDX-License-Identifier: MIT
# SPDX-FileCopyrightText: 2026 sean galloway
#
# Module: test_stream_top_mon_cfg
# Purpose: Prove the monitor CONFIG registers are actually WIRED to the monitor
#          cfg ports -- APB write by name in, cfg_* port value out.
#
# THE TWO PATHS ARE SEPARATE, AND ONLY ONE OF THEM IS APB
# -------------------------------------------------------
#   s_apb_*        IN   config only. Enables, thresholds, masks. Carries no
#                       packet -- grep for s_apb.*pkt returns nothing.
#   m_axil_mon_*   OUT  the packets. A 64-bit AXI-Lite write master, not APB.
#
# So "a monitor packet class did not appear on the board" has two independent
# causes, and they need different tests:
#
#   (1) the config never reached the cone          <-- THIS FILE
#   (2) the packet was emitted and then dropped    <-- monbus/AXIL egress,
#                                                      test_stream_top_monbus.py
#                                                      and [[AMBA-MONTRACK]]
#
# stream_core already covers the middle: given config ON ITS PORTS, the cone
# fires (dv/tests/macro/test_stream_core_mon_classes.py). What that test CANNOT
# see is whether an APB write ever gets to those ports, because stream_core has
# no APB -- the register block lives here, one level up.
#
# WHY THIS IS THE HIGH-VALUE RUNG
# --------------------------------
# Every config-plumbing defect found in this area was invisible to both the FUB
# tests (which drive the ports directly) and to a board coverage run (which only
# sees packets, or their absence):
#   * cfg_compl_enable     wired to int_cfg_*_mon_enable     (aliased)
#   * cfg_threshold_enable wired to *_mon_perf_enable        (aliased)
#   * cfg_timeout_cycles   squashed 16 -> 4 bits in twelve wrappers
# A register-name-in / port-value-out check catches all three by construction.

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

# (register, field) -> cfg port on stream_core, per monitor block.
# The pairing IS the thing under test: a field and the port that shares its
# meaning must move together. Anything that fails here is an aliasing or width
# defect, not a monitor bug.
CFG_MAP = {
    'RDMON': ('cfg_rdeng_mon', 'RDMON'),
    'WRMON': ('cfg_wreng_mon', 'WRMON'),
}

ENABLE_FIELDS = [
    # (ENABLE field name, cfg port suffix)
    ('MON_EN',     'enable'),
    ('COMPL_EN',   'compl_enable'),
    ('TIMEOUT_EN', 'timeout_enable'),
    ('THRESH_EN',  'thresh_enable'),
    ('PERF_EN',    'perf_enable'),
]

# (register, field, cfg port suffix, test value). Values chosen ABOVE 15 on
# purpose: a 4-bit squash of a 16-bit field passes any test that only ever
# writes small numbers, which is exactly how the timeout squash survived.
VALUE_FIELDS = [
    ('{mon}_TIMEOUT',        'TIMEOUT_CYCLES',  'timeout_cycles', 50_000),
    ('{mon}_LATENCY_THRESH', 'VALUE',           'latency_thresh', 0x0001_2345),
    ('{mon}_PKT_MASK',       'PKT_MASK',        'pkt_mask',       0xBEEF),
]


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


def _field_offset(regs, reg_name, field):
    reg = regs[reg_name]
    if field not in reg:
        raise KeyError(f"{reg_name} has no field {field}")
    return int(reg[field]['offset'])


def _core_node(dut, log=None):
    """Find the node that carries the monitor cfg ports.

    SEARCHED, not assumed. The RTL path is
    g_stream_core_mon_enabled.u_stream_core, but Verilator may inline or rename
    a generate scope, so a hardcoded path fails for reasons that have nothing to
    do with the design. The marker is a port only stream_core has.
    """
    MARKER = 'cfg_rdeng_mon_enable'

    if hasattr(dut, MARKER):
        return dut                      # flattened all the way to the top

    seen = set()

    def walk(node, depth):
        if depth > 3 or id(node) in seen:
            return None
        seen.add(id(node))
        if hasattr(node, MARKER):
            return node
        try:
            children = list(node)
        except Exception:
            children = []
        for child in children:
            found = walk(child, depth + 1)
            if found is not None:
                return found
        return None

    for path in ('g_stream_core_mon_enabled', 'g_stream_core_mon_disabled'):
        blk = getattr(dut, path, None)
        if blk is not None:
            core = getattr(blk, 'u_stream_core', None)
            if core is not None and hasattr(core, MARKER):
                return core
            found = walk(blk, 1)
            if found is not None:
                return found

    found = walk(dut, 0)
    if found is not None:
        if log:
            log.info(f"cfg ports found on {found._path if hasattr(found, '_path') else found}")
        return found

    raise AttributeError(
        f"no node exposes {MARKER} -- the monitor cfg ports are not reachable, "
        f"so this test cannot check the register->port hookup by probing. "
        f"Verilator may have inlined the generate scope; --public-flat-rw is "
        f"already set. Consider checking the EFFECT (packet emitted) instead.")


@cocotb.test(timeout_time=2000, timeout_unit="us")
async def cocotb_test_mon_cfg_hookup(dut):
    """Every monitor cfg register field must reach the cfg port of that name."""
    # apb_addr_width is a CONSTRUCTOR kwarg defaulting to 12 -- it is NOT read
    # from the environment, so setting APB_ADDR_WIDTH in extra_env does nothing
    # here. At 12 bits every MON address (0x1000+) silently TRUNCATES into the
    # functional block: RDMON_ENABLE 0x10E0 -> 0x0E0 (unmapped, 0xDEADBEEF) and
    # WRMON_ENABLE 0x1100 -> 0x100, which is GLOBAL_CTRL. The test was writing
    # the DMA's global control register and reading the result as a monitor
    # hookup failure.
    tb = StreamCoreTB(dut, apb_addr_width=13)
    await tb.setup_clocks_and_reset()
    await tb.init_apb4_master()

    core = _core_node(dut, tb.log)
    regs = _regmap()
    failures = []

    # GLOBAL_EN must be set FIRST. The master monitor enable is gated by it --
    #   cfg_rdeng_mon_enable = reg_rdmon_enable_mon_en & reg_global_ctrl_global_en
    # (stream_config_block.sv:325) -- while every CLASS enable is a straight
    # assign. So MON_EN alone cannot raise the port, and a test that forgets
    # this reports a wiring defect on the one bit that is deliberately ANDed.
    #
    # The asymmetry is worth knowing when debugging silence from the board: a
    # host that clears GLOBAL_EN silences all monitors regardless of the
    # per-class bits, and the class bits still read back exactly as written.
    await tb.write_reg('GLOBAL_CTRL', 1)      # GLOBAL_EN
    await ClockCycles(dut.aclk, 5)

    for mon, (pfx, reg_pfx) in CFG_MAP.items():
        # ---- ENABLE fields: one bit at a time -------------------------------
        # One at a time ON PURPOSE. Writing all-ones and reading all-ones passes
        # even when two fields drive the SAME port, which is precisely the
        # aliasing defect this file exists to catch.
        for field, port_suffix in ENABLE_FIELDS:
            port = getattr(core, f"{pfx}_{port_suffix}", None)
            if port is None:
                failures.append(f"{mon}: no port {pfx}_{port_suffix}")
                continue
            bit = _field_offset(regs, f"{reg_pfx}_ENABLE", field)

            await tb.write_reg(f"{reg_pfx}_ENABLE", 0)
            await ClockCycles(dut.aclk, 5)
            low = int(port.value)

            await tb.write_reg(f"{reg_pfx}_ENABLE", 1 << bit)
            await ClockCycles(dut.aclk, 5)
            high = int(port.value)
            # READ BACK. Without this, "port did not change" cannot be told
            # apart from "the APB write never landed" -- and one of those is a
            # design defect while the other is a broken test.
            rb = int(await tb.read_reg(f"{reg_pfx}_ENABLE"))
            if rb == 0xDEADBEEF:
                failures.append(
                    f"{mon}.{field}: APB read returned the NO-RESPONSE sentinel "
                    f"0xDEADBEEF -- the register is unreachable (window too "
                    f"narrow? MON regfile is at 0x1000+). Nothing about the "
                    f"hookup can be concluded.")
                continue
            if rb != (1 << bit):
                failures.append(
                    f"{mon}.{field}: APB READBACK failed (reg reads 0x{rb:X} "
                    f"after writing bit {bit}) -- the register itself did not "
                    f"take the write, so the port result says nothing")
                continue

            if not (low == 0 and high == 1):
                extra = ("  [MON_EN is ANDed with GLOBAL_CTRL.GLOBAL_EN at "
                         "stream_config_block.sv:325 -- is GLOBAL_EN set?]"
                         if field == 'MON_EN' else "")
                failures.append(
                    f"{mon}.{field} (bit {bit}) -> {pfx}_{port_suffix}: "
                    f"cleared={low} set={high}, expected 0 then 1{extra}")
            else:
                tb.log.info(f"  OK {reg_pfx}_ENABLE.{field}[{bit}] -> "
                            f"{pfx}_{port_suffix}")

        # ---- ENABLE aliasing: each bit must move ONLY its own port ----------
        for field, port_suffix in ENABLE_FIELDS:
            bit = _field_offset(regs, f"{reg_pfx}_ENABLE", field)
            await tb.write_reg(f"{reg_pfx}_ENABLE", 1 << bit)
            await ClockCycles(dut.aclk, 5)
            for other, other_port in ENABLE_FIELDS:
                if other == field:
                    continue
                p = getattr(core, f"{pfx}_{other_port}", None)
                if p is not None and int(p.value) == 1:
                    failures.append(
                        f"{mon}: setting ONLY {field} also raised "
                        f"{pfx}_{other_port} -- the two share a driver "
                        f"(aliasing)")

        # ---- VALUE fields: full width, not just small numbers ---------------
        for reg_tmpl, field, port_suffix, value in VALUE_FIELDS:
            reg_name = reg_tmpl.format(mon=reg_pfx)
            if reg_name not in regs:
                continue
            port = getattr(core, f"{pfx}_{port_suffix}", None)
            if port is None:
                failures.append(f"{mon}: no port {pfx}_{port_suffix}")
                continue
            width = len(port)
            expect = value & ((1 << width) - 1)
            await tb.write_reg(reg_name, value)
            await ClockCycles(dut.aclk, 5)
            got = int(port.value)
            rb = int(await tb.read_reg(reg_name))
            if rb != (value & ((1 << 32) - 1)):
                failures.append(
                    f"{mon}.{field}: APB READBACK 0x{rb:X} != written 0x{value:X} "
                    f"-- register did not take the write; port value is moot")
                continue
            if got != expect:
                failures.append(
                    f"{mon}.{field}: wrote 0x{value:X} -> {pfx}_{port_suffix} "
                    f"({width} b) reads 0x{got:X}, expected 0x{expect:X}"
                    + ("  [value >15: a 4-bit squash looks exactly like this]"
                       if value > 15 and got == min(expect, 0xF) else ""))
            else:
                tb.log.info(f"  OK {reg_name}.{field}=0x{value:X} -> "
                            f"{pfx}_{port_suffix}[{width}] = 0x{got:X}")

    assert not failures, (
        "monitor config does not reach the monitor:\n  "
        + "\n  ".join(failures)
        + "\n\nThis is the APB->cfg_port hookup, NOT the monitor: "
          "test_stream_core_mon_classes.py proves the cones fire when the cfg "
          "PORTS are driven directly.")
    tb.log.info("monitor cfg hookup: all register fields reach their ports")


def test_stream_top_mon_cfg(request):
    """APB register field -> stream_core cfg port, for every monitor class."""
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
    rtl_parameters = {
        'NUM_CHANNELS': 4,
        'DATA_WIDTH': 128,
        'AXI_ID_WIDTH': 8,
        'USE_AXI_MONITORS': 1,      # the monitors must EXIST to be configured
        # 13 bits = 8 KB. The MON regfile is at 0x1000+, so a 12-bit (4 KB)
        # window cannot address ANY monitor register -- every access returns the
        # no-response sentinel and the whole test reads as a hookup failure.
        'APB_ADDR_WIDTH': 13,
    }

    test_name = "test_stream_top_mon_cfg"
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
        testcase="cocotb_test_mon_cfg_hookup",
        parameters=rtl_parameters,
        sim_build=sim_build,
        extra_env={
            'DUT': dut_name,
            'NUM_CHANNELS': '4',
            'DATA_WIDTH': '128',
            'APB_ADDR_WIDTH': '13',   # the TB sizes its APB master from this
            'LOG_PATH': log_path,
            'COCOTB_LOG_LEVEL': 'INFO',
            'COCOTB_RESULTS_FILE': os.path.join(log_dir, f'results_{test_name}.xml'),
            'RANDOM_SEED': STREAM_TEST_SEED,
            'COCOTB_RANDOM_SEED': STREAM_TEST_SEED,
        },
        keep_files=True,
        compile_args=["-Wno-fatal", "--timescale", "1ns/1ps",
                      "--public-flat-rw",     # probe cfg ports inside the core
                      "--unroll-count", "4096", "--unroll-stmts", "20000"],
    )
