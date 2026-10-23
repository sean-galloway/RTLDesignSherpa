# SPDX-License-Identifier: MIT
# SPDX-FileCopyrightText: 2026 sean galloway
"""fb_data_fabric, every leg: the data fabric under test, alone.

The same TB and the same seed drive each leg's `fb_data_fabric`; the leg is
chosen only by which filelist is compiled (PRD.md section 4). Every leg must
pass identically before it goes into the harness: concurrent traffic from
all four masters with data checked at both ends, IDs {slot, local id} at every
slave (the master's own ID on legs B1 and A2, a remap slot on leg A:
local_id_width), DECERR for unconnected and unmapped targets.

Leg C3 (LiteX) differs by design on two points, set here per leg in
LEG_BEHAVIOUR and checked as such: its slaves see the master's own ID with no
slot bits, and it has no error slave, so an unroutable command is never
accepted -- the TB proves it stays unanswered (fb_fabric_tb.py docstring).

Leg B1 compiles the Xilinx AXI Crossbar from the Vivado install, so
XILINX_VIVADO must point at it (Vivado's settings64.sh sets it).
"""
import os
import random
import re

import pytest
import cocotb
from cocotb_test.simulator import run

from TBClasses.shared.utilities import get_paths, create_view_cmd, sim_build_path
from TBClasses.shared.filelist_utils import get_sources_from_filelist
from tbclasses.fb_fabric_tb import FbFabricTB
from TBClasses.shared.verilator_cfg import FIELD_COMBO_VLT  # noqa: E402  (not -Wno-MULTIDRIVEN)

COUNTS = {'gate': 20, 'func': 120, 'full': 500}
AREA = 'projects/fpga-systems/Genesys2/fabric-benchmark'
LEG_FILELIST = {
    'bridge': f'{AREA}/rtl/filelists/fb_data_fabric_bridge.f',
    'bridge_plain': f'{AREA}/rtl/filelists/fb_data_fabric_bridge_plain.f',
    'xbar':   f'{AREA}/rtl/filelists/fb_data_fabric_xbar_sim.f',
    'forencich': f'{AREA}/rtl/filelists/fb_data_fabric_forencich.f',
    'pulp':   f'{AREA}/rtl/filelists/fb_data_fabric_pulp.f',
    'litex':  f'{AREA}/rtl/filelists/fb_data_fabric_litex.f',
}
LEGS = tuple(LEG_FILELIST)
# (slave-side ID carries the master slot, what an unroutable command gets)
LEG_BEHAVIOUR = {leg: (True, 'decerr') for leg in LEGS} | {'litex': (False, 'hang')}

BRIDGE_PKG = {leg: f'{AREA}/rtl/bridges/generated/{b}/{b}_pkg.sv'
              for leg, b in (('bridge', 'bridge_fb_data'), ('bridge_plain', 'bridge_fb_data_plain'))}
MASTER_ID_W = 8


def local_id_width(repo_root: str, leg: str) -> int:
    """Master-local ID bits at the slaves. Legs B1 and C1-C3 forward the
    master's own ID; a bridge leg reports MASTER_ID_WIDTH in its generated package: a remap
    slot on leg A (bridge TASK-018), the whole ID on leg A2 (id_remap off)."""
    if leg not in BRIDGE_PKG:
        return MASTER_ID_W
    with open(os.path.join(repo_root, BRIDGE_PKG[leg])) as fh:
        m = re.search(r"localparam int MASTER_ID_WIDTH\s*=\s*(\d+)", fh.read())
    assert m, f"no MASTER_ID_WIDTH in {BRIDGE_PKG[leg]}"
    return int(m.group(1))


@cocotb.test(timeout_time=200, timeout_unit="ms")
async def cocotb_test_fb_fabric(dut):
    tb = FbFabricTB(dut)
    level = os.environ.get('TEST_LEVEL', 'gate').lower()
    n = COUNTS.get(level, COUNTS['gate'])
    tb.preload()
    await tb.setup_clocks_and_reset()

    ok = await tb.run_traffic(n)
    tb.log.info(f"traffic: {'ok' if ok else 'FAILED'}")
    ok = ok and tb.check_memory()
    tb.log.info(f"memory: {'ok' if ok else 'FAILED'}")
    if ok:
        ok = await tb.run_decerr()
        tb.log.info(f"decerr: {'ok' if ok else 'FAILED'}")
    await tb.wait_clocks('aclk', 20)
    assert tb.report(), f"{len(tb.errors)} error(s); first: {tb.errors[0] if tb.errors else ''}"
    # A pass must have exercised what it claims (an idle run is not a pass).
    assert tb.stats['rd'] >= 2 * n and tb.stats['wr'] >= 2 * n, tb.stats
    unroutable = 'hang' if tb.unmapped == 'hang' else 'decerr'
    assert tb.stats[unroutable] == 4 and tb.stats['ids'] >= 4 * n, tb.stats


def generate_test_params():
    """(leg, test_level)"""
    reg = os.environ.get('REG_LEVEL', 'FUNC').upper()
    level = {'GATE': 'gate', 'FUNC': 'func', 'FULL': 'full'}.get(reg, 'func')
    return [(leg, level) for leg in LEGS]


@pytest.mark.parametrize("leg, test_level", generate_test_params())
def test_fb_fabric(request, leg, test_level):
    """fb_data_fabric per leg (rtl/generated/fb_data_fabric_<leg>/fb_data_fabric.sv)."""
    if leg == 'xbar' and not os.environ.get('XILINX_VIVADO'):
        pytest.fail("XILINX_VIVADO is not set: leg B1 compiles the AXI Crossbar from the "
                    "Vivado install (source Vivado's settings64.sh)")
    module, repo_root, tests_dir, log_dir, rtl_dict = get_paths({})
    dut_name = 'fb_data_fabric'
    worker_id = os.environ.get('PYTEST_XDIST_WORKER', 'gw0')
    name = f"test_{worker_id}_fb_fabric_{leg}_{test_level}"
    log_path = os.path.join(log_dir, f'{name}.log')
    sim_build = sim_build_path(tests_dir, name)
    os.makedirs(sim_build, exist_ok=True)
    os.makedirs(log_dir, exist_ok=True)
    verilog_sources, includes = get_sources_from_filelist(
        repo_root=repo_root, filelist_path=LEG_FILELIST[leg])
    enable_waves = bool(int(os.environ.get('WAVES', '0')))
    extra_env = {
        'TEST_LEVEL': test_level, 'FB_LEG': leg,
        'FB_LOCAL_ID_W': str(local_id_width(repo_root, leg)),
        'FB_ID_SLOT': '1' if LEG_BEHAVIOUR[leg][0] else '0', 'FB_UNMAPPED': LEG_BEHAVIOUR[leg][1],
        'TRACE_FILE': f"{sim_build}/dump.fst", 'VERILATOR_TRACE': '1' if enable_waves else '0',
        'DUT': dut_name, 'LOG_PATH': log_path, 'COCOTB_LOG_LEVEL': 'INFO',
        'COCOTB_RESULTS_FILE': os.path.join(log_dir, f'results_{name}.xml'),
        'SEED': os.environ.get('SEED', str(random.randint(0, 100000))),
    }
    compile_args = ["-Wno-fatal", "-Werror-MULTIDRIVEN", "-Wno-lint", "-Wno-style", FIELD_COMBO_VLT]
    if enable_waves:
        compile_args += ["--trace-fst", "--trace-structs"]
    create_view_cmd(log_dir, log_path, sim_build, module, name)
    run(python_search=[tests_dir], verilog_sources=verilog_sources, includes=includes,
        toplevel=dut_name, module=module, testcase="cocotb_test_fb_fabric",
        sim_build=sim_build, extra_env=extra_env, waves=enable_waves, keep_files=True,
        compile_args=compile_args,
        sim_args=(["--trace-fst", "--trace-structs"] if enable_waves else []),
        plus_args=(["--trace"] if enable_waves else []))
