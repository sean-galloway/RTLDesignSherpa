# SPDX-License-Identifier: MIT
# SPDX-FileCopyrightText: 2026 sean galloway
#
# RTL Design Sherpa - Industry-Standard RTL Design and Verification
# https://github.com/sean-galloway/RTLDesignSherpa
#
# Module: test_wb4_slave
# Purpose: wb4_slave alone. The framework WB4Master drives the Wishbone side,
#          a WB4Monitor checks the wires, GAXI BFMs on the cmd/rsp queues with
#          the TB as the FUB. Includes the abort case (CYC dropped with
#          requests outstanding) that a master<->slave loop cannot produce.
#
# Documentation: docs/markdown/rtl-amba/wb4/wb4_slave.md
# Subsystem: amba
# Author: sean galloway
# Created: 2026-09-09
"""REG_LEVEL: GATE 1 config; FUNC widths x depths x MAX_OUTSTANDING; FULL the product.
TEST_LEVEL scales the requests per profile phase."""
import os
import random
from itertools import product

import pytest
import cocotb
from cocotb_test.simulator import run

from TBClasses.amba.wb4_slave_tb import WB4SlaveTB
from TBClasses.shared.utilities import get_paths, create_view_cmd, sim_build_path
from TBClasses.shared.filelist_utils import get_sources_from_filelist

# (WB4Master profile, cmd GAXI profile, rsp GAXI profile)
PHASES = [
    ('fixed',  'fixed',       'fixed'),
    ('fixed',  'backtoback',  'backtoback'),
    ('gappy',  'burst_pause', 'fast'),
    ('fixed',  'fast',        'burst_pause'),
    ('sparse', 'constrained', 'constrained'),
]
COUNTS = {'gate': 60, 'func': 200, 'full': 400}


@cocotb.test(timeout_time=20, timeout_unit="ms")
async def wb4_slave_test(dut):
    tb = WB4SlaveTB(dut)
    seed = int(os.environ.get('SEED', '0'))
    rng = random.Random(seed)
    level = os.environ.get('TEST_LEVEL', 'gate').lower()
    level = level if level in COUNTS else 'gate'
    tb.log.info(f"seed={seed} level={level}")
    await tb.setup_clocks_and_reset()
    phases = PHASES if level != 'gate' else PHASES[:3]
    peak = 0
    for prof in phases:
        tb.set_profiles(*prof)
        tb.mon.max_inflight = 0
        ok = await tb.run_traffic(COUNTS[level], rng, mix=0.2)
        tb.log.info(f"phase {prof}: {'ok' if ok else 'FAILED'} max_inflight={tb.mon.max_inflight}")
        peak = max(peak, tb.mon.max_inflight)
        if not ok:
            break
    if not tb.errors:
        # Abort, then prove the DUT pairs the next cycle's requests correctly.
        tb.set_profiles('fixed', 'fixed', 'fixed')
        await tb.run_abort(rng, outstanding=4)
        if not tb.errors:
            ok = await tb.run_traffic(COUNTS[level] // 2, rng, mix=0.2)
            tb.log.info(f"post-abort traffic: {'ok' if ok else 'FAILED'}")
    await tb.wait_clocks('clk', 20)
    tb.done = True
    passed = tb.report()
    assert passed, f"{len(tb.errors)} error(s); first: {tb.errors[0] if tb.errors else ''}"
    assert peak > 1, f"max_inflight={peak}: never pipelined"
    assert tb.mon.aborts >= 1, "the abort phase never dropped CYC with requests outstanding"
    s = tb.stats
    assert s['ack'] and s['err'] and s['rty'], f"not every status exercised: {s}"


def generate_test_params():
    reg_level = os.environ.get('REG_LEVEL', 'FUNC').upper()
    if reg_level == 'GATE':
        return [(32, 32, 2, 2, 16, 'gate')]
    if reg_level == 'FUNC':
        return [(32, 32, 2, 2, 16, 'func'), (32, 64, 4, 4, 4, 'func'), (32, 32, 2, 8, 2, 'func')]
    return list(product([32], [32, 64], [2, 4], [2, 4, 8], [2, 4, 16], ['full']))


@pytest.mark.parametrize("addr_width, data_width, cmd_depth, rsp_depth, max_outstanding, test_level",
                         generate_test_params())
def test_wb4_slave(request, addr_width, data_width, cmd_depth, rsp_depth, max_outstanding, test_level):
    """wb4_slave (rtl/amba/wb4/wb4_slave.sv) against the framework Wishbone master."""
    tag = f"aw{addr_width:03d}_dw{data_width:03d}_cd{cmd_depth}_rd{rsp_depth}_mo{max_outstanding}_{test_level}"
    _run(request, "wb4_slave", "rtl/amba/filelists/wb4_slave.f", tag,
         {'ADDR_WIDTH': str(addr_width), 'DATA_WIDTH': str(data_width),
          'CMD_DEPTH': str(cmd_depth), 'RSP_DEPTH': str(rsp_depth), 'MAX_OUTSTANDING': str(max_outstanding)},
         {'TEST_LEVEL': test_level, 'ADDR_WIDTH': str(addr_width), 'DATA_WIDTH': str(data_width),
          'MAX_OUTSTANDING': str(max_outstanding)})

def _run(request, dut_name, filelist, tag, rtl_parameters, extra_env):
    worker_id = os.environ.get('PYTEST_XDIST_WORKER', 'gw0')
    module, repo_root, tests_dir, log_dir, rtl_dict = get_paths({
        'rtl_amba': 'rtl/amba', 'rtl_amba_includes': 'rtl/amba/includes'})
    verilog_sources, includes = get_sources_from_filelist(repo_root=repo_root, filelist_path=filelist)
    name = f"test_{worker_id}_{dut_name}_{tag}"
    log_path = os.path.join(log_dir, f'{name}.log')
    sim_build = sim_build_path(tests_dir, name)
    os.makedirs(sim_build, exist_ok=True)
    os.makedirs(log_dir, exist_ok=True)
    enable_waves = bool(int(os.environ.get('WAVES', '0')))
    extra_env.update({
        'TRACE_FILE': f"{sim_build}/dump.fst", 'VERILATOR_TRACE': '1' if enable_waves else '0',
        'DUT': dut_name, 'LOG_PATH': log_path, 'COCOTB_LOG_LEVEL': 'INFO',
        'COCOTB_RESULTS_FILE': os.path.join(log_dir, f'results_{name}.xml'),
        'SEED': os.environ.get('SEED', str(random.randint(0, 100000))),
    })
    compile_args = ["-Wno-DECLFILENAME", "-Wno-UNUSEDPARAM"]
    if enable_waves:
        compile_args += ["--trace-fst", "--trace-structs"]
    create_view_cmd(log_dir, log_path, sim_build, module, name)
    run(python_search=[tests_dir], verilog_sources=verilog_sources, includes=includes,
        toplevel=dut_name, module=module, parameters=rtl_parameters, sim_build=sim_build,
        extra_env=extra_env, waves=enable_waves, keep_files=True, compile_args=compile_args,
        sim_args=(["--trace-fst", "--trace-structs"] if enable_waves else []),
        plus_args=(["--trace"] if enable_waves else []))
