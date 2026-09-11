# SPDX-License-Identifier: MIT
# SPDX-FileCopyrightText: 2026 sean galloway
"""wb4_to_axil4: Wishbone B4 slave in, AXI4-Lite master out.

Phases:
  sequential   one transfer at a time, reads and writes over a shared memory
               model, plus an out-of-range window that answers SLVERR and so
               must reach Wishbone as ERR
  pipelined    the master BFM keeps several requests moving, against gappy
               and sparse request pacing
  ordering     directed write-then-read pairs where the AXI side answers the
               read FIRST every time (slow B channel, fast R channel). B4
               terminates in issue order, so the converter must hold the read
               back; a status or data mismatch here is a response that
               overtook its predecessor.
"""
import os
import random
from itertools import product

import pytest
import cocotb
from cocotb_test.simulator import run

from TBClasses.shared.utilities import get_paths, create_view_cmd, sim_build_path
from TBClasses.shared.filelist_utils import get_sources_from_filelist
from projects.components.converters.dv.tbclasses.wb4_to_axil4_tb import WB4ToAXIL4TB

COUNTS = {'gate': 40, 'func': 120, 'full': 300}


@cocotb.test(timeout_time=120, timeout_unit="ms")
async def cocotb_test_wb4_to_axil4(dut):
    tb = WB4ToAXIL4TB(dut)
    level = os.environ.get('TEST_LEVEL', 'gate').lower()
    level = level if level in COUNTS else 'gate'
    n = COUNTS[level]
    rng = random.Random(int(os.environ.get('SEED', '0')))
    await tb.setup_clocks_and_reset()

    ok = await tb.run_traffic(n, rng)
    tb.log.info(f"sequential: {'ok' if ok else 'FAILED'}")

    if ok:
        for prof in ('gappy', 'sparse'):
            tb.set_profile(prof)
            ok = await tb.run_traffic(n // 2, rng)
            tb.log.info(f"pipelined {prof}: {'ok' if ok else 'FAILED'} "
                        f"max_inflight={tb.mon.max_inflight}")
            if not ok:
                break

    if ok:
        tb.set_profile('fixed')
        ok = await tb.run_ordering_probe(rng, pairs=max(4, n // 8))
        tb.log.info(f"ordering probe: {'ok' if ok else 'FAILED'}")

    await tb.wait_idle()
    assert tb.report(), f"{len(tb.errors)} error(s); first: {tb.errors[0] if tb.errors else ''}"
    assert tb.stats['ack'] and tb.stats['err'], \
        f"both termination kinds must be exercised: {tb.stats}"
    if tb.classic:
        assert tb.mon.max_inflight == 1, \
            f"max_inflight={tb.mon.max_inflight}: classic mode holds one request at a time"


def generate_test_params():
    """(addr_width, data_width, classic, outstanding, test_level)"""
    reg = os.environ.get('REG_LEVEL', 'FUNC').upper()
    if reg == 'GATE':
        return [(32, 32, 0, 1, 'gate'), (32, 32, 0, 4, 'gate')]
    if reg == 'FUNC':
        return [(32, 32, 0, 1, 'func'), (32, 32, 0, 4, 'func'),
                (32, 32, 1, 1, 'func'), (32, 64, 0, 2, 'func')]
    return list(product([32], [32, 64], [0, 1], [1, 2, 4], ['full']))


@pytest.mark.parametrize("addr_width, data_width, classic, outstanding, test_level",
                         generate_test_params())
def test_wb4_to_axil4(request, addr_width, data_width, classic, outstanding, test_level):
    """wb4_to_axil4 (projects/components/converters/rtl/wb4_to_axil4.sv)."""
    module, repo_root, tests_dir, log_dir, rtl_dict = get_paths({
        'rtl_converters': 'projects/components/converters/rtl',
        'rtl_amba_includes': 'rtl/amba/includes'})
    dut_name = 'wb4_to_axil4'
    worker_id = os.environ.get('PYTEST_XDIST_WORKER', 'gw0')
    name = (f"test_{worker_id}_{dut_name}_aw{addr_width:03d}_dw{data_width:03d}"
            f"_{'classic' if classic else 'pipe'}_o{outstanding}_{test_level}")
    log_path = os.path.join(log_dir, f'{name}.log')
    sim_build = sim_build_path(tests_dir, name)
    os.makedirs(sim_build, exist_ok=True)
    os.makedirs(log_dir, exist_ok=True)
    verilog_sources, includes = get_sources_from_filelist(
        repo_root=repo_root,
        filelist_path='projects/components/converters/rtl/filelists/wb4_to_axil4.f')
    rtl_parameters = {'ADDR_WIDTH': str(addr_width), 'DATA_WIDTH': str(data_width),
                      'CLASSIC': str(classic), 'OUTSTANDING': str(outstanding),
                      'MAX_OUTSTANDING': str(max(1, outstanding))}
    enable_waves = bool(int(os.environ.get('WAVES', '0')))
    extra_env = {
        'TEST_LEVEL': test_level, 'ADDR_WIDTH': str(addr_width), 'DATA_WIDTH': str(data_width),
        'CLASSIC': str(classic), 'OUTSTANDING': str(outstanding),
        'WR_DELAY': '6', 'RD_DELAY': '1',
        'TRACE_FILE': f"{sim_build}/dump.fst", 'VERILATOR_TRACE': '1' if enable_waves else '0',
        'DUT': dut_name, 'LOG_PATH': log_path, 'COCOTB_LOG_LEVEL': 'INFO',
        'COCOTB_RESULTS_FILE': os.path.join(log_dir, f'results_{name}.xml'),
        'SEED': os.environ.get('SEED', str(random.randint(0, 100000))),
    }
    compile_args = ["-Wno-DECLFILENAME", "-Wno-UNUSEDPARAM", "-Wno-UNUSEDSIGNAL"]
    if enable_waves:
        compile_args += ["--trace-fst", "--trace-structs"]
    create_view_cmd(log_dir, log_path, sim_build, module, name)
    run(python_search=[tests_dir], verilog_sources=verilog_sources, includes=includes,
        toplevel=dut_name, module=module, testcase="cocotb_test_wb4_to_axil4",
        parameters=rtl_parameters, sim_build=sim_build, extra_env=extra_env, waves=enable_waves,
        keep_files=True, compile_args=compile_args,
        sim_args=(["--trace-fst", "--trace-structs"] if enable_waves else []),
        plus_args=(["--trace"] if enable_waves else []))
