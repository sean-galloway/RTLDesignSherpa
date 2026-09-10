# SPDX-License-Identifier: MIT
# SPDX-FileCopyrightText: 2026 sean galloway
"""wb4_master_retry: wb4_retry in front of wb4_master.

Phases (profiles for the cmd producer, rsp consumer and the slave):
  budget 3, delay 4     fixed / back-to-back pipelined / stally, mixed windows
  budget 0 (pass-through) every RTY reaches the FUB, retry_count unchanged
  budget 1, delay 0     immediate re-issue; RTY_K addresses with k > 1 exhaust
The model predicts every response, the number of re-issues (retry_count,
monitor transfer count, slave RTY count) and, with INFLIGHT = 1, the read
data through a byte mirror.
"""
import os
import random
from itertools import product

import pytest
import cocotb
from cocotb_test.simulator import run

from TBClasses.amba.wb4_master_retry_tb import WB4MasterRetryTB
from TBClasses.shared.utilities import get_paths, create_view_cmd, sim_build_path
from TBClasses.shared.filelist_utils import get_sources_from_filelist

PHASES = [
    ((3, 4), ('fixed',      'fixed',      'fixed')),
    ((3, 4), ('backtoback', 'backtoback', 'slow_ack')),
    ((3, 4), ('fast',       'burst_pause', 'stally')),
    ((0, 4), ('backtoback', 'backtoback', 'fixed')),
    ((1, 0), ('fast',       'fast',       'mixed')),
    ((3, 1), ('constrained', 'constrained', 'mixed')),
]
COUNTS = {'gate': 40, 'func': 120, 'full': 300}


@cocotb.test(timeout_time=60, timeout_unit="ms")
async def wb4_master_retry_test(dut):
    tb = WB4MasterRetryTB(dut)
    rng = random.Random(int(os.environ.get('SEED', '0')))
    level = os.environ.get('TEST_LEVEL', 'gate').lower()
    level = level if level in COUNTS else 'gate'
    await tb.setup_clocks_and_reset()
    phases = PHASES if level != 'gate' else PHASES[:4]
    peak = 0
    for (budget, delay), prof in phases:
        tb.set_retry(budget, delay)
        tb.set_profiles(*prof)
        tb.mon.max_inflight = 0
        ok = await tb.run_traffic(COUNTS[level], rng)
        peak = max(peak, tb.mon.max_inflight)
        tb.log.info(f"phase budget={budget} delay={delay} {prof}: {'ok' if ok else 'FAILED'} "
                    f"max_inflight={tb.mon.max_inflight} retry_count={int(dut.retry_count.value)}")
        if not ok:
            break
    await tb.wait_clocks('clk', 20)
    assert tb.report(), f"{len(tb.errors)} error(s); first: {tb.errors[0] if tb.errors else ''}"
    assert tb.expected_retries > 0 and tb.expected_rty_to_fub > 0, "retry paths not exercised"
    if tb.inflight == 1 or tb.classic:
        assert peak == 1, f"max_inflight={peak}: INFLIGHT=1 / classic must keep one transfer on the bus"
    else:
        assert peak > 1, f"max_inflight={peak}: INFLIGHT>1 never pipelined"


def generate_test_params():
    """(addr_width, data_width, inflight, classic, test_level)"""
    reg = os.environ.get('REG_LEVEL', 'FUNC').upper()
    if reg == 'GATE':
        return [(32, 32, 1, 0, 'gate'), (32, 32, 4, 0, 'gate')]
    if reg == 'FUNC':
        return [(32, 32, 1, 0, 'func'), (32, 32, 4, 0, 'func'), (32, 32, 1, 1, 'func'),
                (32, 64, 2, 0, 'func')]
    return list(product([32], [32, 64], [1, 2, 4], [0, 1], ['full']))


@pytest.mark.parametrize("addr_width, data_width, inflight, classic, test_level", generate_test_params())
def test_wb4_master_retry(request, addr_width, data_width, inflight, classic, test_level):
    """wb4_master_retry (rtl/amba/wb4/wb4_master_retry.sv) against the framework
    Wishbone slave with retry-provoking address windows."""
    tag = (f"aw{addr_width:03d}_dw{data_width:03d}_if{inflight}"
           f"_{'classic' if classic else 'pipe'}_{test_level}")
    worker_id = os.environ.get('PYTEST_XDIST_WORKER', 'gw0')
    module, repo_root, tests_dir, log_dir, rtl_dict = get_paths({
        'rtl_amba': 'rtl/amba', 'rtl_amba_includes': 'rtl/amba/includes'})
    verilog_sources, includes = get_sources_from_filelist(
        repo_root=repo_root, filelist_path="rtl/amba/filelists/wb4_master_retry.f")
    name = f"test_{worker_id}_wb4_master_retry_{tag}"
    log_path = os.path.join(log_dir, f'{name}.log')
    sim_build = sim_build_path(tests_dir, name)
    os.makedirs(sim_build, exist_ok=True)
    os.makedirs(log_dir, exist_ok=True)
    enable_waves = bool(int(os.environ.get('WAVES', '0')))
    rtl_parameters = {'ADDR_WIDTH': str(addr_width), 'DATA_WIDTH': str(data_width),
                      'INFLIGHT': str(inflight), 'CLASSIC': str(classic)}
    extra_env = {
        'TEST_LEVEL': test_level, 'ADDR_WIDTH': str(addr_width), 'DATA_WIDTH': str(data_width),
        'INFLIGHT': str(inflight), 'CLASSIC': str(classic),
        'TRACE_FILE': f"{sim_build}/dump.fst", 'VERILATOR_TRACE': '1' if enable_waves else '0',
        'DUT': 'wb4_master_retry', 'LOG_PATH': log_path, 'COCOTB_LOG_LEVEL': 'INFO',
        'COCOTB_RESULTS_FILE': os.path.join(log_dir, f'results_{name}.xml'),
        'SEED': os.environ.get('SEED', str(random.randint(0, 100000))),
    }
    compile_args = ["-Wno-DECLFILENAME", "-Wno-UNUSEDPARAM"]
    if enable_waves:
        compile_args += ["--trace-fst", "--trace-structs"]
    create_view_cmd(log_dir, log_path, sim_build, module, name)
    run(python_search=[tests_dir], verilog_sources=verilog_sources, includes=includes,
        toplevel='wb4_master_retry', module=module, parameters=rtl_parameters, sim_build=sim_build,
        extra_env=extra_env, waves=enable_waves, keep_files=True, compile_args=compile_args,
        sim_args=(["--trace-fst", "--trace-structs"] if enable_waves else []),
        plus_args=(["--trace"] if enable_waves else []))
