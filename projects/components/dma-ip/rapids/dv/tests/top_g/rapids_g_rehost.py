# SPDX-License-Identifier: MIT
# SPDX-FileCopyrightText: 2026 sean galloway
"""Re-host a product RAPIDS top suite on the rapids-g tops (rapids TASK-034).

The product files (dv/tests/top/test_rapids_top.py, test_rapids_cxs_top.py)
are not edited. A -g test file imports one, points that module's `_run_top`
at the runner made here, and re-exports its `test_*` wrappers, which pytest
then collects in this directory. Every wrapper therefore runs exactly the
product's cocotb test and parameters, against the -g top:

    rapids_top, rapids_8ch_top          -> rapids_g_top
    rapids_cxs_top, rapids_8ch_cxs_top  -> rapids_g_cxs_top
    rapids_16ch_top                     -> rapids_g_16ch_top      (rapids TASK-036)
    rapids_16ch_cxs_top                 -> rapids_g_16ch_cxs_top

The runner is the product `_run_top` with the filelist taken from
rtl/filelists/top_g/, the cocotb module loaded from the product directory,
and the logs and builds kept in this one.
"""

import os
import sys

import pytest
from cocotb_test.simulator import run

from TBClasses.shared.utilities import create_view_cmd, get_repo_root, sim_build_path
from TBClasses.shared.filelist_utils import get_sources_from_filelist
from TBClasses.shared.test_levels import level_env
from TBClasses.shared.verilator_cfg import FIELD_COMBO_VLT

REPO = get_repo_root()
PRODUCT_DIR = os.path.join(REPO, 'projects/components/dma-ip/rapids/dv/tests/top')
HERE = os.path.dirname(os.path.abspath(__file__))
for _p in (REPO, PRODUCT_DIR):
    if _p not in sys.path:
        sys.path.insert(0, _p)

G_TOP = {
    'rapids_top': 'rapids_g_top', 'rapids_8ch_top': 'rapids_g_top',
    'rapids_cxs_top': 'rapids_g_cxs_top', 'rapids_8ch_cxs_top': 'rapids_g_cxs_top',
    'rapids_16ch_top': 'rapids_g_16ch_top', 'rapids_16ch_cxs_top': 'rapids_g_16ch_cxs_top',
}


def make_runner(product_module: str, product_rtl_params: dict):
    """A drop-in `_run_top` for `product_module` (its signature and naming)."""

    def _run_top(testcase, test_name, extra_params=None, test_level='gate', dut=None, nch=8, **kw):
        dut = dut or ('rapids_cxs_top' if 'cxs' in product_module else 'rapids_top')
        if dut not in G_TOP:
            pytest.skip(f"rapids-g has no {dut}")
        g_dut = G_TOP[dut]
        test_name = f"{test_name.replace('test_rapids', 'test_rapids_g', 1)}_{test_level}"
        if extra_params:
            test_name += "_" + "_".join(f"{k.lower()}{v}" for k, v in sorted(extra_params.items()))
        worker_id = os.environ.get('PYTEST_XDIST_WORKER', '')
        if worker_id:
            test_name = f"{test_name}_{worker_id}"
        log_dir = os.path.join(HERE, 'logs')
        log_path = os.path.join(log_dir, f'{test_name}.log')
        results_path = os.path.join(log_dir, f'results_{test_name}.xml')
        sim_build = sim_build_path(HERE, test_name)
        os.makedirs(log_dir, exist_ok=True)

        verilog_sources, includes = get_sources_from_filelist(
            repo_root=REPO, filelist_path=f'projects/components/dma-ip/rapids/rtl/filelists/top_g/{g_dut}.f')
        params = dict(product_rtl_params, NUM_CHANNELS=nch)
        if extra_params:
            params.update(extra_params)
        extra_env = {
            'DUT': g_dut, 'LOG_PATH': log_path, 'COCOTB_LOG_LEVEL': 'INFO',
            'COCOTB_RESULTS_FILE': results_path, **level_env(test_level),
            'TEST_NUM_CHANNELS': str(nch), 'TEST_ADDR_WIDTH': str(params['ADDR_WIDTH']),
            'TEST_DATA_WIDTH': str(params['DATA_WIDTH']), 'TEST_AXI_ID_WIDTH': str(params['AXI_ID_WIDTH']),
            'TEST_APB_ADDR_WIDTH': str(params['APB_ADDR_WIDTH']), 'TEST_APB_DATA_WIDTH': '32',
            # as the product CXS runner: the BFMs build the top's link and straps
            'TEST_CXS_MAX_CREDIT': str(params.get('CXS_MAX_CREDIT', 32)),
            'TEST_TILE_CREDITS': str(params.get('TILE_CREDITS', 0)),
            'TEST_TILE_LAND_FLITS': str(params.get('TILE_LAND_FLITS', 16)),
            'TEST_TILE_DESC_PER_CORE': str(params.get('TILE_DESC_PER_CORE', 2)),
        }
        for k, v in kw.items():
            extra_env[k] = str(v)
        enable_waves = bool(int(os.environ.get('WAVES', '0')))
        compile_args = ["-Wno-fatal", "-Werror-MULTIDRIVEN", "-Wno-TIMESCALEMOD", "-Wno-WIDTH",
                        "-Wno-UNOPTFLAT", "-Wno-CASEINCOMPLETE", FIELD_COMBO_VLT, "-Wno-SELRANGE",
                        "-Wno-UNUSEDSIGNAL"]
        if enable_waves:
            compile_args += ['--trace', '--trace-structs', '--trace-max-array', '512']
        cmd_filename = create_view_cmd(log_dir, log_path, sim_build, product_module, test_name)
        try:
            run(python_search=[PRODUCT_DIR, HERE, os.path.join(REPO, 'projects/components/dma-ip/rapids/dv/tbclasses')],
                verilog_sources=verilog_sources, includes=includes, toplevel=g_dut,
                module=product_module, testcase=testcase, parameters=params,
                simulator='verilator', sim_build=sim_build, results_xml=results_path,
                extra_env=extra_env, compile_args=compile_args, waves=enable_waves,
                keep_files=True, plus_args=['--trace'] if enable_waves else [])
        except Exception:
            print(f"Logs: {log_path}")
            if os.path.exists(cmd_filename):
                print(f"View: {cmd_filename}")
            raise

    return _run_top


def rehost(product, namespace: dict, product_rtl_params: dict):
    """Point `product._run_top` at the -g runner and copy its wrappers into
    `namespace` (the -g test module's globals)."""
    product._run_top = make_runner(product.__name__, product_rtl_params)
    for name in dir(product):
        if name.startswith('test_') and callable(getattr(product, name)):
            namespace[name] = getattr(product, name)
