# SPDX-License-Identifier: MIT
# SPDX-FileCopyrightText: 2026 sean galloway
"""Shared configuration grid and pytest runner for the chi family tests.

A test file must not import another test file: cocotb registers every
@cocotb.test it sees at import time (see wb4_test_common). Shared pieces
live here.

A grid point is the CHI property set (a CHIConfig) plus the RTL-only
parameters (LINK_CTRL comes from the config's link_control). GATE is one
default-width point; FUNC adds the other data widths, a one-credit
receiver, an interface without link control and the widest legal flit with
every optional bus; FULL adds the synchronizer / skid / FIFO corners.
"""
import os
import random
from dataclasses import dataclass
from typing import Optional

from cocotb_test.simulator import run

from CocoTBFramework.components.chi import CHIConfig
from TBClasses.chi.chi_tb_common import PARAM_NAMES
from TBClasses.shared.utilities import get_paths, create_view_cmd, sim_build_path
from TBClasses.shared.filelist_utils import get_sources_from_filelist


@dataclass(frozen=True)
class ChiPoint:
    tag: str
    cfg: CHIConfig = CHIConfig()
    skid_depth: int = 4
    rx_fifo_depth: Optional[int] = None         # None = MAX_LCREDIT
    sync_stages: int = 2

    def short_name(self):
        return self.tag

    def rtl_parameters(self):
        p = {k: v for k, v in self.cfg.rtl_parameters().items() if k in PARAM_NAMES}
        p['LINK_CTRL'] = int(self.cfg.link_control)
        p['SKID_DEPTH'] = self.skid_depth
        p['RX_FIFO_DEPTH'] = self.rx_fifo_depth if self.rx_fifo_depth is not None else self.cfg.max_lcredit
        p['LINKACTIVE_SYNC_STAGES'] = self.sync_stages
        return p


_WIDE = CHIConfig(nodeid_width=16, addr_width=52, data_width=256, req_rsvdc_width=8, dat_rsvdc_width=8,
                  mpam_width=15, pbha_width=4, mecid_width=16, streamid_width=16, secsid1_width=1,
                  data_check=True, poison=True)

GATE_POINTS = [
    ChiPoint('dw128'),
]

FUNC_POINTS = GATE_POINTS + [
    ChiPoint('dw256', CHIConfig(data_width=256)),
    ChiPoint('dw512', CHIConfig(data_width=512)),
    ChiPoint('lc1fd1', CHIConfig(max_lcredit=1), rx_fifo_depth=1),
    ChiPoint('nolink', CHIConfig(link_control=False)),
    ChiPoint('wide', _WIDE),
]

FULL_POINTS = FUNC_POINTS + [
    ChiPoint('sync0', sync_stages=0),
    ChiPoint('skid2', skid_depth=2),
    ChiPoint('skid8', skid_depth=8),
    ChiPoint('fd2lc15', rx_fifo_depth=2),
    ChiPoint('lc4', CHIConfig(max_lcredit=4)),
]

# Operations per traffic phase
COUNTS = {'gate': 12, 'func': 40, 'full': 100}


def points_for_level():
    """[(point, test_level)] for REG_LEVEL."""
    reg_level = os.environ.get('REG_LEVEL', 'FUNC').upper()
    if reg_level == 'GATE':
        return [(c, 'gate') for c in GATE_POINTS]
    if reg_level == 'FUNC':
        return [(c, 'func') for c in FUNC_POINTS]
    return [(c, 'full') for c in FULL_POINTS]


def current_test_level():
    level = os.environ.get('TEST_LEVEL', 'gate').lower()
    return level if level in COUNTS else 'gate'


def run_chi(request, dut_name, point, test_level, extra_params=None, tag_extra=''):
    worker_id = os.environ.get('PYTEST_XDIST_WORKER', 'gw0')
    module, repo_root, tests_dir, log_dir, rtl_dict = get_paths({
        'rtl_amba': 'rtl/amba', 'rtl_amba_includes': 'rtl/amba/includes'})
    # get_paths() takes the module AND the test directory from its caller --
    # this helper. Both come from the test file instead.
    module = os.path.splitext(os.path.basename(str(request.fspath)))[0]
    tests_dir = os.path.dirname(os.path.abspath(str(request.fspath)))
    log_dir = os.path.join(tests_dir, 'logs')
    # CHI_FILELIST_OVERRIDE points a run at another filelist: how a mutation check runs the
    # same test against a defective COPY of the RTL without touching rtl/**
    filelist = os.environ.get('CHI_FILELIST_OVERRIDE') or f"rtl/amba/filelists/{dut_name}.f"
    verilog_sources, includes = get_sources_from_filelist(repo_root=repo_root, filelist_path=filelist)
    rtl_parameters = {k: str(v) for k, v in point.rtl_parameters().items()}
    rtl_parameters.update({k: str(v) for k, v in (extra_params or {}).items()})
    name = f"test_{worker_id}_{dut_name}_{point.short_name()}{tag_extra}_{test_level}"
    log_path = os.path.join(log_dir, f'{name}.log')
    sim_build = sim_build_path(tests_dir, name)
    os.makedirs(sim_build, exist_ok=True)
    os.makedirs(log_dir, exist_ok=True)
    enable_waves = bool(int(os.environ.get('WAVES', '0')))
    extra_env = dict(rtl_parameters)
    extra_env.update({
        'TEST_LEVEL': test_level,
        'TRACE_FILE': f"{sim_build}/dump.fst", 'VERILATOR_TRACE': '1' if enable_waves else '0',
        'DUT': dut_name, 'LOG_PATH': log_path, 'COCOTB_LOG_LEVEL': 'INFO',
        'COCOTB_RESULTS_FILE': os.path.join(log_dir, f'results_{name}.xml'),
        'SEED': os.environ.get('SEED', str(random.randint(0, 100000))),
    })
    compile_args = ["-Wno-DECLFILENAME", "-Wno-UNUSEDPARAM", "-Wno-UNUSEDSIGNAL"]
    if enable_waves:
        compile_args += ["--trace-fst", "--trace-structs"]
    create_view_cmd(log_dir, log_path, sim_build, module, name)
    run(python_search=[tests_dir], verilog_sources=verilog_sources, includes=includes,
        toplevel=dut_name, module=module, parameters=rtl_parameters, sim_build=sim_build,
        extra_env=extra_env, waves=enable_waves, keep_files=True, compile_args=compile_args,
        sim_args=(["--trace-fst", "--trace-structs"] if enable_waves else []),
        plus_args=(["--trace"] if enable_waves else []))


# ---------------------------------------------------------------------------
# chi_{rnf,hnf}_port_monlite: the same CHI points, plus the ocelus parameters
# (table sizes, queue depth). Odd table sizes and a 2-entry table are in on
# purpose: the slot logic must not depend on a power of two, and TABLE_FULL
# needs a table the test can fill.
# ---------------------------------------------------------------------------
MONLITE_EXTRAS = {
    'dw128': [dict(MAX_TRANSACTIONS=8), dict(MAX_TRANSACTIONS=2), dict(MAX_TRANSACTIONS=8, USE_MONITOR=0)],
    'dw256': [dict(MAX_TRANSACTIONS=3, MAX_SNOOPS=2)],
    'dw512': [dict(MAX_TRANSACTIONS=8)],
    'lc1fd1': [dict(MAX_TRANSACTIONS=2)],
    'nolink': [dict(MAX_TRANSACTIONS=4)],
    'wide': [dict(MAX_TRANSACTIONS=8, MAX_SNOOPS=3)],
    'sync0': [dict(MAX_TRANSACTIONS=8)],
    'skid2': [dict(MAX_TRANSACTIONS=2, OUT_DEPTH=2)],
    'skid8': [dict(MAX_TRANSACTIONS=8, OUT_DEPTH=7)],
    'fd2lc15': [dict(MAX_TRANSACTIONS=4)],
    'lc4': [dict(MAX_TRANSACTIONS=3)],
}


def monlite_points_for_level():
    """[(point, test_level, extra_params, tag)] for REG_LEVEL."""
    out = []
    for point, level in points_for_level():
        for extra in MONLITE_EXTRAS[point.tag]:
            extra = dict(extra, ACLK_MHZ=100)
            tag = f"_n{extra['MAX_TRANSACTIONS']}" + ('_nomon' if extra.get('USE_MONITOR') == 0 else '')
            out.append((point, level, extra, tag))
    return out


def monlite_id(v):
    return v.short_name() if hasattr(v, 'short_name') else (v if isinstance(v, str) else None)
