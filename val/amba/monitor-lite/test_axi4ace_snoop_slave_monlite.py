"""axi4ace_snoop_slave_monlite: ACE cache-side snoop transport with lite monitor.

REG_LEVEL grids (mirror the axi4 monitor-lite runner shape):
    GATE: 1 test  - standard config, gate depth
    FUNC: 3 tests - standard gate, deep skid func, more snoops func
    FULL: 9 tests - 3 configs x 3 depths (gate/func/full)

DUT orientation: BFM master on ``m_axi_``, BFM responder on ``fub_``.
"""
# SPDX-License-Identifier: MIT
# SPDX-FileCopyrightText: 2026 sean galloway

import os

import cocotb
import pytest
from cocotb_test.simulator import run

from TBClasses.ace.ace_snoop_monitor_tb import AXI4ACESnoopMonitorTB
from TBClasses.shared.filelist_utils import get_sources_from_filelist
from TBClasses.shared.tbbase import TBBase
from TBClasses.shared.test_levels import level_env, reg_level_grid
from TBClasses.shared.utilities import create_view_cmd, get_paths, sim_build_path


@cocotb.test(timeout_time=30, timeout_unit="sec")
async def axi4ace_snoop_slave_monlite_test(dut):
    """ACE snoop slave monlite integration test."""

    test_level = os.environ.get("TEST_LEVEL", "gate").lower()
    addr_width = int(os.environ.get("TEST_ADDR_WIDTH", "32"))
    data_width = int(os.environ.get("TEST_DATA_WIDTH", "32"))
    unit_id = int(os.environ.get("TEST_UNIT_ID", "1"))
    agent_id = int(os.environ.get("TEST_AGENT_ID", "10"))

    tb = AXI4ACESnoopMonitorTB(
        dut,
        aclk=dut.aclk,
        aresetn=dut.aresetn,
        master_prefix="m_axi_",
        slave_prefix="fub_",
        addr_width=addr_width,
        data_width=data_width,
        unit_id=unit_id,
        agent_id=agent_id,
    )

    await tb.initialize()
    await tb.run_monitor_tests(test_level=test_level)


# (ac_depth, cr_depth, cd_depth, max_transactions, out_depth)
_SNOOP_CONFIGS = [
    (2, 4, 4, 8, 4),   # standard
    (4, 8, 8, 8, 4),   # deep skid buffers
    (2, 4, 4, 16, 8),  # more outstanding snoops, deeper output queue
]


def generate_params():
    """Return the REG_LEVEL-shaped parameter grid.

    Tuple: (addr_width, data_width, ac_depth, cr_depth, cd_depth,
            max_transactions, out_depth, test_level).
    """
    reg_level = os.environ.get("REG_LEVEL", "FUNC").upper()
    addr_w = 32
    data_w = 32

    if reg_level == "GATE":
        ac_d, cr_d, cd_d, max_t, out_d = _SNOOP_CONFIGS[0]
        return [(addr_w, data_w, ac_d, cr_d, cd_d, max_t, out_d, "gate")]

    if reg_level == "FUNC":
        params = []
        # standard at gate depth
        ac_d, cr_d, cd_d, max_t, out_d = _SNOOP_CONFIGS[0]
        params.append((addr_w, data_w, ac_d, cr_d, cd_d, max_t, out_d, "gate"))
        # deep skid at func depth
        ac_d, cr_d, cd_d, max_t, out_d = _SNOOP_CONFIGS[1]
        params.append((addr_w, data_w, ac_d, cr_d, cd_d, max_t, out_d, "func"))
        # more snoops at func depth
        ac_d, cr_d, cd_d, max_t, out_d = _SNOOP_CONFIGS[2]
        params.append((addr_w, data_w, ac_d, cr_d, cd_d, max_t, out_d, "func"))
        return params

    # FULL: 3 configs x 3 levels
    params = []
    for ac_d, cr_d, cd_d, max_t, out_d in _SNOOP_CONFIGS:
        for level in reg_level_grid("FULL"):
            params.append((addr_w, data_w, ac_d, cr_d, cd_d, max_t, out_d, level))
    return params


def validate_params(params):
    for param in params:
        addr_w, data_w, ac_d, cr_d, cd_d, max_t, out_d, _level = param
        if addr_w > 64:
            raise ValueError(f"addr_width={addr_w} exceeds 64: {param}")
        if data_w not in (32, 64):
            raise ValueError(f"data_width={data_w} not supported: {param}")
        if ac_d < 1 or cr_d < 1 or cd_d < 1 or max_t < 1 or out_d < 1:
            raise ValueError(f"depths/max_t/out_d must be positive: {param}")
    return params


@pytest.mark.parametrize(
    "addr_width, data_width, ac_depth, cr_depth, cd_depth, max_transactions, out_depth, test_level",
    validate_params(generate_params()),
)
def test_axi4ace_snoop_slave_monlite(
    request,
    addr_width,
    data_width,
    ac_depth,
    cr_depth,
    cd_depth,
    max_transactions,
    out_depth,
    test_level,
):
    """Run axi4ace_snoop_slave_monlite across the REG_LEVEL grid."""

    worker_id = os.environ.get("PYTEST_XDIST_WORKER", "gw0")
    dut_name = "axi4ace_snoop_slave_monlite"
    reg_level = os.environ.get("REG_LEVEL", "FUNC").upper()

    module, repo_root, tests_dir, log_dir, _rtl_dict = get_paths({
        "rtl_amba": "rtl/amba",
        "rtl_amba_includes": "rtl/amba/includes",
    })

    aw_str = TBBase.format_dec(addr_width, 2)
    dw_str = TBBase.format_dec(data_width, 3)
    acd_str = TBBase.format_dec(ac_depth, 1)
    crd_str = TBBase.format_dec(cr_depth, 1)
    cdd_str = TBBase.format_dec(cd_depth, 1)
    mt_str = TBBase.format_dec(max_transactions, 2)
    od_str = TBBase.format_dec(out_depth, 1)

    test_name = (
        f"test_{worker_id}_{dut_name}_a{aw_str}_d{dw_str}_"
        f"ac{acd_str}_cr{crd_str}_cd{cdd_str}_mt{mt_str}_od{od_str}_"
        f"{test_level}_{reg_level}"
    )

    log_path = os.path.join(log_dir, f"{test_name}.log")
    sim_build = sim_build_path(tests_dir, test_name)
    enable_waves = bool(int(os.environ.get("WAVES", "0")))
    os.makedirs(sim_build, exist_ok=True)
    os.makedirs(log_dir, exist_ok=True)
    results_path = os.path.join(log_dir, f"results_{test_name}.xml")

    verilog_sources, includes = get_sources_from_filelist(
        repo_root=repo_root,
        module=dut_name,
    )
    for src in verilog_sources:
        if not os.path.exists(src):
            raise FileNotFoundError(f"RTL source not found: {src}")

    ac_size = addr_width + 4 + 3
    cr_size = 5
    cd_size = data_width + 1

    rtl_parameters = {
        "USE_MONITOR": "1",
        "UNIT_ID": "1",
        "AGENT_ID": "10",
        "MAX_TRANSACTIONS": str(max_transactions),
        "OUT_DEPTH": str(out_depth),
        "ACLK_MHZ": "100",
        "CFI_MIN_FREQ_MHZ": "100",
        "CFI_MAX_FREQ_MHZ": "100",
        "SKID_DEPTH_AC": str(ac_depth),
        "SKID_DEPTH_CR": str(cr_depth),
        "SKID_DEPTH_CD": str(cd_depth),
        "ADDR_WIDTH": str(addr_width),
        "DATA_WIDTH": str(data_width),
        "AW": str(addr_width),
        "DW": str(data_width),
        "ACSize": str(ac_size),
        "CRSize": str(cr_size),
        "CDSize": str(cd_size),
    }

    timeout_multipliers = {"gate": 1, "func": 2, "full": 4}
    timeout_ms = int(10000 * timeout_multipliers.get(test_level, 1))

    extra_env = {
        "DUT": dut_name,
        "LOG_PATH": log_path,
        "COCOTB_LOG_LEVEL": "INFO",
        "COCOTB_RESULTS_FILE": results_path,
        "COCOTB_TEST_TIMEOUT": str(timeout_ms),
        "TEST_UNIT_ID": "1",
        "TEST_AGENT_ID": "10",
        **level_env(test_level),
        "TEST_ADDR_WIDTH": str(addr_width),
        "TEST_DATA_WIDTH": str(data_width),
        "TEST_CLK_PERIOD": "10",
        "ACE_COMPLIANCE_CHECK": "1",
    }

    compile_args = [
        "--trace-fst",
        "--trace-structs",
        "-Wall",
        "-Wno-SYNCASYNCNET",
        "-Wno-UNUSED",
        "-Wno-DECLFILENAME",
        "-Wno-PINMISSING",
        "-Wno-UNDRIVEN",
        "-Wno-WIDTHEXPAND",
        "-Wno-WIDTHTRUNC",
        "-Wno-SELRANGE",
        "-Wno-CASEINCOMPLETE",
        "-Wno-TIMESCALEMOD",
    ]

    cmd_filename = create_view_cmd(
        os.path.dirname(log_path), log_path, sim_build, module, test_name
    )

    print(f"\n{'='*80}")
    print(f"Running {test_level.upper()} ACE snoop slave monlite test: {dut_name}")
    print(
        f"Config: ADDR={addr_width}, DATA={data_width}, "
        f"AC={ac_depth}, CR={cr_depth}, CD={cd_depth}, "
        f"MAX_SNOOPS={max_transactions}, OUT_DEPTH={out_depth}"
    )
    print(f"Expected duration: {timeout_ms/1000:.1f}s")
    print(f"{'='*80}")

    try:
        run(
            python_search=[tests_dir],
            verilog_sources=verilog_sources,
            includes=includes,
            toplevel=dut_name,
            module=module,
            parameters=rtl_parameters,
            sim_build=sim_build,
            extra_env=extra_env,
            waves=enable_waves,
            keep_files=True,
            compile_args=compile_args,
        )
        print(f"{test_level.upper()} ACE snoop slave monlite test PASSED")
    except Exception as e:
        print(f"{test_level.upper()} ACE snoop slave monlite test FAILED: {e!s}")
        print(f"Logs preserved at: {log_path}")
        print(f"To view the waveforms run: {cmd_filename}")
        raise
