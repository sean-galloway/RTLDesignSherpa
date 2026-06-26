# SPDX-License-Identifier: MIT
# SPDX-FileCopyrightText: 2026 sean galloway
#
# RTL Design Sherpa - Industry-Standard RTL Design and Verification
# https://github.com/sean-galloway/RTLDesignSherpa
#
# Module: test_cdc_open_loop
# Purpose: Exercise rtl/amba/shared/cdc_open_loop.sv across:
#          - Manual STRETCH_CYCLES (back-compat regression)
#          - Auto-computed STRETCH (AUTO_STRETCH=1 with SRC_CLK_HZ/DST_CLK_HZ)
#          - "Cliff" configs that intentionally under-stretch to verify the
#            destination synchronizer drops cleanly (no spurious data).
#
# Subsystem: amba

import os
import random

import cocotb
import pytest
from cocotb_test.simulator import run

from TBClasses.amba.cdc_open_loop import CDCOpenLoopTB
from TBClasses.shared.utilities import create_view_cmd, get_paths


@cocotb.test(timeout_time=30, timeout_unit="ms")
async def cdc_open_loop_test(dut):
    """Drive cdc_open_loop through the phases selected by TEST_LEVEL."""
    tb = CDCOpenLoopTB(dut)

    seed = int(os.environ.get("SEED", "42"))
    random.seed(seed)
    tb.log.info(f"Using seed: {seed}")

    await tb.start_clocks_and_monitor()

    try:
        ok = await tb.run_all_for_level()

        # Let any straggling pulses finish before checking
        await tb.drain_settle()

        tb.log.info("=" * 70)
        tb.log.info(f"FINAL: sent={len(tb.sent_queue)} "
                    f"received={len(tb.received)} "
                    f"errors={tb.total_errors} "
                    f"expect_losses={tb.EXPECT_LOSSES}")
        tb.log.info("=" * 70)

        if not ok or tb.total_errors > 0:
            assert False, (
                f"cdc_open_loop test failed: ok={ok}, "
                f"errors={tb.total_errors}")

    finally:
        tb.done = True


# -----------------------------------------------------------------------------
# Config generation
# -----------------------------------------------------------------------------
def _stretch_eff(auto, sync_stages, src_hz, dst_hz, manual_stretch):
    """Mirror the SV ceil math so we can label configs accurately."""
    if auto:
        return max(1, ((sync_stages + 1) * src_hz + dst_hz - 1) // dst_hz)
    return max(1, manual_stretch)


def generate_cdc_open_loop_test_params():
    """Multiple configs:

    1. MANUAL back-compat: AUTO_STRETCH=0, fixed STRETCH_CYCLES across
       a few src/dst ratios. Should keep working unchanged.

    2. AUTO sized exactly: AUTO_STRETCH=1, SRC/DST clocks consistent
       with the simulated periods. STRETCH_EFF will be the formula's
       answer; the TB will run no-loss phases.

    3. AUTO under-sized (cliff): AUTO_STRETCH=1 with SRC_CLK_HZ that
       claims a SLOW source, but the simulated src period is much
       faster, so STRETCH_EFF is too short for the real ratio. The
       TB's cliff phase will see drops; verifies the dst synchronizer
       drops cleanly (no spurious data).
    """
    params = []

    # ---- 1) Manual back-compat ----
    manual_levels = ['basic', 'func']
    manual_cases = [
        # (src_period_ns, dst_period_ns, stretch_cycles, sync_stages)
        # Picked so STRETCH*src_period >= (SYNC+1)*dst_period in every case
        # so back-compat manual mode is genuinely safe.
        (40, 10,  8, 2),   # 25 MHz -> 100 MHz   (320 ns > 30 ns)
        (10, 40, 16, 2),   # 100 MHz -> 25 MHz   (160 ns >= 120 ns)
        (20, 10,  8, 2),   # 50 MHz -> 100 MHz   (160 ns > 30 ns)
        (10, 20, 10, 2),   # 100 MHz -> 50 MHz   (100 ns >= 60 ns)
        # Keep one SYNC=3 config to verify higher MTBF still works
        (10, 20, 12, 3),   # 100 MHz -> 50 MHz, deeper sync chain
    ]
    for (src_p, dst_p, stretch, syncs) in manual_cases:
        for level in manual_levels:
            params.append({
                'mode'           : 'manual',
                'src_period_ns'  : src_p,
                'dst_period_ns'  : dst_p,
                'stretch_cycles' : stretch,
                'sync_stages'    : syncs,
                'auto_stretch'   : 0,
                'src_clk_hz'     : int(round(1e9 / src_p)),
                'dst_clk_hz'     : int(round(1e9 / dst_p)),
                'test_level'     : level,
            })

    # ---- 2) Auto sized correctly ----
    auto_levels = ['basic', 'func', 'full']
    auto_cases = [
        # (src_period_ns, dst_period_ns) — SRC/DST_CLK_HZ derived from period
        (40, 10),   # 25 MHz -> 100 MHz   → STRETCH_EFF = 1
        (20, 10),   # 50 MHz -> 100 MHz   → STRETCH_EFF = 2
        (10, 10),   # 100 MHz -> 100 MHz  → STRETCH_EFF = 4
        (10, 25),   # 100 MHz -> 40 MHz   → STRETCH_EFF = 2 (≈ (3+1)*100/40)
        (15, 25),   # 66.6 MHz -> 40 MHz  → STRETCH_EFF ≈ 2
        (10, 40),   # 100 MHz -> 25 MHz   → STRETCH_EFF = 1
    ]
    for (src_p, dst_p) in auto_cases:
        src_hz = int(round(1e9 / src_p))
        dst_hz = int(round(1e9 / dst_p))
        for level in auto_levels:
            params.append({
                'mode'           : 'auto',
                'src_period_ns'  : src_p,
                'dst_period_ns'  : dst_p,
                'stretch_cycles' : 8,   # ignored by DUT when AUTO=1
                'sync_stages'    : 2,
                'auto_stretch'   : 1,
                'src_clk_hz'     : src_hz,
                'dst_clk_hz'     : dst_hz,
                'test_level'     : level,
            })

    # ---- 3) Auto under-sized (cliff). Only at 'full' level so we
    # actually run the cliff_probe phase that verifies drops are clean.
    # DUT computes STRETCH from the *claimed* SRC_CLK_HZ (slow), but the
    # simulation drives a much faster src period.
    cliff_cases = [
        # (real_src_period_ns, dst_period_ns, claimed_src_hz, claimed_dst_hz)
        (10, 40, 10_000_000,  100_000_000),  # claim 10 MHz src, actually 100 MHz
        (10, 25, 25_000_000,  100_000_000),  # claim 25 MHz src, actually 100 MHz
    ]
    for (src_p, dst_p, claimed_src_hz, claimed_dst_hz) in cliff_cases:
        params.append({
            'mode'           : 'cliff',
            'src_period_ns'  : src_p,
            'dst_period_ns'  : dst_p,
            'stretch_cycles' : 8,
            'sync_stages'    : 2,
            'auto_stretch'   : 1,
            'src_clk_hz'     : claimed_src_hz,
            'dst_clk_hz'     : claimed_dst_hz,
            'test_level'     : 'full',
        })

    return params


@pytest.mark.parametrize("params", generate_cdc_open_loop_test_params())
def test_cdc_open_loop(request, params):
    """Pytest wrapper for cdc_open_loop.

    Sweeps manual + auto + cliff configs. The TB picks phases based on
    TEST_LEVEL (basic/func/full)."""
    worker_id = os.environ.get('PYTEST_XDIST_WORKER', 'gw0')

    module, repo_root, tests_dir, log_dir, rtl_dict = get_paths({
        'rtl_cmn':           'rtl/common',
        'rtl_amba_shared':   'rtl/amba/shared',
        'rtl_amba_includes': 'rtl/amba/includes',
    })

    dut_name = "cdc_open_loop"
    toplevel = dut_name

    verilog_sources = [
        # Synchronizer used by the DUT
        os.path.join(rtl_dict['rtl_cmn'], "glitch_free_n_dff_arn.sv"),
        # DUT
        os.path.join(rtl_dict['rtl_amba_shared'], f"{dut_name}.sv"),
    ]

    includes = [rtl_dict['rtl_amba_includes']]

    mode         = params['mode']
    src_period   = params['src_period_ns']
    dst_period   = params['dst_period_ns']
    stretch_cyc  = params['stretch_cycles']
    sync_stages  = params['sync_stages']
    auto_stretch = params['auto_stretch']
    src_clk_hz   = params['src_clk_hz']
    dst_clk_hz   = params['dst_clk_hz']
    test_level   = params['test_level']

    stretch_eff = _stretch_eff(
        auto_stretch, sync_stages, src_clk_hz, dst_clk_hz, stretch_cyc
    )

    # Fixed data width keeps the parameter sweep manageable. The walking
    # pattern phase uses this to cover every bit position.
    data_width = 16

    test_name_plus_params = (
        f"test_{worker_id}_cdc_open_loop_"
        f"{mode}_"
        f"src{src_period}ns_dst{dst_period}ns_"
        f"auto{auto_stretch}_stretch{stretch_eff}_"
        f"{test_level}"
    )

    log_path     = os.path.join(log_dir, f'{test_name_plus_params}.log')
    sim_build    = os.path.join(tests_dir, 'local_sim_build', test_name_plus_params)
    enable_waves = bool(int(os.environ.get('WAVES', '0')))
    os.makedirs(sim_build, exist_ok=True)
    os.makedirs(log_dir, exist_ok=True)
    results_path = os.path.join(log_dir, f'results_{test_name_plus_params}.xml')

    # RTL parameter overrides (passed to Verilator)
    rtl_parameters = {
        'DATA_WIDTH'    : str(data_width),
        'STRETCH_CYCLES': str(stretch_cyc),
        'SYNC_STAGES'   : str(sync_stages),
        'AUTO_STRETCH'  : str(auto_stretch),
        'SRC_CLK_HZ'    : str(src_clk_hz),
        'DST_CLK_HZ'    : str(dst_clk_hz),
    }

    # Per-level timeouts scaled by the slower clock period
    base_timeout_ms = {'basic': 2000, 'func': 8000, 'full': 20000}
    slow_factor = max(1.0, max(src_period, dst_period) / 10.0)
    timeout_ms = int(base_timeout_ms[test_level] * slow_factor)

    extra_env = {
        'TRACE_FILE'          : f"{sim_build}/dump.fst",
        'VERILATOR_TRACE'     : '1',
        'DUT'                 : dut_name,
        'LOG_PATH'            : log_path,
        'COCOTB_LOG_LEVEL'    : 'INFO',
        'COCOTB_RESULTS_FILE' : results_path,
        'COCOTB_TEST_TIMEOUT' : str(timeout_ms),
        'SEED'                : str(random.randint(0, 1_000_000)),
        'TEST_LEVEL'          : test_level,
        # TB-class env contract
        'TEST_DATA_WIDTH'     : str(data_width),
        'SRC_PERIOD_NS'       : str(src_period),
        'DST_PERIOD_NS'       : str(dst_period),
        'STRETCH_CYCLES'      : str(stretch_cyc),
        'SYNC_STAGES'         : str(sync_stages),
        'AUTO_STRETCH'        : str(auto_stretch),
        'SRC_CLK_HZ'          : str(src_clk_hz),
        'DST_CLK_HZ'          : str(dst_clk_hz),
    }

    compile_args = [
        "--trace",
        "--trace-depth", "99",
        "--trace-max-array", "1024",
        "--trace-underscore",
        "--trace-threads", "1",
    ]

    sim_args = [
        "--trace",
        "--trace-depth", "99",
        "--trace-max-array", "1024",
        "--trace-underscore",
        "--trace-threads", "1",
    ]

    plus_args = [
        f"+src_period={src_period}",
        f"+dst_period={dst_period}",
        f"+auto_stretch={auto_stretch}",
        f"+stretch_eff={stretch_eff}",
        f"+test_level={test_level}",
    ]

    cmd_filename = create_view_cmd(
        log_dir, log_path, sim_build, module, test_name_plus_params
    )

    print(f"\n{'=' * 80}")
    print(f"cdc_open_loop: mode={mode} level={test_level.upper()}")
    print(f"  src={src_period} ns ({1000/src_period:.2f} MHz)  "
          f"dst={dst_period} ns ({1000/dst_period:.2f} MHz)")
    print(f"  AUTO_STRETCH={auto_stretch}  "
          f"claimed SRC_HZ={src_clk_hz:_}  DST_HZ={dst_clk_hz:_}  "
          f"-> STRETCH_EFF={stretch_eff}")
    print(f"  Timeout: {timeout_ms/1000:.1f}s")
    print(f"{'=' * 80}")

    try:
        run(
            python_search=[tests_dir],
            verilog_sources=verilog_sources,
            includes=includes,
            toplevel=toplevel,
            module=module,
            parameters=rtl_parameters,
            sim_build=sim_build,
            extra_env=extra_env,
            waves=enable_waves,
            keep_files=True,
            compile_args=compile_args,
            sim_args=sim_args,
            plus_args=plus_args,
        )
        print(f"PASSED  cdc_open_loop {mode} {test_level} "
              f"(src={src_period}ns dst={dst_period}ns stretch={stretch_eff})")

    except Exception as e:
        print(f"FAILED  cdc_open_loop {mode} {test_level}: {e}")
        print(f"  log : {log_path}")
        print(f"  view: {cmd_filename}")
        raise
