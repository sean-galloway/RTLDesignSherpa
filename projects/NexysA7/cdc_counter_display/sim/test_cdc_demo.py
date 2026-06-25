#!/usr/bin/env python3
"""
test_cdc_demo.py — CocoTB smoke test for cdc_demo_harness + cdc_counter_domain.

Drives the harness directly via its AXIL slave port (the UART bridge is
verified separately in projects/components/converters/dv/). Checks:

  1. BUILD_ID reads back correct.
  2. SCRATCH read-after-write.
  3. Per-counter cfg writes land (DIVISOR / INIT / INCREMENT / CDC_MODE /
     AUTO_INC).
  4. HOST_PRESS injection increments VALUE + PRESS_COUNT (after enough
     dest-domain time for CDC to settle).
  5. CFG_LOAD reloads VALUE to INIT.

The DUT for this sim is cdc_demo_harness (the AXIL slave + CSR file)
wired up to a *direct* cdc_counter_domain — no UART, no top-level. That
keeps the sim small and focused on the harness contract.
"""

import os
import sys
from pathlib import Path

import pytest


# -----------------------------------------------------------------------------
# Pytest wrapper — invoked by `make sim-demo` (or directly via pytest)
# -----------------------------------------------------------------------------

PROJECT_DIR = Path(__file__).resolve().parent.parent
REPO_ROOT   = PROJECT_DIR.parent.parent.parent

def test_cdc_demo():
    """Pytest entry — builds + runs the cocotb sim of the harness."""
    from cocotb_test.simulator import run

    rtl_sources = [
        str(REPO_ROOT / "rtl/common/clock_divider.sv"),
        str(REPO_ROOT / "rtl/common/gray2bin.sv"),
        str(REPO_ROOT / "rtl/common/sync_pulse.sv"),
        str(PROJECT_DIR / "rtl/cdc_demo_harness.sv"),
        str(PROJECT_DIR / "rtl/cdc_counter_domain.sv"),
        str(PROJECT_DIR / "sim/cdc_demo_sim_top.sv"),
    ]
    includes = [str(REPO_ROOT / "rtl/amba/includes")]

    sim_build = PROJECT_DIR / "sim/sim_build_demo"
    sim_build.mkdir(parents=True, exist_ok=True)

    run(
        verilog_sources = rtl_sources,
        includes        = includes,
        toplevel        = "cdc_demo_sim_top",
        module          = "cocotb_cdc_demo",
        python_search   = [str(PROJECT_DIR / "sim")],
        sim_build       = str(sim_build),
        toplevel_lang   = "verilog",
        compile_args    = ["-sv", "-Wno-WIDTH", "-Wno-UNUSEDSIGNAL", "-Wno-UNUSEDPARAM"],
        sim_args        = ["--timescale", "1ns/1ps"],
        timescale       = "1ns/1ps",
        extra_env       = {"SIM": os.environ.get("SIM", "verilator")},
    )


# -----------------------------------------------------------------------------
# CocoTB test (lives in cocotb_cdc_demo.py — see below for the file layout)
# -----------------------------------------------------------------------------
# This file is purely the pytest wrapper. The cocotb test functions live in
# sim/cocotb_cdc_demo.py and the sim-only top in sim/cdc_demo_sim_top.sv.
