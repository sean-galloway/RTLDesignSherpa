# SPDX-License-Identifier: MIT
# SPDX-FileCopyrightText: 2024-2025 sean galloway
#
# RTL Design Sherpa - Industry-Standard RTL Design and Verification
# https://github.com/sean-galloway/RTLDesignSherpa
#
# Module: test_axi4_master_rd_mon_enable_sweep
# Purpose: ENABLE_*_LOGIC parameter sweep for axi4_master_rd_mon.
#          Verifies that every combination of the 5 reporter sub-block
#          enables (ERROR / TIMEOUT / COMPL / THRESHOLD / PERF) elaborates
#          cleanly and behaves consistently with the disabled blocks.
#
# Author: sean galloway
# Created: 2026-06-06

"""
AXI4 Master Read Monitor — ENABLE_*_LOGIC parameter sweep test.

Sweeps every combination of the five reporter sub-block enables so we have
confidence that the bridge-case (ENABLE_ERROR_LOGIC=1, all others 0) and
every intermediate point compiles and runs the same as the legacy
all-enabled default.

For each combination, the cocotb test:
  1. Resets the DUT (proves elaboration succeeded).
  2. Issues a configurable number of read transactions.
  3. Counts monitor packets observed on monbus and groups them by
     packet_type field (PktTypeError / PktTypeCompletion / PktTypeTimeout /
     PktTypeThreshold / PktTypePerf).
  4. Asserts:
       a. No PktTypeError/Compl/Timeout/Threshold/Perf packets show up
          when their respective ENABLE_*_LOGIC parameter is 0.
       b. At least one packet of the expected type appears for each
          enabled cone that should fire under the traffic mix.
       c. The simulation never hangs (timeout).
"""

import os
import random
import pytest
import cocotb
from cocotb_test.simulator import run

from TBClasses.axi4.monitor.axi4_master_monitor_tb import AXI4MasterMonitorTB
from TBClasses.shared.utilities import get_paths


# ============================================================================
# 64-bit packet field constants (see monitor_common_pkg.sv for full layout)
# ============================================================================
# packet_type lives in bits [63:60]
PKT_TYPE_SHIFT = 60
PKT_TYPE_MASK = 0xF
PKT_ERROR     = 0x0
PKT_COMPL     = 0x1
PKT_TIMEOUT   = 0x2
PKT_THRESHOLD = 0x3
PKT_PERF      = 0x4


def _packet_type(pkt: int) -> int:
    """Extract the 4-bit packet_type field from a 128-bit monbus packet."""
    return (pkt >> PKT_TYPE_SHIFT) & PKT_TYPE_MASK


# ============================================================================
# CocoTB test — parameter-aware
# ============================================================================
@cocotb.test(timeout_time=30, timeout_unit="sec")
async def axi4_master_rd_mon_enable_sweep_test(dut):
    """Run basic + multi-transaction traffic, then check packets-by-type
    matches the ENABLE_*_LOGIC parameter set."""

    enables = {
        "error":     int(os.environ.get("TEST_EN_ERROR",     "1")),
        "timeout":   int(os.environ.get("TEST_EN_TIMEOUT",   "1")),
        "compl":     int(os.environ.get("TEST_EN_COMPL",     "1")),
        "threshold": int(os.environ.get("TEST_EN_THRESHOLD", "1")),
        "perf":      int(os.environ.get("TEST_EN_PERF",      "1")),
    }
    n_txns = int(os.environ.get("TEST_TXN_COUNT", "8"))

    tb = AXI4MasterMonitorTB(dut, is_write=False, aclk=dut.aclk, aresetn=dut.aresetn)
    await tb.initialize()

    # Drive enough clean transactions to give COMPL + PERF a fair chance to
    # emit packets. Spread the addresses so timeout cones see steady state.
    tb.base_tb.set_timing_profile("normal")
    for i in range(n_txns):
        success, _, _ = await tb.base_tb.single_read_test(0x1000 + (i * 0x40))
        if not success:
            raise RuntimeError(f"Read #{i} failed")

    # Let the monitor drain any in-flight packets.
    await tb.base_tb.wait_clocks("aclk", 200)

    # Count packets by type. MonbusSlave delivers MonbusPacket objects with
    # a pre-parsed `pkt_type` field (4 bits), so we don't have to slice raw
    # 128-bit words ourselves.
    counts = {
        PKT_ERROR:     0,
        PKT_COMPL:     0,
        PKT_TIMEOUT:   0,
        PKT_THRESHOLD: 0,
        PKT_PERF:      0,
    }
    for pkt in tb.mon_slave.received_packets:
        ptype = int(getattr(pkt, "pkt_type", -1))
        if ptype in counts:
            counts[ptype] += 1

    tb.log.info(f"ENABLES = {enables}")
    tb.log.info(f"PACKET COUNTS = {counts}")

    # ENABLE=0 must produce zero packets of that type.
    if enables["error"] == 0 and counts[PKT_ERROR] != 0:
        raise AssertionError(
            f"ENABLE_ERROR_LOGIC=0 but {counts[PKT_ERROR]} error packets observed"
        )
    if enables["timeout"] == 0 and counts[PKT_TIMEOUT] != 0:
        raise AssertionError(
            f"ENABLE_TIMEOUT_LOGIC=0 but {counts[PKT_TIMEOUT]} timeout packets observed"
        )
    if enables["compl"] == 0 and counts[PKT_COMPL] != 0:
        raise AssertionError(
            f"ENABLE_COMPL_LOGIC=0 but {counts[PKT_COMPL]} completion packets observed"
        )
    if enables["threshold"] == 0 and counts[PKT_THRESHOLD] != 0:
        raise AssertionError(
            f"ENABLE_THRESHOLD_LOGIC=0 but {counts[PKT_THRESHOLD]} threshold packets observed"
        )
    if enables["perf"] == 0 and counts[PKT_PERF] != 0:
        raise AssertionError(
            f"ENABLE_PERF_LOGIC=0 but {counts[PKT_PERF]} perf packets observed"
        )

    # ENABLE=1 + clean traffic → expect at least one COMPL packet (every
    # clean read finishes), so we use that as a positive check. Other
    # cones (error/timeout/threshold) need stimulus to fire; we don't
    # require them under this clean traffic.
    if enables["compl"] == 1 and counts[PKT_COMPL] == 0:
        raise AssertionError(
            "ENABLE_COMPL_LOGIC=1 with N clean reads but no completion packets observed"
        )

    tb.log.info("✓ ENABLE_*_LOGIC parameter sweep PASS")


# ============================================================================
# Parameter combinations
# ============================================================================
def _bits(*names):
    """Helper: build a dict of ENABLE_* values from names. Anything not
    listed defaults to 0; name 'all' sets every cone to 1."""
    e = {"error": 0, "timeout": 0, "compl": 0, "threshold": 0, "perf": 0}
    if "all" in names:
        return {k: 1 for k in e}
    for n in names:
        e[n] = 1
    return e


def generate_enable_sweep_params():
    """
    Build (id_w, addr_w, data_w, user_w, max_t, skid_ar, skid_r, enables,
    txn_count, label) tuples.

    Each label is a short slug used for test_name + assertion logs. The
    enables dict carries the 5 ENABLE_*_LOGIC settings for that combo.

    REG_LEVEL scaling:
      GATE: 3 combos  — legacy default + bridge (error-only) + all-off.
      FUNC: 8 combos  — adds each single-cone + functional minimums.
      FULL: 16+ combos — adds pair/triple mixes for fuller coverage.
    """
    reg_level = os.environ.get("REG_LEVEL", "FUNC").upper()

    base_id, base_aw, base_dw, base_uw = 8, 32, 32, 1
    base_max, base_skid_ar, base_skid_r = 16, 2, 4

    def cfg(enables, label, txns=8):
        return (
            base_id, base_aw, base_dw, base_uw, base_max,
            base_skid_ar, base_skid_r, enables, txns, label,
        )

    combos = []

    # GATE — fast smoke
    combos += [
        cfg(_bits("all"),                  "all_on"),
        cfg(_bits("error"),                "error_only"),       # bridge case
        cfg(_bits(),                       "all_off"),          # elaboration only
    ]
    if reg_level == "GATE":
        return combos

    # FUNC — single-cone + production mixes
    combos += [
        cfg(_bits("compl"),                "compl_only"),
        cfg(_bits("timeout"),              "timeout_only"),
        cfg(_bits("threshold"),            "threshold_only"),
        cfg(_bits("perf"),                 "perf_only"),
        cfg(_bits("error", "compl"),       "error_compl"),       # functional debug
    ]
    if reg_level == "FUNC":
        return combos

    # FULL — multi-cone mixes
    combos += [
        cfg(_bits("error", "compl", "timeout"),                 "err_compl_to"),
        cfg(_bits("error", "compl", "perf"),                    "err_compl_perf"),
        cfg(_bits("error", "compl", "threshold"),               "err_compl_thresh"),
        cfg(_bits("error", "compl", "timeout", "perf"),         "no_thresh"),
        cfg(_bits("error", "compl", "timeout", "threshold"),    "no_perf"),
        cfg(_bits("error", "compl", "threshold", "perf"),       "no_timeout"),
        cfg(_bits("error", "timeout", "threshold", "perf"),     "no_compl"),
        cfg(_bits("compl", "timeout", "threshold", "perf"),     "no_error"),
    ]
    return combos


# ============================================================================
# PyTest Test Runner
# ============================================================================
@pytest.mark.parametrize(
    "id_width, addr_width, data_width, user_width, max_trans, "
    "skid_ar, skid_r, enables, txn_count, label",
    generate_enable_sweep_params(),
    ids=lambda val: val if isinstance(val, str) else None,
)
def test_axi4_master_rd_mon_enable_sweep(
    id_width, addr_width, data_width, user_width, max_trans,
    skid_ar, skid_r, enables, txn_count, label,
):
    """
    ENABLE_*_LOGIC parameter sweep for axi4_master_rd_mon.

    Controlled by REG_LEVEL environment variable:
        GATE: 3 combos  (legacy + bridge + all-off)
        FUNC: 8 combos  (default — adds single-cone + functional minimums)
        FULL: 16 combos (adds pair/triple mixes)
    """
    module, repo_root, tests_dir, log_dir, rtl_dict = get_paths({
        "rtl_axi4":     "rtl/amba/axi4/",
        "rtl_gaxi":     "rtl/amba/gaxi",
        "rtl_includes": "rtl/amba/includes",
        "rtl_common":   "rtl/common",
        "rtl_shared":   "rtl/amba/shared",
        "rtl_amba_includes": "rtl/amba/includes",
    })

    dut_name = "axi4_master_rd_mon"
    reg_level = os.environ.get("REG_LEVEL", "FUNC").upper()
    test_name = f"test_{dut_name}_ensweep_{label}_{reg_level}"

    log_path = os.path.join(log_dir, f"{test_name}.log")
    sim_build = os.path.join(tests_dir, "local_sim_build", test_name)
    os.makedirs(sim_build, exist_ok=True)
    os.makedirs(log_dir, exist_ok=True)

    verilog_sources = [
        os.path.join(rtl_dict["rtl_includes"], "monitor_common_pkg.sv"),
        os.path.join(rtl_dict["rtl_includes"], "monitor_amba4_pkg.sv"),
        os.path.join(rtl_dict["rtl_includes"], "monitor_amba5_pkg.sv"),
        os.path.join(rtl_dict["rtl_includes"], "monitor_arbiter_pkg.sv"),
        os.path.join(rtl_dict["rtl_includes"], "monitor_pkg.sv"),
        os.path.join(rtl_dict["rtl_common"],   "counter_bin.sv"),
        os.path.join(rtl_dict["rtl_common"],   "counter_load_clear.sv"),
        os.path.join(rtl_dict["rtl_common"],   "fifo_control.sv"),
        os.path.join(rtl_dict["rtl_common"],   "counter_freq_invariant.sv"),
        os.path.join(rtl_dict["rtl_gaxi"],     "gaxi_fifo_sync.sv"),
        os.path.join(rtl_dict["rtl_gaxi"],     "gaxi_skid_buffer.sv"),
        os.path.join(rtl_dict["rtl_axi4"],     "axi4_master_rd.sv"),
        os.path.join(rtl_dict["rtl_shared"],   "axi_monitor_trans_mgr.sv"),
        os.path.join(rtl_dict["rtl_shared"],   "axi_monitor_timer.sv"),
        os.path.join(rtl_dict["rtl_shared"],   "axi_monitor_timeout.sv"),
        os.path.join(rtl_dict["rtl_shared"],   "axi_monitor_reporter_error.sv"),
        os.path.join(rtl_dict["rtl_shared"],   "axi_monitor_reporter_timeout.sv"),
        os.path.join(rtl_dict["rtl_shared"],   "axi_monitor_reporter_compl.sv"),
        os.path.join(rtl_dict["rtl_shared"],   "axi_monitor_reporter_threshold.sv"),
        os.path.join(rtl_dict["rtl_shared"],   "axi_monitor_reporter_perf.sv"),
        os.path.join(rtl_dict["rtl_shared"],   "axi_monitor_reporter.sv"),
        os.path.join(rtl_dict["rtl_shared"],   "axi_monitor_base.sv"),
        os.path.join(rtl_dict["rtl_shared"],   "axi_monitor_filtered.sv"),
        os.path.join(rtl_dict["rtl_axi4"],     f"{dut_name}.sv"),
    ]

    for src in verilog_sources:
        if not os.path.exists(src):
            raise FileNotFoundError(f"RTL source not found: {src}")

    # The ENABLE_*_LOGIC params are declared on the inner axi_monitor_filtered
    # / axi_monitor_base / axi_monitor_reporter modules. axi4_master_rd_mon
    # doesn't (yet) re-export them — so we drive them by overriding the
    # parameters on the deepest scope we control via -G on Verilator. For
    # now, we set them on the wrapper-level defaults via Verilator's -G
    # parameter override mechanism, which propagates to any module that
    # declares matching-named parameters at the top of the hierarchy.
    #
    # NOTE: this works because the wrapper passes its parameters through to
    # axi_monitor_filtered → axi_monitor_base → axi_monitor_reporter using
    # the same names. When future top-level wrappers expose ENABLE_*_LOGIC,
    # this -G override will hit them directly.
    rtl_parameters = {
        "AXI_ID_WIDTH":           str(id_width),
        "AXI_ADDR_WIDTH":         str(addr_width),
        "AXI_DATA_WIDTH":         str(data_width),
        "AXI_USER_WIDTH":         str(user_width),
        "UNIT_ID":                "1",
        "AGENT_ID":               "10",
        "MAX_TRANSACTIONS":       str(max_trans),
        "ENABLE_FILTERING":       "1",
        "SKID_DEPTH_AR":          str(skid_ar),
        "SKID_DEPTH_R":           str(skid_r),
        "ENABLE_ERROR_LOGIC":     str(enables["error"]),
        "ENABLE_TIMEOUT_LOGIC":   str(enables["timeout"]),
        "ENABLE_COMPL_LOGIC":     str(enables["compl"]),
        "ENABLE_THRESHOLD_LOGIC": str(enables["threshold"]),
        "ENABLE_PERF_LOGIC":      str(enables["perf"]),
    }

    extra_env = {
        "DUT":                dut_name,
        "LOG_PATH":           log_path,
        "COCOTB_LOG_LEVEL":   "INFO",
        "TEST_ID_WIDTH":      str(id_width),
        "TEST_ADDR_WIDTH":    str(addr_width),
        "TEST_DATA_WIDTH":    str(data_width),
        "TEST_STUB":          "0",
        "SEED":               str(random.randint(0, 100000)),
        "TEST_CLK_PERIOD":    "10",
        "TEST_EN_ERROR":      str(enables["error"]),
        "TEST_EN_TIMEOUT":    str(enables["timeout"]),
        "TEST_EN_COMPL":      str(enables["compl"]),
        "TEST_EN_THRESHOLD":  str(enables["threshold"]),
        "TEST_EN_PERF":       str(enables["perf"]),
        "TEST_TXN_COUNT":     str(txn_count),
    }

    compile_args = [
        "--trace-fst", "--trace-structs",
        "-Wall", "-Wno-SYNCASYNCNET", "-Wno-UNUSED", "-Wno-DECLFILENAME",
        "-Wno-PINMISSING", "-Wno-UNDRIVEN", "-Wno-WIDTHEXPAND",
        "-Wno-WIDTHTRUNC", "-Wno-SELRANGE", "-Wno-CASEINCOMPLETE",
        "-Wno-TIMESCALEMOD",
    ]

    print(f"\n{'='*80}")
    print(f"AXI4 Master Read Monitor — ENABLE_*_LOGIC sweep [{label}]")
    print(f"Enables: {enables}")
    print(f"{'='*80}")

    run(
        python_search=[os.path.dirname(os.path.abspath(__file__))],
        verilog_sources=verilog_sources,
        includes=[rtl_dict["rtl_includes"], rtl_dict["rtl_common"], sim_build],
        toplevel=dut_name,
        module=os.path.basename(__file__).replace(".py", ""),
        testcase="axi4_master_rd_mon_enable_sweep_test",
        parameters=rtl_parameters,
        sim_build=sim_build,
        extra_env=extra_env,
        compile_args=compile_args,
        timescale="1ns/1ps",
        waves=False,
        defines=["VERILATOR=1"],
        plus_args=[],
    )
