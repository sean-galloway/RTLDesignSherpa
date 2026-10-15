# SPDX-License-Identifier: MIT
# SPDX-FileCopyrightText: 2026 sean galloway
"""MC-003 residual repro at full-harness fidelity: col_major_bl8_gap.

Runs the board's failing scenario (col-major same-bank row thrash, host BL8,
idle gap 8 between txns, refresh live) through the REAL engines + UART bridge
+ granite controller + DFISlavePHY/MemoryModel (address-accurate,
JEDEC-checked model — the loopback model in test_granite_bankfifo_gap does
not model page/refresh interactions). Knobs: TEST_TREFI (default 585 = the
board value), TEST_TXN (default 64), TEST_GAP (default 8).

A hang shows as wait_engine timeout; corruption shows in crc()/mismatches;
JEDEC violations land in the DFISlavePHY log (policy demoted to soft by the
harness, like the smoke).
"""

import os
import sys

import pytest
import cocotb
from cocotb._bridge import bridge
from cocotb.triggers import RisingEdge
from cocotb_test.simulator import run

from TBClasses.shared.utilities import get_paths, sim_build_path
from TBClasses.shared.filelist_utils import get_sources_from_filelist

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from test_granite_char_uart import (  # noqa: E402,F401
    _bringup, CLKS_PER_BIT, UART_BAUD, ROW_W, COL_W, NUM_BANKS, DRAM_BL,
    DFI_RATE, DRAM_BEAT_BYTES, GEAR_RATIO, DRAM_DEVICE_BYTES, BEATS_PER_BURST,
)

_REPO = os.environ["REPO_ROOT"]
_HOST = os.path.join(_REPO, "projects/fpga-systems/NexysA7/mem-ctrl-ip-ddr2/"
                            "build-perf/host")
if _HOST not in sys.path:
    sys.path.insert(0, _HOST)
import ddr2_char as dc                               # noqa: E402
import pumice_master as pm                           # noqa: E402

_FILELIST = ("projects/fpga-systems/NexysA7/mem-ctrl-ip-ddr2/"
             "ddr2_char_framework/dv/filelists/granite_char_uart_tb_top.f")


async def _dfi_monitor(dut):
    """Command-stream tracer (TRACE=1): logs every DFI command with a
    timestamp to /tmp/dfi_trace.txt. Buffered; skips X reads during reset."""
    from cocotb.utils import get_sim_time
    fh = open("/tmp/dfi_trace.txt", "w")
    fh.write("# dfi command trace\n")
    fh.flush()
    buf = []
    try:
        while True:
            await RisingEdge(dut.aclk)
            try:
                cs_n = dut.phy_dfi_cs_n.value
                if not cs_n.is_resolvable:
                    continue
                cs = int(cs_n)
                if cs == (1 << DFI_RATE) - 1:
                    continue                      # NOP this cycle
                t = get_sim_time("ns")
                r = int(dut.phy_dfi_ras_n.value)
                c = int(dut.phy_dfi_cas_n.value)
                w = int(dut.phy_dfi_we_n.value)
                addr = int(dut.phy_dfi_address.value)
                bank = int(dut.phy_dfi_bank.value)
            except Exception as e:
                if not buf:
                    fh.write(f"# read error: {e!r}\n")
                    fh.flush()
                continue
            for p in range(DFI_RATE):
                if (cs >> p) & 1:
                    continue
                key = ((r >> p) & 1, (c >> p) & 1, (w >> p) & 1)
                op = {(0, 0, 1): "REF", (0, 1, 0): "PRE", (0, 0, 0): "MRS",
                      (1, 0, 1): "RD", (1, 0, 0): "WR"}.get(key)
                if op is None:
                    continue
                a = (addr >> (p * 14)) & 0x3FFF
                b = (bank >> (p * 3)) & 0x7
                buf.append(f"{t} {op} b{b} a{a:04x}")
            if len(buf) >= 64:
                fh.write("\n".join(buf) + "\n")
                buf.clear()
    except Exception as e:
        fh.write(f"# monitor died: {e!r}\n")
    finally:
        if buf:
            fh.write("\n".join(buf) + "\n")
        fh.close()


@cocotb.test(timeout_time=60, timeout_unit="ms")
async def cocotb_test_granite_col_major_gap(dut):
    drv, chan, _dfi, _mem = await _bringup(dut)

    t_refi = int(os.environ.get("TEST_TREFI", "585"), 0)
    txn = int(os.environ.get("TEST_TXN", "64"), 0)
    gap = int(os.environ.get("TEST_GAP", "8"), 0)
    seed = int(os.environ.get("TEST_SEED", "0xABCD1234"), 0)
    mismatches = []
    if os.environ.get("TRACE", "0") == "1":
        cocotb.start_soon(_dfi_monitor(dut))
    # col-major: one row in the SAME bank per txn; wrap at the device.
    stride = (1 << COL_W) * DRAM_DEVICE_BYTES          # one row, same bank
    wrap = (1 << ROW_W) * stride - 1                   # device boundary

    def prog():
        results = {}
        results["build_id"] = drv.build_id()
        drv.soft_reset()
        drv.set_dfi_cmd_delay(int(os.environ.get("TEST_CMD_DELAY", "0")))
        drv.set_controller_cfg(memtype=dc.MEMTYPE_DDR2,
                               t_phy_wrlat=int(os.environ.get("TEST_T_PHY_WRLAT", "0")),
                               t_rddata_en=int(os.environ.get("TEST_T_RDDATA_EN", "4")),
                               rd_in_order=True)
        drv.set_dfi_phase(rd_phase=0, wr_phase=0, gear_ratio=GEAR_RATIO, bl=DRAM_BL)
        drv.set_refresh_interval(t_refi)
        drv.program_wr_engine(start_addr=0x0, burst_len=8, txn_count=txn,
                              stride_0=stride, wrap_mask_0=wrap, gap=gap,
                              lfsr_seed=seed, axi_size=dc.AXI_SIZE_8)
        drv.start_wr()
        results["wr"] = pm.wait_engine(drv, "wr", timeout_s=30)
        results["wr_status"] = drv.chargen.read("WR_GEN0_STATUS")
        drv.program_rd_engine(start_addr=0x0, burst_len=8, txn_count=txn,
                              stride_0=stride, wrap_mask_0=wrap, gap=gap,
                              lfsr_seed=seed, axi_size=dc.AXI_SIZE_8)
        drv.start_rd()
        results["rd"] = pm.wait_engine(drv, "rd", timeout_s=30)
        results["rd_status"] = drv.chargen.read("RD_GEN0_STATUS")
        exp, act, match, valid = drv.crc()
        results.update(exp=exp, act=act, match=match, valid=valid,
                       mism=drv.beats_mismatched(),
                       errors=drv.chargen.read("ERRORS"))
        return results

    r = await bridge(prog)()
    dut._log.info("col_major_gap results: tREFI=%d txn=%d gap=%d -> %s",
                  t_refi, txn, gap,
                  {k: v for k, v in r.items() if k != "trace"})
    assert r["wr"], f"WRITE ENGINE HANG: wr never finished ({r})"
    assert r["rd"], f"READ ENGINE HANG: rd never finished ({r})"
    assert r["valid"] and r["match"] and r["mism"] == 0, \
        f"CRC/data mismatch: mism={r['mism']} errors={r['errors']}"


def test_granite_char_col_major_gap(request):
    module, repo_root, tests_dir, log_dir, _ = get_paths({})
    dut_name = "granite_char_uart_tb_top"
    test_name = "cocotb_test_granite_col_major_gap"
    verilog_sources, includes = get_sources_from_filelist(
        repo_root=repo_root, filelist_path=_FILELIST)
    sim_build = sim_build_path(tests_dir, test_name)
    os.makedirs(sim_build, exist_ok=True)
    os.makedirs(log_dir, exist_ok=True)
    run(python_search=[tests_dir], verilog_sources=verilog_sources,
        includes=includes, toplevel=dut_name, module=module, testcase=test_name,
        sim_build=sim_build, simulator="verilator",
        extra_env={"DUT": dut_name,
                   "LOG_PATH": os.path.join(log_dir, f"{test_name}.log"),
                   "COCOTB_RESULTS_FILE": os.path.join(log_dir, f"results_{test_name}.xml")},
        compile_args=["+define+USE_ASYNC_RESET", "--assert", "--public-flat-rw",
                      "-Wno-PINMISSING", "-Wno-MULTIDRIVEN", "-Wno-WIDTHEXPAND",
                      "-Wno-WIDTHTRUNC"],
        keep_files=True, timescale="1ns/1ps")
