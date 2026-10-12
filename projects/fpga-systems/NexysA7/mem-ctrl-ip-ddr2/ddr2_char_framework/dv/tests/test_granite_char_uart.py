# SPDX-License-Identifier: MIT
# SPDX-FileCopyrightText: 2026 sean galloway
"""Granite whole-harness UART equivalence — the blen>=2 split-burst repro.

Clone of the pumice ddr2_char_uart smoke against the GRANITE harness: the
same host program the FPGA receives over ttyUSB3, driven through a cocotb
UART into the REAL uart_axil_bridge + harness_csr + AXIL bridge + char
engines + storage-less granite controller, with the framework DFISlavePHY +
MemoryModel loopback on the DFI pins.

Why this exists (2026-10-12): on the Nexys A7 the fixed granite bit passes
blen=1 engine traffic but ANY multi-beat burst (blen>=2, chopped by
mc_wr_splitter into 1-beat sub-bursts at x16) wedges — zero DFI commands,
engine crc_valid set, host B never returns. The BFM-based granite_top_geared
smoke passes at the identical geometry, so the last unmodeled variable is
the REAL ENGINES' AXI flavor. This TB drives those engines.

Pass condition mirrors the board: engines finish, CRC matches, zero beats
mismatched. A hang here is the reproduction the bring-up needs.
"""

import os
import sys

import pytest
import cocotb
from cocotb.triggers import ClockCycles
from cocotb._bridge import bridge
from cocotb_test.simulator import run

from TBClasses.shared.utilities import get_paths, sim_build_path
from TBClasses.shared.filelist_utils import get_sources_from_filelist

from CocoTBFramework.components.dfi.dfi_signals import DFIVersion, MemoryType
from CocoTBFramework.components.dfi.dfi_slave_phy import DFISlavePHY
from CocoTBFramework.components.dfi.dfi_base import DFIBase
from CocoTBFramework.components.dfi.dram_state import (
    AddressMapping, DramStateModel, ViolationPolicy,
)
from CocoTBFramework.components.dfi.jedec_timings import builtin_timings
from CocoTBFramework.components.shared.memory_model import MemoryModel

_REPO = os.environ["REPO_ROOT"]
_HOST = os.path.join(_REPO, "projects/fpga-systems/NexysA7/mem-ctrl-ip-ddr2/"
                            "build-perf/host")
_TBC = os.path.join(_REPO, "projects/fpga-systems/rtl/mem_char_framework/dv/tbclasses")
for _p in (_HOST, _TBC):
    if _p not in sys.path:
        sys.path.insert(0, _p)

from TBClasses.harness.harness import UartSimHarness      # noqa: E402
import ddr2_char as dc                                  # noqa: E402
import pumice_master as pm                              # noqa: E402

# UART bit rate in system clocks (measured floor 4 on the pumice TB).
CLKS_PER_BIT   = int(os.environ.get("TEST_CLKS_PER_BIT", "4"))
FPGA_CLK_HZ    = 100_000_000
UART_BAUD      = FPGA_CLK_HZ // CLKS_PER_BIT
# Board geometry: rate-2 / 32b beat / x16 device / BL4. This is the
# combination that makes the splitter chop every multi-beat host burst into
# 1-beat DRAM sub-bursts — the board-failing shape.
ROW_W, COL_W   = 13, 10
NUM_BANKS      = 8
DRAM_BL        = int(os.environ.get("TEST_DRAM_BL", "4"))
DFI_RATE        = int(os.environ.get("TEST_DFI_RATE", "2"))
DRAM_BEAT_BYTES = int(os.environ.get("TEST_DRAM_BEAT_BYTES", "4"))   # 32b
GEAR_RATIO      = DFI_RATE.bit_length() - 1
DRAM_DEVICE_BYTES = int(os.environ.get("TEST_DRAM_DEVICE_BYTES", "2"))  # x16
BEATS_PER_BURST  = DRAM_BL


def _make_dfi_slave(dut):
    num_lines = NUM_BANKS * (1 << ROW_W) * (1 << COL_W)
    memory = MemoryModel(num_lines=num_lines, bytes_per_line=DRAM_DEVICE_BYTES,
                         log=dut._log)
    mapping = AddressMapping(num_ranks=1, num_banks=NUM_BANKS,
                             num_rows=1 << ROW_W, num_cols=1 << COL_W,
                             mapping="row|bank|col")
    base = DFIBase(dfi_version=DFIVersion.V2_1, memory_type=MemoryType.DDR2,
                   timings=builtin_timings("ddr2-650-mt47h64m16hr"),
                   mapping=mapping, beats_per_burst=BEATS_PER_BURST)
    _strict = os.environ.get("TEST_STRICT_WRITE_TIMING", "0") == "1"
    _wrlat = int(os.environ.get("TEST_WRITE_LATENCY", "0"))
    _strict_rd = os.environ.get("TEST_STRICT_READ_TIMING", "0") == "1"
    _rdlat = int(os.environ.get("TEST_READ_LATENCY", "8"))
    slave = DFISlavePHY(dut, dut.aclk, base=base, memory=memory,
                        strict_write_timing=_strict, write_latency=_wrlat,
                        strict_read_timing=_strict_rd, read_latency=_rdlat,
                        dfi_phase_bytes=DRAM_BEAT_BYTES)
    # Demote HARD JEDEC violations to SOFT: we validate data loopback, not
    # the controller's exact tRCD/tFAW here.
    slave.dram = DramStateModel(timings=base.timings, num_banks=NUM_BANKS,
                                policy=ViolationPolicy(hard=frozenset()))
    return slave, memory


async def _bringup(dut, *, init_complete_delay: int = 20):
    h = UartSimHarness(dut, clks_per_bit=CLKS_PER_BIT,
                       idle_inputs={"phy_dfi_init_complete": 0,
                                    "phy_dfi_ctrlupd_ack": 0,
                                    "phy_dfi_phyupd_req": 0,
                                    "phy_dfi_phyupd_type": 0})
    chan = await h.start()

    dfi_slave, memory = _make_dfi_slave(dut)

    async def _assert_init_complete():
        await ClockCycles(dut.aclk, init_complete_delay)
        dut.phy_dfi_init_complete.value = 1
    cocotb.start_soon(_assert_init_complete())

    drv = dc.DDR2CharDriver(bridge=h.make_bridge())
    return drv, chan, dfi_slave, memory


@cocotb.test(timeout_time=50, timeout_unit="ms")
async def cocotb_test_granite_uart_smoke(dut):
    """Board-failing shape: multi-beat (blen=4) wr+rd through the REAL
    engines and the REAL UART path. On the A7 this wedges with zero DFI
    commands; here it must pass once the entry-store seam is fixed."""
    drv, chan, _dfi, _mem = await _bringup(dut)

    def prog():
        results = {}
        results["build_id"] = drv.build_id()
        results["scratch"] = drv.scratch(0x00C0FFEE)
        drv.soft_reset()
        drv.set_dfi_cmd_delay(int(os.environ.get("TEST_CMD_DELAY", "0")))
        drv.set_controller_cfg(memtype=dc.MEMTYPE_DDR2,
                               t_phy_wrlat=int(os.environ.get("TEST_T_PHY_WRLAT", "0")),
                               t_rddata_en=int(os.environ.get("TEST_T_RDDATA_EN", "6")),
                               rd_in_order=True)
        drv.set_dfi_phase(rd_phase=int(os.environ.get("TEST_RD_PHASE", "0")),
                          wr_phase=int(os.environ.get("TEST_WR_PHASE", "0")),
                          gear_ratio=GEAR_RATIO, bl=DRAM_BL)
        seed = 0xABCD1234
        stride = 4 * 8
        drv.program_wr_engine(start_addr=0x0, burst_len=4, txn_count=4,
                              stride_0=stride, lfsr_seed=seed,
                              axi_size=dc.AXI_SIZE_8)
        drv.start_wr(); results["wr"] = pm.wait_engine(drv, "wr", timeout_s=30)
        results["wr_gen0_status"] = drv.chargen.read("WR_GEN0_STATUS")
        results["done"] = drv.chargen.read("DONE")
        results["errors"] = drv.chargen.read("ERRORS")
        drv.program_rd_engine(start_addr=0x0, burst_len=4, txn_count=4,
                              stride_0=stride, lfsr_seed=seed,
                              axi_size=dc.AXI_SIZE_8)
        drv.start_rd(); results["rd"] = pm.wait_engine(drv, "rd", timeout_s=30)
        exp, act, match, valid = drv.crc()
        results.update(exp=exp, act=act, match=match, valid=valid,
                       mism=drv.beats_mismatched())
        return results

    r = await bridge(prog)()
    dut._log.info("granite smoke results: %s", {k: v for k, v in r.items() if k != "trace"})
    assert r["build_id"] == 0x44445232, f"BUILD_ID mismatch: 0x{r['build_id']:08X}"
    assert r["scratch"] == 0x00C0FFEE, f"SCRATCH round-trip failed: {r['scratch']:#x}"
    assert r["wr"] and r["rd"], f"engine did not finish (board wedges here): {r}"
    assert r["valid"] and r["match"] and r["mism"] == 0, f"CRC/data mismatch: {r}"
    tx = chan.tx_bytes()
    assert tx.count(b"\n") >= 10, "too few UART commands captured"
    assert tx.startswith((b"R ", b"W ")), f"unexpected first bytes: {tx[:8]!r}"


# =============================================================================
# pytest wrapper
# =============================================================================
def test_granite_uart_smoke(request):
    module, repo_root, tests_dir, log_dir, _ = get_paths({})
    dut_name = "granite_char_uart_tb_top"
    filelist_path = ("projects/fpga-systems/NexysA7/mem-ctrl-ip-ddr2/"
                     "ddr2_char_framework/dv/filelists/granite_char_uart_tb_top.f")
    verilog_sources, includes = get_sources_from_filelist(
        repo_root=repo_root, filelist_path=filelist_path)

    tag = request.node.name.replace("[", "_").replace("]", "").replace("-", "_")
    sim_build = sim_build_path(tests_dir, tag)
    os.makedirs(sim_build, exist_ok=True)
    os.makedirs(log_dir, exist_ok=True)

    extra_env = {
        "TEST_T_PHY_WRLAT": os.environ.get("TEST_T_PHY_WRLAT", "0"),
        "TEST_RDDATA_DELAY": os.environ.get("TEST_RDDATA_DELAY", "0"),
        "DUT": dut_name,
        "COCOTB_LOG_LEVEL": "INFO",
        "COCOTB_RESULTS_FILE": os.path.join(log_dir, f"results_{tag}.xml"),
        "TEST_DFI_RATE": str(DFI_RATE),
        "TEST_GEAR_RATIO": str(GEAR_RATIO),
        "TEST_DRAM_BL": str(DRAM_BL),
        "TEST_DRAM_BEAT_BYTES": str(DRAM_BEAT_BYTES),
        "TEST_DRAM_DEVICE_BYTES": str(DRAM_DEVICE_BYTES),
        "TEST_STRICT_WRITE_TIMING": os.environ.get("TEST_STRICT_WRITE_TIMING", "0"),
        "TEST_WRITE_LATENCY": os.environ.get("TEST_WRITE_LATENCY", "0"),
        "TEST_CMD_DELAY": os.environ.get("TEST_CMD_DELAY", "0"),
        "TEST_STRICT_READ_TIMING": os.environ.get("TEST_STRICT_READ_TIMING", "0"),
        "TEST_READ_LATENCY": os.environ.get("TEST_READ_LATENCY", "8"),
        "TEST_RD_PHASE": os.environ.get("TEST_RD_PHASE", "0"),
        "TEST_WR_PHASE": os.environ.get("TEST_WR_PHASE", "0"),
        "TEST_T_RDDATA_EN": os.environ.get("TEST_T_RDDATA_EN", "6"),
    }
    params = {"FPGA_CLK_HZ": str(FPGA_CLK_HZ),
              "UART_BAUD": str(UART_BAUD),
              "ROW_WIDTH": str(ROW_W),
              "DRAM_BEAT_WIDTH": str(DRAM_BEAT_BYTES * 8),
              "DRAM_DEVICE_WIDTH": str(DRAM_DEVICE_BYTES * 8),
              "DFI_RATE": str(DFI_RATE),
              "DRAM_BL": str(DRAM_BL)}
    compile_args = [
        "+define+USE_ASYNC_RESET",
        "-Wno-MULTIDRIVEN", "-Wno-UNUSED", "-Wno-UNDRIVEN", "-Wno-WIDTH",
        "-Wno-CASEINCOMPLETE", "-Wno-SELRANGE", "-Wno-DECLFILENAME",
        "-Wno-UNUSEDSIGNAL", "-Wno-VARHIDDEN", "-Wno-IMPLICIT",
        "-Wno-CASEOVERLAP", "-Wno-MODDUP", "-Wno-PINMISSING",
    ]
    run(python_search=[tests_dir], verilog_sources=verilog_sources, includes=includes,
        toplevel=dut_name, module=module,
        testcase="cocotb_test_granite_uart_smoke",
        sim_build=sim_build, simulator="verilator", extra_env=extra_env,
        parameters=params,
        compile_args=compile_args,
        waves=bool(int(os.environ.get("WAVES", "0"))),
        plus_args=(["--trace"] if int(os.environ.get("WAVES", "0")) else []),
        keep_files=True, timescale="1ns/1ps")
