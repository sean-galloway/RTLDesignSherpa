# SPDX-License-Identifier: MIT
# SPDX-FileCopyrightText: 2026 sean galloway
"""Run the SAME host program against the harness in simulation, over UART.

This is the sim half of the silicon/sim equivalence. `ddr2_char_uart_tb_top`
wraps the full `ddr2_char_harness` (real UART bridge + harness_csr + engines +
pumice controller); a cocotb UARTMaster/Monitor drives the identical ASCII W/R
byte stream the host sends to the FPGA. The DFI side is the framework's
DFISlavePHY + MemoryModel loopback (no a7ddrphy — not simulatable). The
synchronous host program runs in a worker thread via cocotb.external and talks
to the sim through CocotbUartChannel (see cocotb_uart_bridge.py).

Tests:
  * uart_smoke  — BUILD_ID + SCRATCH round-trip over the real bridge RTL,
                  then a tiny write->read CRC pass. Proves the byte protocol
                  and the engine path round-trip in sim.
  * uart_simple — the UNMODIFIED pumice_master.SimpleTest program (init + a
                  write-then-read integrity pass). Proves the authored-once
                  program runs in sim exactly as on silicon.
"""

import os
import sys

import cocotb
import pytest
from cocotb.clock import Clock
from cocotb.triggers import ClockCycles, Timer
from cocotb_test.simulator import run

from TBClasses.shared.utilities import get_paths
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
_HOST = os.path.join(_REPO, "projects/NexysA7/ddr2-characterization/"
                            "flows-ours-uart/host")
_TBC = os.path.join(_REPO, "projects/NexysA7/ddr2-characterization/"
                           "ddr2_char_framework/dv/tbclasses")
_BRIDGE = os.path.join(_REPO, "projects/components/converters/bin")
for _p in (_HOST, _TBC, _BRIDGE):
    if _p not in sys.path:
        sys.path.insert(0, _p)

from cocotb_uart_bridge import make_uart_channel        # noqa: E402
from uart_axi_bridge import UARTAxiBridge               # noqa: E402
from byte_channel import TracingChannel                 # noqa: E402
import ddr2_char as dc                                  # noqa: E402
import pumice_master as pm                              # noqa: E402


# Matches ddr2_char_uart_tb_top default (FPGA_CLK_HZ / UART_BAUD = 16).
CLKS_PER_BIT   = 16
# DFI loopback geometry — MUST match the harness controller (ROW_WIDTH=13,
# COL_WIDTH=10) so the BFM decodes DFI addresses the same way (a mismatch
# corrupts the read path). MemoryModel is lazily zero-paged, so the large
# num_lines only commits the pages the small workloads actually touch.
# beat = 64b = 8 bytes; rate-2 DFI (GEAR=1).
ROW_W, COL_W   = 13, 10
NUM_BANKS      = 8
DRAM_BEAT_BYTES = 8
DRAM_BL        = 4    # DDR2 MR0 default BL — must match the controller


def _make_dfi_slave(dut):
    num_lines = NUM_BANKS * (1 << ROW_W) * (1 << COL_W)
    memory = MemoryModel(num_lines=num_lines, bytes_per_line=DRAM_BEAT_BYTES,
                         log=dut._log)
    mapping = AddressMapping(num_ranks=1, num_banks=NUM_BANKS,
                             num_rows=1 << ROW_W, num_cols=1 << COL_W,
                             mapping="row|bank|col")
    base = DFIBase(dfi_version=DFIVersion.V2_1, memory_type=MemoryType.DDR2,
                   timings=builtin_timings("ddr2-650-mt47h64m16hr"),
                   mapping=mapping, beats_per_burst=DRAM_BL)
    slave = DFISlavePHY(dut, dut.aclk, base=base, memory=memory)
    # Demote HARD JEDEC violations to SOFT: we validate data loopback, not
    # the controller's exact tRCD/tFAW here.
    slave.dram = DramStateModel(timings=base.timings, num_banks=NUM_BANKS,
                                policy=ViolationPolicy(hard=frozenset()))
    return slave, memory


async def _bringup(dut, *, init_complete_delay: int = 20):
    """Clock + reset + DFI loopback BFM + UART pump; returns a DDR2CharDriver
    whose transport is the sim UART (traced)."""
    cocotb.start_soon(Clock(dut.aclk, 10, units="ns").start())

    # DFI PHY-side inputs the BFM does not drive.
    dut.phy_dfi_init_complete.value = 0
    dut.phy_dfi_ctrlupd_ack.value   = 0
    dut.phy_dfi_phyupd_req.value    = 0
    dut.phy_dfi_phyupd_type.value   = 0
    dut.i_uart_rx.value = 1  # UART idle = high

    dut.aresetn.value = 0
    await Timer(100, units="ns")
    dut.aresetn.value = 1
    await ClockCycles(dut.aclk, 10)

    dfi_slave, memory = _make_dfi_slave(dut)

    async def _assert_init_complete():
        await ClockCycles(dut.aclk, init_complete_delay)
        dut.phy_dfi_init_complete.value = 1
    cocotb.start_soon(_assert_init_complete())

    chan = TracingChannel(
        make_uart_channel(dut, dut.aclk, CLKS_PER_BIT, log=dut._log))
    drv = dc.DDR2CharDriver(bridge=UARTAxiBridge(channel=chan))
    return drv, chan, dfi_slave, memory


@cocotb.test(timeout_time=50, timeout_unit="ms")
async def cocotb_test_uart_smoke(dut):
    drv, chan, _dfi, _mem = await _bringup(dut)

    def prog():
        results = {}
        results["build_id"] = drv.build_id()
        results["scratch"] = drv.scratch(0x00C0FFEE)
        # tiny write -> read integrity pass. Mirrors the known-good macro sim
        # flow: BL=4 (= DRAM BL), LFSR pattern (data_mode off), and NO
        # clear_stats between wr and rd (that would drop the latched CRC).
        drv.soft_reset()
        drv.set_controller_cfg(memtype=dc.MEMTYPE_DDR2, t_phy_wrlat=4,
                               t_rddata_en=4, rd_in_order=True)
        seed = 0xABCD1234
        # stride = burst_len * bytes_per_beat, so bursts don't overlap
        stride = 4 * 8
        drv.program_wr_engine(start_addr=0x0, burst_len=4, txn_count=4,
                              stride_0=stride, lfsr_seed=seed,
                              axi_size=dc.AXI_SIZE_8)
        drv.start_wr(); results["wr"] = pm.wait_engine(drv, "wr", timeout_s=30)
        drv.program_rd_engine(start_addr=0x0, burst_len=4, txn_count=4,
                              stride_0=stride, lfsr_seed=seed,
                              axi_size=dc.AXI_SIZE_8)
        drv.start_rd(); results["rd"] = pm.wait_engine(drv, "rd", timeout_s=30)
        exp, act, match, valid = drv.crc()
        results.update(exp=exp, act=act, match=match, valid=valid,
                       mism=drv.beats_mismatched())
        return results

    r = await cocotb.external(prog)()
    dut._log.info("smoke results: %s", r)
    assert r["build_id"] == 0x44445232, f"BUILD_ID mismatch: 0x{r['build_id']:08X}"
    assert r["scratch"] == 0x00C0FFEE, f"SCRATCH round-trip failed: {r['scratch']:#x}"
    assert r["wr"] and r["rd"], f"engine did not finish: {r}"
    assert r["valid"] and r["match"] and r["mism"] == 0, f"CRC/data mismatch: {r}"
    # Wire sanity: the host->device stream is well-formed W/R ASCII lines.
    tx = chan.tx_bytes()
    assert tx.count(b"\n") >= 10, "too few UART commands captured"
    assert tx.startswith((b"R ", b"W ")), f"unexpected first bytes: {tx[:8]!r}"


@cocotb.test(timeout_time=200, timeout_unit="ms")
async def cocotb_test_uart_simple(dut):
    drv, chan, _dfi, _mem = await _bringup(dut)

    def prog():
        # The UNMODIFIED authored-once program. t_rddata_en=4 matches the
        # known-good DFI-loopback config; leveling is skipped (loopback needs
        # none — the read eye is trivially wide).
        st = pm.SimpleTest(drv, base_addr=0x0, t_phy_wrlat=4, t_rddata_en=4)
        st.init(do_leveling=False)
        return st.run(burst_len=8, txn_count=8)

    res = await cocotb.external(prog)()
    dut._log.info("SimpleTest: ok=%s exp=0x%08X act=0x%08X mism=%d",
                  res.ok, res.expected, res.actual, res.mismatched)
    assert res.ok, (f"SimpleTest failed: exp=0x{res.expected:08X} "
                    f"act=0x{res.actual:08X} mismatched={res.mismatched}")


@cocotb.test(timeout_time=400, timeout_unit="ms")
async def cocotb_test_uart_leveling(dut):
    drv, chan, _dfi, _mem = await _bringup(dut)

    def prog():
        # The UNMODIFIED authored-once leveling program. Over DFI loopback the
        # read data is correct at every tap (no analog eye), so leveling should
        # find a full window and centre the tap. This validates the leveling
        # data-eye search + the PHY-CSR poke path end-to-end over UART.
        drv.soft_reset()
        drv.set_controller_cfg(memtype=dc.MEMTYPE_DDR2, t_phy_wrlat=4,
                               t_rddata_en=4, rd_in_order=True)
        return pm.A7Leveling(drv, base_addr=0x0, txn_count=4,
                             verbose=False).run()

    lev = await cocotb.external(prog)()
    dut._log.info("A7Leveling: ok=%s wr_phase=%s rd_tap=%s window=%s",
                  lev.ok, lev.wr_phase, lev.rd_tap, lev.rd_window)
    assert lev.ok, f"leveling found no window over loopback: {lev.notes}"
    lo, hi = lev.rd_window
    assert lo <= lev.rd_tap <= hi, "read tap not centred in window"


# =============================================================================
# pytest wrappers
# =============================================================================
def _run(testcase: str):
    module, repo_root, tests_dir, log_dir, _ = get_paths({})
    dut_name = "ddr2_char_uart_tb_top"
    filelist_path = ("projects/NexysA7/ddr2-characterization/"
                     "ddr2_char_framework/dv/filelists/ddr2_char_uart_tb_top.f")
    verilog_sources, includes = get_sources_from_filelist(
        repo_root=repo_root, filelist_path=filelist_path)

    sim_build = os.path.join(tests_dir, "local_sim_build", testcase)
    os.makedirs(sim_build, exist_ok=True)
    os.makedirs(log_dir, exist_ok=True)

    extra_env = {
        "DUT": dut_name,
        "COCOTB_LOG_LEVEL": "INFO",
        "COCOTB_RESULTS_FILE": os.path.join(log_dir, f"results_{testcase}.xml"),
    }
    compile_args = [
        "+define+USE_ASYNC_RESET",
        "-Wno-MULTIDRIVEN", "-Wno-UNUSED", "-Wno-UNDRIVEN", "-Wno-WIDTH",
        "-Wno-CASEINCOMPLETE", "-Wno-SELRANGE", "-Wno-DECLFILENAME",
        "-Wno-UNUSEDSIGNAL", "-Wno-VARHIDDEN", "-Wno-IMPLICIT",
        "-Wno-CASEOVERLAP", "-Wno-MODDUP",
    ]
    run(python_search=[tests_dir],
        verilog_sources=verilog_sources, includes=includes,
        toplevel=dut_name, module="test_ddr2_char_uart",
        testcase=testcase,
        sim_build=sim_build, simulator="verilator",
        extra_env=extra_env, compile_args=compile_args,
        keep_files=True, timescale="1ns/1ps")


def test_ddr2_char_uart_smoke(request):
    _run("cocotb_test_uart_smoke")


def test_ddr2_char_uart_simple(request):
    _run("cocotb_test_uart_simple")


def test_ddr2_char_uart_leveling(request):
    _run("cocotb_test_uart_leveling")
