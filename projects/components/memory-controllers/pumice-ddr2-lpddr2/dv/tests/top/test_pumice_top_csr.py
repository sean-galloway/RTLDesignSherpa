# SPDX-License-Identifier: MIT
# SPDX-FileCopyrightText: 2024-2026 sean galloway

"""
pumice_top (core + PeakRDL CSR) verified with config PROGRAMMED VIA THE CSR.

Config is written through the register cpuif (by the RDL offsets / regmap), not
ports — proving the generated pumice_csr drives the controller. Then an AXI
write->read burst is checked against the strict DFISlavePHY + golden MemoryModel.
"""

import os
import sys
import random

import cocotb
from cocotb.clock import Clock
from cocotb.triggers import RisingEdge, ClockCycles

from cocotb_test.simulator import run
from TBClasses.shared.utilities import get_paths
from TBClasses.shared.filelist_utils import get_sources_from_filelist

from CocoTBFramework.components.dfi.dfi_base import DFIBase
from CocoTBFramework.components.dfi.dfi_signals import DFIVersion, MemoryType
from CocoTBFramework.components.dfi.dfi_slave_phy import DFISlavePHY
from CocoTBFramework.components.dfi.dram_state import (
    AddressMapping, DramStateModel, ViolationPolicy,
)
from CocoTBFramework.components.dfi.jedec_timings import builtin_timings
from CocoTBFramework.components.shared.memory_model import MemoryModel

_FILELIST = ("projects/components/memory-controllers/pumice-ddr2-lpddr2/"
             "dv/tb/pumice_top_csr_tb_top.f")

NUM_BANKS, ROW_WIDTH, COL_WIDTH = 8, 14, 10
DFI_RATE, DRAM_BEAT = 2, 64
DW = DRAM_BEAT * DFI_RATE
SW = DW // 8
BL = 8
BL_WORDS = BL // DFI_RATE
BURST_INCR = 1

# RDL register offsets
CTRL, TIM_RCD, TIM_RFC, TIM_RRD, TIM_CLWR = 0x000, 0x010, 0x014, 0x018, 0x01C
REFRESH_TUNING, INIT0, INIT1, ADDR_MAP, TIM_RTP, DFI_PHASE, PHY_TIMING = \
    0x048, 0x058, 0x05C, 0x04C, 0x054, 0x060, 0x064


async def _csr_wr(dut, addr, val):
    dut.s_cpuif_req.value = 1
    dut.s_cpuif_req_is_wr.value = 1
    dut.s_cpuif_addr.value = addr
    dut.s_cpuif_wr_data.value = val
    dut.s_cpuif_wr_biten.value = 0xFFFFFFFF
    await RisingEdge(dut.aclk)
    for _ in range(20):
        if int(dut.s_cpuif_wr_ack.value):
            break
        await RisingEdge(dut.aclk)
    dut.s_cpuif_req.value = 0
    dut.s_cpuif_req_is_wr.value = 0
    await RisingEdge(dut.aclk)


async def _csr_rd(dut, addr):
    dut.s_cpuif_req.value = 1
    dut.s_cpuif_req_is_wr.value = 0
    dut.s_cpuif_addr.value = addr
    await RisingEdge(dut.aclk)
    val = 0
    for _ in range(20):
        if int(dut.s_cpuif_rd_ack.value):
            val = int(dut.s_cpuif_rd_data.value)
            break
        await RisingEdge(dut.aclk)
    dut.s_cpuif_req.value = 0
    await RisingEdge(dut.aclk)
    return val


@cocotb.test(timeout_time=30, timeout_unit="ms")
async def cocotb_test_pumice_top_csr(dut):
    cocotb.start_soon(Clock(dut.aclk, 10, units="ns").start())
    cocotb.start_soon(Clock(dut.dfi_clk, 4, units="ns").start())
    # idle
    dut.s_cpuif_req.value = 0; dut.s_cpuif_req_is_wr.value = 0
    dut.s_cpuif_addr.value = 0; dut.s_cpuif_wr_data.value = 0; dut.s_cpuif_wr_biten.value = 0
    for s in ("awid","awaddr","awlen","awsize","awburst","awlock","awcache","awprot",
              "awqos","awregion","awuser","awvalid","wdata","wstrb","wlast","wuser","wvalid",
              "arid","araddr","arlen","arsize","arburst","arlock","arcache","arprot","arqos",
              "arregion","aruser","arvalid"):
        getattr(dut, f"s_axi_{s}").value = 0
    dut.s_axi_awburst.value = BURST_INCR; dut.s_axi_arburst.value = BURST_INCR
    dut.s_axi_bready.value = 1; dut.s_axi_rready.value = 1
    dut.aresetn.value = 0; dut.dfi_rstn.value = 0
    await ClockCycles(dut.aclk, 10)
    dut.aresetn.value = 1; dut.dfi_rstn.value = 1
    await ClockCycles(dut.aclk, 6)

    # ---- PROGRAM CONFIG VIA THE CSR (register writes, by RDL offset) ----
    def pk(*pairs):   # (value, lsb) -> packed word
        w = 0
        for v, lsb in pairs:
            w |= (v << lsb)
        return w
    await _csr_wr(dut, TIM_RCD,  pk((6, 0), (3, 8), (3, 16), (4, 24)))   # tRC,tRCD,tRP,tRAS
    await _csr_wr(dut, TIM_RFC,  pk((8, 0), (0x0400, 16)))               # tRFC, tREFI
    await _csr_wr(dut, TIM_RRD,  pk((2, 0), (6, 8), (2, 16), (1, 24)))   # tRRD,tFAW,tWTR,tCCD
    await _csr_wr(dut, TIM_CLWR, pk((3, 0), (2, 8), (3, 16)))            # CL,CWL,tWR
    await _csr_wr(dut, TIM_RTP,  pk((2, 0), (2, 8)))                     # tRTP,tRTW
    # rd_phase, wr_phase, gear_ratio = log2(DFI_RATE), bl. gear/bl became
    # runtime CSR fields (DFI_PHASE[8:7]/[12:9]) in the config-not-param
    # work; this hand-packed write predates them, and leaving them 0
    # programs a zero-beat burst — the read path then never returns data
    # (PUMICE-002's zero-R-beats signature).
    await _csr_wr(dut, DFI_PHASE, pk((0, 0), (0, 4),
                                     (DFI_RATE.bit_length() - 1, 7), (BL, 9)))
    await _csr_wr(dut, PHY_TIMING, pk((1, 0), (2, 8), (0, 16), (1, 20))) # wrlat,rddata_en,memtype,refresh_burst
    await _csr_wr(dut, REFRESH_TUNING, pk((0, 2)))                        # page_policy_or=OPEN @ [3:2]
    await _csr_wr(dut, ADDR_MAP, pk((10, 0)))                             # bank_lsb=10=ROW_MAJOR
    await _csr_wr(dut, INIT0, 0)                                          # fast init
    await _csr_wr(dut, INIT1, 0)

    # read back one register to prove the CSR round-trips
    rb = await _csr_rd(dut, TIM_RCD)
    assert (rb & 0xFF) == 6 and ((rb >> 8) & 0xFF) == 3, f"CSR readback {rb:#010x} wrong"

    # ---- strict DFISlavePHY + golden memory ----
    mapping = AddressMapping(num_ranks=1, num_banks=NUM_BANKS,
                             num_rows=1 << ROW_WIDTH, num_cols=1 << COL_WIDTH,
                             mapping="row|bank|col")
    memory = MemoryModel(num_lines=NUM_BANKS * (1 << ROW_WIDTH) * (1 << COL_WIDTH),
                         bytes_per_line=DRAM_BEAT // 8, log=dut._log)
    base = DFIBase(dfi_version=DFIVersion.V2_1, memory_type=MemoryType.DDR2,
                   timings=builtin_timings("ddr2-650-mt47h64m16hr"),
                   mapping=mapping, beats_per_burst=BL)
    slave = DFISlavePHY(dut, dut.dfi_clk, base=base, memory=memory,
                        dfi_phase_bytes=DRAM_BEAT // 8)
    slave.dram = DramStateModel(timings=base.timings, num_banks=NUM_BANKS,
                                policy=ViolationPolicy(hard=frozenset()))

    dut.phy_dfi_init_complete.value = 0

    async def _drive_init():
        for _ in range(3000):
            await RisingEdge(dut.dfi_clk)
            try:
                st = int(dut.phy_dfi_init_start.value)
            except Exception:
                st = 1
            if st:
                await ClockCycles(dut.dfi_clk, 4)
                dut.phy_dfi_init_complete.value = 1
                return
    cocotb.start_soon(_drive_init())

    for _ in range(800):
        await RisingEdge(dut.aclk)
        if int(dut.init_done_o.value):
            break
    assert int(dut.init_done_o.value) == 1, "init never completed (CSR-programmed config)"

    rng = random.Random(int(os.environ.get("SEED", "1")))
    n = {"basic": 6, "medium": 16, "full": 32}.get(os.environ.get("TEST_LEVEL", "basic").lower(), 6)
    seen, reqs = set(), []
    while len(reqs) < n:
        bank = rng.randint(0, NUM_BANKS - 1); row = rng.randint(0, 63); col = rng.randint(0, 63) * BL
        word = (row << (COL_WIDTH + 3)) | (bank << COL_WIDTH) | col
        addr = word << 3
        if addr in seen:
            continue
        seen.add(addr)
        reqs.append((addr, [rng.randrange(1 << DW) for _ in range(BL_WORDS)]))

    for k, (addr, data) in enumerate(reqs):
        await _aw(dut, addr, k & 0xF); await _w(dut, data)
        for _ in range(400):
            await RisingEdge(dut.aclk)
            if int(dut.s_axi_bvalid.value) and int(dut.s_axi_bready.value):
                break
    for k, (addr, data) in enumerate(reqs):
        got = []
        cocotb.start_soon(_r_sink(dut, got))
        await _ar(dut, addr, k & 0xF)
        for _ in range(800):
            await RisingEdge(dut.aclk)
            if len(got) >= BL_WORDS:
                break
        assert got[:BL_WORDS] == data, (f"read {k} @ {addr:#x}: got "
            f"{[hex(x) for x in got[:BL_WORDS]]} != {[hex(x) for x in data]}")

    dut._log.info(f"PASS: config PROGRAMMED VIA CSR (regblock hwif) -> init done -> "
                  f"{n} AXI bursts written+read-back vs DFISlavePHY golden")


async def _r_sink(dut, out):
    while len(out) < BL_WORDS:
        await RisingEdge(dut.aclk)
        if int(dut.s_axi_rvalid.value) and int(dut.s_axi_rready.value):
            out.append(int(dut.s_axi_rdata.value) & ((1 << DW) - 1))


async def _aw(dut, addr, wid):
    dut.s_axi_awid.value = wid; dut.s_axi_awaddr.value = addr
    dut.s_axi_awlen.value = BL_WORDS - 1; dut.s_axi_awvalid.value = 1
    await RisingEdge(dut.aclk)
    while int(dut.s_axi_awready.value) == 0:
        await RisingEdge(dut.aclk)
    dut.s_axi_awvalid.value = 0


async def _w(dut, data):
    for i, d in enumerate(data):
        dut.s_axi_wdata.value = d; dut.s_axi_wstrb.value = (1 << SW) - 1
        dut.s_axi_wlast.value = 1 if i == len(data) - 1 else 0; dut.s_axi_wvalid.value = 1
        await RisingEdge(dut.aclk)
        while int(dut.s_axi_wready.value) == 0:
            await RisingEdge(dut.aclk)
    dut.s_axi_wvalid.value = 0; dut.s_axi_wlast.value = 0


async def _ar(dut, addr, rid):
    dut.s_axi_arid.value = rid; dut.s_axi_araddr.value = addr
    dut.s_axi_arlen.value = BL_WORDS - 1; dut.s_axi_arvalid.value = 1
    await RisingEdge(dut.aclk)
    while int(dut.s_axi_arready.value) == 0:
        await RisingEdge(dut.aclk)
    dut.s_axi_arvalid.value = 0


def test_pumice_top_csr(request):
    module, repo_root, tests_dir, log_dir, _ = get_paths({})
    dut_name = "pumice_top_csr_tb_top"
    test_name = "cocotb_test_pumice_top_csr"
    verilog_sources, includes = get_sources_from_filelist(repo_root=repo_root, filelist_path=_FILELIST)
    sim_build = os.path.join(tests_dir, "local_sim_build", test_name)
    os.makedirs(sim_build, exist_ok=True); os.makedirs(log_dir, exist_ok=True)
    params = {"AXI_ID_WIDTH": "8", "AXI_ADDR_WIDTH": "32", "NUM_RANKS": "1",
              "NUM_BANKS": str(NUM_BANKS), "ROW_WIDTH": str(ROW_WIDTH),
              "COL_WIDTH": str(COL_WIDTH), "DFI_RATE": str(DFI_RATE),
              "DRAM_BEAT_WIDTH": str(DRAM_BEAT), "BL": str(BL),
              "NUM_ENTRIES": "8", "N_SRAM_SLOTS": "8"}
    extra_env = {"DUT": dut_name, "LOG_PATH": os.path.join(log_dir, f"{test_name}.log"),
                 "COCOTB_LOG_LEVEL": "INFO",
                 "COCOTB_RESULTS_FILE": os.path.join(log_dir, f"results_{test_name}.xml"),
                 "SEED": os.environ.get('SEED', str(random.randint(0, 100000))),
                 "TEST_LEVEL": os.environ.get("TEST_LEVEL", "basic")}
    extra_env.update(params)
    run(python_search=[tests_dir], verilog_sources=verilog_sources, includes=includes,
        toplevel=dut_name, module=module, testcase="cocotb_test_pumice_top_csr",
        sim_build=sim_build, simulator="verilator", extra_env=extra_env, parameters=params,
        compile_args=["+define+USE_ASYNC_RESET", "--public-flat-rw", "-Wno-MULTIDRIVEN"],
        waves=False, keep_files=True, timescale="1ns/1ps")
