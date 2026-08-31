# SPDX-License-Identifier: MIT
# SPDX-FileCopyrightText: 2024-2026 sean galloway

"""
End-to-end smoke for `pumice_core` (the new 3-layer controller).

Two async clocks. A DFI-domain memory model on the pins: drives dfi_init_complete
after dfi_init_start (so the scheduler's init finishes), captures the write burst
off dfi_wrdata, and returns it on dfi_rddata when the read window opens. The host
drives an AXI write burst then a read burst to the same address; the read data
must equal what was written — proving IFC -> scheduler -> DFI -> (PHY) -> back.
"""

import os
import sys
import random
from collections import deque

import cocotb
from cocotb.clock import Clock
from cocotb.triggers import RisingEdge
from cocotb_test.simulator import run

from TBClasses.shared.utilities import get_paths, sim_build_path
from TBClasses.shared.filelist_utils import get_sources_from_filelist

_FILELIST = ("projects/components/memory-controllers/pumice-ddr2-lpddr2/"
             "rtl/filelists/top/pumice_core.f")

# dv/ on sys.path so `tbclasses.*` resolves; import AFTER the insert.
_DV_DIR = os.path.abspath(os.path.join(os.path.dirname(__file__), "../.."))
if _DV_DIR not in sys.path:
    sys.path.insert(0, _DV_DIR)

from tbclasses.pumice_axi_bfm import PumiceAxiBfm      # noqa: E402

DFI_RATE, DRAM_BEAT = 2, 64
DW = DRAM_BEAT * DFI_RATE          # 128 (host AXI = DFI word)
SW = DW // 8
BL = 8
BL_WORDS = BL // DFI_RATE          # 4  (host AXI burst beats)
BURST_INCR = 1


@cocotb.test(timeout_time=10, timeout_unit="ms")
async def cocotb_test_pumice_core(dut):
    cocotb.start_soon(Clock(dut.aclk, 10, units='ns').start())
    cocotb.start_soon(Clock(dut.dfi_clk, 4, units='ns').start())
    _idle(dut)
    dut.aresetn.value = 0
    dut.dfi_rstn.value = 0
    for _ in range(10):
        await RisingEdge(dut.aclk)
    dut.aresetn.value = 1
    dut.dfi_rstn.value = 1
    for _ in range(6):
        await RisingEdge(dut.aclk)

    bfm = _init_masters(dut)

    captured = []
    rmodel = {"cap": captured}
    cocotb.start_soon(_dfi_model(dut, rmodel))

    # wait for init to complete
    for _ in range(400):
        await RisingEdge(dut.aclk)
        if int(dut.init_done_o.value):
            break
    assert int(dut.init_done_o.value) == 1, "init never completed"

    rng = random.Random(int(os.environ.get("SEED", "1")))
    data = [rng.randrange(1 << DW) for _ in range(BL_WORDS)]
    addr = 0x2000

    # ---- AXI write burst, then read the same address back ----
    # Both go through the master BFMs, which own the handshakes and block
    # through B / collect R for us -- so the old poll-for-bvalid and
    # background _r_sink loops are gone with the hand driving.
    await bfm.write(addr, data, wid=1)
    rd = await bfm.read(addr, rid=1)

    assert len(captured) >= BL_WORDS, f"only {len(captured)} words hit the DFI write bus"
    assert captured[:BL_WORDS] == data, \
        f"DFI write burst {[hex(x) for x in captured[:BL_WORDS]]} != {[hex(x) for x in data]}"
    assert rd[:BL_WORDS] == data, \
        f"AXI read-back {[hex(x) for x in rd[:BL_WORDS]]} != {[hex(x) for x in data]}"
    dut._log.info("PASS: init done; AXI write burst -> DFI -> read burst back == written data")


def _idle(dut):
    dut.memtype_i.value = 0
    dut.page_policy_i.value = 0          # OPEN
    dut.bank_lsb_i.value  = 10   # ROW_MAJOR
    dut.hash_en_i.value   = 0
    dut.hash_seed_i.value = 0
    for t, v in [("t_rcd_i", 2), ("t_rp_i", 2), ("t_ras_i", 3), ("t_rc_i", 4),
                 ("t_wr_i", 2), ("t_rtp_i", 2), ("t_faw_i", 4), ("t_rrd_i", 1),
                 ("t_wtr_i", 1), ("t_rtw_i", 1), ("t_ccd_i", 1)]:
        getattr(dut, t).value = v
    dut.t_refi_i.value = 0x7FFF
    dut.t_rfc_i.value = 8
    dut.refresh_burst_i.value = 1
    for t in ("t_init_wait_i", "t_dll_wait_i"):
        getattr(dut, t).value = 0
    for t in ("t_mrd_wait_i", "t_rp_wait_i", "t_rfc_wait_i"):
        getattr(dut, t).value = 0
    dut.rd_phase_i.value = 0
    dut.wr_phase_i.value = 0
    dut.t_phy_wrlat_i.value = 1
    dut.t_rddata_en_i.value = 1
    # NO s_axi_* here. The master BFMs own every signal on that port,
    # including bready/rready -- a second driver on a BFM-owned signal is a
    # conflict, not a convenience (PUMICE-014).
    dut.dfi_rddata_i.value = 0
    dut.dfi_rddata_valid_i.value = 0
    dut.dfi_init_complete_i.value = 0


async def _dfi_model(dut, m):
    """DFI-domain model: finish init, capture writes, return them on reads."""
    ret = []
    returning = False
    ri = 0
    gap = 0
    pend = deque()
    while True:
        await RisingEdge(dut.dfi_clk)
        if int(dut.dfi_init_start_o.value):
            dut.dfi_init_complete_i.value = 1
        if int(dut.dfi_wrdata_en_o.value) != 0:
            m["cap"].append(int(dut.dfi_wrdata_o.value))
        if int(dut.dfi_rddata_en_o.value) != 0 and not returning and not pend:
            pend.append(list(m["cap"]))
        if pend and not returning:
            gap += 1
            if gap >= 3:
                ret = pend.popleft(); returning = True; ri = 0; gap = 0
        if returning:
            dut.dfi_rddata_i.value = ret[ri]
            dut.dfi_rddata_valid_i.value = (1 << DFI_RATE) - 1
            ri += 1
            if ri >= len(ret):
                returning = False
        else:
            dut.dfi_rddata_valid_i.value = 0


def _init_masters(dut):
    """AXI4 master BFMs on s_axi -- the ONLY thing that drives that port."""
    return PumiceAxiBfm(dut, data_width=DW, bl_words=BL_WORDS)


def test_pumice_core(request):
    module, repo_root, tests_dir, log_dir, _ = get_paths({})
    dut_name = "pumice_core"
    test_name = "cocotb_test_pumice_core"
    verilog_sources, includes = get_sources_from_filelist(repo_root=repo_root, filelist_path=_FILELIST)
    sim_build = sim_build_path(tests_dir, test_name)
    os.makedirs(sim_build, exist_ok=True)
    os.makedirs(log_dir, exist_ok=True)
    params = {"AXI_ID_WIDTH": "8", "AXI_ADDR_WIDTH": "32", "NUM_RANKS": "1",
              "NUM_BANKS": "8", "ROW_WIDTH": "14", "COL_WIDTH": "10",
              "DFI_RATE": str(DFI_RATE), "DRAM_BEAT_WIDTH": str(DRAM_BEAT), "DRAM_BL": str(BL),
              "NUM_ENTRIES": "8", "N_SRAM_SLOTS": "8"}
    extra_env = {"DUT": dut_name, "LOG_PATH": os.path.join(log_dir, f"{test_name}.log"),
                 "COCOTB_LOG_LEVEL": "INFO",
                 "COCOTB_RESULTS_FILE": os.path.join(log_dir, f"results_{test_name}.xml"),
                 "SEED": os.environ.get('SEED', str(random.randint(0, 100000)))}
    extra_env.update(params)
    run(python_search=[tests_dir], verilog_sources=verilog_sources, includes=includes,
        toplevel=dut_name, module=module, testcase="cocotb_test_pumice_core",
        sim_build=sim_build, simulator="verilator", extra_env=extra_env, parameters=params,
        compile_args=["+define+USE_ASYNC_RESET", "--assert"], waves=False, keep_files=True, timescale="1ns/1ps")
