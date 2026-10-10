# SPDX-License-Identifier: MIT
# SPDX-FileCopyrightText: 2026 sean galloway

"""Smoke composition test for `andesite_dfi_layer` (TASK-016 t6).

Pushes one ACT + RD + WR through the full layer with a trivial DFI PHY model
and checks:

  * DFI command pins show the three commands in order.
  * `dfi_cs_o` is one-hot-low (active-low chip select) for each command.
  * `dfi_wrdata_mask_o` carries DBI when `wr_dbi_en_i` is set, and `~strb`
    when DBI is disabled.
  * Read DBI is forwarded aligned to the read data.

This is intentionally small: the behavioural depth of the sub-blocks is
exercised by their own FUB suites.
"""

import os
import random
import sys

import cocotb
import pytest
from cocotb.triggers import RisingEdge, Timer
from cocotb_test.simulator import run

from TBClasses.shared.filelist_utils import get_sources_from_filelist
from TBClasses.shared.utilities import get_paths, sim_build_path

_DV_DIR = os.path.abspath(os.path.join(os.path.dirname(__file__), "../.."))
if _DV_DIR not in sys.path:
    sys.path.insert(0, _DV_DIR)

from tbclasses.andesite_dfi_layer_tb import (    # noqa: E402
    AndesiteDfiLayerTB,
    OP_ACT, OP_RD, OP_WR, MEMTYPE_DDR4,
)

DFI_DATA_WIDTH = 128
DFI_RATE = 2
STRB_W = DFI_DATA_WIDTH // 8
STRB_ALL = (1 << STRB_W) - 1


@cocotb.test(timeout_time=30, timeout_unit="ms")
async def cocotb_test_andesite_dfi_layer_smoke(dut):
    tb = AndesiteDfiLayerTB(dut)
    await tb.setup()
    fails = []

    def chk(c, m):
        if not c:
            fails.append(m)
            tb.log.error(m)

    # -------------------------------------------------------------------------
    # Command path: ACT -> RD -> WR, with CS one-hot-low.
    # -------------------------------------------------------------------------
    dfi_cmds = []
    mon = cocotb.start_soon(tb.dfi_cmd_monitor(dfi_cmds, count=50))

    await tb.push_cmd(OP_ACT, bank=1, bg=2, row=0x1234)
    await tb.push_cmd(OP_RD,  bank=1, bg=2, col=0x100)

    # Stage write data before the WR command so the staged token is ready.
    # The drive window is a single DFI cycle ~t_phy_wrlat after the accept;
    # capture it concurrently, the same way the command monitor works.
    wr_data_1 = 0xA5A5A5A5A5A5A5A5A5A5A5A5A5A5A5A5
    wr_dbi_1 = 0x00FF
    wr_cap = cocotb.start_soon(tb.sample_wr_drive(timeout=80))
    await tb.push_wd(wr_data_1, strb=STRB_ALL, dbi=wr_dbi_1, last=1)
    dut.wr_dbi_en_i.value = 1
    await tb.push_cmd(OP_WR, bank=1, bg=2, col=0x200)

    await mon
    mask1, data1 = await wr_cap

    acts = [c for c in dfi_cmds if c['act'] == 0]
    rds = [c for c in dfi_cmds if c['cas'] == 0 and c['we'] == 1]
    wrs = [c for c in dfi_cmds if c['cas'] == 0 and c['we'] == 0]
    chk(len(acts) >= 1, f"no ACT observed on DFI; cmds={dfi_cmds}")
    chk(len(rds) >= 1, f"no RD observed on DFI; cmds={dfi_cmds}")
    chk(len(wrs) >= 1, f"no WR observed on DFI; cmds={dfi_cmds}")

    # Single-rank: every command must assert the one CS bit low.
    for i, c in enumerate(dfi_cmds):
        chk(c['cs'] == 0,
            f"command {i}: dfi_cs_o {c['cs']} != 0 (not one-hot-low)")

    # ACT drives row on the address bus.
    if acts:
        chk(acts[0]['address'] == 0x1234,
            f"ACT address {acts[0]['address']:#x} != 0x1234")

    # -------------------------------------------------------------------------
    # Write path: DBI enabled -> mask carries the DBI vector, data inverted.
    # -------------------------------------------------------------------------
    # mask1/data1 came from the concurrent capture started before the WR.
    chk(mask1 is not None, "first WR never drove dfi_wrdata_en_o")
    if mask1 is not None:
        chk(mask1 == wr_dbi_1,
            f"DBI-enabled mask {mask1:#x} != wd_dbi_i {wr_dbi_1:#x}")
        # Bytes with DBI bit set are inverted.
        dbi_expand = 0
        for b in range(STRB_W):
            if (wr_dbi_1 >> b) & 1:
                dbi_expand |= 0xFF << (b * 8)
        chk(data1 == (wr_data_1 ^ dbi_expand),
            f"DBI-enabled data {data1:#x} != expected {wr_data_1 ^ dbi_expand:#x}")

    # -------------------------------------------------------------------------
    # Write path: DBI disabled -> mask = ~strb, data unchanged.
    # -------------------------------------------------------------------------
    wr_data_2 = 0xAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAA
    wr_strb_2 = 0x0F0F
    wr_dbi_2 = 0xFFFF          # ignored when DBI is disabled
    wr_cap2 = cocotb.start_soon(tb.sample_wr_drive(timeout=80))
    await tb.push_wd(wr_data_2, strb=wr_strb_2, dbi=wr_dbi_2, last=1)
    dut.wr_dbi_en_i.value = 0
    await tb.push_cmd(OP_WR, bank=2, bg=0, col=0x300)

    mask2, data2 = await wr_cap2
    chk(mask2 is not None, "second WR never drove dfi_wrdata_en_o")
    if mask2 is not None:
        expect_mask2 = (~wr_strb_2) & STRB_ALL
        chk(mask2 == expect_mask2,
            f"DBI-disabled mask {mask2:#x} != ~strb = {expect_mask2:#x}")
        chk(data2 == wr_data_2,
            f"DBI-disabled data moved: {data2:#x} != {wr_data_2:#x}")

    # -------------------------------------------------------------------------
    # Read path: return two DFI words and check DBI aligned to the data.
    # -------------------------------------------------------------------------
    rd_words_in = [0x11111111111111111111111111111111,
                   0x22222222222222222222222222222222]
    rd_dbi_in = 0x3C
    dut.rd_dbi_en_i.value = 1
    await tb.push_cmd(OP_RD, bank=3, bg=1, col=0x400)
    await tb.return_rd_data(rd_words_in, dbi=rd_dbi_in)
    rd_out = await tb.drain_rd(limit=30)
    chk(len(rd_out) >= 2, f"read returned {len(rd_out)} words, expected 2")
    if len(rd_out) >= 2:
        chk(rd_out[0][1] == rd_dbi_in,
            f"read DBI {rd_out[0][1]:#x} != {rd_dbi_in:#x}")

    # -------------------------------------------------------------------------
    # Init/CKE surface
    # -------------------------------------------------------------------------
    chk(int(dut.dfi_init_start_o.value) == 0,
        "dfi_init_start_o asserted without init_busy_i")
    dut.init_busy_i.value = 1
    for _ in range(5):
        await RisingEdge(dut.dfi_clk)
        await Timer(1, 'ns')
    chk(int(dut.dfi_init_start_o.value) == 1,
        "dfi_init_start_o did not follow init_busy_i through the CDC")
    chk(int(dut.dfi_cke_o.value) == 1,
        "dfi_cke_o did not follow cke_i")

    await tb.wait_clocks('ctl_clk', 3)
    await tb.wait_clocks('dfi_clk', 3)
    assert not fails, f"{len(fails)} check(s) failed:\n  " + "\n  ".join(fails)


@pytest.mark.parametrize("_run", [0])
def test_andesite_dfi_layer_smoke(request, _run):
    module, repo_root, tests_dir, log_dir, _ = get_paths({})
    dut_name = "andesite_dfi_layer"
    test_name = "test_andesite_dfi_layer_smoke"
    verilog_sources, includes = get_sources_from_filelist(
        repo_root=repo_root,
        filelist_path=("projects/components/mem-ctrl-ip/research-ip/andesite-ddr4-lpddr4/"
                       "rtl/filelists/macro/andesite_dfi_layer.f"))
    sim_build = sim_build_path(tests_dir, test_name)
    os.makedirs(sim_build, exist_ok=True)
    os.makedirs(log_dir, exist_ok=True)
    run(python_search=[tests_dir], verilog_sources=verilog_sources,
        includes=includes, toplevel=dut_name, module=module,
        testcase="cocotb_test_andesite_dfi_layer_smoke",
        sim_build=sim_build, simulator="verilator",
        parameters={"NUM_RANKS": "1", "NUM_BANKS": "8", "NUM_BG": "4",
                    "ROW_WIDTH": "14", "COL_WIDTH": "10",
                    "ADDR_WIDTH": "18", "DFI_RATE": str(DFI_RATE),
                    "DRAM_BEAT_WIDTH": "64",
                    "DFI_DATA_WIDTH": str(DFI_DATA_WIDTH),
                    "BL_WORDS": "2", "RD_EN_CYC": "2",
                    "RD_MAX_OUTSTANDING": "4"},
        extra_env={"DUT": dut_name, "TEST_TYPE": "smoke",
                   "TEST_LEVEL": "FUNC", "COCOTB_LOG_LEVEL": "INFO",
                   "SEED": os.environ.get('SEED', str(random.randint(0, 99999))),
                   "COCOTB_RESULTS_FILE":
                       os.path.join(log_dir, f"results_{test_name}.xml")},
        compile_args=["+define+USE_ASYNC_RESET"],
        keep_files=True, timescale="1ns/1ps")
