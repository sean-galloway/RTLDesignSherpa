# SPDX-License-Identifier: MIT
# SPDX-FileCopyrightText: 2024-2026 sean galloway

"""
End-to-end runner for `pumice_dfi_layer` (two async clocks).

A DFI-domain memory model on the pin side captures the write burst off
dfi_wrdata (when dfi_wrdata_en) and returns it on dfi_rddata/valid after the
read window (dfi_rddata_en). Proves the whole layer + single CDC: ctl cmd ->
DFI command bus, ctl wrdata -> dfi_wrdata (t_phy_wrlat), dfi_rddata -> ctl
rddata, all across the async boundary.
"""

import os
import sys
import random
from collections import deque

import cocotb
from cocotb.clock import Clock
from cocotb.triggers import RisingEdge
from cocotb_test.simulator import run

from TBClasses.shared.utilities import get_paths
from TBClasses.shared.filelist_utils import get_sources_from_filelist

_FILELIST = ("projects/components/memory-controllers/pumice-ddr2-lpddr2/"
             "rtl/filelists/macro/pumice_dfi_layer.f")

# config
NUM_BANKS, ROW_WIDTH, COL_WIDTH = 8, 14, 10
RKW, BKW = 1, 3
DFI_RATE, DRAM_BEAT = 2, 64
DFI_DW = DRAM_BEAT * DFI_RATE          # 128
DFI_SW = DFI_DW // 8
BL = 8
BL_WORDS = BL // DFI_RATE              # 4
WRLAT, RDEN = 2, 2

OP_WR, OP_RD = 4, 2

# CDC FIFO payload packings
WD_DW = 1 + DFI_SW + DFI_DW            # {last,strb,data}
RD_DW = 1 + 2 + DFI_DW                 # {last,resp,data}


def pack_cmd(op, bank, row, col, ap=0):
    v = op & 0xF
    v |= (0 & ((1 << RKW) - 1)) << 4
    v |= (bank & ((1 << BKW) - 1)) << (4 + RKW)
    v |= (row & ((1 << ROW_WIDTH) - 1)) << (4 + RKW + BKW)
    v |= (col & ((1 << COL_WIDTH) - 1)) << (4 + RKW + BKW + ROW_WIDTH)
    v |= (ap & 1) << (4 + RKW + BKW + ROW_WIDTH + COL_WIDTH)
    return v


def pack_wd(data, strb, last):
    return (data & ((1 << DFI_DW) - 1)) | (strb << DFI_DW) | (last << (DFI_DW + DFI_SW))


@cocotb.test(timeout_time=5, timeout_unit="ms")
async def cocotb_test_pumice_dfi_layer(dut):
    cocotb.start_soon(Clock(dut.ctl_clk, 10, units='ns').start())
    cocotb.start_soon(Clock(dut.dfi_clk, 4, units='ns').start())
    dut.ctl_rstn.value = 0
    dut.dfi_rstn.value = 0
    dut.cmd_valid_i.value = 0
    dut.cmd_data_i.value = 0
    dut.wd_valid_i.value = 0
    dut.wd_data_i.value = 0
    dut.rd_ready_i.value = 1
    dut.init_start_i.value = 0
    dut.memtype_i.value = 0
    dut.rd_phase_i.value = 0
    dut.wr_phase_i.value = 0
    dut.t_phy_wrlat_i.value = WRLAT
    dut.t_rddata_en_i.value = RDEN
    dut.dfi_rddata_i.value = 0
    dut.dfi_rddata_valid_i.value = 0
    for _ in range(8):
        await RisingEdge(dut.ctl_clk)
    dut.ctl_rstn.value = 1
    dut.dfi_rstn.value = 1
    for _ in range(6):
        await RisingEdge(dut.ctl_clk)

    rng = random.Random(int(os.environ.get("SEED", "1")))
    burst = [rng.randrange(1 << DFI_DW) for _ in range(BL_WORDS)]
    captured = []          # words captured off dfi_wrdata
    rd_out = []            # words received back on the ctl rddata stream

    # ---- DFI-domain memory model (dfi_clk) ----
    async def dfi_model():
        rd_pending = deque()      # words queued to return
        returning = False
        ret = []
        ret_i = 0
        rd_gap = 0
        while True:
            await RisingEdge(dut.dfi_clk)
            # capture writes
            if int(dut.dfi_wrdata_en_o.value) != 0:
                captured.append(int(dut.dfi_wrdata_o.value))
            # on read window, schedule the stored burst back after a few cycles
            if int(dut.dfi_rddata_en_o.value) != 0 and not returning and not rd_pending:
                rd_pending.append(list(captured))    # return what we captured
            # start returning after a small read latency
            if rd_pending and not returning:
                rd_gap += 1
                if rd_gap >= 3:
                    ret = rd_pending.popleft()
                    returning = True
                    ret_i = 0
                    rd_gap = 0
            if returning:
                dut.dfi_rddata_i.value = ret[ret_i]
                dut.dfi_rddata_valid_i.value = (1 << DFI_RATE) - 1
                ret_i += 1
                if ret_i >= len(ret):
                    returning = False
            else:
                dut.dfi_rddata_valid_i.value = 0

    # ---- ctl rddata sink ----
    async def rd_sink():
        while True:
            await RisingEdge(dut.ctl_clk)
            if int(dut.rd_valid_o.value) and int(dut.rd_ready_i.value):
                rd = int(dut.rd_data_o.value)
                rd_out.append(rd & ((1 << DFI_DW) - 1))

    cocotb.start_soon(dfi_model())
    cocotb.start_soon(rd_sink())

    # ---- push write data (fill the FIFO first so the drive is bubble-free) ----
    async def push_cmd(v):
        dut.cmd_data_i.value = v
        dut.cmd_valid_i.value = 1
        await RisingEdge(dut.ctl_clk)
        while int(dut.cmd_ready_o.value) == 0:
            await RisingEdge(dut.ctl_clk)
        dut.cmd_valid_i.value = 0

    for i, w in enumerate(burst):
        dut.wd_data_i.value = pack_wd(w, (1 << DFI_SW) - 1, 1 if i == BL_WORDS - 1 else 0)
        dut.wd_valid_i.value = 1
        await RisingEdge(dut.ctl_clk)
        while int(dut.wd_ready_o.value) == 0:
            await RisingEdge(dut.ctl_clk)
    dut.wd_valid_i.value = 0

    await push_cmd(pack_cmd(OP_WR, bank=3, row=0x123, col=0x40))
    for _ in range(40):
        await RisingEdge(dut.ctl_clk)
    await push_cmd(pack_cmd(OP_RD, bank=3, row=0x123, col=0x40))

    for _ in range(400):
        if len(rd_out) >= BL_WORDS:
            break
        await RisingEdge(dut.ctl_clk)

    assert captured == burst, \
        f"write burst on DFI {[hex(x) for x in captured]} != {[hex(x) for x in burst]}"
    assert rd_out[:BL_WORDS] == burst, \
        f"read burst back {[hex(x) for x in rd_out[:BL_WORDS]]} != {[hex(x) for x in burst]}"
    dut._log.info(f"PASS: wrote {BL_WORDS} words to DFI, read them back through the CDC")


def test_pumice_dfi_layer(request):
    module, repo_root, tests_dir, log_dir, _ = get_paths({})
    dut_name = "pumice_dfi_layer"
    test_name = "cocotb_test_pumice_dfi_layer"
    verilog_sources, includes = get_sources_from_filelist(repo_root=repo_root, filelist_path=_FILELIST)
    sim_build = os.path.join(tests_dir, "local_sim_build", test_name)
    os.makedirs(sim_build, exist_ok=True)
    os.makedirs(log_dir, exist_ok=True)
    params = {"NUM_RANKS": "1", "NUM_BANKS": str(NUM_BANKS), "ROW_WIDTH": str(ROW_WIDTH),
              "COL_WIDTH": str(COL_WIDTH), "DFI_RATE": str(DFI_RATE),
              "DRAM_BEAT_WIDTH": str(DRAM_BEAT), "BL": str(BL)}
    extra_env = {"DUT": dut_name, "LOG_PATH": os.path.join(log_dir, f"{test_name}.log"),
                 "COCOTB_LOG_LEVEL": "INFO",
                 "COCOTB_RESULTS_FILE": os.path.join(log_dir, f"results_{test_name}.xml"),
                 "SEED": os.environ.get('SEED', str(random.randint(0, 100000)))}
    extra_env.update(params)
    run(python_search=[tests_dir], verilog_sources=verilog_sources, includes=includes,
        toplevel=dut_name, module=module, testcase="cocotb_test_pumice_dfi_layer",
        sim_build=sim_build, simulator="verilator", extra_env=extra_env, parameters=params,
        compile_args=["+define+USE_ASYNC_RESET"], waves=False, keep_files=True, timescale="1ns/1ps")
