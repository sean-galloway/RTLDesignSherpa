# SPDX-License-Identifier: MIT
# SPDX-FileCopyrightText: 2024-2026 sean galloway
#
# Author: sean galloway
# Created: 2026-06-17

"""
Test runner for axi_frontend_macro.

Methodology mirrors stream's macro-level test runners (e.g.,
projects/components/stream/dv/tests/macro/test_datapath_rd_test.py):

  - pytest parametrize generates the test matrix
  - cocotb_test.simulator.run invokes Verilator/Icarus
  - One cocotb test function dispatches to per-TEST_TYPE handlers
  - TB class encapsulates DUT interactions (see tbclasses/)

Test types (initial set):
  - smoke         : push one AW, push a matching AR -> expect forward hit
  - miss          : push one AW, push a non-matching AR -> expect rd push
  - partial_strb  : AW with full_strb=0, matching AR -> expect rd push
  - len_mismatch  : AW for 8 beats, AR for 4 beats -> expect rd push
"""

import os
import sys
import random
import logging
import pytest

import cocotb
from cocotb.triggers import RisingEdge, ReadOnly
from cocotb_test.simulator import run

from TBClasses.shared.utilities import get_paths, get_repo_root
from TBClasses.shared.filelist_utils import get_sources_from_filelist

# Add the component's dv/ directory to sys.path so `tbclasses.*` is importable.
# Hyphens in the path (memory-controllers, ddr2-lpddr2) preclude a dotted-import
# from repo root, so we keep the import root-relative to the component dv dir.
_DV_DIR = os.path.abspath(os.path.join(os.path.dirname(__file__), "../.."))
if _DV_DIR not in sys.path:
    sys.path.insert(0, _DV_DIR)

from tbclasses.axi_frontend_macro_tb import (  # noqa: E402
    AxiFrontendMacroTB,
    WriteEntry,
)


# ---------------------------------------------------------------------------
# CocoTB top-level test (dispatches by TEST_TYPE)
# ---------------------------------------------------------------------------

@cocotb.test(timeout_time=1, timeout_unit="ms")
async def cocotb_test_axi_frontend(dut):
    test_type = os.environ.get("TEST_TYPE", "smoke")
    log = logging.getLogger("axi_frontend_test")
    log.info(f"TEST_TYPE = {test_type}")

    tb = AxiFrontendMacroTB(dut)
    await tb.setup()

    scenarios = {
        "smoke":              _run_smoke,
        "miss":               _run_miss,
        "partial_strb":       _run_partial_strb,
        "len_mismatch":       _run_len_mismatch,
        "wr_stream":          _run_wr_stream,
        "rd_stream":          _run_rd_stream,
        "mixed_stream":       _run_mixed_stream,
        "snarf_stream":       _run_snarf_stream,
        "same_id_in_order":   _run_same_id_in_order,
        "mixed_id_ooo":       _run_mixed_id_ooo,
        "wr_full_lifecycle":  _run_wr_full_lifecycle,
        "rd_full_lifecycle":  _run_rd_full_lifecycle,
        "wr_cam_full":        _run_wr_cam_full,
        "last_write_wins":    _run_last_write_wins,
        "issued_then_snarf":  _run_issued_then_snarf,
        "concurrent_aw_ar":   _run_concurrent_aw_ar,
    }
    if test_type not in scenarios:
        raise ValueError(f"Unknown TEST_TYPE: {test_type}")
    await scenarios[test_type](tb)


# ---------------------------------------------------------------------------
# Test scenarios
# ---------------------------------------------------------------------------

async def _run_smoke(tb):
    """Push one AW; push a same-address AR with same length and full_strb.
    Expect: forward hit (no rd CAM push)."""
    aw = WriteEntry(addr=0x0000_4080, axi_id=3, length=4,
                    w_buf_ptr=0, strb_ptr=0, full_strb=True)
    aw_slot = await tb.push_aw(aw)

    # Let snapshot stabilize one cycle before driving the AR
    await RisingEdge(tb.dut.mc_clk)

    outcome = await tb.push_ar(addr=0x0000_4080, axi_id=3, length=4)
    assert outcome["kind"] == "forward", f"expected forward, got {outcome}"
    assert outcome["src_slot"] == aw_slot, \
        f"src_slot {outcome['src_slot']} != aw_slot {aw_slot}"
    assert outcome["w_buf_ptr"] == aw.w_buf_ptr, \
        f"w_buf_ptr {outcome['w_buf_ptr']} != aw.w_buf_ptr {aw.w_buf_ptr}"
    assert await tb.rd_cam_occupancy() == 0, "rd CAM should be empty on forward hit"
    assert await tb.wr_cam_occupancy() == 1, "wr CAM should hold the in-flight write"
    tb.log.info("smoke PASS")


async def _run_miss(tb):
    """Push one AW; push a different-address AR. Expect: rd CAM push."""
    aw = WriteEntry(addr=0x0000_4080, axi_id=3, length=4,
                    w_buf_ptr=0, strb_ptr=0, full_strb=True)
    await tb.push_aw(aw)

    await RisingEdge(tb.dut.mc_clk)

    outcome = await tb.push_ar(addr=0x0000_8080, axi_id=5, length=4)
    assert outcome["kind"] == "rd_push", f"expected rd_push, got {outcome}"
    assert await tb.rd_cam_occupancy() == 1, "rd CAM should hold the read"
    assert await tb.wr_cam_occupancy() == 1, "wr CAM still holds the write"
    tb.log.info("miss PASS")


async def _run_partial_strb(tb):
    """AW with full_strb=False; matching AR. Expect: rd CAM push (no forward)."""
    aw = WriteEntry(addr=0x0000_4080, axi_id=3, length=4,
                    w_buf_ptr=0, strb_ptr=0, full_strb=False)
    await tb.push_aw(aw)

    await RisingEdge(tb.dut.mc_clk)

    outcome = await tb.push_ar(addr=0x0000_4080, axi_id=3, length=4)
    assert outcome["kind"] == "rd_push", \
        f"partial-strb writes must NOT forward; got {outcome}"
    tb.log.info("partial_strb PASS")


async def _run_len_mismatch(tb):
    """AW for 8 beats; AR for 4 beats. Expect: rd CAM push (no forward)."""
    aw = WriteEntry(addr=0x0000_4080, axi_id=3, length=8,
                    w_buf_ptr=0, strb_ptr=0, full_strb=True)
    await tb.push_aw(aw)

    await RisingEdge(tb.dut.mc_clk)

    outcome = await tb.push_ar(addr=0x0000_4080, axi_id=3, length=4)
    assert outcome["kind"] == "rd_push", \
        f"length mismatch must NOT forward; got {outcome}"
    tb.log.info("len_mismatch PASS")


# ---------------------------------------------------------------------------
# Pytest wrapper
# ---------------------------------------------------------------------------

#---------------------------------------------------------------------------
# Streaming + lifecycle + ordering scenarios
#
# Address-mapper default layout (ROW_MAJOR, NB=8, COL=10, BYTE_OFFSET=3):
#   axi_addr[2:0]   = byte offset (stripped)
#   axi_addr[12:3]  = col[9:0]
#   axi_addr[15:13] = bank[2:0]
#   axi_addr[29:16] = row[13:0]
#   axi_addr[NR:..] = rank (none at NUM_RANKS=1)
#---------------------------------------------------------------------------

# Stride that keeps (rank,bank,row) constant and increments only col. col
# steps by 1 word (8 bytes). Picking strides of 8 bytes walks through one
# row's columns without ever hitting a new bank or row.
_COL_STRIDE = 8


def _mk_writes(count: int, base_addr: int = 0x0000_4000,
               stride: int = _COL_STRIDE, full_strb: bool = True,
               base_id: int = 0, length: int = 4) -> list:
    out = []
    for i in range(count):
        out.append(WriteEntry(
            addr=base_addr + i * stride,
            axi_id=(base_id + i) & 0xF,
            length=length,
            w_buf_ptr=i * length,     # rough placeholder allocation
            strb_ptr=i * length,
            full_strb=full_strb,
        ))
    return out


def _mk_reads(count: int, base_addr: int = 0x0000_4000,
              stride: int = _COL_STRIDE, base_id: int = 0,
              length: int = 4) -> list:
    return [(base_addr + i * stride, (base_id + i) & 0xF, length)
            for i in range(count)]


async def _run_wr_stream(tb):
    """8 back-to-back AWs with non-overlapping addresses. Verify all land."""
    writes = _mk_writes(8)
    slots = await tb.push_aw_stream(writes)
    assert len(set(slots)) == 8, f"slots not unique: {slots}"
    assert await tb.wr_cam_occupancy() == 8
    assert await tb.rd_cam_occupancy() == 0
    tb.log.info("wr_stream PASS — 8 back-to-back AW")


async def _run_rd_stream(tb):
    """8 back-to-back ARs, none matching any write. Verify all push to rd CAM."""
    reads = _mk_reads(8, base_addr=0x0000_8000)   # disjoint from any write
    outcomes = await tb.push_ar_stream(reads)
    for o in outcomes:
        assert o["kind"] == "rd_push", o
    rd_slots = [o["rd_slot"] for o in outcomes]
    assert len(set(rd_slots)) == 8, f"rd slots not unique: {rd_slots}"
    assert await tb.rd_cam_occupancy() == 8
    assert await tb.wr_cam_occupancy() == 0
    tb.log.info("rd_stream PASS — 8 back-to-back AR all rd_push")


async def _run_mixed_stream(tb):
    """Push 4 writes, then 4 reads at totally different addresses. Verify
    no forwards, both CAMs hold 4."""
    writes = _mk_writes(4, base_addr=0x0000_4000)
    await tb.push_aw_stream(writes)
    reads = _mk_reads(4, base_addr=0x0000_8000)
    outcomes = await tb.push_ar_stream(reads)
    for o in outcomes:
        assert o["kind"] == "rd_push", o
    assert await tb.wr_cam_occupancy() == 4
    assert await tb.rd_cam_occupancy() == 4
    tb.log.info("mixed_stream PASS")


async def _run_snarf_stream(tb):
    """Push 8 writes; immediately stream 8 reads to the SAME addresses with
    the SAME burst length and full_strb. Every read must forward; rd CAM
    must stay empty."""
    writes = _mk_writes(8, base_addr=0x0000_4000)
    aw_slots = await tb.push_aw_stream(writes)

    reads = _mk_reads(8, base_addr=0x0000_4000)
    outcomes = await tb.push_ar_stream(reads)

    for i, o in enumerate(outcomes):
        assert o["kind"] == "forward", f"read {i} did not forward: {o}"
        # The forward source should be one of the AW slots (no exact-index
        # contract — depends on which slot the priority encoder chose).
        assert o["src_slot"] in aw_slots, f"unknown src_slot {o['src_slot']}"
    assert await tb.rd_cam_occupancy() == 0, "no rd push should have happened"
    assert await tb.wr_cam_occupancy() == 8, "writes still in flight"
    assert tb.forward_hits == 8 and tb.forward_misses == 0
    tb.log.info("snarf_stream PASS — all 8 reads forwarded")


async def _run_same_id_in_order(tb):
    """Stream 4 reads with the SAME AXI ID. The rd CAM should allocate
    successive slots; per-ID in-order is preserved by virtue of slot
    allocation order."""
    reads = [(0x0000_8000 + i * _COL_STRIDE, 5, 4) for i in range(4)]
    outcomes = await tb.push_ar_stream(reads)
    for o in outcomes:
        assert o["kind"] == "rd_push", o
    # Slots should be the lowest 4 free
    slots = [o["rd_slot"] for o in outcomes]
    assert slots == sorted(slots), f"slots not in allocation order: {slots}"
    tb.log.info(f"same_id_in_order PASS — slots {slots}")


async def _run_mixed_id_ooo(tb):
    """Stream 4 reads with DIFFERENT AXI IDs. CAM allocation is still
    lowest-first; downstream OoO completion is the rd_data_path's job."""
    reads = [(0x0000_8000 + i * _COL_STRIDE, (i + 1) * 3 & 0xF, 4)
             for i in range(4)]
    outcomes = await tb.push_ar_stream(reads)
    for o in outcomes:
        assert o["kind"] == "rd_push", o
    slots = [o["rd_slot"] for o in outcomes]
    ids = [o["id"] for o in outcomes]
    assert len(set(ids)) == 4, f"IDs not distinct: {ids}"
    assert slots == sorted(slots), f"slots not allocated in order: {slots}"
    tb.log.info(f"mixed_id_ooo PASS — slots {slots} ids {ids}")


async def _run_wr_full_lifecycle(tb):
    """Push one write, take it through the full lifecycle:
    push -> issued -> beats pulled -> b_complete -> slot free."""
    w = WriteEntry(addr=0x0000_4000, axi_id=2, length=4,
                   w_buf_ptr=0, strb_ptr=0, full_strb=True)
    slot = await tb.push_aw(w)
    assert await tb.wr_cam_occupancy() == 1

    await tb.drain_wr_slot(slot, length=4)
    assert await tb.wr_cam_occupancy() == 0, "slot should be free after b_complete"
    tb.log.info("wr_full_lifecycle PASS")


async def _run_rd_full_lifecycle(tb):
    """Push one read; mark issued; strobe 4 beats; verify entry_complete
    fires on the last beat and slot frees."""
    reads = [(0x0000_8000, 7, 4)]
    outcomes = await tb.push_ar_stream(reads)
    assert outcomes[0]["kind"] == "rd_push"
    rd_slot = outcomes[0]["rd_slot"]
    assert await tb.rd_cam_occupancy() == 1

    await tb.drain_rd_slot(rd_slot, length=4)
    # entry_complete is observed combinationally on the last beat cycle
    assert await tb.rd_cam_occupancy() == 0
    tb.log.info("rd_full_lifecycle PASS")


async def _run_wr_cam_full(tb):
    """Push WR_CAM_DEPTH (16) writes — all accepted. Then attempt one more
    while continuing to drive aw_valid_i — aw_ready_o should go low."""
    writes = _mk_writes(16)
    await tb.push_aw_stream(writes)
    assert await tb.wr_cam_occupancy() == 16

    # Drive one more and confirm ready stays low
    tb.dut.aw_valid_i.value = 1
    tb.dut.aw_addr_i.value = 0x0000_9000
    tb.dut.aw_id_i.value = 0
    tb.dut.aw_len_i.value = 4
    tb.dut.aw_w_buf_ptr_i.value = 0
    tb.dut.aw_strb_ptr_i.value = 0
    tb.dut.aw_full_strb_i.value = 1

    for _ in range(4):
        await RisingEdge(tb.dut.mc_clk)
        await tb.settle()
        assert int(tb.dut.aw_ready_o.value) == 0, \
            "aw_ready_o must be low when CAM is full"

    tb.dut.aw_valid_i.value = 0
    tb.log.info("wr_cam_full PASS — backpressure asserts at depth 16")


async def _run_last_write_wins(tb):
    """Push two writes to the SAME address. Then read. The forwarder must
    pick the higher-slot write (more recently pushed)."""
    w0 = WriteEntry(addr=0x0000_4080, axi_id=1, length=4,
                    w_buf_ptr=0, strb_ptr=0, full_strb=True)
    w1 = WriteEntry(addr=0x0000_4080, axi_id=2, length=4,
                    w_buf_ptr=16, strb_ptr=16, full_strb=True)
    s0 = await tb.push_aw(w0)
    s1 = await tb.push_aw(w1)
    assert s1 > s0, f"second write should land in higher slot than first (s0={s0}, s1={s1})"

    await RisingEdge(tb.dut.mc_clk)
    outcome = await tb.push_ar(addr=0x0000_4080, axi_id=3, length=4)
    assert outcome["kind"] == "forward", outcome
    assert outcome["src_slot"] == s1, \
        f"last-write-wins broken: src_slot={outcome['src_slot']}, expected newest={s1}"
    assert outcome["w_buf_ptr"] == w1.w_buf_ptr
    tb.log.info(f"last_write_wins PASS — picked slot {s1} (newest)")


async def _run_issued_then_snarf(tb):
    """A write that has been marked-issued (scheduler claimed it) but whose
    b_complete has NOT yet fired must still be forwardable — the data is
    still in w_buf, and DRAM hasn't been written yet (b_complete signals
    completion). This is correctness for AXI ordering."""
    w = WriteEntry(addr=0x0000_4080, axi_id=1, length=4,
                   w_buf_ptr=0, strb_ptr=0, full_strb=True)
    slot = await tb.push_aw(w)
    await tb.mark_wr_issued(slot)
    for _ in range(4):
        await tb.pull_wr_beat(slot)
    # NOT calling b_complete — slot still valid in the CAM

    outcome = await tb.push_ar(addr=0x0000_4080, axi_id=3, length=4)
    assert outcome["kind"] == "forward", \
        f"read must still forward while wr is in-flight pre-b_complete: {outcome}"
    assert outcome["src_slot"] == slot
    tb.log.info("issued_then_snarf PASS")


async def _run_concurrent_aw_ar(tb):
    """Drive AW and AR valid in the same cycle. Both address mappers must
    fire independently; both CAM pushes accepted."""
    # Pre-drive both with non-matching addresses
    tb.dut.aw_valid_i.value = 1
    tb.dut.aw_addr_i.value = 0x0000_4000
    tb.dut.aw_id_i.value = 1
    tb.dut.aw_len_i.value = 4
    tb.dut.aw_w_buf_ptr_i.value = 0
    tb.dut.aw_strb_ptr_i.value = 0
    tb.dut.aw_full_strb_i.value = 1

    tb.dut.ar_valid_i.value = 1
    tb.dut.ar_addr_i.value = 0x0000_8000
    tb.dut.ar_id_i.value = 2
    tb.dut.ar_len_i.value = 4

    await tb.settle()
    assert int(tb.dut.aw_ready_o.value) == 1
    assert int(tb.dut.ar_ready_o.value) == 1
    aw_slot = int(tb.dut.aw_slot_o.value)
    rd_slot = int(tb.dut.rd_slot_o.value)

    await RisingEdge(tb.dut.mc_clk)
    tb.dut.aw_valid_i.value = 0
    tb.dut.ar_valid_i.value = 0

    await tb.settle()
    assert await tb.wr_cam_occupancy() == 1, "AW push missed"
    assert await tb.rd_cam_occupancy() == 1, "AR push missed"
    tb.log.info(f"concurrent_aw_ar PASS — aw_slot={aw_slot} rd_slot={rd_slot}")


#---------------------------------------------------------------------------
# Parametrize
#---------------------------------------------------------------------------

params = [
    "smoke",
    "miss",
    "partial_strb",
    "len_mismatch",
    "wr_stream",
    "rd_stream",
    "mixed_stream",
    "snarf_stream",
    "same_id_in_order",
    "mixed_id_ooo",
    "wr_full_lifecycle",
    "rd_full_lifecycle",
    "wr_cam_full",
    "last_write_wins",
    "issued_then_snarf",
    "concurrent_aw_ar",
]


@pytest.mark.parametrize("test_type", params)
def test_axi_frontend_macro(request, test_type):
    """Pytest wrapper for the axi_frontend_macro tests."""
    module, repo_root, tests_dir, log_dir, _ = get_paths({})
    dut_name = "axi_frontend_macro"
    test_name = f"test_axi_frontend_macro_{test_type}"

    filelist_path = (
        "projects/components/memory-controllers/ddr2-lpddr2/"
        "rtl/filelists/macro/axi_frontend_macro.f"
    )
    verilog_sources, includes = get_sources_from_filelist(
        repo_root=repo_root, filelist_path=filelist_path
    )

    sim_build = os.path.join(tests_dir, "local_sim_build", test_name)
    os.makedirs(sim_build, exist_ok=True)

    log_path = os.path.join(log_dir, f"{test_name}.log")
    results_path = os.path.join(log_dir, f"results_{test_name}.xml")

    extra_env = {
        "DUT": dut_name,
        "LOG_PATH": log_path,
        "COCOTB_LOG_LEVEL": "INFO",
        "COCOTB_RESULTS_FILE": results_path,
        "SEED": str(random.randint(0, 100000)),
        "TEST_TYPE": test_type,
    }

    # Enable waves with WAVES=1
    enable_waves = bool(int(os.environ.get("WAVES", "0")))
    compile_args = []
    plus_args = []
    if enable_waves:
        compile_args += ["--trace", "--trace-structs"]
        extra_env["VERILATOR_TRACE"] = "1"

    run(
        python_search=[tests_dir],
        verilog_sources=verilog_sources,
        includes=includes,
        toplevel=dut_name,
        module=module,
        testcase="cocotb_test_axi_frontend",
        sim_build=sim_build,
        simulator="verilator",
        extra_env=extra_env,
        compile_args=compile_args,
        plus_args=plus_args,
        timescale="1ns/1ps",
    )
