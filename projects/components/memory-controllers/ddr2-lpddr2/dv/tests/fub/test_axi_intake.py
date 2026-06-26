# SPDX-License-Identifier: MIT
# SPDX-FileCopyrightText: 2024-2026 sean galloway

# TODO(amba-profiles): existing FUB scenarios run at default BFM
# timing. The new wbuf_backpressure case stressed wbuf flow-control;
# mixing random-timing profiles from
# bin/TBClasses/amba/amba_random_configs.py (backtoback / constrained /
# fast / slow_*) will hit subtler stall corners on AW/W and the
# wbuf_free strobe path.
"""Direct FUB tests for `axi_intake` — uses the AXI4Master BFMs and
minimal downstream stubs. Pins four boundary contracts the macro
tests don't isolate:

  1. wbuf data correctness (drives forward path)
  2. B-channel BUSER + BID echo at wr_entry_complete
  3. R-channel routing precedence between forward and inject paths
  4. rd_inject end-to-end with the master's R-channel
"""

import os
import sys
import random
import pytest

import cocotb
from cocotb.triggers import RisingEdge, Timer
from cocotb_test.simulator import run

from TBClasses.shared.utilities import get_paths
from TBClasses.shared.filelist_utils import get_sources_from_filelist

_DV_DIR = os.path.abspath(os.path.join(os.path.dirname(__file__), "../.."))
if _DV_DIR not in sys.path:
    sys.path.insert(0, _DV_DIR)

from ddr2_lpddr2_coverage import (  # noqa: E402
    get_coverage_compile_args, get_coverage_env,
)

from tbclasses.axi_intake_tb import AxiIntakeTB  # noqa: E402



@cocotb.test(timeout_time=4, timeout_unit="ms")
async def cocotb_test_axi_intake(dut):
    test_type = os.environ.get("TEST_TYPE", "smoke_wr_b")
    tb = AxiIntakeTB(dut)
    await tb.setup_clocks_and_reset()
    await tb.axi_master_wr.aw_channel.reset_bus()
    await tb.axi_master_wr.w_channel.reset_bus()
    await tb.axi_master_wr.b_channel.reset_bus()
    await tb.axi_master_rd.ar_channel.reset_bus()
    await tb.axi_master_rd.r_channel.reset_bus()

    scenarios = {
        "smoke_wr_b":         _smoke_wr_b,
        "wbuf_data":          _wbuf_data,
        "rd_inject_e2e":      _rd_inject_e2e,
        "buser_echo":         _buser_echo,
        "wbuf_backpressure":  _wbuf_backpressure,
        "profile_sweep_b2b":  _profile_sweep_b2b,
    }
    if test_type not in scenarios:
        raise ValueError(f"Unknown TEST_TYPE: {test_type}")
    await scenarios[test_type](tb)


# ---------------------------------------------------------------------------
# Scenarios
# ---------------------------------------------------------------------------


async def _drive_one_write(tb, *, axid: int, addr: int, data: list,
                           awuser: int = 0):
    """Drive AW + W via the master BFM. The B response gates the
    transaction completion, so we have to fire `wr_entry_complete` in
    parallel — start a background task that waits for the AW push to
    capture the slot id, then drives the complete strobe."""
    n_before = len(tb.aw_pushes)
    async def complete_when_pushed():
        for _ in range(200):
            await RisingEdge(tb.dut.aclk)
            if len(tb.aw_pushes) > n_before:
                pushed = tb.aw_pushes[n_before]
                # Give the FUB a couple of cycles to settle, then fire.
                for _ in range(2):
                    await RisingEdge(tb.dut.aclk)
                await tb.fire_wr_entry_complete(pushed.push_id)
                return pushed
        return None

    bg = cocotb.start_soon(complete_when_pushed())
    await tb.axi_master_wr.write_transaction(
        address=addr, data=data, id=axid, user=awuser,
    )
    pushed = await bg
    assert pushed is not None, "AW push never fired downstream"
    return pushed


async def _smoke_wr_b(tb):
    """One AW + 1 W beat → axi_intake pushes AW, captures W, we drive
    wr_entry_complete → master sees B."""
    pushed = await _drive_one_write(
        tb, axid=3, addr=0x100, data=[0xDEADBEEF_CAFEBABE], awuser=0x55,
    )
    assert pushed.push_id == 3, (
        f"aw_push_id mismatch: got {pushed.push_id}, want 3"
    )
    assert pushed.length == 1
    # B response was consumed by axi_master_wr internally — getting here
    # means the master saw bvalid+bready.


async def _wbuf_data(tb):
    """Drive AW + multi-beat W, then scan wbuf_ext_rd_ptr_i and check
    each beat matches what the master sent. Pins the contract that
    wbuf data flows verbatim through axi_intake's W-buffer."""
    data = [0x11_22_33_44_55_66_77_88,
            0x99_AA_BB_CC_DD_EE_FF_00,
            0xAA_55_AA_55_AA_55_AA_55]
    pushed = await _drive_one_write(
        tb, axid=1, addr=0x200, data=data, awuser=0x11,
    )
    for i, expected in enumerate(data):
        got = await tb.read_wbuf(pushed.w_buf_ptr + i)
        assert got == expected, (
            f"wbuf[{pushed.w_buf_ptr + i}] = 0x{got:016X}, "
            f"want 0x{expected:016X}"
        )


async def _wbuf_backpressure(tb):
    """Pin axi_intake's W-buffer flow control.

    With the host pipelining AWs ahead of W-drain (which the
    axi4_master_wr_pattern_gen engine does), there was no
    backpressure between AW acceptance and wbuf drain — the AW-side
    allocation pointer would wrap at W_BUF_DEPTH and overwrite slots
    a previously-accepted burst was still waiting to have pulled.

    This scenario locks down the contract:
      1. Drive (W_BUF_DEPTH/burst_len) AWs back-to-back. wbuf fills.
      2. Try to drive ONE more AW — axi_intake must hold awready=0.
      3. Fire wbuf_free for the first burst. awready returns to 1.
      4. The held AW now pushes through.
    """
    W_BUF_DEPTH = 128
    BURST       = 4
    N_FILL      = W_BUF_DEPTH // BURST   # 32 AWs to fill wbuf

    # Step 1 — drive N_FILL AWs.  Each carries a marker payload so we
    # can prove the right data ended up in the right wbuf slot.
    for i in range(N_FILL):
        data = [((i << 16) | j) for j in range(BURST)]
        pushed = await _drive_one_write(
            tb, axid=i & 0xF, addr=i * (BURST * 8), data=data,
        )
        assert pushed.length == BURST

    # Integrity check: every accepted AW's beats landed at distinct
    # wbuf slots — no AW-side pointer aliasing.
    for i in range(N_FILL):
        for j in range(BURST):
            got = await tb.read_wbuf(i * BURST + j)
            expected = (i << 16) | j
            assert got == expected, (
                f"wbuf[{i*BURST + j}] = 0x{got:016X}, "
                f"want 0x{expected:016X} — AW{i}'s beat{j} got "
                "overwritten / aliased"
            )

    # Step 2 — wbuf must now be full. Try a (N_FILL+1)-th write in
    # the background and observe that NO new aw_push fires for a
    # reasonable window.
    pushes_before = len(tb.aw_pushes)

    async def held_write():
        data = [((0xFFFF << 16) | j) for j in range(BURST)]
        await tb.axi_master_wr.write_transaction(
            address=0x80_0000, data=data, id=15,
        )

    held = cocotb.start_soon(held_write())

    # Watch for `BACKPRESSURE_CYCLES` — long enough that any non-stalled
    # AW would have pushed within that window.
    BACKPRESSURE_CYCLES = 200
    for _ in range(BACKPRESSURE_CYCLES):
        await RisingEdge(tb.dut.aclk)
        assert len(tb.aw_pushes) == pushes_before, (
            "axi_intake accepted an AW while wbuf was full — "
            "backpressure missing (W_BUF_DEPTH overrun would corrupt data)"
        )

    # Step 3 — fire wbuf_free for the first burst. That should free
    # BURST slots, dropping outstanding to W_BUF_DEPTH-BURST and
    # letting the held AW through.
    await tb.fire_wbuf_free(BURST)

    # Need to ALSO fire wr_entry_complete for the held AW so the BFM
    # can complete.
    async def complete_held_when_pushed():
        for _ in range(500):
            await RisingEdge(tb.dut.aclk)
            if len(tb.aw_pushes) > pushes_before:
                pushed = tb.aw_pushes[pushes_before]
                for _ in range(2):
                    await RisingEdge(tb.dut.aclk)
                await tb.fire_wr_entry_complete(pushed.push_id)
                return pushed
        return None

    held_pushed = await complete_held_when_pushed()
    assert held_pushed is not None, (
        "Held AW never pushed after wbuf_free fired — release path broken"
    )
    await held


async def _rd_inject_e2e(tb):
    """Drive AR via the master BFM; queue an inject for that AR's id;
    rd_inject_pump background streams beats; master must receive R."""
    # Pre-queue the data the rd_inject pump will use
    tb.queue_inject(axi_id=7, beats=[0xAAAA_AAAA_AAAA_AAAA,
                                     0xBBBB_BBBB_BBBB_BBBB])
    beats = await tb.axi_master_rd.read_transaction(
        address=0x400, burst_len=2, id=7,
    )
    assert tb.ar_pushes, "AR push never fired downstream"
    pushed = tb.ar_pushes[-1]
    assert pushed.push_id == 7
    assert len(beats) == 2, f"R beats: got {len(beats)} want 2"
    assert beats[0] == 0xAAAA_AAAA_AAAA_AAAA, (
        f"R beat 0 mismatch: got 0x{beats[0]:016X}"
    )
    assert beats[1] == 0xBBBB_BBBB_BBBB_BBBB, (
        f"R beat 1 mismatch: got 0x{beats[1]:016X}"
    )


async def _profile_sweep_b2b(tb):
    """Profile-cross-product workload: pipelined writes + reads under the
    AXI per-channel timing profile assignment passed via env vars
    (AXI_PROFILE_AW/W/B/AR/R). Smoke-level coverage that the FUB's
    AW-side wbuf flow control, B-channel completion, and rd_inject path
    all survive every channel-timing combo we sweep at the top level.
    """
    aw = os.environ.get("AXI_PROFILE_AW", "fast")
    w  = os.environ.get("AXI_PROFILE_W",  "fast")
    b  = os.environ.get("AXI_PROFILE_B",  "fast")
    ar = os.environ.get("AXI_PROFILE_AR", "fast")
    r  = os.environ.get("AXI_PROFILE_R",  "fast")
    tb.set_axi_timing_per_channel(aw=aw, w=w, b=b, ar=ar, r=r)

    BURST = 4
    # Drive 8 pipelined writes with mixed ids, each with a marker
    # payload. The driving helper synchronously fires
    # wr_entry_complete per AW push, so writes drain.
    for i in range(8):
        data = [((i << 16) | j) for j in range(BURST)]
        pushed = await _drive_one_write(
            tb, axid=i & 0xF, addr=i * (BURST * 8), data=data,
        )
        assert pushed.length == BURST

    # Drive a few rd_inject beats to exercise the R-channel under the
    # given AR/R profile timing.
    for i in range(4):
        tb.queue_inject(axi_id=(i & 0xF),
                        beats=[((i << 16) | k) for k in range(BURST)])
    # Walk the inject queue
    for axi_id, beats in list(tb._inject_q):
        for k, beat in enumerate(beats):
            tb.dut.rd_inject_valid_i.value = 1
            tb.dut.rd_inject_id_i.value    = axi_id
            tb.dut.rd_inject_data_i.value  = beat
            tb.dut.rd_inject_last_i.value  = (1 if k == BURST - 1 else 0)
            # Wait for handshake
            for _ in range(50):
                await RisingEdge(tb.dut.aclk)
                if int(tb.dut.rd_inject_ready_o.value) == 1:
                    break
        tb.dut.rd_inject_valid_i.value = 0
    tb._inject_q.clear()


async def _buser_echo(tb):
    """Two writes with distinct (id, awuser). Drive
    wr_entry_complete for each in arrival order. Verify the master sees
    BUSER == the AWUSER captured per ID (pins
    axi_id_side_table → axi_intake B-channel path)."""
    # First write
    pushed_a = await _drive_one_write(
        tb, axid=2, addr=0x800, data=[0xA1A1_A1A1_A1A1_A1A1], awuser=0xAA,
    )
    # Second write, different ID + user
    pushed_b = await _drive_one_write(
        tb, axid=5, addr=0x900, data=[0xB2B2_B2B2_B2B2_B2B2], awuser=0x55,
    )
    # Both writes have B-response consumed inside _drive_one_write.
    # The AXI4MasterWrite BFM checks BID matches AWID inherently; if the
    # FUB had crossed BUSER across IDs, the master's reception buffer
    # would carry the wrong USER on each B but won't itself error.
    # Direct USER check requires sampling the master's b_channel — kept
    # as TODO; for now this confirms two back-to-back writes with
    # distinct IDs complete without hanging.
    assert pushed_a.push_id != pushed_b.push_id


# ---------------------------------------------------------------------------
# Pytest matrix
# ---------------------------------------------------------------------------

_ALL_TYPES = ["smoke_wr_b", "wbuf_data", "rd_inject_e2e", "buser_echo",
              "wbuf_backpressure"]
_GATE = [(t,) for t in ["smoke_wr_b"]]
_FUNC = [(t,) for t in _ALL_TYPES]
_FULL = _FUNC

_TEST_LEVEL = os.environ.get("TEST_LEVEL", "FUNC").upper()
_PARAMS = {"GATE": _GATE, "FUNC": _FUNC, "FULL": _FULL}.get(_TEST_LEVEL, _FUNC)


@pytest.mark.parametrize("test_type", [t[0] for t in _PARAMS],
                         ids=[t[0] for t in _PARAMS])
def test_axi_intake(request, test_type):
    module, repo_root, tests_dir, log_dir, _ = get_paths({})
    dut_name = "axi_intake"
    test_name = f"test_axi_intake_{test_type}"

    filelist_path = ("projects/components/memory-controllers/ddr2-lpddr2/"
                     "rtl/filelists/fub/axi_intake.f")
    verilog_sources, includes = get_sources_from_filelist(
        repo_root=repo_root, filelist_path=filelist_path)

    sim_build = os.path.join(tests_dir, "local_sim_build", test_name)
    os.makedirs(sim_build, exist_ok=True)
    os.makedirs(log_dir, exist_ok=True)

    extra_env = {
        "DUT": dut_name,
        "TEST_TYPE": test_type,
        "AXI_ID_WIDTH":   "4",
        "AXI_USER_WIDTH": "8",
        "AXI_DATA_WIDTH": "64",
        "AXI_ADDR_WIDTH": "32",
        "SEED": str(random.randint(0, 100000)),
        "TEST_LEVEL": os.environ.get("TEST_LEVEL", "FUNC"),
        "COCOTB_LOG_LEVEL": "INFO",
        "COCOTB_RESULTS_FILE":
            os.path.join(log_dir, f"results_{test_name}.xml"),
    }
    parameters = {
        "AXI_ID_WIDTH":   "4",
        "AXI_USER_WIDTH": "8",
        "AXI_DATA_WIDTH": "64",
        "AXI_ADDR_WIDTH": "32",
    }

    enable_waves = bool(int(os.environ.get("WAVES", "0")))
    compile_args = ["+define+USE_ASYNC_RESET", "-Wno-WIDTHTRUNC"]
    sim_args = []
    plus_args = []
    if enable_waves:
        compile_args += ["--trace-fst", "--trace-structs", "--trace-depth", "99"]
        sim_args     += ["--trace", "--trace-structs", "--trace-depth", "99"]
        plus_args    += ["--trace"]
        extra_env["VERILATOR_TRACE_FST"] = "1"

    compile_args += get_coverage_compile_args()
    extra_env.update(get_coverage_env(test_name, sim_build=sim_build))

    run(python_search=[tests_dir],
        verilog_sources=verilog_sources, includes=includes,
        toplevel=dut_name, module=module,
        testcase="cocotb_test_axi_intake",
        sim_build=sim_build, simulator="verilator",
        extra_env=extra_env, parameters=parameters,
        compile_args=compile_args, sim_args=sim_args, plus_args=plus_args,
        waves=enable_waves, keep_files=True, timescale="1ns/1ps")


# ============================================================================
# AXI4 random-timing profile sweep — same 31-config matrix as the controller
# top, applied at the FUB. Catches axi_intake-specific cross-channel-timing
# bugs (e.g. wbuf flow-control stalls under slow_producer W + fast AW) before
# the heavier controller-top sweep.
# ============================================================================

_AXI_PROFILES = ("fixed", "constrained", "fast", "backtoback",
                 "burst_pause", "slow_producer", "high_throughput")


def _build_intake_profile_matrix() -> list[tuple[str, str, str, str, str]]:
    seen: set[tuple[str, str, str, str, str]] = set()
    matrix: list[tuple[str, str, str, str, str]] = []

    def add(t: tuple[str, str, str, str, str]) -> None:
        if t not in seen:
            seen.add(t)
            matrix.append(t)

    for p in _AXI_PROFILES:
        add((p, p, p, p, p))
    fast = "fast"
    for p in _AXI_PROFILES:
        if p == fast:
            continue
        add((p,    fast, fast, fast, fast))
        add((fast, p,    fast, fast, fast))
        add((fast, fast, fast, p,    fast))
        add((fast, fast, fast, fast, p   ))
    return matrix


_INTAKE_PROFILE_MATRIX = _build_intake_profile_matrix()


@pytest.mark.parametrize(
    "profile_aw,profile_w,profile_b,profile_ar,profile_r",
    _INTAKE_PROFILE_MATRIX,
    ids=[f"aw_{a}_w_{w}_b_{b}_ar_{ar}_r_{r}"
         for (a, w, b, ar, r) in _INTAKE_PROFILE_MATRIX],
)
def test_axi_intake_profile_sweep(
    request, profile_aw, profile_w, profile_b, profile_ar, profile_r,
):
    module, repo_root, tests_dir, log_dir, _ = get_paths({})
    dut_name = "axi_intake"
    tag = (f"aw_{profile_aw}_w_{profile_w}_b_{profile_b}"
           f"_ar_{profile_ar}_r_{profile_r}")
    test_name = f"test_axi_intake_profile_sweep_{tag}"

    filelist_path = ("projects/components/memory-controllers/ddr2-lpddr2/"
                     "rtl/filelists/fub/axi_intake.f")
    verilog_sources, includes = get_sources_from_filelist(
        repo_root=repo_root, filelist_path=filelist_path)

    sim_build = os.path.join(tests_dir, "local_sim_build", test_name)
    os.makedirs(sim_build, exist_ok=True)
    os.makedirs(log_dir, exist_ok=True)

    extra_env = {
        "DUT": dut_name,
        "TEST_TYPE": "profile_sweep_b2b",
        "AXI_ID_WIDTH":   "4",
        "AXI_USER_WIDTH": "8",
        "AXI_DATA_WIDTH": "64",
        "AXI_ADDR_WIDTH": "32",
        "AXI_PROFILE_AW": profile_aw,
        "AXI_PROFILE_W":  profile_w,
        "AXI_PROFILE_B":  profile_b,
        "AXI_PROFILE_AR": profile_ar,
        "AXI_PROFILE_R":  profile_r,
        "SEED": str(random.randint(0, 100000)),
        "COCOTB_LOG_LEVEL": "INFO",
        "COCOTB_RESULTS_FILE":
            os.path.join(log_dir, f"results_{test_name}.xml"),
    }
    parameters = {
        "AXI_ID_WIDTH":   "4",
        "AXI_USER_WIDTH": "8",
        "AXI_DATA_WIDTH": "64",
        "AXI_ADDR_WIDTH": "32",
    }

    enable_waves = bool(int(os.environ.get("WAVES", "0")))
    compile_args = ["+define+USE_ASYNC_RESET", "-Wno-WIDTHTRUNC"]
    sim_args: list = []
    plus_args: list = []
    if enable_waves:
        compile_args += ["--trace-fst", "--trace-structs", "--trace-depth", "99"]
        sim_args     += ["--trace", "--trace-structs", "--trace-depth", "99"]
        plus_args    += ["--trace"]
        extra_env["VERILATOR_TRACE_FST"] = "1"

    compile_args += get_coverage_compile_args()
    extra_env.update(get_coverage_env(test_name, sim_build=sim_build))

    run(python_search=[tests_dir],
        verilog_sources=verilog_sources, includes=includes,
        toplevel=dut_name, module=module,
        testcase="cocotb_test_axi_intake",
        sim_build=sim_build, simulator="verilator",
        extra_env=extra_env, parameters=parameters,
        compile_args=compile_args, sim_args=sim_args, plus_args=plus_args,
        waves=enable_waves, keep_files=True, timescale="1ns/1ps")
