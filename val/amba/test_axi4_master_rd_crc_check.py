# SPDX-License-Identifier: MIT
# SPDX-FileCopyrightText: 2024-2026 sean galloway

# TODO(amba-profiles): exercise every BFM here with the random-timing
# profiles in bin/TBClasses/amba/amba_random_configs.py (backtoback /
# constrained / fast / slow_*). Current scenarios use default timing
# only and miss valid/ready stall-pattern edge cases.
"""Unit-test runner for `axi4_master_rd_crc_check`."""

import os
import sys
import random
import pytest

import cocotb
from cocotb.triggers import RisingEdge, Timer
from cocotb_test.simulator import run

from TBClasses.shared.utilities import get_paths, sim_build_path
from TBClasses.shared.filelist_utils import get_sources_from_filelist
from TBClasses.axi4.axi4_master_rd_crc_check_tb import RdCrcCheckTB


@cocotb.test(timeout_time=200, timeout_unit="ms")
async def cocotb_test_axi4_master_rd_crc_check(dut):
    test_type = os.environ.get("TEST_TYPE", "smoke_match")
    slave_profile = os.environ.get("SLAVE_PROFILE", "backtoback")
    tb = RdCrcCheckTB(dut)
    await tb.setup_clocks_and_reset()
    tb.set_slave_delay_profile(slave_profile)
    scenarios = {
        "smoke_match":         _smoke_match,
        "multi_burst_match":   _multi_burst_match,
        "address_walk":        _address_walk,
        "data_mismatch_sticky": _data_mismatch_sticky,
        "beats_mismatched_count": _beats_mismatched_count,
        "rresp_error_sticky":  _rresp_error_sticky,
        "rerun_after_done":    _rerun_after_done,
        "rd_gap_inserts_idle": _rd_gap_inserts_idle,
        "hash_mode_match":     _hash_mode_match,
        "hash_mode_low_entropy": _hash_mode_low_entropy,
        "arvalid_no_drop":     _arvalid_no_drop,
        "id_mode_counter":     _id_mode_counter,
        "id_mode_lfsr":        _id_mode_lfsr,
        "kb4":                 _kb4,
        "kb32":                _kb32,
        "stray_beat_drained":  _stray_beat_drained,
        "rready_never_throttles": _rready_never_throttles,
        "outstanding_dial":    _outstanding_dial,
    }
    if test_type not in scenarios:
        raise ValueError(f"Unknown TEST_TYPE: {test_type}")
    await scenarios[test_type](tb)


# ---------------------------------------------------------------------------
# Scenarios
# ---------------------------------------------------------------------------


async def _smoke_match(tb: RdCrcCheckTB):
    """Slave returns the matching LFSR pattern → no data_error,
    actual_crc valid at cfg_done."""
    await tb.program(start_addr=0x100, burst_len=1, txn_count=1,
                     axi_id=3, lfsr_seed=0xDEADBEEF)
    await tb.pulse_start()
    await tb.wait_done()
    assert len(tb.ar_log) == 1
    assert int(tb.dut.o_data_error.value)       == 0
    assert int(tb.dut.o_rresp_error.value)      == 0
    assert int(tb.dut.o_actual_crc_valid.value) == 1
    assert int(tb.dut.o_beats_mismatched.value) == 0


async def _multi_burst_match(tb: RdCrcCheckTB):
    """4 bursts of 4 beats, all matching → all clean."""
    BURST = 4
    N = 4
    await tb.program(start_addr=0x200, stride_0=0x20, burst_len=BURST,
                     txn_count=N, axi_id=5)
    await tb.pulse_start()
    await tb.wait_done()
    assert len(tb.ar_log) == N
    assert int(tb.dut.o_data_error.value)       == 0
    assert int(tb.dut.o_beats_mismatched.value) == 0


async def _address_walk(tb: RdCrcCheckTB):
    BASE = 0x4000
    STRIDE = 0x100
    N = 6
    await tb.program(start_addr=BASE, stride_0=STRIDE, burst_len=2,
                     txn_count=N)
    await tb.pulse_start()
    await tb.wait_done()
    assert len(tb.ar_log) == N
    for i, ar in enumerate(tb.ar_log):
        expected = BASE + i * STRIDE
        assert ar.addr == expected, (
            f"AR[{i}].addr = 0x{ar.addr:X} want 0x{expected:X}"
        )


async def _data_mismatch_sticky(tb: RdCrcCheckTB):
    """Slave returns garbage → o_data_error latches."""
    tb.return_lfsr_data = False
    tb.garbage_word = 0xBADCAFE_DEADBEEF
    await tb.program(start_addr=0, burst_len=2, txn_count=2)
    await tb.pulse_start()
    await tb.wait_done()
    assert int(tb.dut.o_data_error.value) == 1, (
        "o_data_error did not latch on garbage R data"
    )


async def _beats_mismatched_count(tb: RdCrcCheckTB):
    """Garbage data → o_beats_mismatched counts every mismatching beat."""
    tb.return_lfsr_data = False
    BURST = 4
    N = 3
    await tb.program(start_addr=0, burst_len=BURST, txn_count=N)
    await tb.pulse_start()
    await tb.wait_done()
    expected_mismatches = BURST * N
    got = int(tb.dut.o_beats_mismatched.value)
    assert got == expected_mismatches, (
        f"o_beats_mismatched = {got}, want {expected_mismatches}"
    )


async def _rresp_error_sticky(tb: RdCrcCheckTB):
    """Slave returns SLVERR on rresp → o_rresp_error latches."""
    tb.rresp_override = 2   # SLVERR
    await tb.program(start_addr=0, burst_len=2, txn_count=2)
    await tb.pulse_start()
    await tb.wait_done()
    assert int(tb.dut.o_rresp_error.value) == 1


async def _rd_gap_inserts_idle(tb: RdCrcCheckTB):
    """cfg_rd_gap > 0 inserts idle cycles between AR bursts. Clean
    workload still completes; LFSR phase still matches what's preloaded
    in MemoryModel. Stride must be ≥ burst_len*bpp so each beat lands
    at a unique address (memory-backed slave can't return different
    data for the same addr)."""
    BURST = 2
    await tb.program(start_addr=0, stride_0=BURST * tb.BYTES_PER_BEAT,
                     burst_len=BURST, txn_count=3, rd_gap=7)
    await tb.pulse_start()
    await tb.wait_done()
    assert len(tb.ar_log) == 3
    assert int(tb.dut.o_data_error.value) == 0


async def _id_mode_counter(tb: RdCrcCheckTB):
    """id_mode=COUNTER: AR IDs walk start..start+N-1 (mod 256)."""
    BURST = 2
    N = 5
    START = 23
    await tb.program(start_addr=0, burst_len=BURST, txn_count=N,
                     axi_id=START, id_mode=1)
    await tb.pulse_start()
    await tb.wait_done()
    assert len(tb.ar_log) == N
    for i, ar in enumerate(tb.ar_log):
        expected = (START + i) & 0xFF
        assert ar.axid == expected, (
            f"AR[{i}].id = {ar.axid} want {expected}"
        )


async def _id_mode_lfsr(tb: RdCrcCheckTB):
    """id_mode=LFSR: AR IDs are an 8-bit Fibonacci LFSR."""
    BURST = 1
    N = 16
    SEED_IN = 0x42
    await tb.program(start_addr=0, burst_len=BURST, txn_count=N,
                     axi_id=SEED_IN, id_mode=2)
    await tb.pulse_start()
    await tb.wait_done()
    assert len(tb.ar_log) == N
    ids = [ar.axid for ar in tb.ar_log]
    distinct = len(set(ids))
    assert distinct >= N // 2, (
        f"LFSR id distribution looks stuck: only {distinct}/{N} distinct"
    )
    assert all(i != 0 for i in ids)


async def _arvalid_no_drop(tb: RdCrcCheckTB):
    """At cfg_rd_gap=0 with pipelined AR, arvalid must NOT drop between
    the first AR being driven and the last AR being handshaked."""
    BURST = 4
    N = 4
    await tb.program(start_addr=0x200, stride_0=BURST * 8,
                     burst_len=BURST, txn_count=N, rd_gap=0)
    await tb.pulse_start()

    saw_arvalid_high = False
    ar_handshakes = 0
    drops_observed = 0
    prev_v = 0
    # Sample at FallingEdge: AXI4SlaveRead drives arready on a
    # FallingEdge-aligned coroutine; sample-at-rising-edge would miss
    # the second-and-later handshakes by ~200ps.
    from cocotb.triggers import FallingEdge as _FallingEdge
    MAX_CYCLES = 50_000
    for _ in range(MAX_CYCLES):
        await _FallingEdge(tb.dut.aclk)
        v = int(tb.dut.m_axi_arvalid.value)
        r = int(tb.dut.m_axi_arready.value)
        if v and r:
            ar_handshakes += 1
            if ar_handshakes == N:
                break
        if v:
            saw_arvalid_high = True
        if prev_v == 1 and v == 0 and ar_handshakes < N:
            drops_observed += 1
        prev_v = v
    assert ar_handshakes == N, (
        f"only saw {ar_handshakes}/{N} AR handshakes in {MAX_CYCLES} cycles"
    )
    assert drops_observed == 0, (
        f"arvalid dropped {drops_observed} cycles mid-run at gap=0"
    )
    await tb.wait_done()


async def _outstanding_dial(tb: RdCrcCheckTB):
    """cfg_max_outstanding caps bursts in flight below the built ceiling.

    MAX_OUTSTANDING is the hardware ceiling; this port dials the ACTIVE limit
    down without a rebuild, so one bitstream can walk a bandwidth-vs-
    outstanding curve instead of needing one build per point. The property
    under test is the cap: (ARs handshaked - RLASTs seen) must never exceed
    the programmed limit.

    Checked in three tiers, because "never exceeds" on its own is satisfied by
    a dial that does nothing at all:
      - Under EVERY slave profile, peak <= limit. The safety property.
      - Dialled DOWN (1, 2, 4) under a back-pressuring profile, peak == limit.
        The proof the dial binds rather than sitting above the natural depth.
        A back-to-back slave retires each burst before the next AR goes out, so
        its peak is 1 whatever the limit says, and asserting equality there
        would fail a correct design -- hence the profile list.
      - At the CEILING, peak > the deepest dialled-down value. Not equality:
        saturating exactly at the ceiling is a race between the AR issue rate
        and the slave's stall pattern, and burst_pause genuinely reaches 7 of 8
        on some seeds. What must hold is that the cap was lifted.

    0 means "as built" and is the reset value, so that case is also the proof
    that an instance which never writes the field behaves exactly as it did
    before the field existed.
    """
    from cocotb.triggers import FallingEdge as _FallingEdge

    BUILT = 8        # MAX_OUTSTANDING, pinned in the run() parameters below
    BURST = 2
    N     = 24       # comfortably more than the deepest limit under test
    profile = os.environ.get("SLAVE_PROFILE", "backtoback")
    # Profiles that hold R off long enough for ARs to queue up. On the others
    # the engine never reaches its limit and only the ceiling is checkable.
    BINDING = ("constrained", "burst_pause", "slow_producer")

    async def _run_at(limit, expect, exact):
        await tb.program(start_addr=0x1000, stride_0=BURST * 8,
                         burst_len=BURST, txn_count=N,
                         max_outstanding=limit)
        await tb.pulse_start()
        live = peak = rlasts = 0
        for _ in range(200_000):
            await _FallingEdge(tb.dut.aclk)
            if int(tb.dut.m_axi_arvalid.value) and int(tb.dut.m_axi_arready.value):
                live += 1
                peak = max(peak, live)
            if (int(tb.dut.m_axi_rvalid.value) and int(tb.dut.m_axi_rready.value)
                    and int(tb.dut.m_axi_rlast.value)):
                live -= 1
                rlasts += 1
                if rlasts == N:
                    break
        assert rlasts == N, f"limit={limit}: only {rlasts}/{N} bursts completed"
        await tb.wait_done()
        assert int(tb.dut.o_data_error.value) == 0, \
            f"limit={limit}: throttling the AR path corrupted the compare"
        assert peak <= expect, \
            f"limit={limit}: {peak} bursts in flight, cap is {expect}"
        if profile in BINDING and exact:
            assert peak == expect, (
                f"limit={limit} on {profile}: peak {peak} never reached the "
                f"cap {expect} -- the dial is not binding"
            )
        elif profile in BINDING:
            # At the ceiling, exact saturation is a race between the AR issue
            # rate and the slave's stall pattern -- burst_pause reaches 7 of 8
            # on some seeds, which is a correct design and a wrong assertion.
            # What must hold is that the cap was LIFTED: the engine goes
            # strictly deeper than the deepest value it was dialled down to.
            assert peak > DIALLED[-1], (
                f"limit={limit} on {profile}: peak {peak} is no deeper than "
                f"the dialled-down cap {DIALLED[-1]} -- 'as built' is not "
                f"releasing the limit"
            )

    DIALLED = (1, 2, 4)
    for limit in DIALLED:
        await _run_at(limit, limit, exact=True)

    await _run_at(0, BUILT, exact=False)

    # Above the ceiling saturates rather than wrapping. The port is only
    # $clog2(BUILT+1) bits -- sized from the ceiling, not from the host field --
    # so the largest over-request expressible here is all-ones. A CSR field
    # WIDER than the port (chargen_regs carries six bits whatever the build) is
    # clamped before it reaches this port, in char_gen_unit's g_os_limit; that
    # is where a 40-into-an-8-deep-engine write is caught.
    OSW = BUILT.bit_length()          # == $clog2(BUILT + 1) for every BUILT
    await _run_at((1 << OSW) - 1, BUILT, exact=False)


async def _hash_mode_match(tb: RdCrcCheckTB):
    """data_mode=1: slave responder returns addr_hash32 of each beat's
    byte address; DUT regenerates the same hash locally and compares per
    beat. Asserts clean compare and o_actual_crc_valid stays low (CRC is
    not the contract in hash mode)."""
    SEEDS = (0x9E3779B9, 0x85EBCA6B, 0xC2B2AE35)
    BURST = 4
    N = 3
    BYTES_PER_BEAT = tb.AXI_DATA_WIDTH // 8
    await tb.program(start_addr=0x100, stride_0=BURST * BYTES_PER_BEAT,
                     burst_len=BURST, txn_count=N, data_mode=1,
                     hash_seed0=SEEDS[0], hash_seed1=SEEDS[1],
                     hash_seed2=SEEDS[2])
    await tb.pulse_start()
    await tb.wait_done()
    assert len(tb.ar_log) == N
    assert int(tb.dut.o_data_error.value)       == 0
    assert int(tb.dut.o_beats_mismatched.value) == 0
    assert int(tb.dut.o_actual_crc_valid.value) == 0


async def _hash_mode_low_entropy(tb: RdCrcCheckTB):
    """Low-entropy addresses (start at 0, contiguous bytes) must NOT
    produce stuck/repeating data — the whole point of the hash seeds is
    to defeat that. Run with start_addr=0 and check that consecutive
    beats produce distinct data."""
    SEEDS = (0xDEADBEEF, 0xCAFEBABE, 0x12345678)
    BURST = 8
    N = 1
    BYTES_PER_BEAT = tb.AXI_DATA_WIDTH // 8
    await tb.program(start_addr=0, stride_0=BURST * BYTES_PER_BEAT,
                     burst_len=BURST, txn_count=N, data_mode=1,
                     hash_seed0=SEEDS[0], hash_seed1=SEEDS[1],
                     hash_seed2=SEEDS[2])
    await tb.pulse_start()
    await tb.wait_done()
    assert int(tb.dut.o_data_error.value) == 0
    # Sanity check on the Python mirror itself: consecutive byte addresses
    # at addr=0 must not collide. (If they do, the hash is broken even
    # before talking about RTL.)
    from TBClasses.axi4.axi4_master_wr_pattern_gen_tb import WrPatternGenTB
    vals = set()
    for k in range(BURST):
        byte_addr = (k * BYTES_PER_BEAT) & 0xFFFFFFFF
        v = WrPatternGenTB.addr_hash32(byte_addr, *SEEDS)
        vals.add(v)
    assert len(vals) == BURST, (
        f"hash collisions at low-entropy addrs: only {len(vals)}/{BURST} distinct"
    )


async def _kb4(tb: RdCrcCheckTB):
    """4 KiB engine read — 128 bursts × 4 beats × 8 bytes from BASE=0.

    MemoryModel is preloaded with LFSR-derived bytes before
    cfg_start fires; reader engine walks the same descriptor and its
    per-beat compare must match every preloaded value (o_data_error=0).
    Isolates the reader engine against the RD-side AXI4 slave BFM —
    pass here pins any NexysA7 kb4 read mismatch on the controller."""
    BURST = 4
    N = 128
    STRIDE = BURST * tb.BYTES_PER_BEAT
    await tb.program(start_addr=0, stride_0=STRIDE, burst_len=BURST,
                     txn_count=N, axi_id=0, id_mode=0,
                     lfsr_seed=0xDEAD_BEEF)
    await tb.pulse_start()
    await tb.wait_done(timeout_cycles=200_000)
    assert int(tb.dut.o_data_error.value) == 0, (
        f"kb4 reader saw mismatched data after preloading 4 KiB of LFSR "
        f"pattern; beats_mismatched={int(tb.dut.o_beats_mismatched.value)}"
    )
    assert int(tb.dut.o_rresp_error.value) == 0
    assert len(tb.ar_log) == N
    assert int(tb.dut.o_actual_crc_valid.value) == 1


async def _kb32(tb: RdCrcCheckTB):
    """32 KiB engine read — 1024 bursts × 4 beats × 8 bytes. Same
    structure as kb4 scaled out to the kb32 workload that fails in
    NexysA7. Isolates reader engine + RD-side AXI BFM."""
    BURST = 4
    N = 1024
    STRIDE = BURST * tb.BYTES_PER_BEAT
    await tb.program(start_addr=0, stride_0=STRIDE, burst_len=BURST,
                     txn_count=N, axi_id=0, id_mode=0,
                     lfsr_seed=0xDEAD_BEEF)
    await tb.pulse_start()
    await tb.wait_done(timeout_cycles=2_000_000)
    assert int(tb.dut.o_data_error.value) == 0, (
        f"kb32 reader saw mismatched data after preloading 32 KiB of "
        f"LFSR pattern; "
        f"beats_mismatched={int(tb.dut.o_beats_mismatched.value)}"
    )
    assert int(tb.dut.o_rresp_error.value) == 0
    assert len(tb.ar_log) == N
    assert int(tb.dut.o_actual_crc_valid.value) == 1


async def _rerun_after_done(tb: RdCrcCheckTB):
    """A second cfg_start pulse after cfg_done must re-run cleanly.
    Both runs use stride = burst_len*bpp so each beat reads a unique
    addr (memory-backed slave preload requirement)."""
    BPP = tb.BYTES_PER_BEAT
    await tb.program(start_addr=0x100, stride_0=2 * BPP,
                     burst_len=2, txn_count=2)
    await tb.pulse_start()
    await tb.wait_done()
    tb.ar_log.clear()
    await tb.program(start_addr=0x800, stride_0=4 * BPP,
                     burst_len=4, txn_count=3, axi_id=7)
    await tb.pulse_start()
    await tb.wait_done()
    assert len(tb.ar_log) == 3
    assert tb.ar_log[0].addr == 0x800
    assert tb.ar_log[0].axid == 7
    assert int(tb.dut.o_data_error.value) == 0


async def _stray_beat_drained(tb: RdCrcCheckTB):
    """A stray R beat between runs is counted AND genuinely drained.

    The drain once detected on the m_axi pins while popping on the FUB side
    of the internal skid: the stray was counted, accepted into the skid, and
    PARKED there -- poisoning the next run's first compare (near-certain
    o_data_error) exactly as the mechanism's own header said it prevents.
    Detection now rides fub_rvalid; this scenario is the regression lock:
    pre-fix RTL fails the second run's clean-compare assertion.
    """
    BPP = tb.BYTES_PER_BEAT
    await tb.program(start_addr=0x100, stride_0=2 * BPP,
                     burst_len=2, txn_count=2)
    await tb.pulse_start()
    await tb.wait_done()
    assert int(tb.dut.o_data_error.value) == 0
    assert int(tb.dut.o_stray_beat_error.value) == 0

    # Unsolicited R beat: drive the slave BFM's R channel directly (no AR
    # outstanding -- the engine is in S_DONE).
    pkt = tb.slave.r_channel.create_packet(
        data=0xDEAD_BEEF, id=0, resp=0, last=1)
    await tb.slave.r_channel.send(pkt)
    await tb.wait_clocks('aclk', 20)

    assert int(tb.dut.o_stray_beat_error.value) == 1, \
        "stray beat not flagged"
    assert int(tb.dut.o_stray_beats.value) == 1, \
        f"stray count {int(tb.dut.o_stray_beats.value)} != 1"

    # Second run must compare clean: pre-fix RTL pops the parked stray as
    # this run's first beat and o_data_error goes sticky.
    await tb.program(start_addr=0x800, stride_0=2 * BPP,
                     burst_len=2, txn_count=2)
    await tb.pulse_start()
    await tb.wait_done()
    assert int(tb.dut.o_data_error.value) == 0, \
        "stray beat poisoned the following run's compare"


# ---------------------------------------------------------------------------
# Pytest matrix
# ---------------------------------------------------------------------------

_ALL_TYPES = ["smoke_match", "multi_burst_match", "address_walk",
              "data_mismatch_sticky", "beats_mismatched_count",
              "rresp_error_sticky", "rerun_after_done",
              "rd_gap_inserts_idle", "hash_mode_match",
              "hash_mode_low_entropy", "arvalid_no_drop",
              "id_mode_counter", "id_mode_lfsr",
              "kb4", "kb32", "stray_beat_drained", "rready_never_throttles",
              "outstanding_dial"]
_GATE = ["smoke_match", "multi_burst_match", "data_mismatch_sticky"]
_FUNC = list(_ALL_TYPES)
_FULL = list(_ALL_TYPES)

_TEST_LEVEL = os.environ.get("TEST_LEVEL", "FUNC").upper()
_SCENARIOS = {"GATE": _GATE, "FUNC": _FUNC, "FULL": _FULL}.get(_TEST_LEVEL, _FUNC)

_SLAVE_PROFILES = ("backtoback", "fixed", "fast", "constrained",
                   "burst_pause", "high_throughput", "slow_producer")


@pytest.mark.parametrize("slave_profile", _SLAVE_PROFILES)
@pytest.mark.parametrize("test_type", _SCENARIOS)
def test_axi4_master_rd_crc_check(request, test_type, slave_profile):
    module, repo_root, tests_dir, log_dir, _ = get_paths({})
    dut_name = "axi4_master_rd_crc_check"
    test_name = f"test_axi4_master_rd_crc_check_{test_type}_{slave_profile}"

    filelist_path = "rtl/amba/filelists/axi4_master_rd_crc_check.f"
    verilog_sources, includes = get_sources_from_filelist(
        repo_root=repo_root, filelist_path=filelist_path)

    sim_build = sim_build_path(tests_dir, test_name)
    os.makedirs(sim_build, exist_ok=True)
    os.makedirs(log_dir, exist_ok=True)

    extra_env = {
        "DUT": dut_name,
        "TEST_TYPE": test_type,
        "SLAVE_PROFILE": slave_profile,
        "AXI_DATA_WIDTH": "64",
        "AXI_ID_WIDTH":   "8",
        "SEED": os.environ.get('SEED', str(random.randint(0, 100000))),
        "TEST_LEVEL": os.environ.get("TEST_LEVEL", "FUNC"),
        "COCOTB_LOG_LEVEL": "INFO",
        "COCOTB_RESULTS_FILE":
            os.path.join(log_dir, f"results_{test_name}.xml"),
    }
    parameters = {
        "AXI_DATA_WIDTH": "64",
        "AXI_ID_WIDTH":   "8",
        "AXI_ADDR_WIDTH": "32",
        "AXI_USER_WIDTH": "1",
        # Pinned rather than left at the module default: outstanding_dial
        # asserts against this number, and a test whose expectations track a
        # default it does not state stops testing the moment the default moves.
        "MAX_OUTSTANDING": "8",
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

    run(python_search=[tests_dir],
        verilog_sources=verilog_sources, includes=includes,
        toplevel=dut_name, module=module,
        testcase="cocotb_test_axi4_master_rd_crc_check",
        sim_build=sim_build, simulator="verilator",
        extra_env=extra_env, parameters=parameters,
        compile_args=compile_args, sim_args=sim_args, plus_args=plus_args,
        waves=enable_waves, keep_files=True, timescale="1ns/1ps")


async def _rready_never_throttles(tb: RdCrcCheckTB):
    """The read path must NEVER back-pressure R: rready stays asserted for the
    whole run, so every gap between beats is the SLAVE's and none is ours.

    Why this is a gate and not a curiosity. On 2026-09-10 the board measured
    read bandwidth pinned at 48.7% of peak while writes reached 95.7%, and the
    first suspect was this generator consuming R at half rate -- if it did, the
    controller would have been blamed for a harness bug. It does not, and this
    test is what says so: across all seven slave timing profiles, rready is
    high on 100% of run cycles and the stall count is exactly zero. A future
    change that makes the checker throttle R would silently halve every board
    read number, and would fail here instead.
    """
    from cocotb.triggers import RisingEdge

    BL, N = 16, 8
    await tb.program(start_addr=0x1000, burst_len=BL, txn_count=N,
                     axi_id=1, lfsr_seed=0xA5A5F00D, stride_0=BL * 8)

    st = {"cyc": 0, "beats": 0, "rready_hi": 0, "stall": 0}
    done = {"f": False}

    async def mon():
        while not done["f"]:
            await RisingEdge(tb.dut.aclk)
            rv = int(tb.dut.m_axi_rvalid.value)
            rr = int(tb.dut.m_axi_rready.value)
            st["cyc"] += 1
            st["rready_hi"] += rr
            st["stall"] += (rv and not rr)
            st["beats"] += (rv and rr)

    task = cocotb.start_soon(mon())
    await tb.pulse_start()
    await tb.wait_done()
    done["f"] = True
    await RisingEdge(tb.dut.aclk)

    tb.log.info("rready: %d/%d beats, rready high %d/%d cycles, stalls %d",
                st["beats"], BL * N, st["rready_hi"], st["cyc"], st["stall"])
    assert st["beats"] == BL * N, (
        f"lost beats: {st['beats']} of {BL*N}")
    assert st["stall"] == 0, (
        f"the checker back-pressured R on {st['stall']} cycles -- it must "
        f"never throttle reads; every R gap has to be the slave's. This "
        f"halves board read bandwidth without failing any integrity check.")
    assert st["rready_hi"] == st["cyc"], (
        f"rready was low on {st['cyc'] - st['rready_hi']} of {st['cyc']} run "
        f"cycles; it must be held continuously for the whole run")
    assert int(tb.dut.o_data_error.value) == 0
    assert int(tb.dut.o_beats_mismatched.value) == 0
