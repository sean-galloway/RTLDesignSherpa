# SPDX-License-Identifier: MIT
# SPDX-FileCopyrightText: 2024-2026 sean galloway

# TODO(amba-profiles): exercise every BFM here with the random-timing
# profiles in bin/TBClasses/amba/amba_random_configs.py (backtoback /
# constrained / fast / slow_*) so we hit interface-level edge cases —
# skid races, FIFO drain corners, mid-burst stalls. Current scenarios
# only use default timing, which masks bugs only triggered by specific
# valid/ready stall patterns.
"""Unit-test runner for `axi4_master_wr_pattern_gen`.

Pins the contracts the harness (and the read-side counterpart) rely on:
  - cfg_start → AW/W → cfg_done end-to-end
  - dma_address_gen walks per descriptor (base + N*stride)
  - W data matches the documented LFSR sequence
  - cfg_done waits for ALL B's, not just AW's
  - o_bresp_error is sticky on any non-OKAY B
  - re-running after cfg_done re-samples the program cleanly
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
from TBClasses.axi4.axi4_master_wr_pattern_gen_tb import WrPatternGenTB


@cocotb.test(timeout_time=200, timeout_unit="ms")
async def cocotb_test_axi4_master_wr_pattern_gen(dut):
    test_type = os.environ.get("TEST_TYPE", "smoke")
    slave_profile = os.environ.get("SLAVE_PROFILE", "backtoback")
    tb = WrPatternGenTB(dut)
    await tb.setup_clocks_and_reset()
    tb.set_slave_delay_profile(slave_profile)
    scenarios = {
        "smoke":             _smoke,
        "multi_burst":       _multi_burst,
        "address_walk":      _address_walk,
        "data_matches_lfsr": _data_matches_lfsr,
        "done_waits_for_b":  _done_waits_for_b,
        "bresp_error_sticky": _bresp_error_sticky,
        "rerun_after_done":  _rerun_after_done,
        "wr_gap_inserts_idle": _wr_gap_inserts_idle,
        "hash_mode_data":    _hash_mode_data,
        "awvalid_no_drop":   _awvalid_no_drop,
        "id_mode_counter":   _id_mode_counter,
        "id_mode_lfsr":      _id_mode_lfsr,
        "kb4":               _kb4,
        "kb32":              _kb32,
    }
    if test_type not in scenarios:
        raise ValueError(f"Unknown TEST_TYPE: {test_type}")
    await scenarios[test_type](tb)


# ---------------------------------------------------------------------------
# Scenarios
# ---------------------------------------------------------------------------


async def _smoke(tb: WrPatternGenTB):
    """One burst of 1 beat. cfg_done asserts. Master saw 1 AW + 1 W."""
    await tb.program(start_addr=0x100, burst_len=1, txn_count=1,
                     axi_id=3, lfsr_seed=0xDEADBEEF)
    await tb.pulse_start()
    await tb.wait_done()
    assert len(tb.aw_log) == 1, f"expected 1 AW, got {len(tb.aw_log)}"
    assert len(tb.w_log)  == 1, f"expected 1 W beat, got {len(tb.w_log)}"
    assert tb.aw_log[0].addr == 0x100
    assert tb.aw_log[0].axid == 3
    assert tb.w_log[0].last == 1
    assert int(tb.dut.o_bresp_error.value) == 0
    assert int(tb.dut.o_expected_crc_valid.value) == 1


async def _multi_burst(tb: WrPatternGenTB):
    """4 bursts of 4 beats. Verify counts + last positions."""
    BURST = 4
    N = 4
    await tb.program(start_addr=0x200, stride_0=0x20, burst_len=BURST,
                     txn_count=N, axi_id=5)
    await tb.pulse_start()
    await tb.wait_done()
    assert len(tb.aw_log) == N, f"AWs: got {len(tb.aw_log)} want {N}"
    assert len(tb.w_log)  == N * BURST, (
        f"W beats: got {len(tb.w_log)} want {N * BURST}"
    )
    # wlast asserts on the last beat of each burst, low otherwise.
    for k, w in enumerate(tb.w_log):
        is_last_of_burst = ((k + 1) % BURST) == 0
        assert w.last == int(is_last_of_burst), (
            f"beat {k}: wlast = {w.last}, "
            f"expected {int(is_last_of_burst)}"
        )


async def _address_walk(tb: WrPatternGenTB):
    """ARaddr per burst follows base + N*stride. Pins dma_address_gen
    consumption + stride semantics under serial-burst v1."""
    BASE = 0x4000
    STRIDE = 0x100
    N = 6
    await tb.program(start_addr=BASE, stride_0=STRIDE, burst_len=2,
                     txn_count=N)
    await tb.pulse_start()
    await tb.wait_done()
    assert len(tb.aw_log) == N
    for i, aw in enumerate(tb.aw_log):
        expected = BASE + i * STRIDE
        assert aw.addr == expected, (
            f"AW[{i}].addr = 0x{aw.addr:X} want 0x{expected:X}"
        )


async def _data_matches_lfsr(tb: WrPatternGenTB):
    """W beats follow the documented Fibonacci LFSR sequence with the
    32-bit value replicated across the data bus. Catches any drift
    between the RTL LFSR step and the Python mirror that the read-side
    block relies on."""
    BURST = 4
    N = 3
    SEED = 0xCAFEBABE
    await tb.program(start_addr=0, burst_len=BURST, txn_count=N,
                     lfsr_seed=SEED)
    await tb.pulse_start()
    await tb.wait_done()
    total_beats = N * BURST
    expected = tb.expected_data_words(total_beats, seed=SEED)
    assert len(tb.w_log) == total_beats
    for k, (w, e) in enumerate(zip(tb.w_log, expected)):
        assert w.data == e, (
            f"W beat {k}: data 0x{w.data:016X} want 0x{e:016X}"
        )


async def _done_waits_for_b(tb: WrPatternGenTB):
    """cfg_done must NOT assert until all B responses received. We
    delay the B responder by gating it from outside."""
    # Override the B responder: park bresp_outstanding until we release
    BURST = 2
    N = 3
    await tb.program(start_addr=0, burst_len=BURST, txn_count=N)
    await tb.pulse_start()

    # Wait until all AW + W are issued. The b_responder will drive the
    # first burst's B before we stall, so to stall we'd need a per-test
    # gate. Instead: just verify cfg_done eventually goes high AND that
    # we saw exactly N B handshakes by counting from b_outstanding's
    # initial backlog.
    await tb.wait_done()
    # All AWs should have queued + drained through b_outstanding
    assert len(tb.aw_log) == N
    # At cfg_done, every queued B must have drained
    assert len(tb.b_outstanding) == 0, (
        f"cfg_done fired with {len(tb.b_outstanding)} B's still pending"
    )


async def _bresp_error_sticky(tb: WrPatternGenTB):
    """A single non-OKAY BRESP must latch o_bresp_error for the rest
    of the run."""
    BURST = 2
    N = 4
    tb.bresp_override = 2   # SLVERR
    await tb.program(start_addr=0, burst_len=BURST, txn_count=N)
    await tb.pulse_start()
    await tb.wait_done()
    assert int(tb.dut.o_bresp_error.value) == 1, (
        "o_bresp_error did not latch on SLVERR B"
    )


async def _wr_gap_inserts_idle(tb: WrPatternGenTB):
    """cfg_wr_gap > 0 inserts N idle cycles between bursts. Verify the
    workload still completes (cfg_done asserts) with the same AW/W counts
    as the no-gap path; the timing change isn't directly observable from
    aw_log/w_log but the test catches FSM-stuck regressions."""
    BURST = 2
    N = 3
    await tb.program(start_addr=0, burst_len=BURST, txn_count=N, wr_gap=5)
    await tb.pulse_start()
    await tb.wait_done()
    assert len(tb.aw_log) == N
    assert len(tb.w_log)  == N * BURST


async def _id_mode_counter(tb: WrPatternGenTB):
    """id_mode=COUNTER: AW IDs walk start..start+N-1 (mod 256)."""
    BURST = 2
    N = 6
    START = 17
    await tb.program(start_addr=0, burst_len=BURST, txn_count=N,
                     axi_id=START, id_mode=1)
    await tb.pulse_start()
    await tb.wait_done()
    assert len(tb.aw_log) == N
    for i, aw in enumerate(tb.aw_log):
        expected = (START + i) & 0xFF
        assert aw.axid == expected, (
            f"AW[{i}].id = {aw.axid} want {expected}"
        )


async def _id_mode_lfsr(tb: WrPatternGenTB):
    """id_mode=LFSR: AW IDs are an 8-bit Fibonacci LFSR. The exact
    sequence is deterministic but we don't pin it here — just assert:
    (a) the IDs are not stuck (>=N/2 distinct in N samples for N>=8)
    (b) the IDs are non-zero (the seed mask | 0x01 prevents 0)
    """
    BURST = 1
    N = 16
    SEED_IN = 0x42
    await tb.program(start_addr=0, burst_len=BURST, txn_count=N,
                     axi_id=SEED_IN, id_mode=2)
    await tb.pulse_start()
    await tb.wait_done()
    assert len(tb.aw_log) == N
    ids = [aw.axid for aw in tb.aw_log]
    distinct = len(set(ids))
    assert distinct >= N // 2, (
        f"LFSR id distribution looks stuck: only {distinct}/{N} distinct"
    )
    assert all(i != 0 for i in ids), (
        f"LFSR id sequence produced a 0: {ids}"
    )


async def _awvalid_no_drop(tb: WrPatternGenTB):
    """At cfg_wr_gap=0 with pipelined AW, awvalid must NOT drop between
    the first AW being driven and the last AW being handshaked. (After
    the last AW handshake awvalid is allowed to deassert — no more work.)

    Engine contract per AXI4: once awvalid asserts, master holds it high
    until awready handshakes. Test counts handshakes until N seen and
    observes any awvalid 1→0 transitions in the gap between assertion
    and final handshake — that's the bug we're guarding against.
    """
    BURST = 4
    N = 4
    await tb.program(start_addr=0x200, stride_0=BURST * 8,
                     burst_len=BURST, txn_count=N, wr_gap=0)
    await tb.pulse_start()

    saw_awvalid_high = False
    aw_handshakes = 0
    drops_observed = 0
    prev_v = 0
    # Watch the AW channel until N handshakes complete OR timeout. The
    # cycle window is generous enough for the AXI4SlaveWrite BFM's
    # per-packet pacing (handshakes are ~1-N cycles apart in the
    # backtoback profile) — it's the engine's contract that matters,
    # not how fast the BFM accepts.
    # Sample at FallingEdge: AXI4SlaveWrite drives awready on a
    # FallingEdge-aligned coroutine, so awready transitions ~300ps
    # into the cycle. Sampling at FallingEdge (mid-cycle) is the only
    # point where both engine valid and BFM ready are guaranteed stable.
    from cocotb.triggers import FallingEdge as _FallingEdge
    MAX_CYCLES = 50_000
    for _ in range(MAX_CYCLES):
        await _FallingEdge(tb.dut.aclk)
        v = int(tb.dut.m_axi_awvalid.value)
        r = int(tb.dut.m_axi_awready.value)
        if v and r:
            aw_handshakes += 1
            if aw_handshakes == N:
                break
        if v:
            saw_awvalid_high = True
        # 1→0 transition on awvalid mid-stream: engine dropped valid
        # before completing all N handshakes. AXI4 violation.
        if prev_v == 1 and v == 0 and aw_handshakes < N:
            drops_observed += 1
        prev_v = v
    assert aw_handshakes == N, (
        f"only saw {aw_handshakes}/{N} AW handshakes in {MAX_CYCLES} cycles"
    )
    assert drops_observed == 0, (
        f"awvalid dropped {drops_observed} time(s) mid-stream — engine "
        f"violates AXI4 (master must hold valid until ready)"
    )
    assert drops_observed == 0, (
        f"awvalid dropped {drops_observed} cycles mid-run at gap=0"
    )
    await tb.wait_done()


async def _hash_mode_data(tb: WrPatternGenTB):
    """data_mode=1: W beats are addr_hash32 of the per-beat byte address.
    The Python mirror computes the same hash per beat, so we can compare
    bit-for-bit. Also asserts o_expected_crc_valid stays low in hash mode
    (CRC is not the integrity contract there)."""
    BURST = 4
    N = 3
    SEEDS = (0x9E3779B9, 0x85EBCA6B, 0xC2B2AE35)
    BYTES_PER_BEAT = tb.AXI_DATA_WIDTH // 8
    BASE = 0x100
    STRIDE = BURST * BYTES_PER_BEAT
    await tb.program(start_addr=BASE, stride_0=STRIDE, burst_len=BURST,
                     txn_count=N, data_mode=1,
                     hash_seed0=SEEDS[0], hash_seed1=SEEDS[1],
                     hash_seed2=SEEDS[2])
    await tb.pulse_start()
    await tb.wait_done()
    assert len(tb.w_log) == N * BURST
    # Walk the same address sequence the writer walks
    for burst_idx in range(N):
        burst_base = BASE + burst_idx * STRIDE
        for beat in range(BURST):
            byte_addr = (burst_base + beat * BYTES_PER_BEAT) & 0xFFFFFFFF
            expected = tb.expected_hash_beat_data(byte_addr, SEEDS)
            got = tb.w_log[burst_idx * BURST + beat].data
            assert got == expected, (
                f"burst {burst_idx} beat {beat}: data 0x{got:016X} "
                f"want 0x{expected:016X} (addr 0x{byte_addr:08X})"
            )
    # CRC valid should NOT assert in hash mode — per-beat compare on the
    # read side is the contract.
    assert int(tb.dut.o_expected_crc_valid.value) == 0


async def _kb4(tb: WrPatternGenTB):
    """4 KiB engine write — 128 bursts × 4 beats × 8 bytes from BASE=0.

    Pins the writer alone against the AXI4SlaveWrite BFM + MemoryModel:
    after cfg_done, every beat-addr in [0, N*BURST*BPP) must hold
    exactly the LFSR-derived value from the shared mirror. If this
    PASSES, the writer engine + AXI4 slave WR path are clean at 4 KiB
    same-id workload — any kb4 NexysA7 failure is in the controller.
    """
    BURST = 4
    N = 128
    BPP = tb.BYTES_PER_BEAT
    STRIDE = BURST * BPP
    SEED = 0xDEAD_BEEF
    await tb.program(start_addr=0, stride_0=STRIDE, burst_len=BURST,
                     txn_count=N, axi_id=0, id_mode=0,
                     lfsr_seed=SEED)
    await tb.pulse_start()
    await tb.wait_done(timeout_cycles=200_000)

    expected = tb.expected_data_words(N * BURST, seed=SEED)
    first_bad = None
    for k in range(N * BURST):
        byte_addr = k * BPP
        got_bytes = bytes(tb.memory.read(byte_addr, BPP))
        got_int = int.from_bytes(got_bytes, "little")
        if got_int != expected[k]:
            first_bad = (k, byte_addr, expected[k], got_int)
            break
    if first_bad is not None:
        # Dump diagnostics: AW count + addrs around the mismatch, and the
        # first 5 / last 5 aw_log entries so we can see whether the BFM
        # recorded the right ARs or got out of order.
        bi = first_bad[0] // BURST
        tb.log.error("kb4 FAIL: beat=%d (burst=%d beat=%d) addr=0x%X "
                     "expected=0x%016X memory=0x%016X",
                     first_bad[0], bi, first_bad[0] % BURST,
                     first_bad[1], first_bad[2], first_bad[3])
        tb.log.error("aw_log[0..7]: %s",
                     [(i, f"addr=0x{a.addr:X} id={a.axid} len={a.awlen}")
                      for i, a in enumerate(tb.aw_log[:8])])
        if bi < len(tb.aw_log):
            tb.log.error("aw_log[%d..%d]: %s",
                         max(0, bi-2), min(len(tb.aw_log), bi+3),
                         [(i, f"addr=0x{a.addr:X} id={a.axid} len={a.awlen}")
                          for i, a in enumerate(
                              tb.aw_log[max(0, bi-2):bi+3],
                              start=max(0, bi-2))])
        tb.log.error("aw_log size=%d (expected %d)", len(tb.aw_log), N)
        tb.log.error("w_log size=%d (expected %d)",
                     len(tb.w_log), N * BURST)
        # Also dump the expected vs actual for beats near the mismatch
        for k in range(max(0, first_bad[0]-2), min(N*BURST, first_bad[0]+5)):
            ba = k * BPP
            got = int.from_bytes(bytes(tb.memory.read(ba, BPP)), "little")
            marker = " <-- FIRST BAD" if k == first_bad[0] else ""
            tb.log.error("  beat=%d addr=0x%X expected=0x%016X memory=0x%016X%s",
                         k, ba, expected[k], got, marker)
    assert first_bad is None, (
        f"kb4 WR mismatch at beat={first_bad[0]} "
        f"byte_addr=0x{first_bad[1]:X}: "
        f"expected 0x{first_bad[2]:016X}, "
        f"memory holds 0x{first_bad[3]:016X}"
    )
    assert int(tb.dut.o_bresp_error.value) == 0
    assert len(tb.aw_log) == N
    assert len(tb.w_log)  == N * BURST


async def _kb32(tb: WrPatternGenTB):
    """32 KiB engine write — 1024 bursts × 4 beats × 8 bytes. Same
    verification structure as kb4, scaled out to the kb32 workload that
    fails in NexysA7. Isolates writer engine + WR-side AXI BFM."""
    BURST = 4
    N = 1024
    BPP = tb.BYTES_PER_BEAT
    STRIDE = BURST * BPP
    SEED = 0xDEAD_BEEF
    await tb.program(start_addr=0, stride_0=STRIDE, burst_len=BURST,
                     txn_count=N, axi_id=0, id_mode=0,
                     lfsr_seed=SEED)
    await tb.pulse_start()
    await tb.wait_done(timeout_cycles=2_000_000)

    expected = tb.expected_data_words(N * BURST, seed=SEED)
    first_bad = None
    for k in range(N * BURST):
        byte_addr = k * BPP
        got_bytes = bytes(tb.memory.read(byte_addr, BPP))
        got_int = int.from_bytes(got_bytes, "little")
        if got_int != expected[k]:
            first_bad = (k, byte_addr, expected[k], got_int)
            break
    assert first_bad is None, (
        f"kb32 WR mismatch at beat={first_bad[0]} "
        f"byte_addr=0x{first_bad[1]:X}: "
        f"expected 0x{first_bad[2]:016X}, "
        f"memory holds 0x{first_bad[3]:016X}"
    )
    assert int(tb.dut.o_bresp_error.value) == 0
    assert len(tb.aw_log) == N
    assert len(tb.w_log)  == N * BURST


async def _rerun_after_done(tb: WrPatternGenTB):
    """After cfg_done, a second cfg_start pulse must re-run the workload
    cleanly with fresh state (no leftover counters / errors)."""
    # Run #1
    await tb.program(start_addr=0x100, burst_len=2, txn_count=2)
    await tb.pulse_start()
    await tb.wait_done()
    aw1 = len(tb.aw_log)
    w1  = len(tb.w_log)
    # Re-program with fresh values, pulse start again
    tb.aw_log.clear()
    tb.w_log.clear()
    await tb.program(start_addr=0x800, burst_len=4, txn_count=3,
                     axi_id=7)
    await tb.pulse_start()
    await tb.wait_done()
    assert len(tb.aw_log) == 3, (
        f"second run: AWs got {len(tb.aw_log)} want 3"
    )
    assert len(tb.w_log) == 12, (
        f"second run: W beats got {len(tb.w_log)} want 12"
    )
    assert tb.aw_log[0].addr == 0x800
    assert tb.aw_log[0].axid == 7


# ---------------------------------------------------------------------------
# Pytest matrix — scenarios × slave-delay profiles
# ---------------------------------------------------------------------------

_ALL_TYPES = ["smoke", "multi_burst", "address_walk",
              "data_matches_lfsr", "done_waits_for_b",
              "bresp_error_sticky", "rerun_after_done",
              "wr_gap_inserts_idle", "hash_mode_data",
              "awvalid_no_drop", "id_mode_counter",
              "id_mode_lfsr", "kb4", "kb32"]
_GATE = ["smoke", "multi_burst", "address_walk"]
_FUNC = list(_ALL_TYPES)
_FULL = list(_ALL_TYPES)

_TEST_LEVEL = os.environ.get("TEST_LEVEL", "FUNC").upper()
_SCENARIOS = {"GATE": _GATE, "FUNC": _FUNC, "FULL": _FULL}.get(_TEST_LEVEL, _FUNC)

# Slave-delay profiles applied to the AXI4SlaveWrite BFM's AW/W/B
# randomizers. backtoback = 0-delay always-ready; the rest add varying
# stall patterns to exercise the engine's hold-valid-until-ready contract
# under different downstream pacing.
_SLAVE_PROFILES = ("backtoback", "fixed", "fast", "constrained",
                   "burst_pause", "high_throughput", "slow_producer")


@pytest.mark.parametrize("slave_profile", _SLAVE_PROFILES)
@pytest.mark.parametrize("test_type", _SCENARIOS)
def test_axi4_master_wr_pattern_gen(request, test_type, slave_profile):
    module, repo_root, tests_dir, log_dir, _ = get_paths({})
    dut_name = "axi4_master_wr_pattern_gen"
    test_name = f"test_axi4_master_wr_pattern_gen_{test_type}_{slave_profile}"

    filelist_path = "rtl/amba/filelists/axi4_master_wr_pattern_gen.f"
    verilog_sources, includes = get_sources_from_filelist(
        repo_root=repo_root, filelist_path=filelist_path)

    sim_build = os.path.join(tests_dir, "local_sim_build", test_name)
    os.makedirs(sim_build, exist_ok=True)
    os.makedirs(log_dir, exist_ok=True)

    extra_env = {
        "DUT": dut_name,
        "TEST_TYPE": test_type,
        "SLAVE_PROFILE": slave_profile,
        "AXI_DATA_WIDTH": "64",
        "AXI_ID_WIDTH":   "8",
        "SEED": str(random.randint(0, 100000)),
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
        testcase="cocotb_test_axi4_master_wr_pattern_gen",
        sim_build=sim_build, simulator="verilator",
        extra_env=extra_env, parameters=parameters,
        compile_args=compile_args, sim_args=sim_args, plus_args=plus_args,
        waves=enable_waves, keep_files=True, timescale="1ns/1ps")
