# SPDX-License-Identifier: MIT
# SPDX-FileCopyrightText: 2024-2026 sean galloway

"""Tests for ddr2_lpddr2_core_macro — the AXI-to-DFI macro.

The DUT is the core controller WITHOUT the CSR slave layer; cfg signals
are driven directly by the TB. Two BFM populations drive the DUT:

  - AXI4MasterWrite + AXI4MasterRead on s_axi_* (host traffic)
  - DFISlavePHY + MemoryModel on phy_dfi_* (DFI loopback with
    preloadable / inspectable backing memory)

The headline test is `test_ddr2_lpddr2_core_macro_profile_sweep` —
parametric 31-config cross-product across the AXI_RANDOMIZER_CONFIGS
profiles applied per channel. Catches cross-channel-timing bugs that
the controller-top env can hit, but here at the AXI-to-DFI level
without CSR overhead so each sim is faster.
"""

from __future__ import annotations

import os
import random
import sys
from typing import Optional

import cocotb
import pytest
from cocotb.triggers import ClockCycles

from cocotb_test.simulator import run

from TBClasses.shared.utilities import get_paths
from TBClasses.shared.filelist_utils import get_sources_from_filelist

_DV_DIR = os.path.abspath(os.path.join(os.path.dirname(__file__), ".."))
if _DV_DIR not in sys.path:
    sys.path.insert(0, _DV_DIR)

from tbclasses.ddr2_lpddr2_core_macro_tb import DDR2LPDDR2CoreMacroTB  # noqa: E402


# ---------------------------------------------------------------------------
# cocotb entry
# ---------------------------------------------------------------------------


@cocotb.test(timeout_time=2000, timeout_unit="ms")
async def cocotb_test_ddr2_lpddr2_core_macro(dut):
    test_type = os.environ.get("TEST_TYPE", "smoke")
    mem_type  = os.environ.get("MEM_TYPE", "DDR2").upper()

    tb = DDR2LPDDR2CoreMacroTB(dut, num_ranks=1)
    await tb.reset(mem_type=mem_type, init_complete_delay=20)
    tb.init_dfi_slave()
    tb.init_axi_masters()
    await tb.axi_master_wr.aw_channel.reset_bus()
    await tb.axi_master_wr.w_channel.reset_bus()
    await tb.axi_master_wr.b_channel.reset_bus()
    await tb.axi_master_rd.ar_channel.reset_bus()
    await tb.axi_master_rd.r_channel.reset_bus()
    await tb.wait_for_init_done()

    if test_type == "smoke":
        # Single write + read at one address to prove the AXI+DFI path
        # comes up clean under default timing.
        data_word = 0xCAFEBABE_DEADBEEF
        await tb.axi_master_wr.write_transaction(
            address=0x0001_0000, data=[data_word], id=0, size=3,
        )
        await ClockCycles(dut.mc_clk, 100)
        got = await tb.axi_master_rd.read_transaction(
            address=0x0001_0000, burst_len=1, id=0, size=3,
        )
        assert got[0] == data_word, (
            f"smoke roundtrip: wrote 0x{data_word:016X}, read 0x{got[0]:016X}"
        )

    elif test_type == "engine_mirror_kbN":
        # Engine-faithful mirror with the same axis knobs as macro top:
        #   KBN_N           — number of bursts
        #   KBN_BURST_LEN   — beats per burst
        #   KBN_BASE_ADDR   — start address (hex string ok via int(..., 0))
        #   KBN_ID_MODE     — FIXED / COUNTER / LFSR
        #   KBN_AXI_ID_BASE — first AXI id (interpretation depends on mode)
        #   KBN_SLAVE_PROFILE — AXI4Master timing profile
        # Mirrors NexysA7 engines' cfg knobs.
        import os as _os
        N         = int(_os.environ.get("KBN_N", "128"))
        BURST     = int(_os.environ.get("KBN_BURST_LEN", "4"))
        BASE      = int(_os.environ.get("KBN_BASE_ADDR", "0x10000"), 0)
        id_mode   = _os.environ.get("KBN_ID_MODE", "FIXED").upper()
        id_base   = int(_os.environ.get("KBN_AXI_ID_BASE", "0"))
        slave_profile = _os.environ.get("KBN_SLAVE_PROFILE", "backtoback")
        if slave_profile != "backtoback":
            tb.set_axi_timing_profile(slave_profile)
        tb.log.info(
            "engine_mirror_kbN: N=%d BURST=%d id_mode=%s id_base=%d "
            "slave_profile=%s base=0x%X",
            N, BURST, id_mode, id_base, slave_profile, BASE,
        )
        await tb.wait_for_init_done()

        from tbclasses.ddr2_lpddr2_sequences import (
            build_b2b_wr_rd_sequences, diff_results,
        )
        from CocoTBFramework.components.axi4.axi4_sequence import (
            run_axi4_sequence,
        )

        ID_MASK = (1 << tb.axi_id_width) - 1

        def _id_pick(bi: int) -> int:
            if id_mode == "FIXED":
                return id_base & ID_MASK
            if id_mode == "COUNTER":
                return (id_base + bi) & ID_MASK
            if id_mode == "LFSR":
                v = max(id_base, 1) & 0xFF
                for _ in range(bi):
                    fb = ((v >> 7) ^ (v >> 5) ^ (v >> 4) ^ (v >> 3)) & 1
                    v = ((v << 1) | fb) & 0xFF
                return v & ID_MASK
            return id_base & ID_MASK

        wr_seq, rd_seq, expected = build_b2b_wr_rd_sequences(
            n_bursts=N, burst_len=BURST, base_addr=BASE,
            data_width=tb.axi_data_width,
            wr_axid_fn=_id_pick,
            rd_axid_fn=_id_pick,
            name=f"engine_mirror_core_{id_mode}_id{id_base}_bl{BURST}_n{N}",
        )
        await run_axi4_sequence(wr_seq, master_wr=tb.axi_master_wr)
        from cocotb.triggers import ClockCycles as _CC_kbn
        await _CC_kbn(dut.mc_clk, 100)

        # === LOCALIZER A: AXI-WR ↔ DFI-WR ===
        # After WR drains, the DFISlavePHY's MemoryModel should hold
        # exactly what the AXI WR bursts intended. A mismatch here
        # means the controller corrupted on the way down — wbuf /
        # wr_beat_sequencer / dfi_signal_pack.
        STRIDE = BURST * (tb.axi_data_width // 8)
        wr_expected: dict[int, bytes] = {}
        for bi, beats in enumerate(expected):
            payload = bytearray()
            for beat in beats:
                payload += int(beat).to_bytes(tb.axi_data_width // 8,
                                              "little")
            wr_expected[BASE + bi * STRIDE] = bytes(payload)
        wr_bad = tb.verify_wr_path(wr_expected)
        assert wr_bad is None, (
            f"WR PATH CORRUPTION (kbN N={N}) at byte_addr=0x{wr_bad[0]:X} "
            f"offset={wr_bad[1]}: expected=0x{wr_bad[2]:02X} "
            f"actual=0x{wr_bad[3]:02X} — controller corrupted between AXI "
            f"WR ingress and DFI WR egress (wbuf / wr_beat_sequencer / "
            f"dfi_signal_pack)"
        )
        tb.log.info("WR-path localizer OK: all %d bursts × %d beats "
                    "intact in MemoryModel", N, BURST)

        rd_dicts = await run_axi4_sequence(
            rd_seq, master_rd=tb.axi_master_rd,
        )
        results = [r["data"] for r in rd_dicts]

        # === LOCALIZER B: DFI-RD ↔ AXI-RD ===
        # MemoryModel is now the source of truth for what DFI replays.
        # Each AXI RD burst's beats should equal MemoryModel[addr].
        # Mismatch here = corruption on the way up — rd_cl_aligner /
        # axi_intake R-emit.
        rd_first_bad: tuple | None = None
        for bi in range(N):
            bad = tb.verify_rd_path(
                BASE + bi * STRIDE, results[bi],
                data_width_bits=tb.axi_data_width,
            )
            if bad is not None:
                rd_first_bad = (bi, *bad)
                break
        assert rd_first_bad is None, (
            f"RD PATH CORRUPTION (kbN N={N}) at burst={rd_first_bad[0]} "
            f"beat={rd_first_bad[1]}: MemoryModel had 0x{rd_first_bad[2]:016X} "
            f"AXI returned 0x{rd_first_bad[3]:016X} — controller corrupted "
            f"between DFI RD ingress and AXI RD egress (rd_cl_aligner / "
            f"axi_intake R-emit)"
        )
        tb.log.info("RD-path localizer OK: all %d bursts intact across "
                    "DFI→AXI", N)

        # End-to-end (kept for completeness; both localizers already
        # passed if we got here).
        first_bad = diff_results(expected, results)
        assert first_bad is None, (
            f"engine_mirror_kbN (N={N}) corrupted at "
            f"burst={first_bad[0]} beat={first_bad[1]}: "
            f"wrote 0x{first_bad[2]:016X} read 0x{first_bad[3]:016X}"
        )
        tb.log.info("engine_mirror_kbN OK N=%d", N)

    elif test_type == "profile_sweep_b2b":
        # Per-channel random-timing profile sweep at the AXI-to-DFI
        # macro level. Pipelines 17 writes then 17 reads via
        # AXI4Sequence so the BFM dispatches ARs/AWs back-to-back
        # the way an engine would. NEVER start_soon parallel
        # read_transaction / write_transaction — that's per-id
        # deque contention, not real bus traffic.
        aw = os.environ.get("AXI_PROFILE_AW", "fast")
        w  = os.environ.get("AXI_PROFILE_W",  "fast")
        b  = os.environ.get("AXI_PROFILE_B",  "fast")
        ar = os.environ.get("AXI_PROFILE_AR", "fast")
        r  = os.environ.get("AXI_PROFILE_R",  "fast")
        tb.set_axi_timing_per_channel(aw=aw, w=w, b=b, ar=ar, r=r)

        N_BURSTS = 17
        BURST_LEN = 4
        BASE = 0x0001_0000

        from tbclasses.ddr2_lpddr2_sequences import (
            build_b2b_wr_rd_sequences, diff_results,
        )
        from CocoTBFramework.components.axi4.axi4_sequence import (
            run_axi4_sequence,
        )
        wr_seq, rd_seq, expected = build_b2b_wr_rd_sequences(
            n_bursts=N_BURSTS, burst_len=BURST_LEN, base_addr=BASE,
            data_width=tb.axi_data_width,
            name="profile_sweep_b2b",
        )
        await run_axi4_sequence(wr_seq, master_wr=tb.axi_master_wr)
        await ClockCycles(dut.mc_clk, 200)  # let B drain
        rd_dicts = await run_axi4_sequence(
            rd_seq, master_rd=tb.axi_master_rd,
        )
        results = [d["data"] for d in rd_dicts]

        first_bad = diff_results(expected, results)
        assert first_bad is None, (
            f"profile_sweep_b2b "
            f"(aw={aw} w={w} b={b} ar={ar} r={r}) "
            f"corrupted at burst={first_bad[0]} beat={first_bad[1]}: "
            f"wrote 0x{first_bad[2]:016X} read 0x{first_bad[3]:016X}"
        )
        tb.log.info(
            "profile_sweep_b2b OK aw=%s w=%s b=%s ar=%s r=%s",
            aw, w, b, ar, r,
        )

    else:
        raise ValueError(f"Unknown TEST_TYPE: {test_type}")


# ---------------------------------------------------------------------------
# Pytest matrix
# ---------------------------------------------------------------------------

_AXI_PROFILES = ("fixed", "constrained", "fast", "backtoback",
                 "burst_pause", "slow_producer", "high_throughput")


def _build_core_profile_matrix() -> list[tuple[str, str, str, str, str]]:
    """31-config matrix — same shape as controller-top + FUB sweeps."""
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


_CORE_PROFILE_MATRIX = _build_core_profile_matrix()


def _run_core_macro(*, test_name, test_type, extra_env_extra=None):
    module, repo_root, tests_dir, log_dir, _ = get_paths({})
    dut_name = "ddr2_lpddr2_core_macro_tb_top"

    filelist_path = ("projects/components/memory-controllers/ddr2-lpddr2/"
                     "rtl/filelists/macro/ddr2_lpddr2_core_macro.f")
    verilog_sources, includes = get_sources_from_filelist(
        repo_root=repo_root, filelist_path=filelist_path)
    verilog_sources.append(os.path.join(
        repo_root,
        "projects/components/memory-controllers/ddr2-lpddr2/dv/tb/"
        "ddr2_lpddr2_core_macro_tb_top.sv"))

    sim_build = os.path.join(tests_dir, "local_sim_build", test_name)
    os.makedirs(sim_build, exist_ok=True)
    os.makedirs(log_dir, exist_ok=True)

    extra_env = {
        "DUT": dut_name,
        "TEST_TYPE": test_type,
        "MEM_TYPE": "DDR2",
        "NUM_RANKS": "1",
        "SEED": os.environ.get("OVERRIDE_SEED", str(random.randint(0, 100000))),
        "COCOTB_LOG_LEVEL": "INFO",
        "COCOTB_RESULTS_FILE":
            os.path.join(log_dir, f"results_{test_name}.xml"),
    }
    if extra_env_extra:
        extra_env.update(extra_env_extra)
    parameters = {"NUM_RANKS": "1", "PAGE_POLICY": "1"}

    enable_waves = bool(int(os.environ.get("WAVES", "0")))
    compile_args = [
        "+define+USE_ASYNC_RESET",
        "-Wno-MULTIDRIVEN", "-Wno-UNUSED", "-Wno-UNDRIVEN", "-Wno-WIDTH",
        "-Wno-CASEINCOMPLETE", "-Wno-SELRANGE", "-Wno-DECLFILENAME",
        "-Wno-UNUSEDSIGNAL", "-Wno-VARHIDDEN", "-Wno-IMPLICIT",
        "-Wno-CASEOVERLAP",
    ]
    sim_args: list = []
    plus_args: list = []
    if enable_waves:
        compile_args += ["--trace-fst", "--trace-structs", "--trace-depth", "99"]
        sim_args     += ["--trace", "--trace-structs", "--trace-depth", "99"]
        plus_args    += ["--trace"]
        extra_env["VERILATOR_TRACE_FST"] = "1"

    run(python_search=[tests_dir],
        verilog_sources=verilog_sources, includes=includes,
        toplevel=dut_name, module=module,
        testcase="cocotb_test_ddr2_lpddr2_core_macro",
        sim_build=sim_build, simulator="verilator",
        extra_env=extra_env, parameters=parameters,
        compile_args=compile_args, sim_args=sim_args, plus_args=plus_args,
        waves=enable_waves, keep_files=True, timescale="1ns/1ps")


def test_ddr2_lpddr2_core_macro_smoke():
    _run_core_macro(test_name="test_ddr2_lpddr2_core_macro_smoke",
                    test_type="smoke")


# ---------------------------------------------------------------------------
# Engine-mirror matrix — core_macro carries 3-5x the workload coverage of
# macro top, on the principle that the fastest-to-iterate environment (no
# CSR/init flow, no APB indirection) should bear the bulk of the stress.
# Axes:
#   - N (txn count): full sweep from just-under-CAM (16) to kb32 (1024)
#   - BL (burst length): 1/2/4/8 for single-beat + power-of-2 multi-beat
#   - id_mode + id_base: FIXED / COUNTER / LFSR across id-space corners
#   - slave-delay profile: backtoback + 6 stress profiles
#   - base addr: 0x10000 + a few row-crossing / bank-spread variants
# Tier by TEST_LEVEL so quick smokes don't pay the kb32 cost.
# ---------------------------------------------------------------------------


def _eng(label, **kw):
    """Helper — build (id, env-dict) tuple from kwargs."""
    env = {f"KBN_{k.upper()}": str(v) for k, v in kw.items()}
    return (label, env)


# --- 1. N-depth sweep at BL=4, id_mode=FIXED@0, base=0x10000 (11 cfg)
_DEPTH = [
    _eng(f"depth_n{n}", N=n) for n in
    (16, 17, 18, 20, 24, 32, 48, 64, 96, 128, 1024)
]

# --- 2. BL sweep × N=32, FIXED@0 (4 cfg)
_BL = [
    _eng(f"bl{bl}_n32", N=32, BURST_LEN=bl) for bl in (1, 2, 4, 8)
]
# --- 2b. BL sweep × N=128 (kb4 scale) (4 cfg)
_BL += [
    _eng(f"bl{bl}_n128", N=128, BURST_LEN=bl) for bl in (1, 2, 4, 8)
]

# --- 3. id_mode × id_base sweep at N=64, BL=4 (12 cfg)
_ID = []
for mode, ids_ in [
    ("FIXED",   [0, 5, 7, 15]),
    ("COUNTER", [0, 5, 15]),
    ("LFSR",    [1, 7, 42, 0x9B, 0xFE]),
]:
    for ib in ids_:
        _ID.append(_eng(f"id_{mode.lower()}_{ib}_n64",
                        N=64, ID_MODE=mode, AXI_ID_BASE=ib))

# --- 4. id_mode at N=128 (kb4 scale) (5 cfg)
_ID += [
    _eng("id_counter_0_n128",  N=128, ID_MODE="COUNTER", AXI_ID_BASE=0),
    _eng("id_counter_15_n128", N=128, ID_MODE="COUNTER", AXI_ID_BASE=15),
    _eng("id_lfsr_42_n128",    N=128, ID_MODE="LFSR",    AXI_ID_BASE=42),
    _eng("id_fixed_5_n128",    N=128, ID_MODE="FIXED",   AXI_ID_BASE=5),
    _eng("id_fixed_15_n128",   N=128, ID_MODE="FIXED",   AXI_ID_BASE=15),
]

# --- 5. base address variants (row-spread, bank-spread) (6 cfg)
# row-spread bursts: large stride across row boundary
_ADDR = [
    _eng("base_0x10000_n64", N=64, BASE_ADDR="0x10000"),
    _eng("base_0x20000_n64", N=64, BASE_ADDR="0x20000"),
    _eng("base_0x40000_n64", N=64, BASE_ADDR="0x40000"),
    _eng("base_0x80000_n64", N=64, BASE_ADDR="0x80000"),
    _eng("base_0x100000_n64", N=64, BASE_ADDR="0x100000"),
    _eng("base_0x200000_n64", N=64, BASE_ADDR="0x200000"),
]

# --- 6. Slave-delay profile cross at kb4 (6 cfg)
_PROFILE_KB4 = [
    _eng(f"profile_{p}_kb4", N=128, SLAVE_PROFILE=p)
    for p in ("backtoback", "fast", "constrained",
              "burst_pause", "slow_producer", "high_throughput")
]

# --- 7. Slave-delay profile cross at N=64 (cheaper than kb4) (6 cfg)
_PROFILE_N64 = [
    _eng(f"profile_{p}_n64", N=64, SLAVE_PROFILE=p)
    for p in ("backtoback", "fast", "constrained",
              "burst_pause", "slow_producer", "high_throughput")
]

# --- 8. Combined id_mode × profile at N=64 (catches cross-axis stalls) (12 cfg)
_ID_PROFILE = []
for mode in ("FIXED", "COUNTER", "LFSR"):
    for p in ("backtoback", "constrained", "burst_pause", "slow_producer"):
        ib = 0 if mode == "FIXED" else (5 if mode == "COUNTER" else 42)
        _ID_PROFILE.append(_eng(
            f"id_{mode.lower()}_{p}_n64",
            N=64, ID_MODE=mode, AXI_ID_BASE=ib, SLAVE_PROFILE=p,
        ))

# --- 9. Pathological smokes (boundary conditions, single-cfg each) (5 cfg)
_PATHO = [
    _eng("patho_single_burst",      N=1,    BURST_LEN=1),
    _eng("patho_bl256_n1",          N=1,    BURST_LEN=64),
    _eng("patho_n2048",             N=2048),
    _eng("patho_high_id_counter",   N=128,  ID_MODE="COUNTER", AXI_ID_BASE=15),
    _eng("patho_lfsr_burst_pause",  N=128,  ID_MODE="LFSR",    AXI_ID_BASE=0xFE,
                                    SLAVE_PROFILE="burst_pause"),
]

# --- 10. BL × N grid (16 cfg)  — every combination at default id_mode
_BL_N = [
    _eng(f"grid_bl{bl}_n{n}", N=n, BURST_LEN=bl)
    for bl in (1, 2, 4, 8)
    for n in (16, 32, 64, 128)
]

# --- 11. id_mode × N grid at multiple id_bases (24 cfg)
_ID_N = []
for n in (32, 64, 128):
    for mode, ib in [
        ("FIXED",   0), ("FIXED",   15),
        ("COUNTER", 0), ("COUNTER", 8),
        ("LFSR",    1), ("LFSR",    42), ("LFSR",    0x9B),
        ("FIXED",   5),  # cover one more
    ]:
        _ID_N.append(_eng(
            f"idn_{mode.lower()}{ib}_n{n}",
            N=n, ID_MODE=mode, AXI_ID_BASE=ib,
        ))

# --- 12. Profile × N grid (21 cfg)
_PROFILE_N = [
    _eng(f"pn_{p}_n{n}", N=n, SLAVE_PROFILE=p)
    for n in (32, 64, 128)
    for p in ("backtoback", "fast", "constrained",
              "burst_pause", "slow_producer", "high_throughput", "fixed")
]

# --- 13. Profile × id_mode × N=64 grid (28 cfg)
_PROFILE_ID = []
for p in ("backtoback", "fast", "constrained", "burst_pause",
          "slow_producer", "high_throughput", "fixed"):
    for mode, ib in [
        ("FIXED",   0),
        ("COUNTER", 0),
        ("COUNTER", 15),
        ("LFSR",    42),
    ]:
        _PROFILE_ID.append(_eng(
            f"pid_{p}_{mode.lower()}{ib}_n64",
            N=64, ID_MODE=mode, AXI_ID_BASE=ib, SLAVE_PROFILE=p,
        ))

# --- 14. BL × id_mode at N=64 grid (12 cfg)
_BL_ID = []
for bl in (1, 2, 4, 8):
    for mode, ib in [
        ("FIXED",   0), ("COUNTER", 0), ("LFSR",    42),
    ]:
        _BL_ID.append(_eng(
            f"blid_bl{bl}_{mode.lower()}{ib}_n64",
            N=64, BURST_LEN=bl, ID_MODE=mode, AXI_ID_BASE=ib,
        ))

# --- 15. Base-addr × N grid (18 cfg) — multi-bank stress
_BASE_N = []
for base in ("0x10000", "0x40000", "0x100000"):
    for n in (32, 64, 128):
        for bl in (4, 8):
            _BASE_N.append(_eng(
                f"basen_{base}_bl{bl}_n{n}",
                N=n, BURST_LEN=bl, BASE_ADDR=base,
            ))

# --- 16. Full kb4-scale stress matrix — every interesting axis at kb4 (24 cfg)
_KB4_STRESS = []
for p in ("backtoback", "constrained", "burst_pause", "slow_producer"):
    for mode in ("FIXED", "COUNTER", "LFSR"):
        for bl in (4, 8):
            ib = 0 if mode == "FIXED" else (5 if mode == "COUNTER" else 42)
            _KB4_STRESS.append(_eng(
                f"kb4stress_{p}_{mode.lower()}{ib}_bl{bl}",
                N=128, BURST_LEN=bl, ID_MODE=mode, AXI_ID_BASE=ib,
                SLAVE_PROFILE=p,
            ))

# --- 17. Wide cross-product at small/medium N: catches axis interactions
#         the structured sweeps miss. (~144 cfg)
_WIDE_CROSS = []
for n in (32, 64):
    for bl in (2, 4, 8):
        for mode, ib in [
            ("FIXED",   0),
            ("FIXED",   15),
            ("COUNTER", 0),
            ("COUNTER", 7),
            ("LFSR",    1),
            ("LFSR",    42),
        ]:
            for p in ("backtoback", "fast", "burst_pause", "slow_producer"):
                _WIDE_CROSS.append(_eng(
                    f"wide_n{n}_bl{bl}_{mode.lower()}{ib}_{p}",
                    N=n, BURST_LEN=bl, ID_MODE=mode, AXI_ID_BASE=ib,
                    SLAVE_PROFILE=p,
                ))

# --- 18. Sparse address sweeps — multi-bank traffic shapes (16 cfg)
_SPARSE = []
for base in ("0x10000", "0x80000", "0x200000", "0x400000"):
    for bl in (1, 4):
        for mode in ("FIXED", "COUNTER"):
            ib = 0 if mode == "FIXED" else 5
            _SPARSE.append(_eng(
                f"sparse_b{int(base, 16):x}_bl{bl}_{mode.lower()}{ib}",
                N=64, BURST_LEN=bl, BASE_ADDR=base,
                ID_MODE=mode, AXI_ID_BASE=ib,
            ))

# --- 19. Deep-N variants at various BL (12 cfg)
_DEEP_N = []
for n in (256, 512, 1024, 2048):
    for bl in (2, 4, 8):
        _DEEP_N.append(_eng(f"deep_n{n}_bl{bl}", N=n, BURST_LEN=bl))

# --- 20. Tiny / boundary fuzzed (12 cfg)
_TINY = []
for n in (1, 2, 3, 4):
    for bl in (1, 2, 4):
        _TINY.append(_eng(f"tiny_n{n}_bl{bl}", N=n, BURST_LEN=bl))

# Tiered matrices
_ENG_GATE = [
    _eng("kb4", N=128),
    _eng("depth_n17", N=17),
    _eng("kb4_lfsr_burst_pause", N=128, ID_MODE="LFSR", AXI_ID_BASE=42,
         SLAVE_PROFILE="burst_pause"),
]
# FUNC: ~ macro-top-sized matrix, fast-leaning
_ENG_FUNC = (_DEPTH + _BL + _ID[:8] + _ADDR[:3]
             + _PROFILE_N64 + _PATHO[:2]
             + _BL_N + _ID_N[:8])                  # ~57 configs
# FULL: 3-5x macro-top coverage at the BFM-iterate-fast environment
_ENG_FULL = (_DEPTH + _BL + _ID + _ADDR
             + _PROFILE_KB4 + _PROFILE_N64
             + _ID_PROFILE + _PATHO
             + _BL_N + _ID_N + _PROFILE_N
             + _PROFILE_ID + _BL_ID + _BASE_N
             + _KB4_STRESS
             + _WIDE_CROSS + _SPARSE + _DEEP_N + _TINY)  # ~400 configs

_TEST_LEVEL_ENG = os.environ.get("TEST_LEVEL", "FUNC").upper()
_ENG_MATRIX = {
    "GATE": _ENG_GATE, "FUNC": _ENG_FUNC, "FULL": _ENG_FULL,
}.get(_TEST_LEVEL_ENG, _ENG_FUNC)


@pytest.mark.parametrize(
    "label,env_overrides",
    _ENG_MATRIX,
    ids=[e[0] for e in _ENG_MATRIX],
)
def test_ddr2_lpddr2_core_macro_engine_mirror_kbN(request, label, env_overrides):
    """Engine-faithful workload matrix at the core_macro level (3-5x the
    coverage of macro top). Same env-var contract as macro top:
    KBN_N / KBN_BURST_LEN / KBN_ID_MODE / KBN_AXI_ID_BASE /
    KBN_BASE_ADDR / KBN_SLAVE_PROFILE."""
    _run_core_macro(
        test_name=f"test_ddr2_lpddr2_core_macro_engine_mirror_{label}",
        test_type="engine_mirror_kbN",
        extra_env_extra=env_overrides,
    )


@pytest.mark.parametrize(
    "profile_aw,profile_w,profile_b,profile_ar,profile_r",
    _CORE_PROFILE_MATRIX,
    ids=[f"aw_{a}_w_{w}_b_{b}_ar_{ar}_r_{r}"
         for (a, w, b, ar, r) in _CORE_PROFILE_MATRIX],
)
def test_ddr2_lpddr2_core_macro_profile_sweep(
    request, profile_aw, profile_w, profile_b, profile_ar, profile_r,
):
    tag = (f"aw_{profile_aw}_w_{profile_w}_b_{profile_b}"
           f"_ar_{profile_ar}_r_{profile_r}")
    test_name = f"test_ddr2_lpddr2_core_macro_profile_sweep_{tag}"
    _run_core_macro(
        test_name=test_name,
        test_type="profile_sweep_b2b",
        extra_env_extra={
            "AXI_PROFILE_AW": profile_aw,
            "AXI_PROFILE_W":  profile_w,
            "AXI_PROFILE_B":  profile_b,
            "AXI_PROFILE_AR": profile_ar,
            "AXI_PROFILE_R":  profile_r,
        },
    )
