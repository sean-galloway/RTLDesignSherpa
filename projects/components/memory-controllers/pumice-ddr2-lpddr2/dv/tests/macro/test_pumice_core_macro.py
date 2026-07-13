# SPDX-License-Identifier: MIT
# SPDX-FileCopyrightText: 2024-2026 sean galloway

"""Tests for pumice_core_macro — the AXI-to-DFI macro.

The DUT is the core controller WITHOUT the CSR slave layer; cfg signals
are driven directly by the TB. Two BFM populations drive the DUT:

  - AXI4MasterWrite + AXI4MasterRead on s_axi_* (host traffic)
  - DFISlavePHY + MemoryModel on phy_dfi_* (DFI loopback with
    preloadable / inspectable backing memory)

The headline test is `test_pumice_core_macro_profile_sweep` —
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

from tbclasses.pumice_core_macro_tb import DDR2LPDDR2CoreMacroTB  # noqa: E402


# ---------------------------------------------------------------------------
# cocotb entry
# ---------------------------------------------------------------------------


@cocotb.test(timeout_time=2000, timeout_unit="ms")
async def cocotb_test_pumice_core_macro(dut):
    test_type = os.environ.get("TEST_TYPE", "smoke")
    mem_type  = os.environ.get("MEM_TYPE", "DDR2").upper()

    # TASK-GEAR: AXI width and DRAM beat width may differ (GEAR>1).
    tb = DDR2LPDDR2CoreMacroTB(
        dut, num_ranks=1,
        axi_data_width=int(os.environ.get("AXI_DATA_WIDTH", "64")),
        dram_beat_width=int(os.environ.get("DRAM_BEAT_WIDTH", "64")),
    )
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

        # FUB trackers — each scope_path resolves to the matching submodule
        # so per-FUB .out files land next to the sim_build dir on exit.
        # Same set as the macro top env, with `.u_core` stripped because
        # core_macro is `u_dut` directly (no top wrapper).
        from tbclasses.trackers._base import wire_trackers as _wire_trackers
        _TRACKER_SCOPES = {
            "sched":   "u_dut.u_command_scheduler.u_scheduler",
            "xbank":   "u_dut.u_command_scheduler.u_xbank_timers",
            "refr":    "u_dut.u_command_scheduler.u_refresh_ctrl",
            "pgpred":  "u_dut.u_command_scheduler.u_page_predictor",
            "pdn":     "u_dut.u_command_scheduler.u_powerdown_ctrl",
            "init":    "u_dut.u_command_scheduler.u_init_sequencer",
            "dficmd":  "u_dut.u_dfi_v21_interface.u_dfi_cmd_formatter",
            "wrbeat":  "u_dut.u_data_path.u_wr_beat_sequencer",
            "rdalign": "u_dut.u_data_path.u_rd_cl_aligner",
        }
        trackers = _wire_trackers(
            dut, output_dir=_os.getcwd(), log=tb.log,
            num_ranks=getattr(tb, "num_ranks", 1), num_banks=8,
            autostart=True,
            scope_paths=_TRACKER_SCOPES,
        )
        tb.log.info(
            "engine_mirror_kbN core_macro: wired %d FUB trackers",
            len(trackers),
        )

        await tb.wait_for_init_done()

        from tbclasses.pumice_sequences import (
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
        await run_axi4_sequence(wr_seq, master_wr=tb.axi_master_wr,
                                raise_on_error=True)
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

        # raise_on_error=True surfaces read_transaction BFM exceptions
        # (e.g. TimeoutError from a missing beat) as a clear RuntimeError
        # instead of a downstream NoneType shape-mismatch — see #31
        # patho_bl256_n1 for the worked example that motivated this.
        rd_dicts = await run_axi4_sequence(
            rd_seq, master_rd=tb.axi_master_rd, raise_on_error=True,
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

        # D-1 divergence check on the wired FUB trackers. Fires an
        # independent per-slot event-count parity assertion on top of
        # the scoreboard — catches #31-shape drops / #32-shape drops
        # even if downstream data happens to line up.
        from tbclasses.trackers import assert_no_divergence
        for tk_short, fub_key in (("rdalign", "rd_cl_aligner"),
                                  ("wrbeat",  "wr_beat_sequencer")):
            if tk_short in trackers:
                assert_no_divergence(fub_key, trackers[tk_short])

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

        from tbclasses.pumice_sequences import (
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
        await run_axi4_sequence(wr_seq, master_wr=tb.axi_master_wr,
                                raise_on_error=True)
        await ClockCycles(dut.mc_clk, 200)  # let B drain
        rd_dicts = await run_axi4_sequence(
            rd_seq, master_rd=tb.axi_master_rd, raise_on_error=True,
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

    elif test_type == "patho_addr_pattern":
        # D-2 pathological address patterns. Env-driven so one dispatch
        # branch handles every variant; each variant sets a different
        # address list and payload.
        #
        # Row-major mapping (default for the core_macro TB) with
        # 64-bit data + 8 banks + 14 row bits + 10 col bits:
        #   byte offset [ 2:0]
        #   col         [12:3]  → col stride     = 0x8 (8 B)
        #   bank        [15:13] → bank stride    = 0x2000 (8 KB)
        #   row         [29:16] → row stride     = 0x10000 (64 KB)
        #
        # Variants (KBN_PATHO_KIND):
        #   bank_hazard   — 16 bursts, all bank 0, sequential rows.
        #                   Every burst is a page-miss on the SAME bank
        #                   → back-to-back tRP+tRCD stalls; scheduler,
        #                   xbank timers, and command queue all stressed.
        #   page_miss_sustained — 16 bursts alternating between rows on
        #                   bank 0 → sustained row-thrash.
        #   page_close_boundary — mix of hits and misses timed so
        #                   incoming hits land close to when the page
        #                   predictor would close.
        #   hit_miss_oscillation — user-flagged internal-burst-pause:
        #                   5 hits → 3 misses → 5 hits → 3 misses → ...
        #                   All on AXI backtoback profile. Induces
        #                   internal queue fill/drain oscillation
        #                   without any external throttling.
        import os as _os
        kind = _os.environ.get("KBN_PATHO_KIND", "bank_hazard")
        BURST     = int(_os.environ.get("KBN_BURST_LEN", "4"))
        slave_profile = _os.environ.get("KBN_SLAVE_PROFILE", "backtoback")
        if slave_profile != "backtoback":
            tb.set_axi_timing_profile(slave_profile)
        tb.log.info("patho_addr_pattern kind=%s BL=%d profile=%s",
                    kind, BURST, slave_profile)

        from tbclasses.pumice_sequences import build_patho_addresses
        addresses = build_patho_addresses(kind, burst_len=BURST)

        # Wire trackers so the D-1 divergence checker runs at end.
        import os as _os2
        from tbclasses.trackers._base import wire_trackers as _wire_trackers
        _TRACKER_SCOPES = {
            "sched":   "u_dut.u_command_scheduler.u_scheduler",
            "xbank":   "u_dut.u_command_scheduler.u_xbank_timers",
            "pgpred":  "u_dut.u_command_scheduler.u_page_predictor",
            "wrbeat":  "u_dut.u_data_path.u_wr_beat_sequencer",
            "rdalign": "u_dut.u_data_path.u_rd_cl_aligner",
        }
        trackers = _wire_trackers(
            dut, output_dir=_os2.getcwd(), log=tb.log,
            num_ranks=getattr(tb, "num_ranks", 1), num_banks=8,
            autostart=True,
            scope_paths=_TRACKER_SCOPES,
        )

        await tb.wait_for_init_done()

        from tbclasses.pumice_sequences import (
            build_addr_pattern_sequences, diff_results,
        )
        from CocoTBFramework.components.axi4.axi4_sequence import (
            run_axi4_sequence,
        )

        # Assign unique IDs per burst so any per-ID ordering effect is
        # neutralized — the pathological stress is address-hazard, not
        # ID-hazard.
        ID_MASK = (1 << tb.axi_id_width) - 1
        wr_seq, rd_seq, expected = build_addr_pattern_sequences(
            burst_len=BURST, data_width=tb.axi_data_width,
            addresses=addresses,
            wr_axid_fn=lambda bi: bi & ID_MASK,
            rd_axid_fn=lambda bi: bi & ID_MASK,
            name=f"patho_{kind}",
        )
        # For patterns that write the same address more than once
        # (page_miss_sustained's ping-pong), the read-back is the
        # LAST write to that address — remap expected accordingly
        # so the scoreboard reflects actual DRAM semantics.
        last_write_by_addr: dict = {}
        for bi, addr in enumerate(addresses):
            last_write_by_addr[addr] = expected[bi]
        expected = [last_write_by_addr[addr] for addr in addresses]
        await run_axi4_sequence(wr_seq, master_wr=tb.axi_master_wr,
                                raise_on_error=True)
        from cocotb.triggers import ClockCycles as _CC_patho
        await _CC_patho(dut.mc_clk, 200)  # let B drain

        # WR-path localizer: what did the memory model actually receive?
        wr_expected: dict[int, bytes] = {}
        for bi, (addr, exp_beats) in enumerate(zip(addresses, expected)):
            payload = bytearray()
            for beat in exp_beats:
                payload += int(beat).to_bytes(tb.axi_data_width // 8,
                                              "little")
            wr_expected[addr] = bytes(payload)
        wr_bad = tb.verify_wr_path(wr_expected)
        assert wr_bad is None, (
            f"patho_{kind} WR PATH corruption at byte_addr=0x{wr_bad[0]:X} "
            f"offset={wr_bad[1]}: expected=0x{wr_bad[2]:02X} "
            f"actual=0x{wr_bad[3]:02X} — controller lost or "
            f"misrouted a WR beat before DFI."
        )
        tb.log.info("patho_%s WR-path localizer OK", kind)

        rd_dicts = await run_axi4_sequence(
            rd_seq, master_rd=tb.axi_master_rd, raise_on_error=True,
        )
        results = [r["data"] for r in rd_dicts]

        first_bad = diff_results(expected, results)
        assert first_bad is None, (
            f"patho_{kind} corrupted at burst={first_bad[0]} "
            f"beat={first_bad[1]}: wrote 0x{first_bad[2]:016X} "
            f"read 0x{first_bad[3]:016X}"
        )
        tb.log.info("patho_%s OK (%d bursts)", kind, len(addresses))

        # D-1 divergence check on the wired FUB trackers.
        from tbclasses.trackers import assert_no_divergence
        for tk_short, fub_key in (("rdalign", "rd_cl_aligner"),
                                  ("wrbeat",  "wr_beat_sequencer")):
            if tk_short in trackers:
                assert_no_divergence(fub_key, trackers[tk_short])

    elif test_type == "perf_page_batching":
        # PERF GATE + runtime-policy proof. Stream many bursts to ONE (bank,row)
        # page and program the runtime page policy. The scheduler must honor it:
        # OPEN -> column ops carry NO auto-precharge (page batched under one
        # ACT); CLOSE -> every column op auto-precharges. FAILS (RED) if the
        # page_policy CSR is inert (pre-fix, cfg ignored -> always auto-precharge)
        # or if OPEN-page batching is broken.
        policy = os.environ.get("PERF_PAGE_POLICY", "OPEN").upper()
        pol_code = {"DEFAULT": 0, "OPEN": 1, "CLOSE": 2, "HYBRID": 3}[policy]
        dut.cfg_page_policy_i.value = pol_code

        from tbclasses.trackers._base import wire_trackers as _wire_trackers
        trackers = _wire_trackers(
            dut, output_dir=os.getcwd(), log=tb.log,
            num_ranks=getattr(tb, "num_ranks", 1), num_banks=8, autostart=True,
            scope_paths={"sched": "u_dut.u_command_scheduler.u_scheduler"},
        )

        # 64 write bursts of 8 beats, walking columns within a single page
        # (row-major: col stride = beat size; stay under the 8 KB bank stride
        # and inside one row) -> all same (bank,row) => all page hits.
        BURST = 8
        NB = 64
        bb = BURST * (tb.axi_data_width // 8)      # 512 B/burst
        base = 0x0002_0000                          # page-aligned into one bank/row
        addresses = [base + i * bb for i in range(NB)]

        from tbclasses.pumice_sequences import build_addr_pattern_sequences
        from CocoTBFramework.components.axi4.axi4_sequence import (
            run_axi4_sequence,
        )
        ID_MASK = (1 << tb.axi_id_width) - 1
        wr_seq, _rd_seq, _expected = build_addr_pattern_sequences(
            burst_len=BURST, data_width=tb.axi_data_width, addresses=addresses,
            wr_axid_fn=lambda bi: bi & ID_MASK, rd_axid_fn=lambda bi: bi & ID_MASK,
            name=f"perf_page_batching_{policy}")
        await run_axi4_sequence(wr_seq, master_wr=tb.axi_master_wr,
                                raise_on_error=True)
        await ClockCycles(dut.mc_clk, 300)

        st = trackers["sched"].stats()
        ap = st["col_ops_with_ap"]
        op = st["col_ops_open_page"]
        acts = st["op_counts"].get("ACT", 0)
        tb.log.info("perf_page_batching[%s]: ACT=%d auto_pre=%d open_page=%d "
                    "(NB=%d)", policy, acts, ap, op, NB)

        if policy == "OPEN":
            # Runtime OPEN must be honored: no auto-precharge, page batched.
            assert op > 0 and ap == 0, (
                f"OPEN not honored: {ap} auto-precharge col ops (expect 0), "
                f"{op} open-page (runtime page_policy CSR inert?)")
            assert acts <= NB // 4, (
                f"poor OPEN page batching: {acts} ACTs for {NB} same-row bursts "
                f"(target <= {NB // 4}; expected ~1 ACT + many batched CAS)")
        elif policy == "CLOSE":
            # Runtime CLOSE must auto-precharge every column op (proves the CSR
            # actually switches policy, not just defaults one way).
            assert ap > 0 and op == 0, (
                f"CLOSE not honored: {op} open-page col ops (expect all "
                f"auto-precharge); runtime page_policy CSR not switching")

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


def _run_core_macro(*, test_name, test_type, extra_env_extra=None,
                    params_extra=None):
    module, repo_root, tests_dir, log_dir, _ = get_paths({})
    dut_name = "pumice_core_macro_tb"

    filelist_path = ("projects/components/memory-controllers/pumice-ddr2-lpddr2/"
                     "rtl/filelists/macro/pumice_core_macro.f")
    verilog_sources, includes = get_sources_from_filelist(
        repo_root=repo_root, filelist_path=filelist_path)
    verilog_sources.append(os.path.join(
        repo_root,
        "projects/components/memory-controllers/pumice-ddr2-lpddr2/dv/tb/"
        "pumice_core_macro_tb.sv"))

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
    if params_extra:
        parameters.update(params_extra)

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
        testcase="cocotb_test_pumice_core_macro",
        sim_build=sim_build, simulator="verilator",
        extra_env=extra_env, parameters=parameters,
        compile_args=compile_args, sim_args=sim_args, plus_args=plus_args,
        waves=enable_waves, keep_files=True, timescale="1ns/1ps")


def test_pumice_core_macro_smoke():
    _run_core_macro(test_name="test_pumice_core_macro_smoke",
                    test_type="smoke")


@pytest.mark.parametrize("policy", ["OPEN", "CLOSE"])
def test_pumice_core_macro_perf_page_batching(policy):
    """Perf regression gate: stream to one page, program the runtime page
    policy, assert the scheduler honors it (OPEN batches CAS under one ACT with
    no auto-precharge; CLOSE auto-precharges every op). Fails if the
    page_policy CSR is inert or OPEN batching is broken."""
    _run_core_macro(
        test_name=f"test_pumice_core_macro_perf_page_batching_{policy}",
        test_type="perf_page_batching",
        extra_env_extra={"PERF_PAGE_POLICY": policy})


def test_pumice_core_macro_gear2():
    """TASK-GEAR end-to-end: AXI=64 host driving a 32-bit DRAM beat at
    DFI_RATE=4 (GEAR=2 — the Nexys A7 a7ddrphy config). Exercises the full
    AXI->intake gearbox->datapath->DFI path with the DRAM-beat-granular
    write buffer + read assembly, checked against the DFISlavePHY memory."""
    _run_core_macro(
        test_name="test_pumice_core_macro_gear2",
        test_type="smoke",
        extra_env_extra={"AXI_DATA_WIDTH": "64", "DRAM_BEAT_WIDTH": "32"},
        params_extra={"AXI_DATA_WIDTH": "64", "DRAM_BEAT_WIDTH": "32",
                      "DFI_RATE": "4"},
    )


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

# Slow-profile N cap. Non-backtoback SLAVE_PROFILEs throttle AXI ready
# cycles hard. The fast MemoryModel (2026-07 rewrite) removed the
# per-transaction bottleneck that made #224 clamp _SLOW_N to 16, so we
# can afford a much higher cap and still stay under the ~1h budget.
_SLOW_PROFILES = frozenset(
    ("constrained", "burst_pause", "slow_producer", "high_throughput"))
_SLOW_N = 64


def _n_for_profile(profile: str, backtoback_N: int) -> int:
    """Return the effective N: full-scale for backtoback / fast, capped
    for the throttled slow-consumer profiles."""
    return _SLOW_N if profile in _SLOW_PROFILES else backtoback_N


# --- 6. Slave-delay profile cross at kb4 (6 cfg) — RESTORED post-mem-perf.
# The kb4-scale profile cross exercises long-running slow-consumer flows
# against a deep AXI queue; it was the axis most likely to catch pipeline
# stall regressions.
_PROFILE_KB4 = []
for p in ("backtoback", "fast", "constrained",
          "burst_pause", "slow_producer", "high_throughput"):
    n = _n_for_profile(p, 128)
    _PROFILE_KB4.append(_eng(
        f"profile_{p}_kb4_n{n}", N=n, SLAVE_PROFILE=p,
    ))

# --- 7. Slave-delay profile cross — slow profiles at _SLOW_N, fast at N=64
_PROFILE_N64 = []
for p in ("backtoback", "fast", "constrained",
          "burst_pause", "slow_producer", "high_throughput"):
    n = _n_for_profile(p, 64)
    _PROFILE_N64.append(_eng(f"profile_{p}_n{n}", N=n, SLAVE_PROFILE=p))

# --- 8. Combined id_mode × profile — slow at _SLOW_N (12 cfg)
_ID_PROFILE = []
for mode in ("FIXED", "COUNTER", "LFSR"):
    for p in ("backtoback", "constrained", "burst_pause", "slow_producer"):
        ib = 0 if mode == "FIXED" else (5 if mode == "COUNTER" else 42)
        n = _n_for_profile(p, 64)
        _ID_PROFILE.append(_eng(
            f"id_{mode.lower()}_{p}_n{n}",
            N=n, ID_MODE=mode, AXI_ID_BASE=ib, SLAVE_PROFILE=p,
        ))

# --- 9. Pathological smokes (5 cfg) — patho_n2048 restored post-mem-perf.
_PATHO = [
    _eng("patho_single_burst",      N=1,    BURST_LEN=1),
    _eng("patho_bl256_n1",          N=1,    BURST_LEN=64),
    _eng("patho_n2048",             N=2048),
    _eng("patho_high_id_counter",   N=128,  ID_MODE="COUNTER", AXI_ID_BASE=15),
    _eng(f"patho_lfsr_burst_pause_n{_SLOW_N}",
         N=_SLOW_N, ID_MODE="LFSR", AXI_ID_BASE=0xFE,
         SLAVE_PROFILE="burst_pause"),
]

# --- 10. BL × N grid (16 cfg)  — every combination at default id_mode
_BL_N = [
    _eng(f"grid_bl{bl}_n{n}", N=n, BURST_LEN=bl)
    for bl in (1, 2, 4, 8)
    for n in (16, 32, 64, 128)
]

# --- 11. id_mode × N grid (24 cfg) — RESTORED post-mem-perf.
_ID_N = []
for n in (32, 64, 128):
    for mode, ib in [
        ("FIXED",   0), ("FIXED",   15),
        ("COUNTER", 0), ("COUNTER", 8),
        ("LFSR",    1), ("LFSR",    42), ("LFSR",    0x9B),
        ("FIXED",   5),
    ]:
        _ID_N.append(_eng(
            f"idn_{mode.lower()}{ib}_n{n}",
            N=n, ID_MODE=mode, AXI_ID_BASE=ib,
        ))

# --- 12. Profile × N grid — RESTORED post-mem-perf.
# Fast/backtoback/fixed span N ∈ {32, 64, 128}; slow profiles collapse
# to a single _SLOW_N entry (they'd otherwise duplicate under the clamp).
_PROFILE_N = []
for n in (32, 64, 128):
    for p in ("backtoback", "fast", "fixed"):
        _PROFILE_N.append(_eng(
            f"pn_{p}_n{n}", N=n, SLAVE_PROFILE=p,
        ))
for p in ("constrained", "burst_pause", "slow_producer", "high_throughput"):
    _PROFILE_N.append(_eng(
        f"pn_{p}_n{_SLOW_N}", N=_SLOW_N, SLAVE_PROFILE=p,
    ))

# --- 13. Profile × id_mode grid — slow profiles at _SLOW_N (28 cfg → 28)
_PROFILE_ID = []
for p in ("backtoback", "fast", "constrained", "burst_pause",
          "slow_producer", "high_throughput", "fixed"):
    for mode, ib in [
        ("FIXED",   0),
        ("COUNTER", 0),
        ("COUNTER", 15),
        ("LFSR",    42),
    ]:
        n = _n_for_profile(p, 64)
        _PROFILE_ID.append(_eng(
            f"pid_{p}_{mode.lower()}{ib}_n{n}",
            N=n, ID_MODE=mode, AXI_ID_BASE=ib, SLAVE_PROFILE=p,
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

# --- 15. Base-addr × N grid (18 cfg) — RESTORED post-mem-perf.
_BASE_N = []
for base in ("0x10000", "0x40000", "0x100000"):
    for n in (32, 64, 128):
        for bl in (4, 8):
            _BASE_N.append(_eng(
                f"basen_{base}_bl{bl}_n{n}",
                N=n, BURST_LEN=bl, BASE_ADDR=base,
            ))

# --- 16. Full kb4-scale stress matrix — slow profiles at _SLOW_N (24 cfg)
_KB4_STRESS = []
for p in ("backtoback", "constrained", "burst_pause", "slow_producer"):
    for mode in ("FIXED", "COUNTER", "LFSR"):
        for bl in (4, 8):
            ib = 0 if mode == "FIXED" else (5 if mode == "COUNTER" else 42)
            n = _n_for_profile(p, 128)
            _KB4_STRESS.append(_eng(
                f"kb4stress_{p}_{mode.lower()}{ib}_bl{bl}_n{n}",
                N=n, BURST_LEN=bl, ID_MODE=mode, AXI_ID_BASE=ib,
                SLAVE_PROFILE=p,
            ))

# --- 17. Wide cross-product — expanded post-mem-perf (~72 cfg).
# Original 144-cfg cube was excessive; this restores N=64 and the
# slow_producer profile that #224 dropped, while trimming redundant
# id_base variants. Slow profiles clamp to _SLOW_N.
_WIDE_CROSS = []
for n_bt in (32, 64):
    for bl in (2, 4, 8):
        for mode, ib in [("FIXED", 0), ("COUNTER", 0), ("LFSR", 42)]:
            for p in ("backtoback", "fast", "burst_pause", "slow_producer"):
                n = _n_for_profile(p, n_bt)
                _WIDE_CROSS.append(_eng(
                    f"wide_n{n_bt}_bl{bl}_{mode.lower()}{ib}_{p}",
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

# --- 19. Deep-N variants (8 cfg) — RESTORED post-mem-perf.
# BL=2 dropped: three N tiers × BL=2 didn't add coverage over BL=4/8
# in the tail behavior; kept BL ∈ {4, 8} across four depth points.
_DEEP_N = []
for n in (256, 512, 1024, 2048):
    for bl in (4, 8):
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


# #26 (non-backtoback SLAVE_PROFILE) was NOT an init-sequencing bug as
# initially speculated — DDR2LPDDR2CoreMacroTB was simply missing
# set_axi_timing_profile(). Method added, profile configs no longer xfail.
#
# #31 (rd_cl_aligner EN-pipeline skip under 16-way intake-split cadence)
# is fixed by the circular-FIFO refactor. Kept _BUG_A_SUBSTRS = ()
# so the wrapper mechanism stays available for future gating without
# marking any label xfail today.
_BUG_A_SUBSTRS: tuple[str, ...] = ()


def _eng_xfail_reason(label: str):
    for s in _BUG_A_SUBSTRS:
        if s in label:
            return "(placeholder — no bug-A configs currently xfailed)"
    return None


def _eng_params(matrix):
    out = []
    for (label, env) in matrix:
        reason = _eng_xfail_reason(label)
        if reason:
            out.append(pytest.param(
                label, env,
                marks=pytest.mark.xfail(reason=reason, strict=False),
            ))
        else:
            out.append((label, env))
    return out


@pytest.mark.parametrize(
    "label,env_overrides",
    _eng_params(_ENG_MATRIX),
    ids=[e[0] for e in _ENG_MATRIX],
)
def test_pumice_core_macro_engine_mirror_kbN(request, label, env_overrides):
    """Engine-faithful workload matrix at the core_macro level (3-5x the
    coverage of macro top). Same env-var contract as macro top:
    KBN_N / KBN_BURST_LEN / KBN_ID_MODE / KBN_AXI_ID_BASE /
    KBN_BASE_ADDR / KBN_SLAVE_PROFILE."""
    _run_core_macro(
        test_name=f"test_pumice_core_macro_engine_mirror_{label}",
        test_type="engine_mirror_kbN",
        extra_env_extra=env_overrides,
    )


# ---------------------------------------------------------------------------
# D-2 pathological address-pattern matrix. Cross of (kind, AXI profile).
# Each kind constructs a specific hazardous access sequence that stresses
# a particular internal pathway. The AXI profile axis lets us hit "all
# AXI fast + internal misses cause internal burst-pause" (the novel
# oscillation stress) and its inverse ("slow AXI + fast internal").
# ---------------------------------------------------------------------------
_PATHO_KINDS = (
    "bank_hazard",           # #3 — 16 misses on bank 0, sequential rows
    "page_miss_sustained",   # #7 — 24 bursts ping-ponging 3 rows on bank 0
    "page_close_boundary",   # #6 — miss + rapid hits at predictor's
                             #      close-decision cycle
    "hit_miss_oscillation",  # #8 — 5 hits → 3 misses × 4 cycles; AXI fast
                             #      but INTERNAL burst-pause via miss bursts
)
_PATHO_PROFILES = ("backtoback", "burst_pause", "slow_producer")

_PATHO_MATRIX = [
    (kind, prof) for kind in _PATHO_KINDS for prof in _PATHO_PROFILES
]


@pytest.mark.parametrize(
    "kind,slave_profile", _PATHO_MATRIX,
    ids=[f"{k}_{p}" for (k, p) in _PATHO_MATRIX],
)
def test_pumice_core_macro_patho_addr_pattern(request, kind, slave_profile):
    """D-2 pathological address patterns. Each variant stresses a
    specific memory-controller pathway (bank timers, page predictor,
    scheduler queue). All variants run through the D-1 divergence
    checker at teardown so per-slot event drops surface as clear
    assertion messages independent of the data scoreboard."""
    test_name = (
        f"test_pumice_core_macro_patho_{kind}_{slave_profile}"
    )
    _run_core_macro(
        test_name=test_name,
        test_type="patho_addr_pattern",
        extra_env_extra={
            "KBN_PATHO_KIND":    kind,
            "KBN_SLAVE_PROFILE": slave_profile,
            "KBN_BURST_LEN":     "4",
        },
    )


@pytest.mark.parametrize(
    "profile_aw,profile_w,profile_b,profile_ar,profile_r",
    _CORE_PROFILE_MATRIX,
    ids=[f"aw_{a}_w_{w}_b_{b}_ar_{ar}_r_{r}"
         for (a, w, b, ar, r) in _CORE_PROFILE_MATRIX],
)
def test_pumice_core_macro_profile_sweep(
    request, profile_aw, profile_w, profile_b, profile_ar, profile_r,
):
    tag = (f"aw_{profile_aw}_w_{profile_w}_b_{profile_b}"
           f"_ar_{profile_ar}_r_{profile_r}")
    test_name = f"test_pumice_core_macro_profile_sweep_{tag}"
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
