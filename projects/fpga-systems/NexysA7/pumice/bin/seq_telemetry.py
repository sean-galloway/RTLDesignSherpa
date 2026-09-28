# SPDX-License-Identifier: MIT
# SPDX-FileCopyrightText: 2026 sean galloway
"""Telemetry invariants ON SILICON (pumice TASK-015 layer 2b).

Runs the SAME invariant module the sim layer runs --
`pumice-ddr2-lpddr2/dv/tbclasses/pumice_telemetry_invariants.py` -- against
counters read off the board. One definition of "arithmetically consistent",
checked in both places, is the whole point: an oracle that exists only in sim
cannot tell you the silicon agrees, and the repo has already shipped a case
where sim converted 54% of activations and the board 3% on stimulus believed
identical.

Per scenario it takes a window (two reads, subtracting, masking the 32-bit wrap
-- the counters free-run and clear only on aresetn) and checks every relation
that arms. `require=` names every rule, so a scenario whose counters did not
move cannot report a clean pass.

    make run SEQ="init write_read telemetry"
    make run SEQ="init telemetry" SEQ_PARAM_tel_txn=4000
"""

from __future__ import annotations

import importlib.util
import os

import pumice_env  # noqa: F401  (import side effect: sys.path setup)

from sequence import Sequence

import pumice_char as pc

_REPO = os.environ.get("REPO_ROOT") or os.path.abspath(
    os.path.join(os.path.dirname(__file__), "..", "..", "..", ".."))
_TI = os.path.join(_REPO, "projects/components/memory-controllers/pumice-ddr2-lpddr2",
                   "dv/tbclasses/pumice_telemetry_invariants.py")

_spec = importlib.util.spec_from_file_location("pumice_telemetry_invariants", _TI)
ti = importlib.util.module_from_spec(_spec)
_spec.loader.exec_module(ti)

# The counter names the invariants key on. PageStats already carries seven of
# them; the eight per-bank hit counters are read here because the invariants need
# them and PageStats predates the relations that use them.
_PER_BANK = tuple(f"OBS_ROW_HIT{b}_ROW_HIT" for b in range(8))


def _read_counters(drv) -> dict:
    f = drv.pumice.regs.field
    out = {
        "PAGE_STATS_HIT":     int(f("PAGE_STATS_HIT", "VAL")),
        "PAGE_STATS_MISS":    int(f("PAGE_STATS_MISS", "VAL")),
        "PAGE_STATS_EMPTY":   int(f("PAGE_STATS_EMPTY", "VAL")),
        "SCHED_STATS_ACT":    int(f("SCHED_STATS_ACT", "VAL")),
        "SCHED_STATS_PRE":    int(f("SCHED_STATS_PRE", "VAL")),
        "REF_STATS_REF":      int(f("REF_STATS_REF", "VAL")),
        "REF_STATS_REF_BUSY": int(f("REF_STATS_REF_BUSY", "VAL")),
    }
    for name in _PER_BANK:
        out[name] = int(f(name, "VAL"))
    return out


def _window(before: dict, after: dict) -> dict:
    return {k: (after[k] - before[k]) & 0xFFFFFFFF for k in after}


class Telemetry(Sequence):
    name = "telemetry"
    description = "layer-2b counter invariants on the board, same rules as sim"
    requires = ("init",)

    def run(self, ctx):
        drv = ctx.bus
        txn = ctx.param("tel_txn", 2000)
        bl = ctx.param("burst_len", 16)
        base = ctx.param("base_addr", 0x0)
        clk = pc.resolve_clk_mhz(drv, ctx.param("clk_mhz"))

        # Families chosen to move DIFFERENT counters: incremental and row_major
        # stream within rows (hits), col_major walks the bank/row axis (misses and
        # opens). A single family arms the rules but exercises one page behaviour.
        #
        # `tel_families`, NOT `families`: the runner already defines --families
        # for the page_policy A/B and defaults it to incremental,row_major. Reading
        # that name silently dropped col_major from this sequence -- it reported
        # "2 window(s)" and passed while covering two thirds of what it claims.
        fams = ctx.param("tel_families",
                         ["incremental", "row_major", "col_major"])

        results, total_armed, windows = {}, 0, []
        for fam_name in fams:
            fam = getattr(pc, f"FAM_{fam_name.upper()}", None)
            if fam is None:
                raise AssertionError(f"unknown scenario family {fam_name!r}")
            sc = pc.Scenario(name=f"tel_{fam_name}", family=fam,
                             burst_len=bl, txn_count=txn)

            before = _read_counters(drv)
            # cfg=ControllerConfig() leaves every mode field at its RESET, which
            # layer 0 has just established IS the shipping configuration. The
            # default here is `CLOSE_PAGE`, which would measure a policy the
            # board does not ship.
            rec = pc.measure(drv, sc, cfg=pc.ControllerConfig(name="shipping_resets"),
                             base_addr=base, clk_mhz=clk)
            after = _read_counters(drv)
            d = _window(before, after)

            ctx.say(f"[telemetry] {fam_name}: col_ops={d['PAGE_STATS_HIT']} "
                    f"ACT={d['SCHED_STATS_ACT']} PRE={d['SCHED_STATS_PRE']} "
                    f"miss={d['PAGE_STATS_MISS']} empty={d['PAGE_STATS_EMPTY']} "
                    f"per_bank_hits={sum(d[n] for n in _PER_BANK)} "
                    f"ACT-col_ops={d['SCHED_STATS_ACT'] - d['PAGE_STATS_HIT']}")

            # Traffic that did not move the counters must not read as clean.
            if d["PAGE_STATS_HIT"] == 0:
                raise AssertionError(
                    f"{fam_name}: no column ops counted over the window -- the "
                    f"telemetry is not reaching the host, or no traffic ran. "
                    f"Window: {d}")

            # BUG-020 is FIXED: OBS_ROW_HIT[8] is driven now, so the two rules
            # that use the per-bank counters are enforced here like the rest.
            # (They were skipped while the counters read zero forever.)
            armed = ti.assert_clean(
                d, require=tuple(r.name for r in ti.RULES),
                context=f"board telemetry / {fam_name}")
            total_armed += armed
            windows.append((fam_name, d))
            results[fam_name] = {
                "col_ops": d["PAGE_STATS_HIT"],
                "acts": d["SCHED_STATS_ACT"],
                "per_bank_hits": sum(d[n] for n in _PER_BANK),
                "armed": armed,
                "integrity_ok": bool(getattr(rec, "ok", True)),
                "mismatched": int(getattr(rec, "mismatched", 0) or 0),
            }
            # Integrity is not the subject here, but a run whose DATA was wrong
            # must not be reported as a clean telemetry result -- that exact
            # shape (healthy number, failed integrity) has shipped before.
            if not results[fam_name]["integrity_ok"]:
                raise AssertionError(
                    f"{fam_name}: telemetry was consistent but the DATA check "
                    f"failed ({results[fam_name]['mismatched']} mismatches). The "
                    f"invariants passing on corrupt traffic is not a pass.")

        ctx.say(f"[telemetry] PASS: {len(fams)} window(s), {len(ti.RULES)} rules "
                f"armed each ({total_armed} evaluations), 0 violations, none skipped.")
        return {"windows": results, "rules": len(ti.RULES),
                "rule_evaluations": total_armed}
