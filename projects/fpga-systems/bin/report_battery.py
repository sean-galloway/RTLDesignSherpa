#!/usr/bin/env python3
# SPDX-License-Identifier: MIT
"""Render a battery-run report from one or more FPGA loop transcripts.

Parses RS/BCH run_smoke transcripts, attributes multi-section logs by their
"=== <image> ===" headers, and emits:

    battery.json
    fig_1_correction_boundary.png
    fig_2_decode_cost.png
    fig_3_soak_timeline.png
    fig_4_injector_envelope.png
    fig_5_solver_agreement.png
    FINDINGS.md

The script never fails on a partial BCH soak tail; it records the state it saw
and notes the limitation.
"""

from __future__ import annotations

import argparse
import json
import math
import os
import re
from collections import defaultdict
from datetime import datetime, timezone
from pathlib import Path
from typing import Any

import matplotlib

matplotlib.use("Agg")
import matplotlib.pyplot as plt


HEADER_BLOCK = """<!-- RTL Design Sherpa Documentation Header -->
<table>
<tr>
<td width="80">
  <a href="https://github.com/sean-galloway/RTLDesignSherpa">
    <img src="https://raw.githubusercontent.com/sean-galloway/RTLDesignSherpa/main/docs/logos/Logo_200px.png" alt="RTL Design Sherpa" width="70">
  </a>
</td>
<td>
  <strong>RTL Design Sherpa</strong> · <em>Learning Hardware Design Through Practice</em><br>
  <sub>
    <a href="https://github.com/sean-galloway/RTLDesignSherpa">GitHub</a> ·
    <a href="https://github.com/sean-galloway/RTLDesignSherpa/blob/main/docs/DOCUMENTATION_INDEX.md">Documentation Index</a> ·
    <a href="https://github.com/sean-galloway/RTLDesignSherpa/blob/main/docs/DOCUMENTATION_INDEX.md">MIT License</a>
  </sub>
</td>
</tr>
</table>

---

<!-- End Header -->
"""

SECTION_RE = re.compile(r"^===\s*(.+?)\s*===$")
INIT_RE = re.compile(
    r"^\[init\]\s+(RS|BCH)\((\d+),(\d+)\)\s+t=(\d+)\s+m=(\d+)\s+(\d+)\s+symbols/beat"
)
TOPO_RE = re.compile(
    r"^\[init\]\s+(\d+)\s+decoder(?:s)?:\s*(.+)$"
)
PROGRAM_FAIL_RE = re.compile(r"PROGRAM\s+FAILED\s+for\s+(\S+)", re.IGNORECASE)
SEQ_RE = re.compile(r"^\[seq\]\s+(\w+)\s+(PASS|FAIL)")
RUN_SUMMARY_RE = re.compile(r"^\[run\].*?(ALL\s+PASS|FAILURES)", re.IGNORECASE)

RS_SMOKE_RE = re.compile(
    r"^\[smoke\]\s+(\S+):\s+([\d.]+)\s+cycles/block,\s+"
    r"riBM\s+ok/corr/unc=(\d+)/(\d+)/(\d+),\s+"
    r"Euclid\s+ok/corr/unc=(\d+)/(\d+)/(\d+),\s+"
    r"A=B=(yes|NO)\s+->\s+(PASS|FAIL)"
)

RS_SWEEP_RE = re.compile(
    r"^\[sweep\]\s+e=\s*(\d+)\s+cyc/blk=\s+([\d.]+)\s+"
    r"riBM\s+ok/corr/unc=(\d+)/(\d+)/(\d+)\s+sym=(\d+)\s+data=(\S+)\s+"
    r"Euclid\s+ok/corr/unc=(\d+)/(\d+)/(\d+)\s+sym=(\d+)\s+data=(\S+)\s+"
    r"A=B:(yes|NO)\s+(PASS|FAIL)"
)

BCH_SMOKE_RE = re.compile(
    r"^\[smoke\]\s+(\S+):\s+([\d.]+)\s+cycles/block,\s+"
    r"ok/corr/unc=(\d+)/(\d+)/(\d+)\s+sym=(\d+)\s+data=(\S+)\s+->\s+(PASS|FAIL)"
)

BCH_SWEEP_RE = re.compile(
    r"^\[sweep\]\s+e=\s*(\d+)\s+cyc/blk=\s+([\d.]+)\s+"
    r"RIBM\s+ok/corr/unc=(\d+)/(\d+)/(\d+)\s+sym=(\d+)\s+data=(\S+)\s+"
    r"(PASS|FAIL)"
)

RANDOM_RE = re.compile(
    r"^\[random\]\s+(\d+)\s+runs\s+x\s+(\d+)\s+blocks\s+on\s+"
    r"(?:RS|BCH)\((\d+),(\d+)\):\s+(.+?);\s+"
    r"blocks\s+(\d+)\s+clean\s+/\s+(\d+)\s+corrected\s+/\s+(\d+)\s+uncorrectable;\s+"
    r"(\d+)\s+failing run\(s\)"
)

CAMPAIGN_RE = re.compile(
    r"^\[(clusters|localized|badblock)\]\s+(\d+)\s+combos\s+x\s+(\d+)\s+blocks\s+"
    r"on\s+(?:RS|BCH)\((\d+),(\d+)\);\s+(\d+)\s+failing combo\(s\)"
)

SOAK_PROGRESS_RE = re.compile(
    r"^\[soak\]\s+([\d,]+)/([\d,]+)\s+blocks\s+([\d.]+)s\s+([\d.]+)\s+blk/s\s+"
    r"clean/corr/unc=(\d+)/(\d+)/(\d+)\s+(\d+)\s+failing run\(s\)"
)

SOAK_FINAL_RE = re.compile(
    r"^\[soak\]\s+([\d,]+)\s+blocks\s+in\s+([\d.]+)s\s+\(([\d.]+)\s+blk/s\);\s+"
    r"([\d,]+)\s+clean\s+/\s+([\d,]+)\s+corrected\s+/\s+([\d,]+)\s+uncorrectable;\s+"
    r"([\d,]+)\s+(bits|symbols) corrected;\s+([\d,]+)\s+failing run\(s\)"
)

SOAK_THRESHOLD_RE = re.compile(
    r"^\[soak\]\s+beyond the threshold:\s+([\d,]+)\s+of\s+([\d,]+)\s+blocks\s+were\s+"
    r"accepted and silently mis-decoded\s+\(([\d.eE+-]+),\s+1\s+in\s+([\d,]+)\)"
)


class LogGroupAction(argparse.Action):
    """Pair --log with subsequent --image arguments until the next --log."""

    def __call__(self, parser, namespace, values, option_string=None):
        groups = getattr(namespace, "log_groups", [])
        if option_string == "--log":
            groups.append({"log": values, "images": []})
        elif option_string == "--image":
            if not groups:
                parser.error("--image must follow a --log")
            groups[-1]["images"].append(values)
        setattr(namespace, "log_groups", groups)


def parse_args(argv=None):
    parser = argparse.ArgumentParser(
        description="Render a battery-run report from FPGA loop transcripts."
    )
    parser.add_argument(
        "--out", required=True, help="output directory for the report artifacts"
    )
    parser.add_argument(
        "--log", action=LogGroupAction, required=True, help="transcript file"
    )
    parser.add_argument(
        "--image", action=LogGroupAction, help="image name for the preceding --log"
    )
    parser.add_argument("--serial", default="unknown", help="board serial number")
    parser.add_argument("--date", default=None, help="report date (ISO-8601)")
    args = parser.parse_args(argv)
    if not args.log_groups:
        parser.error("at least one --log is required")
    for g in args.log_groups:
        if not g["images"]:
            g["images"] = [Path(g["log"]).stem]
    if args.date is None:
        args.date = datetime.now(timezone.utc).strftime("%Y-%m-%d")
    return args


def split_sections(lines, defaults):
    """Split a transcript into sections by === header === lines.

    Returns a list of (name, [lines]) tuples. The first unlabeled section uses
    the first default name; subsequent unlabeled content is folded into the
    current section.
    """
    sections: list[tuple[str, list[str]]] = []
    current_name = defaults[0] if defaults else "unknown"
    current_lines: list[str] = []

    for raw in lines:
        line = raw.rstrip("\n")
        m = SECTION_RE.match(line)
        if m:
            if current_lines:
                sections.append((current_name, current_lines))
            current_name = m.group(1).strip()
            current_lines = []
            continue
        current_lines.append(line)

    if current_lines:
        sections.append((current_name, current_lines))

    # If the file had no headers, attribute the whole file to the first default.
    if not sections:
        sections.append((current_name, []))

    return sections


def parse_smoke(line):
    m = RS_SMOKE_RE.match(line)
    if m:
        return {
            "label": m.group(1),
            "cyc/blk": float(m.group(2)),
            "riBM": {"ok": int(m.group(3)), "corr": int(m.group(4)), "unc": int(m.group(5))},
            "Euclid": {"ok": int(m.group(6)), "corr": int(m.group(7)), "unc": int(m.group(8))},
            "A=B": m.group(9),
            "status": m.group(10),
            "codec": "RS",
        }
    m = BCH_SMOKE_RE.match(line)
    if m:
        return {
            "label": m.group(1),
            "cyc/blk": float(m.group(2)),
            "A": {"ok": int(m.group(3)), "corr": int(m.group(4)), "unc": int(m.group(5))},
            "sym": int(m.group(6)),
            "data": m.group(7),
            "status": m.group(8),
            "codec": "BCH",
        }
    return None


def parse_sweep(line):
    m = RS_SWEEP_RE.match(line)
    if m:
        return {
            "e": int(m.group(1)),
            "cyc/blk": float(m.group(2)),
            "riBM": {"ok": int(m.group(3)), "corr": int(m.group(4)), "unc": int(m.group(5))},
            "riBM_sym": int(m.group(6)),
            "riBM_data": m.group(7),
            "Euclid": {"ok": int(m.group(8)), "corr": int(m.group(9)), "unc": int(m.group(10))},
            "Euclid_sym": int(m.group(11)),
            "Euclid_data": m.group(12),
            "A=B": m.group(13),
            "status": m.group(14),
            "codec": "RS",
        }
    m = BCH_SWEEP_RE.match(line)
    if m:
        return {
            "e": int(m.group(1)),
            "cyc/blk": float(m.group(2)),
            "A": {"ok": int(m.group(3)), "corr": int(m.group(4)), "unc": int(m.group(5))},
            "A_sym": int(m.group(6)),
            "A_data": m.group(7),
            "status": m.group(8),
            "A=B": "yes",  # single decoder is trivially self-agreeing
            "codec": "BCH",
        }
    return None


def parse_section(name, lines, log_file):
    record: dict[str, Any] = {
        "name": name,
        "log_file": log_file,
        "codec": None,
        "params": {},
        "solver": None,
        "topology": None,
        "program_failed": False,
        "program_failed_reason": None,
        "sequences": {},
        "smoke": [],
        "sweep": [],
        "random": None,
        "campaigns": {},
        "soak_progress": [],
        "soak_final": None,
        "errors": [],
        "status": "UNKNOWN",
    }

    active_seq = None
    for line in lines:
        # Header already stripped.
        m = INIT_RE.match(line)
        if m:
            record["codec"] = m.group(1)
            record["params"] = {
                "n": int(m.group(2)),
                "k": int(m.group(3)),
                "t": int(m.group(4)),
                "m": int(m.group(5)),
                "spb": int(m.group(6)),
            }
            continue

        m = TOPO_RE.match(line)
        if m:
            record["topology"] = m.group(1)
            record["solver"] = m.group(2).strip().rstrip(";")
            continue

        m = PROGRAM_FAIL_RE.search(line)
        if m:
            record["program_failed"] = True
            record["program_failed_reason"] = line
            continue

        m = SEQ_RE.match(line)
        if m:
            seq_name, status = m.group(1), m.group(2)
            active_seq = seq_name
            record["sequences"][seq_name] = {"status": status}
            continue

        m = RUN_SUMMARY_RE.search(line)
        if m:
            record["run_summary"] = m.group(1)
            continue

        parsed_smoke = parse_smoke(line)
        if parsed_smoke:
            record["smoke"].append(parsed_smoke)
            continue

        parsed_sweep = parse_sweep(line)
        if parsed_sweep:
            record["sweep"].append(parsed_sweep)
            continue

        m = RANDOM_RE.match(line)
        if m:
            record["random"] = {
                "runs": int(m.group(1)),
                "blocks": int(m.group(2)),
                "n": int(m.group(3)),
                "k": int(m.group(4)),
                "mix": m.group(5),
                "clean": int(m.group(6)),
                "corrected": int(m.group(7)),
                "uncorrectable": int(m.group(8)),
                "failing": int(m.group(9)),
            }
            continue

        m = CAMPAIGN_RE.match(line)
        if m:
            campaign = m.group(1)
            record["campaigns"][campaign] = {
                "combos": int(m.group(2)),
                "blocks": int(m.group(3)),
                "n": int(m.group(4)),
                "k": int(m.group(5)),
                "failing": int(m.group(6)),
            }
            continue

        m = SOAK_PROGRESS_RE.match(line)
        if m:
            record["soak_progress"].append(
                {
                    "done": int(m.group(1).replace(",", "")),
                    "total": int(m.group(2).replace(",", "")),
                    "wall_s": float(m.group(3)),
                    "blk_s": float(m.group(4)),
                    "clean": int(m.group(5)),
                    "corr": int(m.group(6)),
                    "unc": int(m.group(7)),
                    "failing": int(m.group(8)),
                }
            )
            continue

        m = SOAK_FINAL_RE.match(line)
        if m:
            record["soak_final"] = {
                "blocks_final": int(m.group(1).replace(",", "")),
                "wall_s": float(m.group(2)),
                "blk_per_s": float(m.group(3)),
                "clean": int(m.group(4).replace(",", "")),
                "corrected": int(m.group(5).replace(",", "")),
                "uncorrectable": int(m.group(6).replace(",", "")),
                "bits_corrected": int(m.group(7).replace(",", "")),
                "failing_runs": int(m.group(9).replace(",", "")),
            }
            continue

        m = SOAK_THRESHOLD_RE.match(line)
        if m:
            sf = record.setdefault("soak_final", {})
            sf["misdecoded"] = int(m.group(1).replace(",", ""))
            sf["over_t_blocks"] = int(m.group(2).replace(",", ""))
            sf["misdecode_rate"] = f"{m.group(3)} (1 in {m.group(4)})"
            continue

        # Capture explicit failure explanations and tracebacks.
        if "RuntimeError" in line or "Traceback" in line or "ERROR:" in line:
            record["errors"].append(line)

    # Determine status.
    if record["program_failed"]:
        record["status"] = "PROGRAM_FAILED"
    elif record["errors"] or any(
        s.get("status") == "FAIL" for s in record["sequences"].values()
    ):
        record["status"] = "FAIL"
    elif record["soak_progress"] and record["soak_final"] is None:
        record["status"] = "PARTIAL"
    elif record["sequences"] or record["soak_final"]:
        all_pass = all(s.get("status") == "PASS" for s in record["sequences"].values())
        run_ok = record.get("run_summary", "ALL PASS") == "ALL PASS"
        if all_pass and run_ok:
            record["status"] = "PASS"
        else:
            record["status"] = "FAIL"

    return record


def load_records(groups):
    """Return a list of parsed image records, one per section/default image."""
    records = []
    for g in groups:
        log_path = g["log"]
        defaults = g["images"]
        with open(log_path, "r", encoding="utf-8", errors="replace") as f:
            lines = f.readlines()
        sections = split_sections(lines, defaults)
        seen_names = set()
        merged = []
        for name, sec_lines in sections:
            if name in seen_names:
                # Append lines to existing section.
                for i, (n, _) in enumerate(merged):
                    if n == name:
                        merged[i] = (n, _ + sec_lines)
                        break
            else:
                seen_names.add(name)
                merged.append((name, sec_lines))

        # If the file had no headers at all, attribute the whole transcript to
        # the first default image name. Other defaults are ignored with a note.
        if len(merged) == 1 and merged[0][0] in defaults and not any(
            SECTION_RE.match(line) for line in lines
        ):
            merged = [(defaults[0], lines)]

        for name, sec_lines in merged:
            records.append(parse_section(name, sec_lines, log_path))

    return records


def build_summary(records):
    total = len(records)
    passed = sum(1 for r in records if r["status"] == "PASS")
    failed = sum(1 for r in records if r["status"] == "FAIL")
    partial = sum(1 for r in records if r["status"] == "PARTIAL")
    program_failed = sum(1 for r in records if r["status"] == "PROGRAM_FAILED")
    unknown = total - passed - failed - partial - program_failed

    campaigns = defaultdict(lambda: {"combos": 0, "failing": 0})
    for r in records:
        for camp, data in r["campaigns"].items():
            campaigns[camp]["combos"] += data["combos"]
            campaigns[camp]["failing"] += data["failing"]
        if r["random"]:
            campaigns["random"]["combos"] += r["random"]["runs"]
            campaigns["random"]["failing"] += r["random"]["failing"]

    return {
        "images": total,
        "passed": passed,
        "failed": failed,
        "partial": partial,
        "program_failed": program_failed,
        "unknown": unknown,
        "campaigns": dict(campaigns),
    }


def deduplicate_records(records):
    """Keep the richest section per image; list the rest as superseded.

    Priority (highest first):
      1. init PASS + sweep rows
      2. random rows
      3. anything with init FAIL
      4. program-failed / empty sections
    Ties prefer PASS > PARTIAL > FAIL > PROGRAM_FAILED, then a later file.
    """

    def score(r):
        if r["program_failed"] or r["codec"] is None:
            return 0
        if r["sequences"].get("init", {}).get("status") == "FAIL":
            return 1
        if r["sweep"]:
            return 10 + len(r["sweep"])
        if r["random"]:
            return 5
        return 2

    def status_rank(r):
        return {"PASS": 3, "PARTIAL": 2, "FAIL": 1, "PROGRAM_FAILED": 0}.get(r["status"], -1)

    best: dict[str, tuple[int, int, int, dict]] = {}
    superseded = []
    for idx, r in enumerate(records):
        name = r["name"]
        s = score(r)
        rank = status_rank(r)
        entry = (s, rank, idx, r)
        if name not in best:
            best[name] = entry
            continue
        cur = best[name]
        # Higher score wins; on ties prefer better status then later file.
        if (s, rank, idx) > (cur[0], cur[1], cur[2]):
            superseded.append(make_superseded(cur[3], r["log_file"]))
            best[name] = entry
        else:
            superseded.append(make_superseded(r, cur[3]["log_file"]))

    kept = [best[name][3] for name in best]
    # Preserve original order of first appearance for kept records.
    order = {id(r): i for i, r in enumerate(records) if id(r) in {id(best[n][3]) for n in best}}
    kept.sort(key=lambda r: order[id(r)])
    return kept, superseded


def make_superseded(record, kept_log_file):
    reason = "empty / no codec data"
    if record["program_failed"]:
        reason = "program failed"
    elif record["sequences"].get("init", {}).get("status") == "FAIL":
        reason = "init FAIL"
    elif record["sweep"] or record["random"]:
        reason = "superseded by richer section"
    return {
        "image": record["name"],
        "log_file": record["log_file"],
        "status": record["status"],
        "reason": f"{reason} -- kept section from {kept_log_file}",
    }


def figure_path(out_dir, num, name):
    return os.path.join(out_dir, f"fig_{num}_{name}.png")


def save_or_close(fig, path, title=""):
    fig.suptitle(title, fontsize=10, y=0.96)
    fig.tight_layout(rect=[0, 0, 1, 0.94])
    fig.savefig(path, dpi=150)
    plt.close(fig)


def plot_correction_boundary(records, out_dir):
    path = figure_path(out_dir, 1, "correction_boundary")

    sweepers = [r for r in records if r["sweep"]]
    if not sweepers:
        fig, ax = plt.subplots(figsize=(8, 5))
        ax.text(0.5, 0.5, "no sweep data", ha="center", va="center", transform=ax.transAxes)
        ax.set_xticks([])
        ax.set_yticks([])
        save_or_close(fig, path, "Fig 1: correction boundary")
        return path

    n_images = len(sweepers)
    cols = 2
    rows = (n_images + 1) // 2
    fig, axes = plt.subplots(rows, cols, figsize=(10, 4 * rows), sharex=True, sharey=True)
    try:
        axes = axes.flatten().tolist()
    except AttributeError:
        axes = [axes]

    all_es = sorted({row["e"] for r in sweepers for row in r["sweep"]})
    t = sweepers[0]["params"].get("t")

    for idx, (r, ax) in enumerate(zip(sweepers, axes)):
        by_e = {row["e"]: row for row in r["sweep"]}
        corr = []
        unc = []
        for e in all_es:
            row = by_e.get(e)
            if row is None:
                corr.append(0)
                unc.append(0)
                continue
            if row["codec"] == "RS":
                # Both decoders agree on the verdict when A=B=yes; use riBM.
                corr.append(row["riBM"]["corr"])
                unc.append(row["riBM"]["unc"])
            else:
                corr.append(row["A"]["corr"])
                unc.append(row["A"]["unc"])

        ax.bar(all_es, corr, width=0.7, color="tab:green", alpha=0.85, label="corrected")
        ax.bar(all_es, unc, width=0.7, bottom=corr, color="tab:red", alpha=0.7, label="uncorrectable")
        for e, c, u in zip(all_es, corr, unc):
            if c > 0:
                ax.text(e, c / 2, str(c), ha="center", va="center", fontsize=7, color="white")
            if u > 0:
                ax.text(e, c + u / 2, str(u), ha="center", va="center", fontsize=7, color="white")

        if t is not None:
            ax.axvline(t, color="black", linestyle="--", linewidth=1.0, label=f"e=t ({t})")
            ax.axvline(2 * t, color="gray", linestyle="--", linewidth=1.0, label=f"e=2t ({2 * t})")

        ax.set_title(f"{r['name']} ({r['codec']} t={t})")
        ax.set_xlabel("injected errors per block (e)")
        ax.set_ylabel("blocks")
        ax.set_xticks(all_es)
        ax.legend(loc="upper right", fontsize="small")
        ax.grid(True, axis="y", alpha=0.3)

    # Hide unused subplots.
    for ax in axes[n_images:]:
        ax.set_visible(False)

    fig.suptitle("correction boundary: corrected vs uncorrectable by injected error count", y=1.02)
    fig.tight_layout()
    fig.savefig(path, dpi=150, bbox_inches="tight")
    plt.close(fig)
    return path


def plot_decode_cost(records, out_dir):
    path = figure_path(out_dir, 2, "decode_cost")
    fig, ax = plt.subplots(figsize=(8, 5))
    has_data = False
    n_records = max(len(records), 1)
    colors = [plt.cm.tab10(idx / max(n_records - 1, 1)) for idx in range(n_records)]
    for idx, r in enumerate(records):
        if not r["sweep"]:
            continue
        has_data = True
        es = [row["e"] for row in r["sweep"]]
        cycs = [row["cyc/blk"] for row in r["sweep"]]
        t = r["params"].get("t")
        label = f"{r['name']} ({r['codec']} t={t})"
        ax.plot(es, cycs, marker="o", markersize=3, label=label, color=colors[idx])

    if has_data:
        ax.set_xlabel("injected errors per block (e)")
        ax.set_ylabel("cycles per block")
        ax.set_title("decode cost across the correction boundary")
        ax.legend(loc="best", fontsize="small")
        ax.grid(True, alpha=0.3)
    else:
        ax.text(0.5, 0.5, "no sweep data", ha="center", va="center", transform=ax.transAxes)
        ax.set_xticks([])
        ax.set_yticks([])

    save_or_close(fig, path, "Fig 2: decode cost")
    return path


def plot_soak_timeline(records, out_dir):
    path = figure_path(out_dir, 3, "soak_timeline")
    fig, ax = plt.subplots(figsize=(8, 5))
    has_data = False
    n_records = max(len(records), 1)
    colors = [plt.cm.tab10(idx / max(n_records - 1, 1)) for idx in range(n_records)]
    for idx, r in enumerate(records):
        if not r["soak_progress"]:
            continue
        has_data = True
        xs = [p["wall_s"] / 3600.0 for p in r["soak_progress"]]
        ys = [p["done"] for p in r["soak_progress"]]
        total = r["soak_progress"][0]["total"]
        label = f"{r['name']} ({'partial' if r['soak_final'] is None else 'complete'})"
        ax.plot(xs, ys, marker="", label=label, color=colors[idx])
        if total:
            ax.axhline(total, color=colors[idx], linestyle=":", alpha=0.4)

    if has_data:
        ax.set_xlabel("wall time (hours)")
        ax.set_ylabel("blocks completed")
        ax.set_title("soak progress")
        ax.legend(loc="best", fontsize="small")
        ax.grid(True, alpha=0.3)
    else:
        ax.text(0.5, 0.5, "no soak data", ha="center", va="center", transform=ax.transAxes)
        ax.set_xticks([])
        ax.set_yticks([])

    save_or_close(fig, path, "Fig 3: soak timeline")
    return path


def plot_injector_envelope(records, out_dir):
    path = figure_path(out_dir, 4, "injector_envelope")
    fig, ax = plt.subplots(figsize=(8, 5))

    campaigns = ["random", "clusters", "localized", "badblock"]
    images = []
    matrix = defaultdict(lambda: [0] * len(campaigns))
    for r in records:
        row = []
        for c in campaigns:
            if c == "random" and r["random"]:
                row.append(r["random"]["failing"])
            elif c in r["campaigns"]:
                row.append(r["campaigns"][c]["failing"])
            else:
                row.append(0)
        if any(v != 0 for v in row) or r["random"] or r["campaigns"]:
            images.append(r["name"])
            matrix[r["name"]] = row

    if images:
        data = [matrix[name] for name in images]
        x = list(range(len(campaigns)))
        width = 0.8 / len(images)
        for i, name in enumerate(images):
            offset = width * (i - (len(images) - 1) / 2)
            ax.bar([xi + offset for xi in x], data[i], width, label=name)
        ax.set_xticks(x)
        ax.set_xticklabels(campaigns)
        ax.set_ylabel("failing runs / combos")
        ax.set_title("injector envelope failures")
        ax.legend(loc="best", fontsize="small")
        ax.grid(True, axis="y", alpha=0.3)
    else:
        ax.text(0.5, 0.5, "no envelope data", ha="center", va="center", transform=ax.transAxes)
        ax.set_xticks([])
        ax.set_yticks([])

    save_or_close(fig, path, "Fig 4: injector envelope")
    return path


def plot_solver_agreement(records, out_dir):
    path = figure_path(out_dir, 5, "solver_agreement")
    fig, ax = plt.subplots(figsize=(8, 5))

    rs_records = [r for r in records if r["codec"] == "RS" and r["sweep"]]
    if len(rs_records) < 1:
        ax.text(0.5, 0.5, "no RS sweep data", ha="center", va="center", transform=ax.transAxes)
        ax.set_xticks([])
        ax.set_yticks([])
        save_or_close(fig, path, "Fig 5: solver agreement")
        return path

    # Build matrix: rows = images, cols = e values, cell = 1.0 if A=B yes else 0.0.
    all_es = sorted({row["e"] for r in rs_records for row in r["sweep"]})
    names = [r["name"] for r in rs_records]
    matrix = []
    for i, r in enumerate(rs_records):
        by_e = {row["e"]: row for row in r["sweep"]}
        row = []
        for j, e in enumerate(all_es):
            if e in by_e:
                row.append(1.0 if by_e[e]["A=B"].lower() == "yes" else 0.0)
            else:
                row.append(math.nan)
        matrix.append(row)

    im = ax.imshow(matrix, aspect="auto", cmap="RdYlGn", vmin=0, vmax=1)
    ax.set_xticks(list(range(len(all_es))))
    ax.set_xticklabels([str(e) for e in all_es])
    ax.set_yticks(list(range(len(names))))
    ax.set_yticklabels(names)
    ax.set_xlabel("injected errors per block (e)")
    ax.set_title("solver agreement (riBM vs Euclid): green = agree")
    fig.colorbar(im, ax=ax, label="agree")

    # Annotate cells.
    for i in range(len(names)):
        for j in range(len(all_es)):
            val = matrix[i][j]
            if not math.isnan(val):
                text = "Y" if val > 0.5 else "N"
                ax.text(j, i, text, ha="center", va="center", color="black", fontsize=7)

    save_or_close(fig, path, "Fig 5: solver agreement")
    return path


def render_figures(records, out_dir):
    paths = []
    paths.append(plot_correction_boundary(records, out_dir))
    paths.append(plot_decode_cost(records, out_dir))
    paths.append(plot_soak_timeline(records, out_dir))
    paths.append(plot_injector_envelope(records, out_dir))
    paths.append(plot_solver_agreement(records, out_dir))
    return paths


def format_status_badge(status):
    if status == "PASS":
        return "PASS"
    if status == "PARTIAL":
        return "PARTIAL"
    if status == "PROGRAM_FAILED":
        return "PROGRAM FAILED"
    if status == "FAIL":
        return "FAIL"
    return status


def render_findings(records, summary, meta, out_dir, figure_paths, superseded):
    md_path = os.path.join(out_dir, "FINDINGS.md")
    lines = [HEADER_BLOCK, f"# Battery Report — {meta['date']}", ""]
    lines.append(f"Board serial: `{meta['serial']}`  ")
    lines.append(f"Generated: {meta['generated']}  ")
    lines.append("")

    lines.append("## Summary")
    lines.append("")
    lines.append(f"- Images reported: **{summary['images']}**")
    lines.append(f"- Passed: **{summary['passed']}**")
    lines.append(f"- Failed: **{summary['failed']}**")
    lines.append(f"- Partial: **{summary['partial']}**")
    lines.append(f"- Program failed: **{summary['program_failed']}**")
    lines.append("")

    # Confidence statement across all soak campaigns that report threshold data.
    soak_finals = [r["soak_final"] for r in records if r.get("soak_final")]
    threshold_finals = [sf for sf in soak_finals if sf.get("over_t_blocks") is not None]
    if threshold_finals:
        total_blocks = sum(sf.get("blocks_final", 0) for sf in threshold_finals)
        total_over_t = sum(sf.get("over_t_blocks", 0) for sf in threshold_finals)
        total_misdecoded = sum(sf.get("misdecoded", 0) for sf in threshold_finals)
        if total_misdecoded > 0:
            lines.append(
                f"> Confidence: **{total_blocks:,}** blocks across the soak(s); "
                f"**{total_misdecoded:,}** mis-decodes (**{total_over_t:,}** blocks were "
                f"pushed past the correction limit)."
            )
        else:
            lines.append(
                f"> Confidence: **{total_blocks:,}** blocks across the soak(s); "
                f"**0** mis-decodes (**{total_over_t:,}** blocks were pushed past the "
                f"correction limit and every one was flagged)."
            )
        lines.append("")

    lines.append("| Image | Codec | Status | Solver | Sequences |")
    lines.append("|-------|-------|--------|--------|-----------|")
    for r in records:
        seqs = ", ".join(
            f"{k}={v['status']}" for k, v in sorted(r["sequences"].items())
        ) or "-"
        solver = r["solver"] or "-"
        codec = f"{r['codec']}({r['params'].get('n', '?')},{r['params'].get('k', '?')})" if r["codec"] else "-"
        lines.append(
            f"| {r['name']} | {codec} | {format_status_badge(r['status'])} | {solver} | {seqs} |"
        )
    lines.append("")

    lines.append("## Per-Image Findings")
    lines.append("")
    for r in records:
        lines.append(f"### {r['name']}")
        lines.append("")
        if r["program_failed"]:
            lines.append(f"Programming failed: {r['program_failed_reason'] or 'unknown'}")
            lines.append("")
            continue
        if r["params"]:
            p = r["params"]
            lines.append(f"Codec: {r['codec']}({p['n']},{p['k']}) t={p['t']} m={p['m']} {p['spb']} symbols/beat  ")
        if r["solver"]:
            lines.append(f"Solver/topology: {r['solver']}  ")
        lines.append(f"Overall status: **{format_status_badge(r['status'])}**  ")
        lines.append("")
        if r["smoke"]:
            lines.append("Smoke results:")
            lines.append("")
            lines.append("| Mode | cyc/blk | Status |")
            lines.append("|------|---------|--------|")
            for s in r["smoke"]:
                lines.append(f"| {s['label']} | {s['cyc/blk']:.1f} | {s['status']} |")
            lines.append("")
        if r["sweep"]:
            lines.append(f"Sweep: {len(r['sweep'])} error counts from e={r['sweep'][0]['e']} to e={r['sweep'][-1]['e']}.  ")
            fails = [row for row in r["sweep"] if row["status"] == "FAIL"]
            if fails:
                lines.append(f"Failing error counts: {', '.join(str(row['e']) for row in fails)}  ")
            lines.append("")
        if r["random"]:
            rd = r["random"]
            lines.append(
                f"Random campaign: {rd['runs']} runs x {rd['blocks']} blocks; "
                f"{rd['clean']} clean / {rd['corrected']} corrected / "
                f"{rd['uncorrectable']} uncorrectable; {rd['failing']} failing run(s).  "
            )
            lines.append("")
        for camp, data in sorted(r["campaigns"].items()):
            lines.append(
                f"{camp}: {data['combos']} combos x {data['blocks']} blocks; "
                f"{data['failing']} failing combo(s).  "
            )
            lines.append("")
        if r["soak_progress"]:
            last = r["soak_progress"][-1]
            lines.append(
                f"Soak progress: {last['done']} of {last['total']} blocks after "
                f"{last['wall_s']:.0f}s ({last['blk_s']:.0f} blk/s).  "
            )
            if r["soak_final"] is None:
                lines.append("Soak is **partial**; no final summary was present in the transcript.  ")
            lines.append("")
        if r["soak_final"]:
            sf = r["soak_final"]

            def _fmt(value, spec=""):
                if value is None:
                    return "—"
                if spec == "int":
                    return f"{value:,}"
                if spec == "float1":
                    return f"{value:.1f}"
                if spec == "float0":
                    return f"{value:.0f}"
                return str(value)

            lines.append("Soak final counters:")
            lines.append("")
            lines.append("| Metric | Value |")
            lines.append("|--------|-------|")
            lines.append(f"| blocks_final | {_fmt(sf.get('blocks_final'), 'int')} |")
            lines.append(f"| wall_s | {_fmt(sf.get('wall_s'), 'float0')} |")
            lines.append(f"| blk_per_s | {_fmt(sf.get('blk_per_s'), 'float1')} |")
            lines.append(f"| clean | {_fmt(sf.get('clean'), 'int')} |")
            lines.append(f"| corrected | {_fmt(sf.get('corrected'), 'int')} |")
            lines.append(f"| uncorrectable | {_fmt(sf.get('uncorrectable'), 'int')} |")
            lines.append(f"| bits_corrected | {_fmt(sf.get('bits_corrected'), 'int')} |")
            lines.append(f"| failing_runs | {_fmt(sf.get('failing_runs'), 'int')} |")
            lines.append(f"| over_t_blocks | {_fmt(sf.get('over_t_blocks'), 'int')} |")
            lines.append(f"| misdecoded | {_fmt(sf.get('misdecoded'), 'int')} |")
            lines.append(f"| misdecode_rate | {_fmt(sf.get('misdecode_rate'))} |")
            lines.append("")
        if r["errors"]:
            lines.append("Errors/exceptions seen in transcript:")
            lines.append("")
            for err in r["errors"]:
                lines.append(f"- `{err}`")
            lines.append("")

    lines.append("## Figures")
    lines.append("")
    for p in figure_paths:
        fname = os.path.basename(p)
        lines.append(f"![{fname}]({fname})")
        lines.append("")

    lines.append("## Limits")
    lines.append("")
    partial = [r for r in records if r["status"] == "PARTIAL"]
    has_soak = any(r["soak_progress"] or r["soak_final"] for r in records)
    has_sweep = any(r["sweep"] for r in records)
    notes = []
    if partial:
        notes.append(
            "Partial soak logs are reported from the last progress line only; "
            "final tallies and miscorrect-rate are unavailable."
        )
    if not has_soak:
        notes.append("No soak campaign data was present in the transcripts.")
    if not has_sweep:
        notes.append("No sweep data was present in the transcripts.")
    if notes:
        for n in notes:
            lines.append(f"- {n}")
    if superseded:
        lines.append(
            "- Transcript sections that never reached the codec, or were superseded "
            "by a richer section from another transcript, were kept out of the figures:"
        )
        for s in superseded:
            lines.append(f"  - `{s['image']}` from `{s['log_file']}` — {s['reason']}")
    if not notes and not superseded:
        lines.append("- None noted.")
    lines.append("")

    with open(md_path, "w", encoding="utf-8") as f:
        f.write("\n".join(lines))
    return md_path


def main(argv=None):
    args = parse_args(argv)
    out_dir = args.out
    os.makedirs(out_dir, exist_ok=True)

    records = load_records(args.log_groups)
    records, superseded = deduplicate_records(records)
    summary = build_summary(records)

    meta = {
        "serial": args.serial,
        "date": args.date,
        "generated": datetime.now(timezone.utc).strftime("%Y-%m-%dT%H:%M:%SZ"),
        "repo": "https://github.com/sean-galloway/RTLDesignSherpa",
    }

    figure_paths = render_figures(records, out_dir)

    payload = {
        "meta": meta,
        "summary": summary,
        "images": records,
        "superseded": superseded,
    }
    json_path = os.path.join(out_dir, "battery.json")
    with open(json_path, "w", encoding="utf-8") as f:
        json.dump(payload, f, indent=2)

    md_path = render_findings(records, summary, meta, out_dir, figure_paths, superseded)

    print(f"Wrote {json_path}")
    for p in figure_paths:
        print(f"Wrote {p}")
    print(f"Wrote {md_path}")


if __name__ == "__main__":
    main()
