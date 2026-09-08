#!/usr/bin/env python3
"""ABC stime sweep for the 11 STREAM library rows.

For each (row, freq, corner) entry:
  - Generate a yosys script that reads RTL via slang, runs synth + dfflibmap +
    abc with an explicit script that ends in `stime -c; print_stats -m`.
  - Parse Delay (ps), levels, gate/ff counts, area from the log.
  - Validate every result; mark row ERROR if any sanity check fails.
  - Append to assets/timings.csv incrementally so we never lose state.

Deep memories: rows that declare `char_depth_override` are synthesized at the
override depth (control + read-mux timing scales weakly with depth above a
threshold, so we characterize with a tractable depth and report
storage_bits = actual_depth * DATA_WIDTH separately).

Run with `source ~/eda/OpenROAD-flow-scripts/env.sh` first to get bundled yosys
(0.64 + slang).
"""
from __future__ import annotations
import csv
import os
import re
import subprocess
import sys
import time
from dataclasses import dataclass, field
from pathlib import Path

# ---------------------------------------------------------------------------- #
# Paths
# ---------------------------------------------------------------------------- #
ROOT = Path("/mnt/data/github/RTLDesignSherpa/rtl")
RTL = {
    "gaxi_skid_buffer":         ROOT / "amba/gaxi/gaxi_skid_buffer.sv",
    "gaxi_fifo_sync":           ROOT / "amba/gaxi/gaxi_fifo_sync.sv",
    "counter_bin":              ROOT / "common/counter_bin.sv",
    "fifo_control":             ROOT / "common/fifo_control.sv",
    "arbiter_round_robin":      ROOT / "common/arbiter_round_robin.sv",
    "arbiter_priority_encoder": ROOT / "common/arbiter_priority_encoder.sv",
    "axi4_master_rd":           ROOT / "amba/axi4/axi4_master_rd.sv",
    "axi4_master_wr":           ROOT / "amba/axi4/axi4_master_wr.sv",
}
INCLUDES = ROOT / "amba/includes"

# Per-top dependency closure
DEPS = {
    "gaxi_skid_buffer":     ["gaxi_skid_buffer"],
    "gaxi_fifo_sync":       ["gaxi_fifo_sync", "counter_bin", "fifo_control"],
    "arbiter_round_robin":  ["arbiter_round_robin", "arbiter_priority_encoder"],
    "axi4_master_rd":       ["axi4_master_rd", "gaxi_skid_buffer"],
    "axi4_master_wr":       ["axi4_master_wr", "gaxi_skid_buffer"],
}

LIB_DIR = Path.home() / "eda/asap7_merged"
LIB = {c: LIB_DIR / f"asap7sc7p5t_RVT_{c}_nldm.lib" for c in ("TT", "FF", "SS")}

# ---------------------------------------------------------------------------- #
# Rows
# ---------------------------------------------------------------------------- #
# CHAR_DEPTH_LIMIT: above this DEPTH, synthesize at a smaller representative
# depth to keep synthesis tractable. Read-mux and control timing scale as
# clog2(DEPTH) so a representative D=32..64 covers the bulk of the timing arc.
CHAR_DEPTH_LIMIT = 64

@dataclass
class Row:
    label: str
    top: str
    params: dict
    notes: str = ""

ROWS: list[Row] = [
    Row("gaxi_skid_buffer_W64_D2", "gaxi_skid_buffer",
        {"DATA_WIDTH": 64, "DEPTH": 2}),

    Row("gaxi_fifo_W36_D512",   "gaxi_fifo_sync",
        {"DATA_WIDTH": 36, "DEPTH": 512}),
    Row("gaxi_fifo_W64_D2",     "gaxi_fifo_sync",
        {"DATA_WIDTH": 64, "DEPTH": 2}),
    Row("gaxi_fifo_W261_D512",  "gaxi_fifo_sync",
        {"DATA_WIDTH": 261, "DEPTH": 512}),
    Row("gaxi_fifo_W64_D64",    "gaxi_fifo_sync",
        {"DATA_WIDTH": 64, "DEPTH": 64}),
    Row("gaxi_fifo_W9_D16",     "gaxi_fifo_sync",
        {"DATA_WIDTH": 9, "DEPTH": 16}),
    # fifo_mem_t: FIFO_AUTO=0, FIFO_SRL=1, FIFO_BRAM=2 (from fifo_defs.svh)
    Row("gaxi_fifo_W512_D4096_BRAM_REG1", "gaxi_fifo_sync",
        {"DATA_WIDTH": 512, "DEPTH": 4096, "MEM_STYLE": 2, "REGISTERED": 1},
        notes="MEM_STYLE=FIFO_BRAM"),
    Row("gaxi_fifo_W512_D4_AUTO_REG0",    "gaxi_fifo_sync",
        {"DATA_WIDTH": 512, "DEPTH": 4, "MEM_STYLE": 0, "REGISTERED": 0},
        notes="MEM_STYLE=FIFO_AUTO"),

    Row("arbiter_round_robin_N8", "arbiter_round_robin",
        {"CLIENTS": 8, "WAIT_GNT_ACK": 1}),

    Row("axi4_master_rd_AW64_DW512", "axi4_master_rd",
        {"AXI_ADDR_WIDTH": 64, "AXI_DATA_WIDTH": 512, "AXI_ID_WIDTH": 8,
         "AXI_USER_WIDTH": 1, "SKID_DEPTH_AR": 2, "SKID_DEPTH_R": 4}),
    Row("axi4_master_wr_AW64_DW512", "axi4_master_wr",
        {"AXI_ADDR_WIDTH": 64, "AXI_DATA_WIDTH": 512, "AXI_ID_WIDTH": 8,
         "AXI_USER_WIDTH": 1, "SKID_DEPTH_AW": 2, "SKID_DEPTH_W": 4, "SKID_DEPTH_B": 2}),
]

FREQS_MHZ = [500, 750, 1000]
CORNERS   = ["TT", "FF", "SS"]

OUTDIR = Path("/tmp/charwork/asap7/sweep")
OUTDIR.mkdir(parents=True, exist_ok=True)
CSV_OUT = Path(__file__).resolve().parent / "timings.csv"

# ---------------------------------------------------------------------------- #
# Depth handling: characterize at representative depth above CHAR_DEPTH_LIMIT
# ---------------------------------------------------------------------------- #
def resolved_params(row: Row) -> tuple[dict, dict]:
    """Return (synth_params, notes_meta). synth_params is what we actually pass to
    yosys; notes_meta carries actual_depth, char_depth, storage_bits for CSV."""
    sp = dict(row.params)
    meta = {"actual_depth": sp.get("DEPTH", 0),
            "char_depth":   sp.get("DEPTH", 0),
            "storage_bits": sp.get("DEPTH", 0) * sp.get("DATA_WIDTH", 0),
            "notes":        row.notes}
    actual_d = sp.get("DEPTH", 0)
    if actual_d > CHAR_DEPTH_LIMIT:
        sp["DEPTH"] = CHAR_DEPTH_LIMIT
        meta["char_depth"] = CHAR_DEPTH_LIMIT
        extra = f"D={actual_d}->char@{CHAR_DEPTH_LIMIT}; storage_bits={meta['storage_bits']}"
        meta["notes"] = (row.notes + " | " if row.notes else "") + extra
    return sp, meta

# ---------------------------------------------------------------------------- #
# Yosys script builder
# ---------------------------------------------------------------------------- #
def fmt_param(v):
    return str(v)

def build_ys(row: Row, sp: dict, corner: str, period_ps: int, work: Path) -> Path:
    lib = LIB[corner]
    deps = " \\\n        ".join(str(RTL[d]) for d in DEPS[row.top])
    gparams = " ".join(f"-G {k}={fmt_param(v)}" for k, v in sp.items())
    netlist = work / "netlist.v"
    stat    = work / "stat.txt"
    ys_path = work / "synth.ys"

    # yosys's default ABC pass already runs scorr/dc2/dch upstream of us;
    # our job is just to (re-)map with timing constraints, buffer wide
    # fanouts, and emit `stime` + `print_stats -m` for the parser to read.
    abc_script = work / "abc.script"
    abc_script.write_text(
        f"strash\n"
        f"map -p -B 0.2 -A 0.9\n"
        f"buffer -c -N 6\n"
        f"topo\n"
        f"upsize -c\n"
        f"dnsize -c\n"
        f"stime -c\n"
        f"print_stats -m\n"
    )
    ys = f"""\
plugin -i slang
read_slang -DUSE_ASYNC_RESET -I {INCLUDES} \\
    --top {row.top} {gparams} \\
        {deps}
async2sync
read_liberty -lib {lib}
synth -top {row.top} -flatten
dfflibmap -liberty {lib} \\
    -dont_use DFFASRHQN* -dont_use DFFHQN* -dont_use DFFLQN* \\
    -dont_use SDFL* -dont_use DFFLQ*
abc -liberty {lib} -script {abc_script}
opt_clean -purge
tee -o {stat} stat -liberty {lib}
write_verilog -noattr {netlist}
"""
    ys_path.write_text(ys)
    return ys_path

# ---------------------------------------------------------------------------- #
# Parsers
# ---------------------------------------------------------------------------- #
NUM = r"(?:[0-9]+(?:\.[0-9]*)?|\.[0-9]+)(?:[eE][+-]?[0-9]+)?"

ABC_DELAY_RE = re.compile(rf"Delay\s*=\s*({NUM})\s*ps")
ABC_LEV_RE   = re.compile(r"\blev\s*=\s*(\d+)")

# yosys stat lines (DATA_WIDTH=N -> wires, cells, area)
STAT_HEADER_RE = re.compile(rf"^\s*(\d+)\s+({NUM})\s+cells\s*$", re.MULTILINE)
STAT_CELL_RE   = re.compile(rf"^\s+(\d+)\s+({NUM})\s+([A-Za-z][A-Za-z0-9_]+)\s*$", re.MULTILINE)
STAT_AREA_RE   = re.compile(rf"Chip area for module '\\\w+':\s*({NUM})")
STAT_SEQ_RE    = re.compile(rf"of which used for sequential elements:\s*({NUM})")

def parse_abc(log_text: str) -> tuple[float | None, int | None]:
    delay, lev = None, None
    for line in log_text.splitlines():
        m = ABC_DELAY_RE.search(line)
        if m:
            delay = float(m.group(1))
        m = ABC_LEV_RE.search(line)
        if m:
            lev = int(m.group(1))
    return delay, lev

def parse_stat(stat_text: str) -> dict:
    """Return totals + per-DFF counts. All numeric fields tolerate scientific."""
    m_header = STAT_HEADER_RE.search(stat_text)
    total_cells = int(m_header.group(1)) if m_header else 0
    total_area  = float(m_header.group(2)) if m_header else 0.0
    m_area = STAT_AREA_RE.search(stat_text)
    chip_area = float(m_area.group(1)) if m_area else total_area
    m_seq = STAT_SEQ_RE.search(stat_text)
    seq_area = float(m_seq.group(1)) if m_seq else 0.0
    ff_count = 0
    for cnt, _area, name in STAT_CELL_RE.findall(stat_text):
        if name.startswith("DFF"):
            ff_count += int(cnt)
    return {
        "gate_count": total_cells,
        "ff_count":   ff_count,
        "area_um2":   chip_area,
        "seq_area_um2": seq_area,
    }

# ---------------------------------------------------------------------------- #
# Run one entry
# ---------------------------------------------------------------------------- #
def validate(res: dict) -> str | None:
    """Return error string if result is invalid, else None."""
    if res.get("delay_ps") is None: return "missing Delay from ABC"
    if res.get("levels")   is None: return "missing lev from ABC"
    if res.get("gate_count", 0) <= 0: return "stat reported gate_count=0"
    if res.get("area_um2", 0) <= 0:   return "stat reported area=0"
    return None

def run_one(row: Row, sp: dict, meta: dict, corner: str, freq_mhz: int) -> dict:
    period_ps = int(round(1_000_000 / freq_mhz))
    tag = f"{row.label}__{corner}__{freq_mhz}MHz"
    work = OUTDIR / tag
    work.mkdir(parents=True, exist_ok=True)
    ys = build_ys(row, sp, corner, period_ps, work)
    log = work / "yosys.log"
    cmd = ["yosys", "-ql", str(log), str(ys)]
    t0 = time.time()
    r = subprocess.run(cmd, capture_output=True, text=True, cwd=work,
                       timeout=900)  # 15 min max per row
    dt = time.time() - t0
    log_text = log.read_text() if log.exists() else ""
    base = {
        "row": row.label, "corner": corner, "freq_mhz": freq_mhz,
        "period_target_ps": period_ps,
        "actual_depth": meta["actual_depth"],
        "char_depth":   meta["char_depth"],
        "storage_bits": meta["storage_bits"],
        "elapsed_s": round(dt, 1),
        "notes": meta["notes"],
    }
    if r.returncode != 0:
        base.update({"status": "FAIL", "error": (r.stderr[:300] or log_text[-300:])})
        return base
    delay, lev = parse_abc(log_text)
    stat_path = work / "stat.txt"
    stat = parse_stat(stat_path.read_text()) if stat_path.exists() else {}
    base.update({
        "delay_ps": delay, "levels": lev, **stat,
        "slack_ps": (period_ps - delay) if delay else None,
        "fmax_mhz": round(1_000_000 / delay, 1) if delay else None,
    })
    err = validate(base)
    base["status"] = "OK" if err is None else "BAD"
    if err:
        base["error"] = err
    return base

# ---------------------------------------------------------------------------- #
# Driver
# ---------------------------------------------------------------------------- #
COLS = ["row", "corner", "freq_mhz", "period_target_ps", "status",
        "delay_ps", "levels", "slack_ps", "fmax_mhz",
        "gate_count", "ff_count", "area_um2", "seq_area_um2",
        "actual_depth", "char_depth", "storage_bits",
        "elapsed_s", "notes", "error"]

def main():
    only_rows = set(filter(None, os.environ.get("ONLY_ROWS", "").split()))
    only_corners = set(filter(None, os.environ.get("ONLY_CORNERS", "").split()))
    only_freqs = set(filter(None, os.environ.get("ONLY_FREQS", "").split()))

    runs = []
    for row in ROWS:
        if only_rows and row.label not in only_rows:
            continue
        for corner in CORNERS:
            if only_corners and corner not in only_corners:
                continue
            for f in FREQS_MHZ:
                if only_freqs and str(f) not in only_freqs:
                    continue
                runs.append((row, corner, f))

    total = len(runs)
    print(f"[abc_sweep] {total} runs", file=sys.stderr)
    results = []
    t0 = time.time()
    for i, (row, corner, freq) in enumerate(runs, 1):
        sp, meta = resolved_params(row)
        print(f"[{i:3d}/{total}] {row.label}  {corner}  {freq}MHz ... ",
              end="", file=sys.stderr, flush=True)
        try:
            res = run_one(row, sp, meta, corner, freq)
        except subprocess.TimeoutExpired:
            res = {"row": row.label, "corner": corner, "freq_mhz": freq,
                   "period_target_ps": int(round(1_000_000/freq)),
                   "actual_depth": meta["actual_depth"], "char_depth": meta["char_depth"],
                   "storage_bits": meta["storage_bits"],
                   "status": "TIMEOUT", "error": "yosys >15min",
                   "elapsed_s": 900.0, "notes": meta["notes"]}
        results.append(res)
        if res["status"] == "OK":
            print(f"delay={res['delay_ps']:.1f}ps lev={res['levels']} "
                  f"gates={res['gate_count']} ffs={res['ff_count']} "
                  f"area={res['area_um2']:.2f}um2  ({res['elapsed_s']}s)",
                  file=sys.stderr)
        else:
            print(f"{res['status']}  ({res['elapsed_s']}s)  {res.get('error','')[:120]}",
                  file=sys.stderr)
        write_csv(results)

    n_ok = sum(1 for r in results if r["status"] == "OK")
    n_bad = sum(1 for r in results if r["status"] != "OK")
    print(f"[abc_sweep] done in {time.time()-t0:.1f}s  ok={n_ok}  bad={n_bad}  -> {CSV_OUT}",
          file=sys.stderr)
    return 0 if n_bad == 0 else 1

def write_csv(results):
    if not results:
        return
    with CSV_OUT.open("w", newline="") as f:
        w = csv.DictWriter(f, fieldnames=COLS, extrasaction="ignore")
        w.writeheader()
        for r in results:
            w.writerow(r)

if __name__ == "__main__":
    sys.exit(main())
