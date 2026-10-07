#!/usr/bin/env python3
"""All measured tables of the RAPIDS perf report (reports/perf/README.md) from one campaign set.
usage: report_tables.py <json dir> <file prefix>     e.g. reports/perf/json genesys_dw256_   (v1.x files: genesys_)
Files: {prefix}full_matrix.json, {prefix}obs_{A,B,C,E}.json, {prefix}obs_E_interleave.json,
       {prefix}one_channel_xfer_latency.json (optional)"""
import json, os, sys
D, P = sys.argv[1].rstrip("/") + "/", sys.argv[2]
def load(k):
    p = f"{D}{P}{k}.json"
    return json.load(open(p)) if os.path.exists(p) else None
def cfgs(k):
    d = load(k); return d["configs"] if d else []
M = load("full_matrix"); design = (M or {}).get("design") or {}
BB = design.get("beat_bytes", 64); PEAK = BB * 100e6 / 1e9
def kb(beats): b = beats * BB; return f"{b} B" if b < 1024 else f"{b // 1024} KB"
def meter(c, path, iface): return c[path]["perf"]["ifaces"][iface]
def mu(c, p, i): return "%.1f %%" % (100 * meter(c, p, i)["util"])
def mbw(c, p, i): return "%.2f" % (meter(c, p, i)["eff_bw_gb_s"])
def ob(c, path, iface): return c[path]["perf"]["observers"][iface]
def pct(c, p, i): return "%.1f %%" % (100 * ob(c, p, i)["util"])
def bw(c, p, i): return "%.2f" % ob(c, p, i)["eff_bw_gb_s"]
def lat(c, p, i, k): return "%.0f" % ob(c, p, i)["latency"][k]["mean_cyc"]
def row4(c): return [pct(c, "sink", "sin"), pct(c, "sink", "wr"), pct(c, "source", "rd"), pct(c, "source", "sout")]
print(f"design: {design or '(none recorded: 512-bit / 64 B assumed)'}  beat {BB} B, line rate {PEAK:.2f} GB/s\n")
if M:
    mc = M["configs"]; big = max(c["beats"] for c in mc); nch = max(c["active_channels"] for c in mc)
    c = next(x for x in mc if x["beats"] == big and x["active_channels"] == nch)
    print(f"### 1. Headline ({nch} ch x {kb(big)}/ch)")
    print("| Path | Interface | Engaged util | Effective BW | Window (prod / starv) |\n|------|-----------|-------------:|-------------:|-----------------------|")
    for path, iface, name in (("sink","sin","AXIS-in (ingress)"),("sink","wr","AXI4-wr (egress)"),("source","rd","AXI4-rd (ingress)"),("source","sout","AXIS-out (egress)")):
        m = meter(c, path, iface); b = m["buckets"]
        print(f"| {path.upper():6s} | {name:18s} | **{100*m['util']:.1f} %** | {m['eff_bw_gb_s']:.2f} GB/s | {b['prod']} / {b['starv']} |")
    print(f"\n### 3. size sweep at {nch} ch (bare meters)")
    print("| Transfer | AXIS-in | AXI4-wr | AXI4-rd | AXIS-out | wr GB/s | rd GB/s |\n|---|---:|---:|---:|---:|---:|---:|")
    for c in sorted((x for x in mc if x["active_channels"] == nch), key=lambda x: x["beats"]):
        print(f"| {kb(c['beats'])} ({c['beats']} b) | {mu(c,'sink','sin')} | {mu(c,'sink','wr')} | {mu(c,'source','rd')} | {mu(c,'source','sout')} | {mbw(c,'sink','wr')} | {mbw(c,'source','rd')} |")
    print(f"\n### 3.1 channel count at {kb(big)}/ch (bare meters)")
    print("| Channels | AXIS-in | AXI4-wr | AXI4-rd | AXIS-out |\n|---:|---:|---:|---:|---:|")
    for c in sorted((x for x in mc if x["beats"] == big), key=lambda x: x["active_channels"]):
        print(f"| {c['active_channels']} | {mu(c,'sink','sin')} | {mu(c,'sink','wr')} | {mu(c,'source','rd')} | {mu(c,'source','sout')} |")
    print(f"pass: {sum(x['pass'] for x in mc)}/{len(mc)}")
C = cfgs("obs_C")
if C:
    big = max(c["beats"] for c in C)
    print(f"\n### 7.1 (from C at {kb(big)}/ch)")
    print("| Channels | AXIS-in | AXI4-wr | AXI4-rd | AXIS-out | wr GB/s | rd GB/s | AXIS-in byte GB/s | AXIS-out byte GB/s |\n|---:|---:|---:|---:|---:|---:|---:|---:|---:|")
    for c in sorted((x for x in C if x["beats"] == big), key=lambda x: x["active_channels"]):
        print(f"| {c['active_channels']} | " + " | ".join(row4(c)) + f" | {bw(c,'sink','wr')} | {bw(c,'source','rd')} | {ob(c,'sink','sin').get('byte_bw_gb_s',0):.2f} | {ob(c,'source','sout').get('byte_bw_gb_s',0):.2f} |")
    print("\n### 7.2 (from C at 8 ch)")
    print("| beats/ch | AXIS-in | AXI4-wr | AXI4-rd | AXIS-out | wr GB/s | rd GB/s | rd bursts | AR->RLAST | AW->B |\n|---:|---:|---:|---:|---:|---:|---:|---:|---:|---:|")
    for c in sorted((x for x in C if x["active_channels"] == 8), key=lambda x: x["beats"]):
        print(f"| {c['beats']} | " + " | ".join(row4(c)) + f" | {bw(c,'sink','wr')} | {bw(c,'source','rd')} | {ob(c,'source','rd')['buckets']['bursts']} | {lat(c,'source','rd','ar_rlast')} | {lat(c,'sink','wr','aw_b')} |")
    print(f"pass: {sum(x['pass'] for x in C)}/{len(C)}")
A = cfgs("obs_A")
if A:
    print("\n### 7.3 (A)")
    print("| descs/ch | 1 ch wr / sout | 2 ch | 4 ch | 8 ch |\n|---:|---:|---:|---:|---:|")
    for d in sorted({x["descs"] for x in A}):
        cells = []
        for ch in (1, 2, 4, 8):
            c = next(x for x in A if x["descs"] == d and x["active_channels"] == ch)
            cells.append("%.1f / %.1f %%" % (100 * ob(c, "sink", "wr")["util"], 100 * ob(c, "source", "sout")["util"]))
        print(f"| {d} | " + " | ".join(cells) + " |")
    print(f"pass: {sum(x['pass'] for x in A)}/{len(A)}")
B = cfgs("obs_B")
if B:
    print("\n### 7.4 (B)")
    print("| beats/burst | AXIS-in | AXI4-wr | AXI4-rd | AXIS-out | AR->RLAST | AW->B |\n|---:|---:|---:|---:|---:|---:|---:|")
    for c in sorted(B, key=lambda x: x["xfer_beats"]):
        print(f"| {c['xfer_beats']} | " + " | ".join(row4(c)) + f" | {lat(c,'source','rd','ar_rlast')} | {lat(c,'sink','wr','aw_b')} |")
    print(f"pass: {sum(x['pass'] for x in B)}/{len(B)}")
for k, title in (("obs_E", "7.5 (E, sequential)"), ("obs_E_interleave", "7.5b (E, interleaved)")):
    E = cfgs(k)
    if not E: continue
    print(f"\n### {title}")
    print("| delay (cyc) | AXIS-in | AXI4-wr | AXI4-rd | AXIS-out | rd GB/s | wr GB/s | AR->first R | AR->RLAST | AW->B |\n|---:|---:|---:|---:|---:|---:|---:|---:|---:|---:|")
    for c in sorted(E, key=lambda x: x["resp_delay"]):
        print(f"| {c['resp_delay']} | " + " | ".join(row4(c)) + f" | {bw(c,'source','rd')} | {bw(c,'sink','wr')} | {lat(c,'source','rd','ar_first_r')} | {lat(c,'source','rd','ar_rlast')} | {lat(c,'sink','wr','aw_b')} |")
    st = sorted({(kk, v) for x in E for p in ("sink","source") for kk, v in x[p]["perf"].get("observer_sticky", {}).items() if v})
    print(f"pass: {sum(x['pass'] for x in E)}/{len(E)}  sticky: {st or 'none'}")
K = cfgs("one_channel_xfer_latency")
if K:
    print("\n### knobs (1 ch, bare meters): burst | wr/rd at each delay")
    ds = sorted({c["resp_delay"] for c in K})
    print("| burst (beats) | " + " | ".join(f"{d} cyc" for d in ds) + " |\n|---:|" + "---|" * len(ds))
    for x in sorted({c["xfer_beats"] for c in K}):
        cells = []
        for d in ds:
            c = next((c for c in K if c["xfer_beats"] == x and c["resp_delay"] == d), None)
            cells.append((f"{100*meter(c,'sink','wr')['util']:.1f} / {100*meter(c,'source','rd')['util']:.1f}" + ("" if c["pass"] else " FAIL")) if c else "--")
        print(f"| {x} | " + " | ".join(cells) + " |")
    print(f"pass: {sum(x['pass'] for x in K)}/{len(K)}")
