#!/usr/bin/env python3
"""Render every figure of reports/perf/README.md from one campaign set.
usage: report_figures.py <json dir> <file prefix> <outdir> <figure name prefix>
  e.g. report_figures.py reports/perf/json genesys_dw256_ reports/perf/plots dw256_
The plotting itself is plot_char_reports.py (same directory); this only routes each
campaign file to the figures it feeds."""
import sys, os, importlib.util
D, P, OUT, NP = sys.argv[1].rstrip("/") + "/", sys.argv[2], sys.argv[3], sys.argv[4]
spec = importlib.util.spec_from_file_location("pcr", os.path.join(os.path.dirname(os.path.abspath(__file__)), "plot_char_reports.py"))
pcr = importlib.util.module_from_spec(spec); spec.loader.exec_module(pcr)
def cfgs(k):
    p = f"{D}{P}{k}.json"
    return pcr.load(p).get("configs", []) if os.path.exists(p) else []
m = cfgs("full_matrix")
if m:
    nch = pcr._max_channels(m); s = pcr._series(m, channels=nch)
    pcr.size_util(s, OUT, f"{NP}size_util.png"); pcr.size_bw(s, OUT, f"{NP}size_bw.png")
    pcr.headline_bar([c for c in m if c.get("active_channels") == nch], OUT, f"{NP}headline_8ch.png")
    pcr.size_buckets([c for c in m if c.get("active_channels") == nch], OUT, f"{NP}size_buckets.png")
    pcr.channel_scaling(m, OUT, f"{NP}channel_scaling.png")
c = cfgs("obs_C")
if c and pcr._has_observers(c):
    nch = pcr._max_channels(c); os_ = pcr._obs_series(c, channels=nch); ms = pcr._series(c, channels=nch)
    pcr.obs_size_util(os_, ms, OUT, f"{NP}obs_size_util.png"); pcr.obs_size_bw(os_, OUT, f"{NP}obs_size_bw.png")
    pcr.obs_latency(c, nch, OUT, f"{NP}obs_latency.png"); pcr.obs_channel_scaling(c, OUT, f"{NP}obs_channel_scaling.png")
a = cfgs("obs_A");  a and pcr.obs_desc_matrix(a, OUT, f"{NP}obs_desc_matrix.png")
b = cfgs("obs_B");  b and pcr.obs_xfer_knee(b, OUT, f"{NP}obs_xfer_knee.png")
e = cfgs("obs_E");  e and pcr.obs_latency_knee(e, OUT, f"{NP}obs_latency_knee.png")
ei = cfgs("obs_E_interleave"); ei and pcr.obs_latency_knee(ei, OUT, f"{NP}obs_latency_knee_interleave.png")
print("done")
