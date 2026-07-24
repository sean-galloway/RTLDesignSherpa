---
title: Timing triage tool
summary: bin/vivado_timing_failures.py - bucketize failing endpoints.
---

# bin/vivado_timing_failures.py

Parses a Vivado timing report and buckets failing endpoints by
start/end cone so one RTL cause shows as one bucket instead of thousands
of endpoint lines (the -120 ns run was 6,036 failing endpoints = ONE
pick_oldest cone).

Use after route (or a failed place) when the failure count is large:
generate the full report first
(`report_timing_summary` / `report_timing -max_paths N -file`), run the
script on it, then attack buckets largest-first. Read the script header
for current CLI flags - it is the source of truth, this note is the
pointer ([[timing-closure]] for where it sits in the triage order).
