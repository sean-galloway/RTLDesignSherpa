#!/usr/bin/env python3
# SPDX-License-Identifier: MIT
# SPDX-FileCopyrightText: 2026 sean galloway
"""Monitor packet-coverage SCENARIO MATRIX on the board (build-mon).

Drives a MATRIX of scenarios that each try to provoke a different monbus packet
class from the in-core monitors, and reads them back out of the CAM-always
dense tally. The legal-set CAM is loaded with a COMPREHENSIVE CANDIDATE SET
(rd/wr datapath agents x every packet type x its real event codes) -- so which
tuples actually fire is DISCOVERED per scenario, not guessed. Anything the
monitors emit that is not in the candidate set lands in the single UNEXPECTED
bin (flagged loudly).

Every scenario is ONE call to the board's program, CharacterizationRunner
.run_config(): reset_stream -> load_descriptors -> configure_stream (which
applies the scenario's MonitorProgram) -> pre_kick (routing, ranges, timeouts,
the CAM) -> kick -> poll -> CRC. That is the sequence the obs campaign proved
at volume and the cosim runs; the hand-rolled reset/configure/kick this file
used to carry was a second copy of it, and its monitor writes landed BEFORE
the reset that clears them.

Scenarios:
  basic         plain 2-desc DMA                 -> AddrMatch + completion
  single_beat   1-beat bursts (many txns)        -> more AddrMatch/completion
  multi_channel 4 channels                        -> per-channel traffic
  timeout       low TIMEOUT ticks + resp delay    -> TIMEOUT
  threshold     low LATENCY_THRESH + resp delay   -> THRESHOLD
  perf          small PERF window + RUN           -> PERF
  addr_error    range2 allowlist miss             -> ERROR/ADDR_RANGE

Usage:
    source env_python
    python3 host/host_mon_matrix.py                 # one pass of every scenario
    python3 host/host_mon_matrix.py --reps 5        # 5 reps each (accumulate)
    python3 host/host_mon_matrix.py --only timeout,threshold --port /dev/ttyUSB1
"""
import argparse
import os
import sys
import time

_here = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, os.path.abspath(os.path.join(_here, "..", "..", "bin")))
import stream_env  # noqa: F401,E402  (import side effect: sys.path setup)
from harness_addrs import H, autodetect_port, compose, describe_build  # noqa: E402
from characterization import CharacterizationRunner, CharConfig  # noqa: E402
from stream_monitors import (MonitorProgram, route_monbus, arm_addr_ranges,  # noqa: E402
                             set_timeouts, run_perf_windows, DATAPATH_MONITORS,
                             PKT_ERROR, PKT_COMPL, PKT_THRESHOLD, PKT_TIMEOUT,
                             PKT_PERF, PKT_ADDRMATCH, PKT_PERFWIN, PKT_PERFHIST)
import tally  # noqa: E402

MON_N_PROFILE = 32   # tally CAM depth as built; the hardware value overrides


# ----------------------------------------------------------------------------
# Candidate legal set: rd(9)/wr(10) AXI datapath x each packet type x its real
# event codes (monbus_types). Capped at N_PROFILE. Dense bin = position here.
# ----------------------------------------------------------------------------
def gen_candidates():
    c = []
    for ag, who in ((9, "rd"), (10, "wr")):
        c.append((ag, 0, 0x8, 0x01, f"{who}_addrmatch"))                 # AddrMatch
        for ev, nm in ((0x0, "trans"), (0x1, "read"), (0x2, "write"), (0x3, "burst")):
            c.append((ag, 0, 0x1, ev, f"{who}_compl_{nm}"))              # Completion
        # Perf rollup (reporter_perf): event 0x7=COMPLETED_COUNT, 0x8=ERROR_COUNT.
        c.append((ag, 0, 0x4, 0x7, f"{who}_perf_compl"))                 # Perf
        c.append((ag, 0, 0x4, 0x8, f"{who}_perf_err"))                   # Perf
        # PerfWin (0xD) / PerfHist (0xE) are NOT keyed. They are CSR-only: the
        # packet types exist in the packages but nothing in the RTL ever emits
        # them, so keying them burned 4 of the CAM's entries on tuples that can
        # never match. Dropping them takes the set to exactly 32.
        for ev, nm in ((0x0, "slverr"), (0x1, "decerr"), (0xD, "addrrange")):
            c.append((ag, 0, 0x0, ev, f"{who}_err_{nm}"))                # Error
        for ev, nm in ((0x0, "cmd"), (0x1, "data"), (0x2, "resp")):
            c.append((ag, 0, 0x3, ev, f"{who}_timeout_{nm}"))            # Timeout
        # Threshold. axi_monitor_reporter_threshold emits TWO event codes:
        # AXI_THRESH_ACTIVE_COUNT (0x0) and AXI_THRESH_LATENCY (0x1). Keying
        # only 0x0 sent every latency-threshold packet to the UNEXPECTED bin,
        # which read as "threshold is broken" when the class was working --
        # the `threshold` scenario drives LATENCY_THRESH specifically, so 0x1
        # is the code it produces.
        c.append((ag, 0, 0x2, 0x0, f"{who}_threshold_active"))          # Threshold
        c.append((ag, 0, 0x2, 0x1, f"{who}_threshold_latency"))         # Threshold
    # CORE completions (scheduler 48, descriptor-engine 16).
    c.append((48, 4, 0x1, 0x01, "sched_desc_complete"))
    c.append((16, 4, 0x1, 0x40, "desc_loaded"))
    assert len(c) <= MON_N_PROFILE, f"{len(c)} candidates > {MON_N_PROFILE}"
    return c


CANDIDATES = gen_candidates()


# --- scenario setup hooks: run in pre_kick, AFTER the reset + STREAM config ---
def sc_none(bridge, runner):
    pass


def sc_perf(bridge, runner):
    # PERF cone is enabled by the scenario's MonitorProgram. Open a small perf
    # window + RUN so the rollup closes mid-DMA and routes to the tally.
    run_perf_windows(bridge, window_cycles=1000)


def sc_threshold(bridge, runner):
    # TIMEOUT (in us ticks) sits ABOVE the response delay so nothing times
    # out; only the (low, in clocks) latency threshold trips -- isolating
    # THRESHOLD from TIMEOUT.
    set_timeouts(bridge, timeout_us=5000, latency_thresh_clk=20)
    runner.set_resp_delay(2000, 2000)                      # >> threshold, << timeout


def sc_timeout(bridge, runner):
    # UNITS: TIMEOUT counts the monitor's 1 MHz tick, so the value is in
    # MICROSECONDS. 100 written "as cycles" was 100 us = 6000 clocks at 60 MHz,
    # above the ~2000-clock (~33 us) stall the response delay imposes, so the
    # cone never fired and the class read as unimplemented. 5 us (~300 clocks)
    # sits comfortably under the stall, so every transaction trips it.
    set_timeouts(bridge, timeout_us=5)
    runner.set_resp_delay(2000, 2000)


# Each scenario enables ONLY its packet classes so the monbus never floods.
# {1,8} = completion + AddrMatch base; timeout/threshold add just their class.
# addr_error keys the ERROR class alone on the datapath monitors with the
# addr-range checker in MISS mode (see stream_monitors.arm_addr_ranges for why
# a simultaneous match-all range starves the error stream to zero).
#   name, channels, ndesc, bytes, beats, classes, monitors, range mode, launches, setup
SCENARIOS = [
    ("basic",         [0],          2, 4096, 16, {PKT_COMPL, PKT_ADDRMATCH},
     None, "match_all", 1, sc_none),
    ("single_beat",   [0],          2,  512, 1,  {PKT_COMPL, PKT_ADDRMATCH},
     None, "match_all", 1, sc_none),
    ("multi_channel", [0, 1, 2, 3], 1, 4096, 16, {PKT_COMPL, PKT_ADDRMATCH},
     None, "match_all", 1, sc_none),
    ("timeout",       [0],          2, 4096, 16, {PKT_TIMEOUT, PKT_COMPL, PKT_ADDRMATCH},
     None, "match_all", 1, sc_timeout),
    ("threshold",     [0],          2, 4096, 16, {PKT_THRESHOLD, PKT_TIMEOUT, PKT_COMPL, PKT_ADDRMATCH},
     None, "match_all", 1, sc_threshold),
    ("perf",          [0],          2, 4096, 16, {PKT_PERF, PKT_PERFWIN, PKT_PERFHIST, PKT_COMPL, PKT_ADDRMATCH},
     None, "match_all", 1, sc_perf),
    # The low-priority addr_check error stream only accumulates while the miss
    # condition is sustained, so this one launches a few chains back-to-back.
    ("addr_error",    [0],          4, 4096, 16, {PKT_ERROR},
     DATAPATH_MONITORS, "miss", 3, sc_none),
]


def run_scenario(bridge, runner, sc, tally_rd, tally_cfg, unexpected, per_run_timeout_s):
    name, channels, ndesc, xbytes, beats, classes, monitors, rmode, launches, setup = sc
    os.environ["XFER_BEATS"] = str(beats)          # burst size, read by configure_stream
    os.environ["CHAR_POLL_TIMEOUT_S"] = str(per_run_timeout_s)
    runner.mon_config = MonitorProgram(classes, monitors=monitors or ("DAXMON", "RDMON", "WRMON"),
                                       name=name)
    runner.compression = False                     # the tally reassembles RAW records

    def pre_kick(br):
        runner.set_resp_delay(0, 0)                # clean slate; hooks may raise it
        arm_addr_ranges(br, rmode)
        route_monbus(br, "stream_tally")           # the tally is what we SWEEP
        setup(br, runner)
        tally.program_cam(br, tally_cfg, CANDIDATES)

    cfg = CharConfig(name=name, num_channels=len(channels), channels=list(channels),
                     descriptors_per_channel=ndesc, transfer_bytes=xbytes)
    done = False
    counts = {}
    for _ in range(launches):
        res = runner.run_config(cfg, pre_kick=pre_kick)
        done |= bool(res.get("pass"))
        # The perf rollup (reporter_perf) only advances its FSM while the
        # monbus output is idle, so it emits ONLY in the gap AFTER traffic
        # stops. Give it a brief idle window before freezing the tally.
        if name == "perf":
            time.sleep(0.02)
        bridge.write(H("CTRL"), compose("CTRL", FREEZE_TRACE=1))
        time.sleep(0.02)
        # Sweep per launch: the next run_config's reset clears the tally.
        for b, c in tally.sweep_dense(bridge, tally_rd, len(CANDIDATES), unexpected).items():
            counts[b] = counts.get(b, 0) + c
    return done, counts


def run_matrix(bridge, runner, *, reps=1, only=None, per_run_timeout_s=20.0):
    scenarios = [s for s in SCENARIOS if (only is None or s[0] in only)]
    rd, cfgw = tally.windows()
    tally_rd, tally_cfg = rd["stream"], cfgw["stream"]
    unexpected = tally.check_capacity(bridge, tally_cfg, CANDIDATES, MON_N_PROFILE)
    labels = tally.labels(CANDIDATES, unexpected)
    print(f"candidate legal set: {len(CANDIDATES)} tuples (bin0..{len(CANDIDATES) - 1}, "
          f"UNEXPECTED={unexpected}, CAM depth from hardware)")

    agg = {s[0]: {} for s in scenarios}
    done_ok = {s[0]: 0 for s in scenarios}
    for r in range(reps):
        for sc in scenarios:
            name = sc[0]
            try:
                done, counts = run_scenario(bridge, runner, sc, tally_rd, tally_cfg,
                                            unexpected, per_run_timeout_s)
            except Exception as e:
                print(f"  [{name}] EXCEPTION: {e}")
                continue
            done_ok[name] += int(done)
            for b, c in counts.items():
                agg[name][b] = agg[name].get(b, 0) + c
            print(f"rep{r} [{name:13s}] pass={done} {tally.format_counts(counts, labels)}")

    # --- matrix report ---
    print("\n================ SCENARIO x PACKET-CLASS MATRIX ================")
    hit_bins = sorted({b for d in agg.values() for b in d if b != unexpected})
    for name in (s[0] for s in scenarios):
        d = agg[name]
        lit = [labels[b] for b in hit_bins if d.get(b)]
        unexp = d.get(unexpected, 0)
        print(f"  {name:13s} pass={done_ok[name]}/{reps}  "
              f"tuples={sorted(set(l.split('_')[1] if '_' in l else l for l in lit))}  "
              f"UNEXPECTED={unexp}")
    # Per-class coverage across the whole matrix. perfwin/perfhist have NO
    # monbus emit path in the RTL (perfmon RFC Stage B/F pending) -- CSR-only
    # meters that can never land in the tally on any bitstream.
    print("\n---------------- packet classes observed (any scenario) ----------------")
    MONBUS_EMITTABLE = {PKT_ADDRMATCH, PKT_COMPL, PKT_PERF, PKT_ERROR, PKT_TIMEOUT, PKT_THRESHOLD}
    CSR_ONLY = {PKT_PERFWIN: "perfwin", PKT_PERFHIST: "perfhist"}
    classes = {"addrmatch": PKT_ADDRMATCH, "completion": PKT_COMPL, "perf": PKT_PERF,
               "perfwin": PKT_PERFWIN, "perfhist": PKT_PERFHIST, "error": PKT_ERROR,
               "timeout": PKT_TIMEOUT, "threshold": PKT_THRESHOLD}
    seen_class = {}
    for name, d in agg.items():
        for b, c in d.items():
            if b == unexpected or not c:
                continue
            seen_class.setdefault(CANDIDATES[b][2], set()).add(name)
    covered = 0
    for cls, ty in classes.items():
        who = seen_class.get(ty)
        if ty in CSR_ONLY:
            print(f"  {cls:11s} (type {ty:#03x}): CSR-only (no monbus emit path; perfmon RFC pending)")
            continue
        covered += int(bool(who))
        note = "OK  in " + ",".join(sorted(who)) if who else "not seen"
        print(f"  {cls:11s} (type {ty:#03x}): {note}")
    total_unexp = sum(d.get(unexpected, 0) for d in agg.values())
    print(f"\nmonbus-emittable classes covered: {covered}/{len(MONBUS_EMITTABLE)} "
          f"(perfwin/perfhist are CSR-only); total UNEXPECTED={total_unexp}"
          + ("  <-- packets emitted with a tuple NOT in the candidate set" if total_unexp else ""))
    return 0 if any(done_ok.values()) else 1


def main(argv=None):
    ap = argparse.ArgumentParser(description="STREAM monitor scenario-coverage matrix")
    ap.add_argument("--port", default="auto")
    ap.add_argument("--baud", type=int, default=115200)
    ap.add_argument("--reps", type=int, default=1)
    ap.add_argument("--only", default=None, help="comma list of scenario names")
    args = ap.parse_args(argv)
    only = set(args.only.split(",")) if args.only else None

    from uart_axi_bridge import UARTAxiBridge
    port = autodetect_port(args.baud, want=args.port)
    print(f"mon_matrix: port={port} reps={args.reps} "
          f"scenarios={[s[0] for s in SCENARIOS if not only or s[0] in only]}")
    with UARTAxiBridge(port, args.baud) as bridge:
        print(f"  {describe_build(bridge)}")
        runner = CharacterizationRunner(bridge)
        return run_matrix(bridge, runner, reps=args.reps, only=only)


if __name__ == "__main__":
    raise SystemExit(main())
