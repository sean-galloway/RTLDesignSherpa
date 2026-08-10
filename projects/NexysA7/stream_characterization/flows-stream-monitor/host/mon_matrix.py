#!/usr/bin/env python3
"""Monitor packet-coverage SCENARIO MATRIX on the board (flows-stream-monitor).

Where mon_coverage.py soaks one workload, this drives a MATRIX of scenarios that
each try to provoke a different monbus packet class, and reads them back out of
the CAM-always dense tally. The legal-set CAM is loaded with a COMPREHENSIVE
CANDIDATE SET (rd/wr datapath agents x every packet type x its real event codes,
from TBClasses.monbus.monbus_types) -- so which tuples actually fire is
DISCOVERED per scenario, not guessed. Anything the monitors emit that is not in
the candidate set lands in the single UNEXPECTED bin (flagged loudly).

Scenarios (each: soft-reset -> configure -> scenario setup -> (re)load CAM ->
DMA -> freeze -> sweep):
  basic         plain 2-desc DMA                 -> AddrMatch + completion
  single_beat   1-beat bursts (many txns)        -> more AddrMatch/completion
  multi_channel 4 channels                        -> per-channel traffic
  perf_window   small PERF_WINDOW_CYCLES + RUN    -> PERF / PERFWIN
  threshold     low LATENCY_THRESH + resp delay   -> THRESHOLD
  timeout       low TIMEOUT cycles + big delay    -> TIMEOUT

Register-based CAM programming (bus-width independent): CAM_CLEAR(0x100),
CAM_KEY(0x108), CAM_LOAD(0x110)={valid<<31|index}. Dense bins read at 8-byte
stride on the count port.

Usage:
    source env_python
    python3 host/mon_matrix.py                 # one pass of every scenario
    python3 host/mon_matrix.py --reps 5        # 5 reps each (accumulate)
    python3 host/mon_matrix.py --only timeout,threshold --port /dev/ttyUSB1
"""
import argparse
import os
import sys
import time

_here = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, os.path.abspath(os.path.join(_here, "..", "..", "flows-stream-bridge", "host")))
sys.path.insert(0, _here)
for up in range(3, 9):
    cand = os.path.join(_here, *([".."] * up), "projects/components/converters/bin")
    if os.path.isdir(cand):
        sys.path.insert(0, cand)
        break

from harness_addrs import H, autodetect_port, compose
from stream_addrs import A, compose as scompose
from run_characterization import CharacterizationRunner
from stream_device import build_stream_bus

# --- tally address map (monbus_tally_axil) ---
STREAM_TALLY_RD  = 0x0004_0000   # count readback (ingest-window read port)
STREAM_TALLY_CFG = 0x0010_0000   # CAM programming registers
MON = 0x1000
CAM_CLEAR_OFF, CAM_KEY_OFF, CAM_LOAD_OFF = 0x100, 0x108, 0x110
MON_N_PROFILE = 64
UNEXPECTED    = MON_N_PROFILE


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
        # PerfWin window rollup (perfmon Stage A/B): 0x0=WIN_END is the anchor.
        c.append((ag, 0, 0xD, 0x0, f"{who}_perfwin"))                    # PerfWin
        c.append((ag, 0, 0xE, 0x0, f"{who}_perfhist"))                   # PerfHist
        for ev, nm in ((0x0, "slverr"), (0x1, "decerr"), (0xD, "addrrange")):
            c.append((ag, 0, 0x0, ev, f"{who}_err_{nm}"))                # Error
        for ev, nm in ((0x0, "cmd"), (0x1, "data"), (0x2, "resp")):
            c.append((ag, 0, 0x3, ev, f"{who}_timeout_{nm}"))            # Timeout
        c.append((ag, 0, 0x2, 0x0, f"{who}_threshold"))                  # Threshold
    # CORE completions (scheduler 48, descriptor-engine 16).
    c.append((48, 4, 0x1, 0x01, "sched_desc_complete"))
    c.append((16, 4, 0x1, 0x40, "desc_loaded"))
    assert len(c) <= MON_N_PROFILE, f"{len(c)} candidates > {MON_N_PROFILE}"
    return c


CANDIDATES = gen_candidates()
LABELS = {i: t[4] for i, t in enumerate(CANDIDATES)}
LABELS[UNEXPECTED] = "UNEXPECTED"


def cam_key(agent, proto, ptype, evc):
    return (((agent & 0xFFFF) << 16) | ((proto & 0xF) << 12)
            | ((ptype & 0xF) << 8) | (evc & 0xFF))


def program_cam(bridge, cfg_base, legal):
    bridge.write(cfg_base + CAM_CLEAR_OFF, 0)
    for i, t in enumerate(legal):
        bridge.write(cfg_base + CAM_KEY_OFF,  cam_key(*t[:4]))
        bridge.write(cfg_base + CAM_LOAD_OFF, (1 << 31) | i)


def sweep_dense(bridge, rd_base, n_legal):
    counts = {}
    for b in list(range(n_legal)) + [UNEXPECTED]:
        v = bridge.read(rd_base + b * 8) or 0
        if v:
            counts[b] = v
    return counts


# pkt_type -> the *_ENABLE field that arms that cone. Fields are placed by the
# generated regmap (stream_addrs.compose), not by hand-assembled bit indices, so
# a field that moves in the RDL moves here with it. THRESHOLD (2) now has its own
# THRESH_EN field; it used to be gated by PERF_EN, so asking for THRESHOLD alone
# armed nothing. AddrMatch (8) comes from the addr-range checker, not ENABLE.
_EN_FIELD = {0: "ERR_EN", 1: "COMPL_EN", 2: "THRESH_EN", 3: "TIMEOUT_EN", 4: "PERF_EN"}


def enable_monitors(bridge, A, classes):
    """Enable ONLY the requested packet classes so the monbus (1 pkt / 2 cyc)
    never congests. `classes` is a set of pkt_type numbers. PKT_MASK drops every
    type not requested; ENABLE sets just the needed cones; the addr-range checker
    is armed only when AddrMatch (8) is wanted."""
    en_fields = {_EN_FIELD[t]: 1 for t in classes if t in _EN_FIELD}
    mask = 0xFFFF
    for t in classes:
        mask &= ~(1 << t)                       # 0 = allow that type at monbus entry
    for m in ("DAXMON", "RDMON", "WRMON"):
        bridge.write(A(f"{m}_PKT_MASK"), mask & 0xFFFF)
        bridge.write(A(f"{m}_MASK1"), 0x0)      # clear event-code drop masks
        bridge.write(A(f"{m}_MASK2"), 0x0)
        bridge.write(A(f"{m}_MASK3"), 0x0)
        # COMPRESS_EN exists on WRMON only and defaults to 1 in the RDL; the
        # tally reassembles RAW 3-beat records, so hold it clear.
        f = dict(en_fields, **({"COMPRESS_EN": 0} if m == "WRMON" else {}))
        bridge.write(A(f"{m}_ENABLE"), scompose(f"{m}_ENABLE", MON_EN=1, **f))
        bridge.write(A(f"{m}_ERR_CFG"), 0x0)    # BULK_TRACE routing to the tally
    if 8 in classes:                            # arm the match-all AddrMatch ranges
        ctrl = 0x01 | (1 << 4) | (1 << 5)
        for rbase, cbase in ((MON + 0x200, MON + 0x220), (MON + 0x230, MON + 0x250)):
            bridge.write(rbase + 0x00, 0x0); bridge.write(rbase + 0x04, 0xFFFF_FFFF)
            bridge.write(cbase, ctrl)
    bridge.write(A("MON_GROUP_BASE_ADDR"), 0x0004_0000)
    bridge.write(A("MON_GROUP_LIMIT_ADDR"), 0x0007_FFFF)
    bridge.write(A("MON_GROUP_FLUSH_WATERMARK"), 0x0)


# --- scenario setup hooks (applied AFTER enable_monitors, BEFORE the DMA) ---
def _mons(A, reg):
    return [A(f"{m}_{reg}") for m in ("RDMON", "WRMON")]


def sc_none(bridge, A, runner):
    pass


def sc_perf(bridge, A, runner):
    # PERF_EN cone is enabled class-selectively by enable_monitors (type 4/0xD/0xE
    # in the scenario's classes). Here just open a small perf window + RUN so the
    # windowed/histogram perf packets close mid-DMA and route to the tally.
    for m in ("RDMON", "WRMON", "DAXMON"):
        bridge.write(A(f"{m}_PERF_WINDOW_CYCLES"), 1000)   # small window -> closes mid-DMA
        bridge.write(A(f"{m}_PERF_CTRL"), 0x1)             # RUN


def sc_threshold(bridge, A, runner):
    # Threshold packets ride the timeout/completion cone, so the scenario's classes
    # include TIMEOUT (3) to build that cone -- but TIMEOUT is set ABOVE the resp
    # delay so the transaction never times out; only the (low) latency threshold
    # trips, isolating THRESHOLD from TIMEOUT.
    for r in _mons(A, "TIMEOUT"):
        bridge.write(r, 5000)                              # > resp delay -> no timeout
    for r in _mons(A, "LATENCY_THRESH"):
        bridge.write(r, 20)                                # very low latency threshold
    runner.set_resp_delay(2000, 2000)                      # >> threshold, << timeout


def sc_timeout(bridge, A, runner):
    for r in _mons(A, "TIMEOUT"):
        bridge.write(r, 100)                               # low timeout window
    runner.set_resp_delay(2000, 2000)                      # far exceed it


def sc_addr_error(bridge, A, runner):
    # ADDR_RANGE error (type 0, event 0x0D) comes straight from axi_monitor_addr_check
    # -- built whenever N_ADDR_RANGES>0 (=4 here), INDEPENDENT of ENABLE_ERROR_LOGIC.
    # Range 2 is ERROR-flavored (MON_ADDR_RANGE_IS_ERROR=4'b1100) and the error path
    # is an ALLOWLIST: any access OUTSIDE every enabled error range emits the packet.
    # Point range2 at a high region the DMA never touches -> every access misses ->
    # ADDR_RANGE error. CTRL bits: RANGE_EN[3:0], CHECK_EN[4], MATCH_EN[5], MISS_EN[6].
    # ISOLATE the error stream: addr_check is the LOWEST-priority monbus source
    # (reporter > debug > addr_check), so MATCH (AddrMatch) and the reporter cones
    # starve it. Enable ONLY range2 + CHECK + MISS (no MATCH), and the scenario's
    # class set is {0} so the pkt-mask drops every competing type.
    # ADDR_RANGE error (type 0, event 0x0D) from axi_monitor_addr_check, VALIDATED
    # in cosim (dv/tests/test_stream_mon.py TEST_MISS=1). Config mirrors that repro
    # exactly. ENABLE bit layout (per run_characterization): bit0=ERR_EN,1=TIMEOUT,
    # 2=COMPL,3=THRESH. cfg_error_enable = ERR_EN | addr MISS_EN. Range2 is
    # ERROR-flavored; a tiny high exclude window makes every access an allowlist
    # miss. CTRL: RANGE_EN[3:0]/CHECK_EN[4]/MATCH_EN[5]/MISS_EN[6] -- keep range0
    # match + range2 miss (= 0x75), same as the passing sim.
    ctrl = 0x01 | (1 << 2) | (1 << 4) | (1 << 5) | (1 << 6)   # r0(match)+r2+check+match+miss
    for m in ("RDMON", "WRMON"):
        # ERR_EN only (bit0): timeout/compl/thresh OFF so their cones don't flood
        # the monbus and starve the low-priority addr_check error stream. The miss
        # is driven by MISS_EN in the addr ctrl (cfg_error_enable = ERR_EN|MISS_EN).
        # NOTE: in the full matrix flow this class is best exercised by the
        # dedicated host/mon_err_probe.py (reliable wr_err counts); here it is
        # best-effort since the error only accumulates while the DMA is wedged.
        bridge.write(A(f"{m}_ENABLE"),
                     scompose(f"{m}_ENABLE", MON_EN=1, ERR_EN=1,
                              **({"COMPRESS_EN": 0} if m == "WRMON" else {})))
        bridge.write(A(f"{m}_PKT_MASK"), 0xFEFE)           # allow type 0 + 8 only (0=allow)
        bridge.write(A(f"{m}_ADDR_RANGE0_LOW"),  0x0000_0000)
        bridge.write(A(f"{m}_ADDR_RANGE0_HIGH"), 0xFFFF_FFFF)   # range0 match-all (debug)
        bridge.write(A(f"{m}_ADDR_RANGE2_LOW"),  0xFFFF_FFF0)   # range2 exclude window
        bridge.write(A(f"{m}_ADDR_RANGE2_HIGH"), 0xFFFF_FFFF)
        bridge.write(A(f"{m}_ADDR_RANGE_CTRL"),  ctrl)


# Each scenario enables ONLY its packet classes (pkt_type set) so the monbus
# never floods: {1,8}=completion+AddrMatch base; timeout/threshold add just their
# class. (Perf type 4 is a CSR meter, not a tally packet -- covered separately.)
SCENARIOS = [
    # name, channels, ndesc, bytes, beats, classes, setup
    ("basic",         [0],          2, 4096, 16, {1, 8},               sc_none),
    ("single_beat",   [0],          2,  512, 1,  {1, 8},               sc_none),
    ("multi_channel", [0, 1, 2, 3], 1, 4096, 16, {1, 8},               sc_none),
    ("timeout",       [0],          2, 4096, 16, {3, 1, 8},            sc_timeout),
    ("threshold",     [0],          2, 4096, 16, {2, 3, 1, 8},         sc_threshold),
    ("perf",          [0],          2, 4096, 16, {4, 0xD, 0xE, 1, 8},  sc_perf),
    ("addr_error",    [0],          4, 4096, 16, {0},                  sc_addr_error),
]


def run_scenario(bridge, runner, A, sc, per_run_timeout_s):
    name, channels, ndesc, xbytes, beats, classes, setup = sc
    # burst size is read from env by configure_stream.
    os.environ["XFER_BEATS"] = str(beats)
    bridge.write(H("CTRL"), compose("CTRL", SOFT_RESET=1)); time.sleep(0.01)
    runner.clear_stats()
    runner.set_resp_delay(0, 0)                            # reset delay each scenario
    runner.configure_stream(channels)
    # addr_error drives the monitor config entirely in its setup hook (matching the
    # validated probe); enable_monitors' class-based ENABLE/mask would clobber it.
    if name != "addr_error":
        enable_monitors(bridge, A, classes)
    setup(bridge, A, runner)
    program_cam(bridge, STREAM_TALLY_CFG, CANDIDATES)

    stream = build_stream_bus(bridge)["stream"]
    # addr_error drives every command into an allowlist MISS; the low-priority
    # addr_check error stream only accumulates while the miss condition is
    # sustained, so kick a few chains back-to-back before the freeze (matches the
    # validated probe). Other scenarios kick once.
    n_launch = 3 if name == "addr_error" else 1
    done = False
    for _ in range(n_launch):
        kicks = {ch: stream.load_chain(ch, num_descriptors=ndesc, transfer_bytes=xbytes)
                 for ch in channels}
        runner.setup_timer(len(channels) * ndesc * xbytes)
        runner.kick_channels(kicks)
        res = runner.poll_completion(timeout_s=per_run_timeout_s)
        done = bool(res.get("completed"))

    # The perf rollup (reporter_perf) only advances its 5-state FSM while the
    # monbus output is idle, so it emits ONLY in the gap AFTER traffic stops.
    # Give it a brief idle window before freezing the tally (harmless to the
    # other scenarios, which have no idle-only packet class).
    if name == "perf":
        time.sleep(0.02)
    bridge.write(H("CTRL"), compose("CTRL", FREEZE_TRACE=1)); time.sleep(0.02)
    return done, sweep_dense(bridge, STREAM_TALLY_RD, len(CANDIDATES))


def run_matrix(bridge, runner, A, *, reps=1, only=None, per_run_timeout_s=20.0):
    scenarios = [s for s in SCENARIOS if (only is None or s[0] in only)]
    # accumulate per (scenario -> bin -> count)
    agg = {s[0]: {} for s in scenarios}
    done_ok = {s[0]: 0 for s in scenarios}
    for r in range(reps):
        for sc in scenarios:
            name = sc[0]
            try:
                done, counts = run_scenario(bridge, runner, A, sc, per_run_timeout_s)
            except Exception as e:
                print(f"  [{name}] EXCEPTION: {e}")
                continue
            done_ok[name] += int(done)
            for b, c in counts.items():
                agg[name][b] = agg[name].get(b, 0) + c
            tags = " ".join(f"{LABELS[b]}={c}" for b, c in sorted(counts.items()))
            print(f"rep{r} [{name:13s}] done={done} {tags or '(no packets)'}")

    # --- matrix report ---
    print("\n================ SCENARIO x PACKET-CLASS MATRIX ================")
    # union of bins hit anywhere (excluding UNEXPECTED, shown separately)
    hit_bins = sorted({b for d in agg.values() for b in d if b != UNEXPECTED})
    for name in (s[0] for s in scenarios):
        d = agg[name]
        lit = [LABELS[b] for b in hit_bins if d.get(b)]
        unexp = d.get(UNEXPECTED, 0)
        print(f"  {name:13s} done={done_ok[name]}/{reps}  "
              f"tuples={sorted(set(l.split('_')[1] if '_' in l else l for l in lit))}  "
              f"UNEXPECTED={unexp}")
    # per-packet-class coverage across the whole matrix.
    #   error is covered on the SEPARATE error-flavor bitstream (this build omits
    #   the error cone for timing); perfwin/perfhist have NO monbus emit path in
    #   the RTL (perfmon RFC Stage B/F pending) -- they are CSR-only meters, so
    #   they can never land in the tally on any bitstream.
    print("\n---------------- packet classes observed (any scenario) ----------------")
    MONBUS_EMITTABLE = {8, 1, 4, 0, 3, 2}   # tally-coverable packet types
    CSR_ONLY = {0xD: "perfwin", 0xE: "perfhist"}
    classes = {"addrmatch": 8, "completion": 1, "perf": 4, "perfwin": 0xD,
               "perfhist": 0xE, "error": 0, "timeout": 3, "threshold": 2}
    seen_class = {}
    for name, d in agg.items():
        for b, c in d.items():
            if b == UNEXPECTED or not c:
                continue
            ty = CANDIDATES[b][2]
            seen_class.setdefault(ty, set()).add(name)
    covered = 0
    for cls, ty in classes.items():
        who = seen_class.get(ty)
        ok = bool(who)
        if ty in CSR_ONLY:
            print(f"  {cls:11s} (type {ty:#03x}): CSR-only (no monbus emit path; perfmon RFC pending)")
            continue
        covered += int(ok)
        note = "OK  in " + ",".join(sorted(who)) if ok else "not seen"
        print(f"  {cls:11s} (type {ty:#03x}): {note}")
    total_unexp = sum(d.get(UNEXPECTED, 0) for d in agg.values())
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
    print(f"candidate legal set: {len(CANDIDATES)} tuples (bin0..{len(CANDIDATES)-1}, UNEXPECTED={UNEXPECTED})")
    with UARTAxiBridge(port, args.baud) as bridge:
        runner = CharacterizationRunner(bridge)
        return run_matrix(bridge, runner, A, reps=args.reps, only=only)


if __name__ == "__main__":
    raise SystemExit(main())
