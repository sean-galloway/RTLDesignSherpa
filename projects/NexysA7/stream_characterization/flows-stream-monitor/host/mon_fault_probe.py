#!/usr/bin/env python3
"""FAULT-INJECTION probe for the STREAM monitor tally (board + cosim).

Error/timeout/threshold packets are FAULT conditions -- in correct operation they
never occur, so they cannot be covered by healthy traffic (that is mon_matrix.py's
job, which asserts ZERO faults). This tool is the single place that deliberately
misbehaves the slaves/traffic and checks the monitor catches each fault:

  FAULT               INJECTION                              MONITORS -> tally
  ------------------  -------------------------------------  ----------------------
  no_response  ->     slave holds R/B beats (RESP_DELAY hi)  TIMEOUT  (type 3)
                      past the TIMEOUT window
  slow         ->     slave latency past LATENCY_THRESH but  THRESHOLD(type 2)
                      under TIMEOUT (RESP_DELAY moderate)
  addr_range   ->     access outside the ERROR allowlist     ERROR    (type 0, 0x0D)
                      (range2 exclude window; every cmd miss)

(SLVERR/DECERR error EVENTS need a slave forced to return a bad response; the data
slaves have no such hook today -- a bad-address DECERR responder exists for the
control path -- so that event is a documented extension, not yet injected here.)

ENABLE is composed BY FIELD NAME through the generated regmap (stream_addrs.compose),
never as a hand-assembled bitmask. An earlier version of this file hardcoded the
layout from a stale comment (bit0=ERR_EN...) when the RDL actually starts with
MON_EN, so "enable the threshold cone" quietly enabled something else. Dense CAM
below -> the tally resolves each fault to its own bin.

Usage:
    source env_python
    python3 host/mon_fault_probe.py                       # all faults
    python3 host/mon_fault_probe.py --only addr_range --port /dev/ttyUSB1
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
from uart_axi_bridge import UARTAxiBridge

STREAM_TALLY_RD  = 0x0004_0000
STREAM_TALLY_CFG = 0x0010_0000
CAM_CLEAR, CAM_KEY, CAM_LOAD = 0x100, 0x108, 0x110

# Dense CAM: every fault packet gets a bin. Position = dense index.
CAM = [
    (9,  0, 8, 0x01),   # 0 rd AddrMatch          (healthy reference)
    (10, 0, 8, 0x01),   # 1 wr AddrMatch
    (9,  0, 0, 0x0D),   # 2 rd ERROR/ADDR_RANGE
    (10, 0, 0, 0x0D),   # 3 wr ERROR/ADDR_RANGE
    (9,  0, 3, 0x00),   # 4 rd TIMEOUT cmd
    (10, 0, 3, 0x00),   # 5 wr TIMEOUT cmd
    (9,  0, 3, 0x02),   # 6 rd TIMEOUT resp
    (10, 0, 3, 0x02),   # 7 wr TIMEOUT resp
    (9,  0, 2, 0x00),   # 8 rd THRESHOLD
    (10, 0, 2, 0x00),   # 9 wr THRESHOLD
]
LBL = ["rd_addrmatch", "wr_addrmatch", "rd_err", "wr_err",
       "rd_to_cmd", "wr_to_cmd", "rd_to_resp", "wr_to_resp",
       "rd_thresh", "wr_thresh"]
# Which dense bins prove each fault class fired.
FAULT_BINS = {
    "no_response": (4, 5, 6, 7),   # any TIMEOUT bin
    "slow":        (8, 9),         # any THRESHOLD bin
    "addr_range":  (2, 3),         # any ERROR bin
}


def _key(ag, pr, ty, ec):
    return ((ag & 0xFFFF) << 16) | ((pr & 0xF) << 12) | ((ty & 0xF) << 8) | (ec & 0xFF)


def _mon_common(br, pkt_mask, **en_fields):
    # Full monitor setup (mirrors mon_matrix.enable_monitors): ENABLE + type mask
    # + clear the per-type EVENT-code masks (MASK1/2/3) so no fault event is
    # silently dropped + BULK_TRACE routing + tally window.
    # en_fields are ENABLE field NAMES (MON_EN/ERR_EN/COMPL_EN/TIMEOUT_EN/
    # PERF_EN/THRESH_EN) resolved through the regmap, so a field that moves in
    # the RDL moves here too.
    for m in ("DAXMON", "RDMON", "WRMON"):             # all three feed the shared group
        br.write(A(f"{m}_PKT_MASK"), pkt_mask)
        br.write(A(f"{m}_MASK1"), 0x0)
        br.write(A(f"{m}_MASK2"), 0x0)
        br.write(A(f"{m}_MASK3"), 0x0)
        # COMPRESS_EN=0 explicitly: it exists on WRMON_ENABLE only and its RDL
        # default is 1, so composing from defaults would arm compression. The
        # tally's 3-beat record reassembler needs RAW records. (This harness
        # compiles compression out, so it is a no-op here -- state it anyway so
        # a build that turns USE_MON_COMPRESSION on does not silently break.)
        fields = dict(en_fields)
        if m == "WRMON":
            fields["COMPRESS_EN"] = 0
        br.write(A(f"{m}_ENABLE"), scompose(f"{m}_ENABLE", MON_EN=1, **fields))
        br.write(A(f"{m}_ERR_CFG"), 0x0)               # BULK_TRACE -> tally
    br.write(A("MON_GROUP_BASE_ADDR"),       0x0004_0000)
    br.write(A("MON_GROUP_LIMIT_ADDR"),      0x0007_FFFF)
    br.write(A("MON_GROUP_FLUSH_WATERMARK"), 0x0)


# The delay faults keep a match-all DEBUG range0 so the addr_check stays primed.
# Each fault enables ONLY its own cone (see the per-fault helpers below):
# TIMEOUT_EN for the timeout class, THRESH_EN for the threshold class. THRESH_EN
# is a real field now -- the threshold cone used to be gated by PERF_EN, so
# arming it without PERF_EN produced no packets however low LATENCY_THRESH went.
_DELAY_PKT_MASK = 0xFEF5                 # allow types 1,2,3,8 (0=allow)
_MATCH_CTRL     = 0x01 | (1 << 4) | (1 << 5)   # RANGE_EN r0 + CHECK + MATCH


def _arm_match_all(br):
    for m in ("RDMON", "WRMON"):
        br.write(A(f"{m}_ADDR_RANGE0_LOW"),  0x0000_0000)
        br.write(A(f"{m}_ADDR_RANGE0_HIGH"), 0xFFFF_FFFF)
        br.write(A(f"{m}_ADDR_RANGE_CTRL"),  _MATCH_CTRL)


# --- per-fault injection --------------------------------------------------------
def inject_no_response(br, runner):
    """Slave holds responses past the timeout window -> TIMEOUT packets.
    Delay is bounded (>> TIMEOUT window but small enough that the DMA still drains,
    so counts are clean instead of a wedged flood)."""
    _mon_common(br, _DELAY_PKT_MASK, TIMEOUT_EN=1)
    _arm_match_all(br)
    for m in ("RDMON", "WRMON"):
        br.write(A(f"{m}_TIMEOUT"), 50)                 # low timeout window -> trips
        br.write(A(f"{m}_LATENCY_THRESH"), 0x0FFF_FFFF) # high -> threshold stays quiet
    runner.set_resp_delay(500, 500)                     # >> TIMEOUT, still drains


def inject_slow(br, runner):
    """Slave latency past LATENCY_THRESH but under TIMEOUT -> THRESHOLD packets."""
    _mon_common(br, _DELAY_PKT_MASK, THRESH_EN=1)
    _arm_match_all(br)
    for m in ("RDMON", "WRMON"):
        br.write(A(f"{m}_TIMEOUT"), 100_000)            # high: no timeout
        br.write(A(f"{m}_LATENCY_THRESH"), 20)          # low: trips threshold
    runner.set_resp_delay(200, 200)                     # > thresh, << timeout


def inject_addr_range(br, runner):
    """Every command lands outside the ERROR allowlist -> ADDR_RANGE error.
    Range2 is ERROR-flavored (IS_ERROR=4'b1100); a tiny high exclude window makes
    every access (src 0x8000_0000 / dst 0x9000_0000) an allowlist miss."""
    ctrl = 0x01 | (1 << 2) | (1 << 4) | (1 << 5) | (1 << 6)   # r0+r2+CHECK+MATCH+MISS
    # ERR_EN only: no timeout cone -> the wedged DMA can't flood timeout, so the
    # error stream isn't starved. cfg_error_enable = ERR_EN | MISS_EN.
    _mon_common(br, 0xFEF0, ERR_EN=1)
    for m in ("RDMON", "WRMON"):
        br.write(A(f"{m}_ADDR_RANGE0_LOW"),  0x0000_0000)
        br.write(A(f"{m}_ADDR_RANGE0_HIGH"), 0xFFFF_FFFF)     # range0 match-all (debug)
        br.write(A(f"{m}_ADDR_RANGE2_LOW"),  0xFFFF_FFF0)     # range2 exclude window
        br.write(A(f"{m}_ADDR_RANGE2_HIGH"), 0xFFFF_FFFF)
        br.write(A(f"{m}_ADDR_RANGE_CTRL"),  ctrl)
    runner.set_resp_delay(0, 0)


# name -> (inject fn, launches, ndesc, xbytes). Delay faults use a small transfer
# that drains cleanly; addr_range kicks a few larger chains so the low-priority
# miss/error stream stays sustained.
FAULTS = {
    "no_response": (inject_no_response, 1, 2, 2048),
    "slow":        (inject_slow,        1, 2, 2048),
    "addr_range":  (inject_addr_range,  3, 4, 4096),
}


def load_cam(br):
    br.write(STREAM_TALLY_CFG + CAM_CLEAR, 0)
    for i, t in enumerate(CAM):
        br.write(STREAM_TALLY_CFG + CAM_KEY, _key(*t))
        br.write(STREAM_TALLY_CFG + CAM_LOAD, (1 << 31) | i)


def run_fault(br, runner, name):
    inject, launches, ndesc, xbytes = FAULTS[name]
    os.environ["XFER_BEATS"] = "16"
    br.write(H("CTRL"), compose("CTRL", SOFT_RESET=1)); time.sleep(0.02)
    runner.clear_stats(); runner.set_resp_delay(0, 0)
    runner.configure_stream([0])
    # Reset the addr-range checker to a benign state first: SOFT_RESET does NOT
    # clear these CSRs, so a prior fault's ERROR range2/MISS_EN bleeds into the
    # next fault (phantom errors). Disable all ranges before the injection sets
    # only what it needs.
    for m in ("RDMON", "WRMON"):
        br.write(A(f"{m}_ADDR_RANGE_CTRL"), 0x0)
        br.write(A(f"{m}_ADDR_RANGE2_LOW"),  0x0000_0000)
        br.write(A(f"{m}_ADDR_RANGE2_HIGH"), 0xFFFF_FFFF)   # benign: any addr in-range
    inject(br, runner)
    load_cam(br)

    # Baseline the bins AFTER config but BEFORE traffic: a fault that wedges the DMA
    # keeps the monbus busy so the next clear can miss, leaving stale counts. Report
    # the DELTA (this fault's contribution), which is immune to imperfect clearing.
    def snap():
        s = [br.read(STREAM_TALLY_RD + i * 8) or 0 for i in range(len(LBL))]
        s.append(br.read(STREAM_TALLY_RD + 64 * 8) or 0)   # UNEXPECTED
        return s
    base = snap()

    stream = build_stream_bus(br)["stream"]
    for _ in range(launches):
        kick = stream.load_chain(0, num_descriptors=ndesc, transfer_bytes=xbytes)
        runner.setup_timer(ndesc * xbytes)
        runner.kick_channels({0: kick})
        runner.poll_completion(timeout_s=20)

    br.write(H("CTRL"), compose("CTRL", FREEZE_TRACE=1)); time.sleep(0.02)
    fin = snap()
    delta = [max(0, fin[i] - base[i]) for i in range(len(fin))]
    counts = {LBL[i]: delta[i] for i in range(len(LBL)) if delta[i]}
    unexp = delta[len(LBL)]
    caught = sum(delta[b] for b in FAULT_BINS[name])
    return counts, unexp, caught


def main(argv=None):
    ap = argparse.ArgumentParser(description="STREAM monitor fault-injection probe")
    ap.add_argument("--port", default="auto")
    ap.add_argument("--baud", type=int, default=115200)
    ap.add_argument("--only", default=None, help="comma list of fault names")
    args = ap.parse_args(argv)
    only = set(args.only.split(",")) if args.only else set(FAULTS)

    port = autodetect_port(args.baud, want=args.port)
    faults = [f for f in FAULTS if f in only]
    print(f"mon_fault_probe: port={port} faults={faults}")
    rc = 0
    with UARTAxiBridge(port, args.baud) as br:
        runner = CharacterizationRunner(br)
        results = {}
        for name in faults:
            counts, unexp, caught = run_fault(br, runner, name)
            results[name] = (counts, unexp, caught)
            tags = " ".join(f"{k}={v}" for k, v in counts.items()) or "(no packets)"
            print(f"  [{name:12s}] caught={caught:<4d} {tags}  UNEXPECTED={unexp}")

        print("\n================ FAULT-INJECTION COVERAGE ================")
        classes = {"no_response": "TIMEOUT (type 3)", "slow": "THRESHOLD (type 2)",
                   "addr_range": "ERROR/ADDR_RANGE (type 0)"}
        for name in faults:
            _, _, caught = results[name]
            ok = caught > 0
            rc |= (0 if ok else 1)
            print(f"  {classes[name]:28s} via {name:12s}: "
                  f"{'CAUGHT' if ok else 'NOT SEEN'} ({caught} packets)")
    return rc


if __name__ == "__main__":
    raise SystemExit(main())
