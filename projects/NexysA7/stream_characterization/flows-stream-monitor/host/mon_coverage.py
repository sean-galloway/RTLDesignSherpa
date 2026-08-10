#!/usr/bin/env python3
"""Long monitor packet-coverage on the board (flows-stream-monitor), CAM-tally model.

The tally is now the CAM-always dense histogram: the legal-set CAM routes each
monbus packet's {agent,protocol,pkt_type,event_code} tuple to a DENSE bin (its
position in the loaded legal set), or to the single UNEXPECTED bin on a miss.
So coverage = "load the tuples you want to watch into the CAM, run traffic, read
the dense bins." A bin > 0 means that exact tuple was observed on silicon; the
UNEXPECTED bin counts every packet NOT in the loaded set (proof that other
traffic is flowing, even before its exact tuple is enumerated here).

CAM programming is REGISTER-based (bus-width independent):
    CAM_CLEAR (0x100) : any write invalidates all entries
    CAM_KEY   (0x108) : wdata[31:0] = key to load next
    CAM_LOAD  (0x110) : wdata = (1<<31 valid) | index -> load CAM_KEY into entry
Dense bins are read on the count port at 8-byte stride (one 32-bit count / word).

Reuse, don't reinvent: this sits on the COMMON UART HARNESS (UARTAxiBridge +
autodetect_port + by-name CSR via harness_addrs.H / stream regmap A) and drives
the DMA through run_characterization.CharacterizationRunner.

Requires the flows-stream-monitor bitstream built from CURRENT RTL (CAM-always
tally + register CAM programming). A stale bitstream tallies nothing.

Usage:
    source env_python
    python3 host/mon_coverage.py --minutes 10
    python3 host/mon_coverage.py --iters 200 --port /dev/ttyUSB1
"""
import argparse
import os
import sys
import time

_here = os.path.dirname(os.path.abspath(__file__))
_bridge_host = os.path.join(_here, "..", "..", "flows-stream-bridge", "host")
sys.path.insert(0, os.path.abspath(_bridge_host))
sys.path.insert(0, _here)
for up in range(3, 9):
    cand = os.path.join(_here, *([".."] * up), "projects/components/converters/bin")
    if os.path.isdir(cand):
        sys.path.insert(0, cand)
        break

from harness_addrs import H, autodetect_port, compose          # common UART harness
from stream_addrs import A                                       # by-name STREAM regs
from run_characterization import CharacterizationRunner          # shared runner
from stream_device import build_stream_bus                       # STREAM device (DMA)

# Tally address map (see monbus_tally_axil): count readback rides the ingest
# window's read channel; config rides the cfg window's write channel.
STREAM_TALLY_RD  = 0x0004_0000   # count readback (ingest-window read port)
SLAVE_TALLY_RD   = 0x000C_0000
STREAM_TALLY_CFG = 0x0010_0000   # CAM programming registers
SLAVE_TALLY_CFG  = 0x0014_0000
MON = 0x1000                     # MON regfile base in the STREAM APB space

# CAM programming registers (offsets within a *_tally_cfg slave).
CAM_CLEAR_OFF = 0x100
CAM_KEY_OFF   = 0x108
CAM_LOAD_OFF  = 0x110

MON_N_PROFILE = 64               # legal-set capacity; UNEXPECTED bin = index 64
UNEXPECTED    = MON_N_PROFILE

# Coverage legal set: (agent, protocol, pkt_type, event_code, label). Dense bin
# index = position here. AXI(proto 0) rd=agent 9 / wr=agent 10; CORE(proto 4)
# scheduler=48 / descriptor-engine=16. The AddrMatch tuples are validated in sim
# (event 0x01 = AXI_ADDR_RANGE_MATCH); completion/perf event codes are the design
# defaults and get confirmed/extended against the UNEXPECTED catch-all on silicon.
STREAM_LEGAL = [
    (9,  0, 0x8, 0x01, "rd_addrmatch"),
    (10, 0, 0x8, 0x01, "wr_addrmatch"),
    (9,  0, 0x1, 0x00, "rd_completion"),
    (10, 0, 0x1, 0x00, "wr_completion"),
    (9,  0, 0x4, 0x00, "rd_perf"),
    (10, 0, 0x4, 0x00, "wr_perf"),
    (48, 4, 0x1, 0x01, "sched_desc_complete"),
    (16, 4, 0x1, 0x40, "desc_loaded"),
]


def cam_key(agent, proto, ptype, evc):
    """Legal-set key: {agent[15:0], proto[3:0], type[3:0], event[7:0]}."""
    return (((agent & 0xFFFF) << 16) | ((proto & 0xF) << 12)
            | ((ptype & 0xF) << 8) | (evc & 0xFF))


def program_cam(bridge, cfg_base, legal):
    """Register-based CAM load: CLEAR, then per entry {KEY, LOAD(valid|index)}.
    Index rides in LOAD data, so no bus-width/stride hazard."""
    bridge.write(cfg_base + CAM_CLEAR_OFF, 0)
    for i, (ag, pr, ty, ec, _label) in enumerate(legal):
        bridge.write(cfg_base + CAM_KEY_OFF,  cam_key(ag, pr, ty, ec))
        bridge.write(cfg_base + CAM_LOAD_OFF, (1 << 31) | i)


def sweep_dense(bridge, rd_base, n_legal):
    """Read the dense bins (0..n_legal-1) + UNEXPECTED. 8-byte stride."""
    counts = {}
    for b in list(range(n_legal)) + [UNEXPECTED]:
        v = bridge.read(rd_base + b * 8) or 0
        if v:
            counts[b] = v
    return counts


def configure_monitors(bridge, A):
    """Enable the three in-core monitors to EMIT packets: allow all types
    (PKT_MASK=0), clear ADDR_MASK, enable completion+IRQ, ERR_CFG=0 (BULK_TRACE
    -> tally ingest). Match-all DEBUG address range on rd+wr so every AR/AW emits
    AddrMatch; open the perf windows so PERF records flow."""
    for pk, en, err, m3 in (
        ("DAXMON_PKT_MASK", "DAXMON_ENABLE", "DAXMON_ERR_CFG", "DAXMON_MASK3"),
        ("RDMON_PKT_MASK",  "RDMON_ENABLE",  "RDMON_ERR_CFG",  "RDMON_MASK3"),
        ("WRMON_PKT_MASK",  "WRMON_ENABLE",  "WRMON_ERR_CFG",  "WRMON_MASK3"),
    ):
        bridge.write(A(pk),  0x0000_0000)   # drop nothing -> allow every type
        bridge.write(A(m3),  0x0)           # clear ADDR_MASK -> AddrMatch passes
        bridge.write(A(en),  0x0F)          # ENABLE + COMPL + IRQ
        bridge.write(A(err), 0x0)           # BULK_TRACE routing to the tally
    ctrl = 0x01 | (1 << 4) | (1 << 5)       # RANGE_EN | CHECK_EN | MATCH_EN (DEBUG)
    for rbase, cbase in ((MON + 0x200, MON + 0x220), (MON + 0x230, MON + 0x250)):
        bridge.write(rbase + 0x00, 0x0000_0000)
        bridge.write(rbase + 0x04, 0xFFFF_FFFF)
        bridge.write(cbase, ctrl)
    for p in ("RDMON_PERF_CTRL", "WRMON_PERF_CTRL", "DAXMON_PERF_CTRL"):
        bridge.write(A(p), 0x1)             # RUN=1
    # In-core group bulk-trace write window -> debug_sram (stream_tally ingest).
    bridge.write(A("MON_GROUP_BASE_ADDR"),       0x0004_0000)
    bridge.write(A("MON_GROUP_LIMIT_ADDR"),      0x0007_FFFF)
    bridge.write(A("MON_GROUP_FLUSH_WATERMARK"), 0x0000)


def run_coverage(bridge, runner, A, *, channel=0, minutes=10.0, iters=None,
                 xfer_bytes=4096, per_run_timeout_s=15.0):
    seen = {}          # dense bin -> cumulative count over the whole soak
    labels = {i: l[4] for i, l in enumerate(STREAM_LEGAL)}
    labels[UNEXPECTED] = "UNEXPECTED"
    deadline = time.time() + minutes * 60.0
    it = passed = 0
    while (iters is None and time.time() < deadline) or (iters is not None and it < iters):
        # SOFT_RESET first (wipes the tally CAM/counts), then clear + configure +
        # (re)program the CAM post-reset so it survives to DMA time.
        bridge.write(H("CTRL"), compose("CTRL", SOFT_RESET=1))
        time.sleep(0.01)
        runner.clear_stats()
        runner.configure_stream([channel])
        configure_monitors(bridge, A)
        program_cam(bridge, STREAM_TALLY_CFG, STREAM_LEGAL)

        # DMA workload through the monitors.
        stream = build_stream_bus(bridge)["stream"]
        kick = stream.load_chain(channel, num_descriptors=2, transfer_bytes=xfer_bytes)
        runner.setup_timer(2 * xfer_bytes)
        runner.kick_channels({channel: kick})
        res = runner.poll_completion(timeout_s=per_run_timeout_s)
        done = bool(res.get('completed')) and not res.get('error')

        # FREEZE for a coherent read boundary; reads are live (no cache).
        bridge.write(H("CTRL"), compose("CTRL", FREEZE_TRACE=1))
        time.sleep(0.02)
        counts = sweep_dense(bridge, STREAM_TALLY_RD, len(STREAM_LEGAL))
        for b, c in counts.items():
            seen[b] = seen.get(b, 0) + c
        passed += int(done and bool(counts))
        tags = " ".join(f"{labels[b]}={c}" for b, c in sorted(counts.items()))
        print(f"cov[{it:04d}] done={done} bins: {tags or '(empty!)'}")
        it += 1

    print(f"\nmon_coverage: {it} workloads, {passed} with tally hits")
    print("legal-set tuples observed on silicon:")
    for i, (ag, pr, ty, ec, label) in enumerate(STREAM_LEGAL):
        c = seen.get(i, 0)
        print(f"  bin{i:2d} {label:22s} (ag{ag},p{pr},t{ty},e{ec:#04x}): {c}  "
              f"{'OK' if c else 'not seen'}")
    unexp = seen.get(UNEXPECTED, 0)
    print(f"  UNEXPECTED (tuples not in the legal set): {unexp}")
    covered = sum(1 for i in range(len(STREAM_LEGAL)) if seen.get(i))
    print(f"\ntuples seen: {covered}/{len(STREAM_LEGAL)}; UNEXPECTED={unexp} "
          f"({'other packets flowing' if unexp else 'none outside the set'})")
    return 0 if passed else 1


def main(argv=None):
    ap = argparse.ArgumentParser(description="STREAM monitor CAM-tally coverage soak")
    ap.add_argument("--port", default='auto')
    ap.add_argument("--baud", type=int, default=115200)
    ap.add_argument("--channel", type=int, default=0)
    ap.add_argument("--minutes", type=float, default=10.0)
    ap.add_argument("--iters", type=int, default=None)
    ap.add_argument("--bytes", type=int, default=4096)
    args = ap.parse_args(argv)

    from uart_axi_bridge import UARTAxiBridge
    port = autodetect_port(args.baud, want=args.port)
    print(f"mon_coverage: port={port} "
          f"{'iters=' + str(args.iters) if args.iters else str(args.minutes) + ' min'}")
    with UARTAxiBridge(port, args.baud) as bridge:
        runner = CharacterizationRunner(bridge)
        return run_coverage(bridge, runner, A, channel=args.channel,
                            minutes=args.minutes, iters=args.iters, xfer_bytes=args.bytes)


if __name__ == "__main__":
    raise SystemExit(main())
