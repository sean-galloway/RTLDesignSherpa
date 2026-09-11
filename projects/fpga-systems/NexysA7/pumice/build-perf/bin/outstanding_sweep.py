#!/usr/bin/env python3
# SPDX-License-Identifier: MIT
# SPDX-FileCopyrightText: 2026 sean galloway
"""Board sweep: read bandwidth vs OUTSTANDING transactions, at a fixed AxLEN.

The companion to axlen_sweep.py, and the direct measurement of the same model
from the other axis. Little's law on this path says

    beats/cycle = min(outstanding x AxLEN / (latency + AxLEN), 0.95)

so bandwidth climbs linearly with outstanding until the pipe is full and is
flat after. The knee is at roughly (latency / AxLEN) transactions -- about 49
at AxLEN=1 and 13 at AxLEN=4 for pumice's ~49-cycle read. Sweeping AxLEN moves
the knee; sweeping outstanding walks up to it and past it, which is the shape
that says "latency-bound" rather than "some per-transaction overhead".

Why this script did not exist until now: nothing could reach the knee.
GEN_MAX_OUTSTANDING was 8, and the generated data bridges gated the address
channel on a bridge_cam with DEPTH(16), so the whole engine was capped at 16
in flight no matter what the generators were told. Both limits sat below the
knee for every AxLEN under 8, which made every curve look flat-then-flat. The
bridges are gone (char_gen_unit merges the generators directly onto s_axi) and
the ceiling is 32, dialled at runtime by AXI_ATTR.max_outstanding -- so one
bitstream produces the whole curve.

Read the flat tail as confirmation, not as filler: if bandwidth stops climbing
at N and the predicted knee is at N, the model holds and the remaining gap to
peak is latency. If it stops climbing well BEFORE the predicted knee,
something else is the limit and the number it stopped at names it.

    PUMICE_MC_CLK_HZ=75000000 python3 bin/outstanding_sweep.py    # from build-perf/
    AXLENS=1,4 OUTSTANDING=1,2,4,8,16,32 python3 bin/outstanding_sweep.py
"""
import os
import sys

sys.path.insert(0, 'host')
import ddr2_char as dc
from ddr2_char import DDR2CharDriver
import pumice_master as pm
import pumice_char as pc

CLK_MHZ  = float(os.environ.get("PUMICE_MC_CLK_HZ", "75000000")) / 1e6
PEAK_MBS = 8 * CLK_MHZ          # 8 bytes/beat at one beat/cycle

AXLENS      = [int(x) for x in os.environ.get("AXLENS", "1,2,4,8").split(",")]
OUTSTANDING = [int(x) for x in os.environ.get("OUTSTANDING", "1,2,4,8,12,16,24,32").split(",")]


def main() -> int:
    drv = DDR2CharDriver(port=dc.autodetect_port(115200, 'auto'))
    st = pm.SimpleTest(drv, base_addr=0, level_cache='host/level_cache.json')
    st.init(do_leveling=True)
    cfg  = pc.CONFIGS['open_page']
    geom = pc.DEFAULT_GEOM

    for blen in AXLENS:
        print(f"\n=== AxLEN {blen} "
              f"({blen * 8} B/burst, peak {PEAK_MBS:.0f} MB/s) ===")
        print(f"{'outst':>6} {'rd MB/s':>9} {'%peak':>7} {'lat cyc':>8} "
              f"{'predicted':>10} {'err':>7}")
        prev = None
        knee = None
        last_lat = None
        for n in OUTSTANDING:
            sc = pc.Scenario(name=f"os{n}_bl{blen}", family=pc.FAM_ROW_MAJOR,
                             burst_len=blen, txn_count=4000, gap=0,
                             max_outstanding=n)
            r = pc.measure(drv, sc, cfg=cfg, geom=geom, base_addr=0,
                           clk_mhz=CLK_MHZ, timeout_s=40.0)
            lat  = r.rd_avg_latency_cyc
            pred = min((n * blen) / (lat + blen), 0.95) * PEAK_MBS
            err  = (r.rd_bw_mb_s - pred) / pred * 100 if pred else 0.0
            print(f"{n:6} {r.rd_bw_mb_s:9.1f} {r.rd_bw_mb_s / PEAK_MBS * 100:6.1f}% "
                  f"{lat:8.1f} {pred:10.1f} {err:6.1f}%"
                  + ("" if r.ok else "   FAILED"))
            # The knee is the first point that stops buying bandwidth. 3% is
            # above this rig's run-to-run spread and well below the ~2x steps
            # the sweep takes, so it fires on a real plateau rather than noise.
            if prev is not None and knee is None and r.rd_bw_mb_s < prev * 1.03:
                knee = n
            prev = r.rd_bw_mb_s
            last_lat = lat
        if knee and last_lat:
            want = last_lat / blen
            print(f"  knee at ~{knee} outstanding; model wants ~{want:.0f} "
                  f"(measured latency {last_lat:.0f} / AxLEN {blen})")
            if knee < want * 0.7:
                print(f"  knee is EARLY -- something other than latency is "
                      f"capping this at {knee}. That number names the limit.")
        else:
            print(f"  no knee inside {max(OUTSTANDING)} outstanding -- still "
                  f"climbing, so the ceiling is the limit, not the DRAM")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
