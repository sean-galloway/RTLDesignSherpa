#!/usr/bin/env python3
"""OPEN-vs-CLOSE page-policy A/B on the board (runtime-policy bitstream).

Before the fix, the page-policy CSR was inert (compile-time CLOSE) so OPEN==CLOSE
at ~12.7 MB/s. This drives the *runtime* cfg_page_policy_i and measures streaming
(incremental, same-row) + row_major bandwidth under each policy, so the batching
win from the committed fix is visible on silicon.

    ./compare_page_policy.py --port /dev/ttyUSB2 [--txn 2000 --bl 16]
"""
import argparse
import sys

import ddr2_char as dc
from ddr2_char import DDR2CharDriver
import pumice_char as pc
from pumice_master import SimpleTest

# Board-specific DFI knobs (see project_pumice_board_perf_char):
#   t_phy_wrlat=0 is MANDATORY on this board (default 4 misaligns the write and
#   leveling finds "no passing tap"). rddata_delay=8 / rd_phase=0 / t_rddata_en=6.
WRLAT = 0
T_RDDATA_EN = 6


def main() -> int:
    ap = argparse.ArgumentParser(description=__doc__,
                                 formatter_class=argparse.RawDescriptionHelpFormatter)
    ap.add_argument("--port", default="auto")
    ap.add_argument("--baud", type=int, default=115200)
    ap.add_argument("--base", type=lambda x: int(x, 0), default=0x0)
    ap.add_argument("--rd-phase", type=int, default=0)
    ap.add_argument("--rd-delay", type=int, default=8)
    ap.add_argument("--txn", type=int, default=2000,
                    help="txn_count per phase (keep < ~4790 read-wedge ceiling)")
    ap.add_argument("--bl", type=int, default=16, help="burst length (beats)")
    ap.add_argument("--clk-mhz", type=float, default=100.0)
    ap.add_argument("--families", default="incremental,row_major",
                    help="comma list: incremental,row_major")
    args = ap.parse_args()

    args.port = dc.autodetect_port(args.baud, want=args.port)

    drv = DDR2CharDriver(port=args.port, baudrate=args.baud)
    bid = drv.build_id()
    if bid != 0x4444_5232:
        print(f"WARNING: BUILD_ID=0x{bid:08X} (expected 0x44445232 'DDR2')")

    # Init + leveling once, with the board's t_phy_wrlat=0.
    st = SimpleTest(drv, base_addr=args.base, rd_phase=args.rd_phase,
                    rddata_delay=args.rd_delay, t_phy_wrlat=WRLAT,
                    t_rddata_en=T_RDDATA_EN)
    st.init(do_leveling=True)
    if st.level and not st.level.ok:
        print(f"WARNING: leveling not clean: {st.level.notes}")

    _fam_map = {"incremental": pc.FAM_INCREMENTAL, "row_major": pc.FAM_ROW_MAJOR}
    families = [_fam_map[f.strip()] for f in args.families.split(",") if f.strip()]
    policies = [("CLOSE", dc.PAGE_POLICY_CLOSE), ("OPEN", dc.PAGE_POLICY_OPEN)]

    print(f"\n{'family':<14}{'policy':<7}{'wr MB/s':>10}{'rd MB/s':>10}"
          f"{'cyc/beat(rd)':>14}{'ok':>5}")
    print("-" * 60)
    results = {}
    for fam in families:
        sc = pc.Scenario(name=f"{fam}_bl{args.bl}", family=fam,
                         burst_len=args.bl, txn_count=args.txn)
        for pname, pol in policies:
            cfg = pc.ControllerConfig(f"ab_{pname.lower()}",
                                      scheme=dc.SCHEME_ROW_MAJOR, page_policy=pol,
                                      lookahead=0, force_inorder=False,
                                      rd_in_order=True, t_phy_wrlat=WRLAT,
                                      t_rddata_en=T_RDDATA_EN)
            rec = pc.measure(drv, sc, cfg=cfg, base_addr=args.base,
                             clk_mhz=args.clk_mhz)
            cpb = (rec.rd_cycles / (sc.txn_count * sc.burst_len)) if rec.rd_cycles else 0.0
            results[(fam, pname)] = rec
            note = f"  {'; '.join(rec.notes)}" if getattr(rec, "notes", None) else ""
            print(f"{fam:<14}{pname:<7}{rec.wr_bw_mb_s:>10.1f}{rec.rd_bw_mb_s:>10.1f}"
                  f"{cpb:>14.1f}{('OK' if rec.ok else 'FAIL'):>5}{note}")

    print("\n=== OPEN vs CLOSE speedup (read MB/s) ===")
    for fam in families:
        c = results[(fam, "CLOSE")].rd_bw_mb_s
        o = results[(fam, "OPEN")].rd_bw_mb_s
        ratio = (o / c) if c else 0.0
        print(f"  {fam:<14} CLOSE={c:6.1f}  OPEN={o:6.1f}  ->  {ratio:4.2f}x")
    return 0


if __name__ == "__main__":
    sys.exit(main())
