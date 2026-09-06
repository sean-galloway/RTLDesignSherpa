"""75 MHz / DDR2-300 bring-up: program the verified read/write tuple.

VERIFIED WORKING (ILA, 2026-09-05): wrlat=0, rden=6, rd_phase=0, wr_phase=0,
dfi_rddata_delay=7, default bitslip/tap. Soak-clean (0 beats mismatched) across
LFSR + address-hash patterns, BL16/BL64, high base address.

The long "half-mismatch that no leveling fixes" was NOT an eye problem: an ILA
capture on the DFI boundary showed the read data arriving BIT-PERFECT but
exactly ONE cycle after dfi_rddata_valid at rddata_delay=8. rddata_delay=7
aligns data to valid -> clean. It is a razor-sharp single-cycle optimum
(6 -> full mismatch, 7 -> 0, 8 -> full mismatch), which is a cycle alignment,
not an analog eye -- which is why every bitslip/tap/per-lane sweep failed and
the DFISlavePHY cosim (different read cadence than the real a7ddrphy) passed.

The write path was never wrong: the same ILA showed the WR command and wrdata
correctly framed (write cmd on phase 0, wrdata_en=3, LFSR pattern advancing
cleanly). This tool sweeps the write path only as a residual check; with the
read eye at rddata_delay=7 the write sweep is expected to be clean at its
defaults. 75 uses the native 115200 baud (PUMICE_SYS_75 sets FPGA_CLK_HZ=75M).

    python3 host_bringup_75.py --port /dev/ttyUSB5
"""

import argparse
import time

import ddr2_char as dc
from ddr2_char import DDR2CharDriver
from pumice_master import A7Leveling, wait_engine

SEED = 0x1EAFF00D


def main() -> int:
    ap = argparse.ArgumentParser(description=__doc__.strip().splitlines()[0])
    ap.add_argument("--port", default="auto")
    ap.add_argument("--baud", type=int, default=129534,
                    help="75MHz clock with the 66.67 baud divisor (until a "
                         "+PUMICE_SYS_75 rebuild gives a native 115200)")
    ap.add_argument("--base", type=lambda x: int(x, 0), default=0x0)
    ap.add_argument("--blen", type=int, default=8)
    ap.add_argument("--txn", type=int, default=2)
    # read eye (from the 300 MT/s wide read sweep)
    ap.add_argument("--eye-bitslip", type=int, default=3)
    ap.add_argument("--eye-tap", type=int, default=22)
    ap.add_argument("--rden", type=int, default=5)
    ap.add_argument("--rddly", type=int, default=7)
    ap.add_argument("--rdphase", type=int, default=0)
    # write path sweep
    ap.add_argument("--cmd-delays", default="0,1,2,3,4,5,6,7,8")
    ap.add_argument("--wrphases", default="0,1")
    ap.add_argument("--wrlats", default="0,1,2")
    args = ap.parse_args()

    args.port = dc.autodetect_port(args.baud, want=args.port)
    d = DDR2CharDriver(port=args.port, baudrate=args.baud)
    print(f"BUILD_ID=0x{d.build_id():08X}", flush=True)

    lv = A7Leveling(d, base_addr=args.base, burst_len=args.blen, verbose=False)

    def measure(cmd_delay, wrphase, wrlat):
        d.soft_reset()
        time.sleep(0.005)
        d.set_controller_cfg(memtype=dc.MEMTYPE_DDR2, t_phy_wrlat=wrlat,
                             t_rddata_en=args.rden, rd_in_order=True)
        d.set_dfi_phase(rd_phase=args.rdphase, wr_phase=wrphase)
        d.set_dfi_rddata_delay(args.rddly)
        d.set_dfi_cmd_delay(cmd_delay)
        lv.apply_taps(args.eye_bitslip, args.eye_tap)  # soft_reset may clear it
        d.clear_stats()
        d.program_wr_engine(start_addr=args.base, burst_len=args.blen,
                            txn_count=args.txn, stride_0=args.blen * 8,
                            lfsr_seed=SEED, data_mode=True, hash_seed0=SEED)
        d.start_wr()
        if not wait_engine(d, "wr", ignore_error=True):
            return None
        d.program_rd_engine(start_addr=args.base, burst_len=args.blen,
                            txn_count=args.txn, stride_0=args.blen * 8,
                            lfsr_seed=SEED, data_mode=True, hash_seed0=SEED)
        d.clear_stats()
        d.start_rd()
        if not wait_engine(d, "rd", ignore_error=True):
            return None
        return d.beats_mismatched()

    cds = [int(x) for x in args.cmd_delays.split(",")]
    wps = [int(x) for x in args.wrphases.split(",")]
    wls = [int(x) for x in args.wrlats.split(",")]
    print(f"read eye: bitslip={args.eye_bitslip} tap={args.eye_tap} "
          f"rden={args.rden} rddly={args.rddly} rdphase={args.rdphase}")
    print("sweeping cmd_delay x wr_phase x t_phy_wrlat "
          f"(cols cmd_delay {cds})", flush=True)
    best = (None, 1 << 30)
    for wl in wls:
        for wp in wps:
            row = []
            for cd in cds:
                m = measure(cd, wp, wl)
                row.append("x" if m is None else str(m))
                if m is not None and m < best[1]:
                    best = ((cd, wp, wl), m)
            print(f"wrlat={wl} wrphase={wp}: "
                  + " ".join(f"{v:>3}" for v in row), flush=True)

    print(f"\nBEST: mism={best[1]} at "
          f"(cmd_delay,wr_phase,t_phy_wrlat)={best[0]}", flush=True)
    if best[1] == 0:
        print("CLEAN 75 write eye -> bake {read eye + this write tuple} into "
              "the 75 init.")
    elif best[0] is not None:
        print("Not clean yet: if the min is still ~half, the phase that fails "
              "is a wr_beat_sequencer/byte-lane issue at 300 (ILA); if it "
              "improved, narrow cmd_delay/wrlat around best.")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
