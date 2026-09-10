#!/usr/bin/env python3
"""LiteDRAM apples-to-apples characterization host (Nexys A7).

The SAME program that measures pumice, pointed at the LiteDRAM harness:
same UART bridge, same address map (bridge_ddr2_char_axil), same harness_csr,
same chargen_regs generator array, same perf meters and the same
pumice_char scenario suites / CSV writer. The one difference is the
controller behind the AXI port, and that is exactly what the two flows are
there to compare.

What is skipped: every pumice CSR write. LiteDRAM's BIOS initialises and
calibrates the DRAM itself, so there is no geometry to program, no leveling
to run and no paging / scheduling / refresh knob to sweep. The driver
subclass below turns those calls into no-ops so the shared suite runs
unchanged, and a single `litedram` config stands in for the pumice presets.

    make host-litedram_char ARGS="--char-profile matrix --char-scale 1000 \
                                  --csv ../char_results/litedram_YYYY-MM-DD.csv"
"""
from __future__ import annotations

import argparse
import os
import sys
import time
from typing import Dict, List, Optional

# Reuse the pumice host layer in place (build-perf/host) -- no copy.
_HERE = os.path.dirname(os.path.abspath(__file__))
_PUMICE_HOST = os.path.abspath(os.path.join(_HERE, "..", "..", "..", "build-perf", "host"))
if _PUMICE_HOST not in sys.path:
    sys.path.insert(0, _PUMICE_HOST)

import ddr2_char as dc                                  # noqa: E402
from ddr2_char import DDR2CharDriver                    # noqa: E402
import pumice_master as pm                              # noqa: E402  (wait_engine, get_board)
import pumice_char as pc                                # noqa: E402
from boards import get_board                            # noqa: E402

BUILD_ID_LITEDRAM = 0x4C44_5232   # "LDR2" -- char_engine_harness BUILD_ID
# litedram_hp.yml sys_clk_freq: the user_clk the harness timer counts in.
LITEDRAM_CLK_MHZ = 75.0


class LiteDRAMCharDriver(DDR2CharDriver):
    """DDR2CharDriver with the pumice-controller surface neutralised.

    The bridge's ddr2_apb window is terminated in the LiteDRAM harness
    (PREADY=1, reads 0), so a stray pumice write would complete harmlessly;
    making them no-ops here keeps the log honest about what was programmed.
    """
    BUILD_ID_MAGIC = BUILD_ID_LITEDRAM

    # --- pumice controller CSRs: nothing behind the window --------------
    def set_controller_cfg(self, **_) -> None: pass
    def set_jedec_timings(self, mc_clk_hz: float) -> dict: return {}
    def set_dfi_phase(self, *_, **__) -> None: pass
    def set_dfi_cmd_delay(self, *_, **__) -> None: pass
    def set_dfi_rddata_delay(self, *_, **__) -> None: pass
    def set_mr(self, *_, **__) -> None: pass
    def set_mr0(self, *_, **__) -> None: pass
    def init_restart(self) -> None: pass
    def program_geometry(self, *_, **__) -> None: pass
    def set_addr_map_scheme(self, *_, **__) -> None: pass
    def set_page_policy(self, *_, **__) -> None: pass
    def set_page_mode(self, *_, **__) -> None: pass
    def set_page_access_cfg(self, *_, **__) -> None: pass
    def set_page_rbl_cfg(self, *_, **__) -> None: pass
    def set_refresh(self, *_, **__) -> None: pass
    def set_refresh_interval(self, *_, **__) -> None: pass
    def set_sched_policy(self, *_, **__) -> None: pass

    def soft_reset(self, restore_geometry: bool = False, **_) -> None:
        """CTRL.soft_reset resets the generators AND chargen_regs (so every
        generator must be re-programmed before the next GO -- measure() does
        that per scenario). litedram_core is not on the datapath reset (no
        reset input on the user port); the harness holds the reset off until
        the write side is quiescent so the core never sees a half burst."""
        self.regs.write("CTRL", soft_reset=1)

    # --- LiteDRAM init: the BIOS asserts init_done when calibration passes --
    def wait_init(self, timeout_s: float = 10.0) -> dc.Status:
        deadline = time.monotonic() + timeout_s
        while True:
            s = self.status()
            if s.init_fail:
                raise RuntimeError("LiteDRAM reports init_error -- BIOS calibration failed")
            if s.init_done:
                return s
            if time.monotonic() > deadline:
                raise TimeoutError(f"LiteDRAM init_done not seen within {timeout_s} s "
                                   "(core regenerated WITHOUT a BIOS? see regen.sh --bios)")
            time.sleep(0.05)


class LiteDRAMConfig(pc.ControllerConfig):
    """The one 'config' LiteDRAM has: whatever litedram_hp.yml generated
    (ROW_BANK_COL, open page with auto-precharge, cmd_buffer_depth 16).
    apply() programs nothing -- the harness-side rd_in_order/CTRLR_CFG bit is
    a pumice-era engine knob the current generator array does not read."""
    def apply(self, drv: DDR2CharDriver) -> None:
        return None


LITEDRAM = LiteDRAMConfig("litedram", rd_in_order=True, jedec_timings=False)


def litedram_probe():
    """'is this link the LiteDRAM char harness?' -- BUILD_ID by name."""
    def probe(link) -> bool:
        return DDR2CharDriver(bridge=link.bridge()).build_id() == BUILD_ID_LITEDRAM
    return probe


def run(drv: LiteDRAMCharDriver, *, profile: Optional[str], level: str,
        txn_scale: int, base_addr: int, timeout_s: float,
        progress) -> List[pc.CharRecord]:
    """The pumice profile's scenario grid, under the single LiteDRAM config.

    A profile in pumice_char names (configs x scenarios); the configs are
    pumice CSR presets that mean nothing here, so only the scenario half is
    taken and every record is tagged 'litedram'."""
    if profile:
        p = pc.RUN_PROFILES[profile]
        level, families = p["level"], p["families"]
    else:
        families = None
    return pc.run_matrix(drv, configs=[LITEDRAM], level=level,
                         families=families, txn_scale=txn_scale,
                         base_addr=base_addr, timeout_s=timeout_s,
                         clk_mhz=LITEDRAM_CLK_MHZ, progress=progress)


def main() -> int:
    ap = argparse.ArgumentParser(description="LiteDRAM DDR2 characterization (pumice A/B)")
    ap.add_argument("--board", default="nexys_a7_100t", help="board registry name")
    ap.add_argument("--port", default="auto", help="UART device")
    ap.add_argument("--baud", type=int, default=115200)
    ap.add_argument("--base", type=lambda x: int(x, 0), default=0x0,
                    help="DRAM base byte address for the sweeps")
    ap.add_argument("--char-level", default="medium",
                    help="scenario depth (basic/medium/full) when no --char-profile")
    ap.add_argument("--char-scale", type=int, default=1,
                    help="workload multiplier; ~1000 for a board run (as pumice)")
    ap.add_argument("--char-profile", default=None,
                    help=f"pumice_char run profile, scenario half only: "
                         f"{sorted(pc.RUN_PROFILES)}")
    ap.add_argument("--timeout", type=float, default=20.0,
                    help="per-phase engine timeout (s)")
    ap.add_argument("--csv", default=None, help="write records to this CSV path")
    ap.add_argument("--status", action="store_true",
                    help="print build/init/gen status and exit (no sweep)")
    args = ap.parse_args()

    board = get_board(args.board)
    args.port = board.find_uart_port(probe=litedram_probe(), want=args.port,
                                     label="LiteDRAM char harness")
    drv = LiteDRAMCharDriver(port=args.port, baudrate=args.baud)

    bid = drv.build_id()
    if bid != BUILD_ID_LITEDRAM:
        print(f"WARNING: BUILD_ID=0x{bid:08X} (expected 0x{BUILD_ID_LITEDRAM:08X} 'LDR2')"
              " -- is the pumice bitstream still loaded?", file=sys.stderr)
    info = drv.build_info()
    print("[litedram] build: " + " ".join(f"{k}={v}" for k, v in info.items()),
          file=sys.stderr)
    s = drv.wait_init(timeout_s=10.0)
    print(f"[litedram] init_done={s.init_done} init_fail={s.init_fail}", file=sys.stderr)
    gen = drv.gen_config()
    drv.num_gen = min(gen["num_wr_gen"], gen["num_rd_gen"])
    print("[litedram] generators: " + " ".join(f"{k}={v}" for k, v in gen.items()),
          file=sys.stderr)
    if args.status:
        print(f"STATUS = {drv.status()}")
        return 0

    drv.soft_reset()
    time.sleep(0.01)
    drv.clear_stats()

    def _progress(name: str, i: int, n: int) -> None:
        print(f"[char {i}/{n}] {name}", file=sys.stderr)

    recs = run(drv, profile=args.char_profile, level=args.char_level,
               txn_scale=args.char_scale, base_addr=args.base,
               timeout_s=args.timeout, progress=_progress)
    print()
    pc.print_report(recs)
    if args.csv:
        pc.write_csv(recs, args.csv)
        print(f"\nwrote {len(recs)} records to {args.csv}")
    n_ok = sum(1 for r in recs if r.ok)
    return 0 if n_ok == len(recs) else 1


if __name__ == "__main__":
    sys.exit(main())
