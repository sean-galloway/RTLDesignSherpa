#!/usr/bin/env python3
# SPDX-License-Identifier: MIT
# SPDX-FileCopyrightText: 2026 sean galloway
"""Walk every register of every endpoint ON THE BOARD, by name.

Answers with numbers instead of argument: is each endpoint reachable, does it
hold its reset value, and does each writable field take a write and read back?

The walk itself is NOT here -- it is RegisterMap.walk() in
bin/TBClasses/apb/register_map.py. The map already knows every name, address,
default and per-field sw attribute, so one implementation in the base class
serves every block, and the SAME check runs in cocotb and against silicon
because the caller supplies only read/write.

This file is just the board-side wiring: which regmaps, which bases, and a
UART bridge for the accessors.

Endpoints (bases owned by the address modules, never re-typed here):

    stream_apb   STREAM functional + MON regfile   stream_addrs.STREAM_APB_BASE
    harness_csr  char-harness CSRs                 harness_addrs.HARNESS_CSR_BASE
    slvmon_apb   slave-role observer (obs_regs)   obs_addrs.SLAVE_OBS_APB_BASE
    obs_apb      axi4_intf_master_observer regblock       obs_addrs.OBS_APB_BASE

The last two are why this exists. Until the declaration-order fix they were
wired through IMPLICIT 1-BIT WIRES -- the bridge drove 32 bits, the block
expected 32 bits, and the net between was one bit wide. Every board result that
configured the observer or the slave monitors was meaningless, and nothing said
so: writes "succeeded" and reads returned something.

DESTRUCTIVE -- run it FIRST, or reprogram afterwards.

The walk drives patterns into every writable register and then restores the RDL
DEFAULT. For the monitors that default is PKT_MASK=0xFFFF, i.e. drop every
packet type, so a coverage run immediately afterwards sees 0/8 tuples and looks
like a broken design. Observed exactly that; `make program` restores 5/8.
Reset defaults are the safe-but-silent state, not the working state.

Usage:
    source env_python
    make host-reg_walk
    make host-reg_walk ARGS="--endpoint obs --verbose"
"""
import argparse
import contextlib
import io
import logging
import os
import sys

_here = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, os.path.abspath(os.path.join(_here, "..", "..", "bin")))
import stream_env  # noqa: F401,E402  (import side effect: sys.path setup)

from TBClasses.apb.register_map import RegisterMap          # noqa: E402
from harness_addrs import autodetect_port                   # noqa: E402
from uart_axi_bridge import UARTAxiBridge                   # noqa: E402

REPO = stream_env.repo_root()


def _endpoints():
    """(key, label, regmap path, base) -- bases come from the address modules."""
    import stream_addrs
    import harness_addrs
    import obs_addrs

    return [
        ("stream", "stream_apb  STREAM + MON",
         os.path.join(REPO, "projects/components/dmas/stream/rtl/stream_regmap.py"),
         stream_addrs.STREAM_APB_BASE),
        ("harness", "harness_csr",
         os.path.join(REPO, "projects/fpga-systems/Genesys2/stream/rtl/harness_csr_regmap.py"),
         harness_addrs.HARNESS_CSR_BASE),
        # slvmon_apb @ 0x180000 is the SLAVE-ROLE OBSERVER, not dma_slave_monitors.
        # stream_harness.sv:452 routes it to u_slave_observer, and
        # axi4_intf_slave_observer.sv instantiates obs_regs_top -- the SAME
        # regblock the master observer has at 0x190000. Two instances, one map,
        # two bases.
        #
        # This walked it with slvmon_device's map, which describes the retired
        # dma_slave_monitors regblock. The two are unrelated at the same offsets:
        # at 0x024 obs_regs has AXIS_MASK1 where slvmon_regs had
        # RDSLV_ADDR_RANGE_HIGH. So a walk -- or any configuration written
        # through this window -- touched the wrong fields and nothing complained.
        # (STREAM TASK-073.)
        ("slvmon", "slvmon_apb  axi4_intf_slave_observer (obs_regs)",
         obs_addrs._regmap_path(),
         obs_addrs.SLAVE_OBS_APB_BASE),
        ("obs", "obs_apb     axi4_intf_master_observer (obs_regs)",
         obs_addrs._regmap_path(),
         obs_addrs.OBS_APB_BASE),
    ]


def main(argv=None):
    ap = argparse.ArgumentParser(description=__doc__.split("\n")[0])
    ap.add_argument("--port", default="auto")
    ap.add_argument("--baud", type=int, default=115200)
    ap.add_argument("--endpoint", default="all")
    ap.add_argument("--verbose", "-v", action="store_true")
    args = ap.parse_args(argv)

    logging.basicConfig(level=logging.ERROR)
    log = logging.getLogger("reg_walk")
    log.setLevel(logging.ERROR)

    port = autodetect_port() if args.port == "auto" else args.port
    todo = [e for e in _endpoints() if args.endpoint in ("all", e[0])]
    if not todo:
        print(f"unknown endpoint {args.endpoint!r}")
        return 2

    print(f"reg_walk: port={port}  endpoints={[e[0] for e in todo]}")
    all_fails = []
    with UARTAxiBridge(port, args.baud) as br:
        for key, label, path, base in todo:
            if not os.path.exists(path):
                print(f"  {label:<38} SKIP -- no regmap at {path}")
                continue
            # RegisterMap pprints the whole register dict on construction (a
            # debug aid that swamps a 139-register walk).
            with contextlib.redirect_stdout(io.StringIO()):
                rm = RegisterMap(path, apb_data_width=32, apb_addr_width=32,
                                 start_address=base, log=log)
            fails = rm.walk(read=br.read, write=br.write)
            status = "PASS" if not fails else f"FAIL ({len(fails)})"
            print(f"  {label:<38} {len(rm.registers):4d} regs  {status}")
            if fails and args.verbose:
                for f in fails[:20]:
                    print(f"      {f}")
                if len(fails) > 20:
                    print(f"      ... {len(fails)-20} more")
            all_fails += fails

    print()
    if not all_fails:
        print("ALL ENDPOINTS PASS -- every register reachable, reset value "
              "correct, writable fields take and read back")
        return 0
    print(f"FAILURES: {len(all_fails)}"
          + ("" if args.verbose else "  (re-run with --verbose for the list)"))
    return 1


if __name__ == "__main__":
    sys.exit(main())
