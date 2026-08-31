# SPDX-License-Identifier: MIT
# SPDX-FileCopyrightText: 2026 sean galloway
"""Single source of truth for the char-harness CSR addresses.

The harness analog of stream_addrs.A(): every harness CSR address is resolved BY
NAME from harness_csr_regmap.py (which mirrors harness_csr.sv). NEVER hardcode
`HARNESS_CSR_BASE + 0x..` offsets in the TB or host tools -- when the harness
address map changes, only harness_csr_regmap.py changes and every consumer
follows automatically. Kept SEPARATE from stream_addrs.A() (STREAM IP registers)
so the two regmaps never leak into each other.

    from harness_addrs import H
    bridge.write(H("CTRL"), val)
    cyc = bridge.read(H("TIMER_CYCLES_LO"))
    cfg  = bridge.read(H("BUILD_CONFIG"))   # which flavour this bitstream is

Examples use LIVE registers only. They used to show OBS_RD_PROD and
CH5_KICK_ADDR, both long retired -- copying them gets you a KeyError or, worse,
a plausible address that reads back 0. Observer telemetry lives in the
observer's own window now: see bin/obs_addrs.py.
"""

from __future__ import annotations

import contextlib
import io
import logging
import os
from functools import lru_cache
from typing import Optional

from TBClasses.apb.register_map import RegisterMap

HARNESS_CSR_BASE = 0x0001_0000   # harness CSR block base in the char harness map


def _default_regmap() -> str:
    env = os.environ.get("HARNESS_REGMAP")
    if env:
        return env
    # THIS component's regmap, next to the generator that writes it. There used
    # to be a fallback that walked upward looking for the pre-migration copy
    # under projects/NexysA7/.../stream_char_framework/. That fallback was worse
    # than no fallback: after the component moved, every by-name lookup silently
    # resolved against the OLD tree's regmap, so registers added here read back
    # as "unknown" with no error. The old tree is deleted; resolve locally only,
    # and fail loudly rather than resolving against some other copy.
    local = os.path.join(os.path.dirname(os.path.dirname(os.path.abspath(__file__))),
                         "rtl", "harness_csr_regmap.py")
    if os.path.isfile(local):
        return local
    raise FileNotFoundError(
        f"harness_csr_regmap.py not found at {local}; regenerate it with "
        f"bin/gen_harness_regmap.py, or set HARNESS_REGMAP")


@lru_cache(maxsize=1)
def _regmap(path: Optional[str] = None) -> RegisterMap:
    log = logging.getLogger("harness_addrs")
    log.addHandler(logging.NullHandler())
    with contextlib.redirect_stdout(io.StringIO()):
        return RegisterMap(path or _default_regmap(), 32, 32, 0, log)


def H(name: str, base: int = HARNESS_CSR_BASE) -> int:
    """Absolute address of a HARNESS CSR register, by name (base + regmap offset)."""
    regs = _regmap().registers
    if name not in regs:
        raise KeyError(f"unknown HARNESS register {name!r}")
    return (base + int(regs[name]["address"], 16)) & 0xFFFF_FFFF


def has(name: str) -> bool:
    return name in _regmap().registers


def compose(name: str, **fields: int) -> int:
    """Compose a HARNESS CSR word by setting named FIELDS at their regmap
    offsets/widths (unspecified fields keep the reset default). Mirrors
    stream_addrs.compose -- for callers that need the word without a live bridge
    (e.g. the cocotb sim TB's async transport: uart_write(H("CTRL"),
    compose("CTRL", CLEAR_STATS=1))). For a live sync bridge, prefer
    harness_regs(bridge).REG.write(field=..)."""
    info = _regmap().registers.get(name)
    if info is None:
        raise KeyError(f"unknown HARNESS register {name!r}")
    word = int(info.get("default", "0x0"), 16)
    for fname, val in fields.items():
        fld = info.get(fname)
        if not isinstance(fld, dict) or "offset" not in fld:
            raise KeyError(f"unknown field {name}.{fname}")
        off = fld["offset"]
        hi, lo = (int(x) for x in off.split(":")) if ":" in off else (int(off), int(off))
        mask = ((1 << (hi - lo + 1)) - 1) << lo
        word = (word & ~mask) | ((int(val) << lo) & mask)
    return word & 0xFFFF_FFFF


def autodetect_port(baud: int = 115200, want: Optional[str] = None) -> str:
    """Find the ttyUSB the stream char harness is on.

    The USB-UART re-enumerates across reboots/replugs, so never hardcode the
    port. Probe each candidate by round-tripping the harness SCRATCH CSR (RW, no
    side effects); the board that echoes the magic back is ours. `want`: if the
    caller passed --port explicitly (not 'auto'), try that first. Requires
    `uart_axi_bridge` on sys.path (host entrypoints set this up before calling).
    """
    import glob
    from uart_axi_bridge import UARTAxiBridge

    scratch = H("SCRATCH")            # by-name; RW identity register
    magic = 0xC0FFEE5A
    cands = []
    if want and want != "auto":
        cands.append(want)
    cands += sorted(p for p in glob.glob("/dev/ttyUSB*") if p not in cands)

    for port in cands:
        try:
            with UARTAxiBridge(port, baud, timeout=0.4) as b:
                b.write(scratch, magic)
                if b.read(scratch) == magic:
                    try:
                        b.write(scratch, 0)   # leave no footprint
                    except Exception:
                        pass
                    print(f"[autodetect] stream harness found on {port}")
                    return port
        except Exception:
            continue
    raise SystemExit(
        f"[autodetect] no stream harness responded on any of: "
        f"{cands or '(no /dev/ttyUSB* present)'}. "
        f"Is the board powered and programmed with stream_char.bit?")


def harness_regs(bridge, base: int = HARNESS_CSR_BASE):
    """By-name + field-sugar accessor for the harness CSRs over a byte-bridge.

    Returns a `UartRegisterMap` bound to the harness CSR window and backed by the
    same regmap `H()` resolves from, so nothing is hardcoded. Field-level access
    uses the `regs.<REG>.<field>` sugar:

        regs = harness_regs(bridge)
        regs.CTRL.write(start_wr=1)             # self-clearing pulse
        regs.TIMER_EXPECTED_BEATS.write_word(n)  # whole-word write
        if regs.STATUS.init_done: ...           # read one field
        regs.OBS_HIST_SEL.bin = 3               # read-modify-write one field
        cyc = regs.TIMER_CYCLES_LO.read()       # whole-word read

    For a raw absolute address (e.g. building a loop over a register family) use
    `regs.addr("TIMER_CYCLES_LO")` or the module-level `H("TIMER_CYCLES_LO")`.
    """
    from TBClasses.harness.uart_register_map import UartRegisterMap
    return UartRegisterMap(bridge, start_address=base,
                           regmap_file=_default_regmap())


# ---------------------------------------------------------------------------
# Build identity (harness_csr 0x1D0-0x1D8). BUILD_ID names the harness family;
# these say WHICH BUILD of it is on the board. Without them a host infers the
# flavor from whichever .bit was programmed last, and a cone that was compiled
# out reads as a monitor that missed a fault.
# ---------------------------------------------------------------------------


def build_info(bridge) -> dict:
    """Decode the harness build-identity registers."""
    # By NAME, including the field extraction -- the offsets and bit positions
    # live in the generated regmap. An earlier version of this reached the
    # BUILD_* registers as base + 0x1D0 because they were not yet in the regmap
    # table; the fix was to add them there, not to keep the arithmetic.
    regs = harness_regs(bridge)
    return {
        "build_id":     bridge.read(H("BUILD_ID")),
        "version":      bridge.read(H("BUILD_VERSION")),
        "num_channels": regs.field("BUILD_CONFIG", "NUM_CHANNELS"),
        "error_flavor": regs.field("BUILD_CONFIG", "ERROR_FLAVOR"),
        # Present since the union build: ERROR_FLAVOR alone cannot distinguish
        # "error cone only" from "error cone AND the rest".
        "main_cones":   regs.field("BUILD_CONFIG", "MAIN_CONES"),
        "use_monitors": regs.field("BUILD_CONFIG", "USE_MONITORS"),
        "gen_mon":      regs.field("BUILD_CONFIG", "GEN_MON"),
        "n_profile":    bridge.read(H("BUILD_N_PROFILE")),
        # Read, never assumed. Bandwidth is bytes_per_cycle * clk_hz, so a host
        # that guesses the frequency reports plausible-looking numbers that are
        # wrong by exactly the ratio it guessed wrong by -- 100 MHz assumed
        # against a 90 MHz board is +11% on every GB/s figure, silently.
        "clk_hz":       bridge.read(H("BUILD_CLK_HZ")),
    }


def describe_build(bridge) -> str:
    b = build_info(bridge)
    err, main = b["error_flavor"], b["main_cones"]
    flavor = ("all-cones"          if err and main else
              "error-only"         if err          else
              "all-except-error"   if main         else
              "no-datapath-cones")
    mhz = (b.get("clk_hz") or 0) / 1e6
    return (f"build v{b['version']} {flavor} nch={b['num_channels']} "
            f"clk={mhz:.1f}MHz "
            f"n_profile={b['n_profile']} monitors={b['use_monitors']} "
            f"gen_mon={b['gen_mon']}")
