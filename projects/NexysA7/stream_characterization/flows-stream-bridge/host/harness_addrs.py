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
    bridge.write(H("KICK_GO"), mask)
    cyc = bridge.read(H("TIMER_CYCLES_LO"))
    prod = bridge.read(H("OBS_RD_PROD"))
    addr = H("CH5_KICK_ADDR")            # kick-addr shadow regs, split around 0xC0
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
    d = os.path.dirname(os.path.abspath(__file__))
    rel = "projects/NexysA7/stream_characterization/stream_char_framework/rtl/harness_csr_regmap.py"
    for _ in range(12):
        cand = os.path.join(d, rel)
        if os.path.isfile(cand):
            return cand
        d = os.path.dirname(d)
    raise FileNotFoundError("harness_csr_regmap.py not found; set HARNESS_REGMAP")


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
        regs.KICK_GO.write_word(mask)           # whole-word write
        if regs.STATUS.init_done: ...           # read one field
        regs.OBS_HIST_SEL.bin = 3               # read-modify-write one field
        prod = regs.OBS_RD_PROD.read()          # whole-word read

    For a raw absolute address (e.g. per-channel CH{n}_KICK_ADDR in a loop) use
    `regs.addr("CH5_KICK_ADDR")` or the module-level `H("CH5_KICK_ADDR")`.
    """
    from TBClasses.harness.uart_register_map import UartRegisterMap
    return UartRegisterMap(bridge, start_address=base,
                           regmap_file=_default_regmap())
