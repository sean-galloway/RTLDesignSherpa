#!/usr/bin/env python3
# SPDX-License-Identifier: MIT
# SPDX-FileCopyrightText: 2026 sean galloway
"""By-name register access for the char harness over the UART/AXIL bridge.

Adapts the house register methodology — `bin/TBClasses/apb/register_map.py`
(`RegisterMap`, which loads a PeakRDL-generated `top_block`) — for the AXIL-
over-UART transport used by the char harness. `RegisterMap` is reused *as-is*
for register/field parsing and offset/mask math; only the transaction emission
differs: instead of building APBPackets, `UartRegisterMap` drives an injected
bridge's `write(addr, val)` / `read(addr)`.

This gives host/sim programs `instance.register_name = value` access (plus an
optional read-modify-write) with no hardcoded offsets — the offsets come from
`harness_csr_regmap.py`, generated from `harness_csr.rdl`. Because the bridge
is injected, the identical calls run against the FPGA (pyserial) or a cocotb
UART master, so silicon and sim are byte-for-byte equivalent.

    from TBClasses.harness.uart_register_map import UartRegisterMap
    regs = UartRegisterMap(bridge, start_address=0x0001_0000,
                           regmap_file="<proj>/harness_csr_regmap.py")
    regs.write("CTRLR_CFG", memtype=0, t_phy_wrlat=4, t_rddata_en=6)  # merged word
    regs.write("CTRL", clear_stats=1)                                 # pulse
    if regs.field("STATUS", "init_done"):
        ...
    regs.write("OBS_HIST_SEL", rmw=True, bin=3)   # preserve other fields

Project-agnostic: pass the project's PeakRDL-generated `<top>_regmap.py` path
and the harness base address. Shared by the NexysA7 char flows (ddr2/stream/cdc).
"""

from __future__ import annotations

import contextlib
import io
import logging
from typing import Optional

from TBClasses.apb.register_map import RegisterMap  # bin/ on PYTHONPATH via env_python


class _RegisterHandle:
    """Attribute-style view of ONE register, for `dev.<REG>.<field>` access.

    Returned by `UartRegisterMap.__getattr__` / `Device.__getattr__`. Reading a
    field attribute reads the register and extracts the field; assigning a field
    attribute does a read-modify-write (preserving the other fields). For a
    multi-field update in one bus transaction use `.write(a=1, b=2)`; for the
    whole word use `.read()` / `.write_word(v)`.

        pumice.SCHED_TUNING.force_inorder = 1          # RMW one field
        if harness.STATUS.init_done: ...               # read one field
        pumice.SCHED_TUNING.write(force_inorder=1, lookahead_active=4)  # batched
    """

    __slots__ = ("_rm", "_reg")

    def __init__(self, rm: "UartRegisterMap", reg: str):
        object.__setattr__(self, "_rm", rm)
        object.__setattr__(self, "_reg", reg)

    def __getattr__(self, field: str) -> int:
        return self._rm.field(self._reg, field)

    def __setattr__(self, field: str, value: int) -> None:
        self._rm.write(self._reg, rmw=True, **{field: value})

    def read(self) -> int:
        return self._rm.read(self._reg)

    def write(self, rmw: bool = False, **fields: int) -> int:
        return self._rm.write(self._reg, rmw=rmw, **fields)

    def write_word(self, value: int) -> None:
        self._rm.write_word(self._reg, value)

    def __repr__(self) -> str:
        return f"<reg {self._reg} @ {self._rm.addr(self._reg):#x}>"


class UartRegisterMap:
    """Named register access over a byte-bridge, backed by the PeakRDL regmap.

    Composes a `RegisterMap` (for the parsed register/field model + offset/mask
    helpers) with an injected bridge that speaks `read(addr)->int|None` and
    `write(addr, val)->bool` (the char harness `UARTAxiBridge`).
    """

    DATA_WIDTH = 32

    def __init__(self, bridge, start_address: int, regmap_file: str,
                 log: Optional[logging.Logger] = None):
        self.bridge = bridge
        self.start_address = start_address
        self.data_mask = (1 << self.DATA_WIDTH) - 1
        log = log or logging.getLogger("uart_regmap")
        # RegisterMap.__init__ pprints the whole map to stdout (debug wart in
        # the shared class); swallow it so the host tool stays quiet.
        with contextlib.redirect_stdout(io.StringIO()):
            self._rm = RegisterMap(regmap_file, self.DATA_WIDTH,
                                   self.DATA_WIDTH, start_address, log)

    # ----- attribute-style register access (dev.<REG>.<field>) -------------
    def __getattr__(self, name: str) -> "_RegisterHandle":
        # __getattr__ runs only when normal lookup fails, so methods/attrs are
        # unaffected. Expose each RDL register as an attribute handle.
        if name.startswith("_"):
            raise AttributeError(name)
        rm = self.__dict__.get("_rm")
        if rm is not None and name in rm.registers:
            return _RegisterHandle(self, name)
        raise AttributeError(name)

    # ----- introspection ---------------------------------------------------
    @property
    def registers(self) -> dict:
        return self._rm.registers

    def _reg(self, reg: str) -> dict:
        if reg not in self._rm.registers:
            raise KeyError(f"unknown register {reg!r}")
        return self._rm.registers[reg]

    def addr(self, reg: str) -> int:
        """Absolute bus address of a register (start_address + offset)."""
        off = int(self._reg(reg)["address"], 16)
        return (self.start_address + off) & self._rm.addr_mask

    def _field_lo_width(self, reg: str, field: str):
        info = self._reg(reg)
        finfo = info.get(field)
        if not isinstance(finfo, dict) or finfo.get("type") != "field":
            raise KeyError(f"unknown field {reg}.{field}")
        lo, hi = self._rm._parse_offset(finfo["offset"])  # (low, high)
        return lo, (hi - lo + 1)

    # ----- reads -----------------------------------------------------------
    def read(self, reg: str) -> int:
        """Read the whole 32-bit register word by name."""
        val = self.bridge.read(self.addr(reg))
        if val is None:
            raise IOError(f"bridge read failed at register {reg}")
        return val & self.data_mask

    def field(self, reg: str, field: str, word: Optional[int] = None) -> int:
        """Extract a named field. Reads the register if `word` not supplied."""
        if word is None:
            word = self.read(reg)
        lo, width = self._field_lo_width(reg, field)
        return (word >> lo) & ((1 << width) - 1)

    # ----- writes ----------------------------------------------------------
    def write_word(self, reg: str, value: int) -> None:
        """Write a raw 32-bit value to a register by name."""
        if not self.bridge.write(self.addr(reg), value & self.data_mask):
            raise IOError(f"bridge write failed at register {reg}")

    def write(self, reg: str, rmw: bool = False, **fields: int) -> int:
        """Write named fields of a register.

        Fields not named are written as 0 unless `rmw=True`, in which case the
        register is read first and only the named fields are spliced in (a true
        read-modify-write round-trip over the bridge). Returns the word written.
        """
        word = self.read(reg) if rmw else 0
        for name, val in fields.items():
            lo, width = self._field_lo_width(reg, name)
            mask = ((1 << width) - 1) << lo
            word = (word & ~mask) | ((int(val) << lo) & mask)
        self.write_word(reg, word)
        return word & self.data_mask
