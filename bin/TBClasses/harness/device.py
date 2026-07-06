# SPDX-License-Identifier: MIT
# SPDX-FileCopyrightText: 2026 sean galloway
"""Generic named IP-instance device over an injected bridge.

`Device` is the IP-agnostic spine for "one instance of a register-mapped IP,
addressed entirely by name". It composes a per-instance `UartRegisterMap` (base
address + PeakRDL regmap) over an injected bridge and exposes thin by-name
passthroughs (`write`/`read`/`field`/`addr`). Several instances share one bridge
at distinct base addresses, so a multi-IP system reads as `dev0.<reg>`,
`dev1.<reg>`:

    a = Device(bridge, "core0", regs_base=0x00_0000, regmap_file=CORE_REGMAP)
    b = Device(bridge, "core1", regs_base=0x10_0000, regmap_file=CORE_REGMAP)
    a.write("CTRL", start=1);  print(b.field("STATUS", "done"))

The transport spine (byte_channel / cocotb_axil_bridge / UARTAxiBridge) is
unchanged and common; only the base address and regmap differ per instance, so
the SAME object drives cocotb sim and the FPGA (bridge injection). IP-specific
subclasses (e.g. STREAM's `Stream`) add descriptor/kick/status operations on top.
"""

from __future__ import annotations

import logging
from typing import Optional

from TBClasses.harness.uart_register_map import UartRegisterMap


class Device:
    """One register-mapped IP instance, addressed by name."""

    def __init__(self, bridge, name: str, *, regs_base: int, regmap_file: str,
                 log: Optional[logging.Logger] = None):
        self.name = name
        self.bridge = bridge
        self.regs = UartRegisterMap(bridge, start_address=regs_base,
                                    regmap_file=regmap_file, log=log)

    # ----- named register access (thin passthroughs) ----------------------
    def write(self, reg: str, **fields: int) -> int:
        return self.regs.write(reg, **fields)

    def write_word(self, reg: str, value: int) -> None:
        self.regs.write_word(reg, value)

    def read(self, reg: str) -> int:
        return self.regs.read(reg)

    def field(self, reg: str, field: str) -> int:
        return self.regs.field(reg, field)

    def addr(self, reg: str) -> int:
        return self.regs.addr(reg)

    @property
    def registers(self) -> dict:
        return self.regs.registers

    def __repr__(self) -> str:
        return (f"<{type(self).__name__} {self.name!r} "
                f"@ {self.regs.start_address:#010x}>")
