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
from typing import Dict, Optional, Type

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

    def field(self, reg: str, field: str, word: Optional[int] = None) -> int:
        return self.regs.field(reg, field, word)

    def addr(self, reg: str) -> int:
        return self.regs.addr(reg)

    # Attribute-style register access: dev.<REG>.<field> (delegates to the
    # UartRegisterMap handle). Only register names are proxied; real methods
    # and attributes resolve normally.
    def __getattr__(self, name: str):
        if name.startswith("_"):
            raise AttributeError(name)
        regs = self.__dict__.get("regs")
        if regs is not None and name in regs.registers:
            return getattr(regs, name)
        raise AttributeError(name)

    @property
    def registers(self) -> dict:
        return self.regs.registers

    def __repr__(self) -> str:
        return (f"<{type(self).__name__} {self.name!r} "
                f"@ {self.regs.start_address:#010x}>")


class DeviceBus:
    """A unified, by-name view of every register-mapped IP behind ONE bridge.

    This is the framework spine for the NexysA7 characterization harnesses:
    one UART/AXIL bridge fans out to N named IP instances, each a `Device`
    (its own PeakRDL regmap + base address). Registers are ALWAYS by name --
    `bus["pumice0"].write("DFI_PHASE", rd_phase=1)` -- never by offset. Because
    an instance is just (base address, regmap), the SAME IP can appear multiple
    times at different bases (e.g. two pumice controllers), and heterogeneous IP
    (harness_csr + pumice + a debug block) compose in one bus. The same bus
    drives cocotb sim and the FPGA -- only the injected bridge differs.

        bus = DeviceBus(bridge)
        bus.add("harness", base=0x01_0000, regmap_file=HARNESS_REGMAP)
        bus.add("pumice0", base=0x00_0000, regmap_file=PUMICE_REGMAP, cls=Pumice)
        bus.add("pumice1", base=0x00_2000, regmap_file=PUMICE_REGMAP, cls=Pumice)
        bus["pumice0"].write("SCHED_TUNING", force_inorder=1)
        print(bus["pumice1"].field("STATUS", "init_done"))
    """

    def __init__(self, bridge, *, log: Optional[logging.Logger] = None):
        self.bridge = bridge
        self._log = log
        self.devices: Dict[str, Device] = {}

    def add(self, name: str, *, base: int, regmap_file: str,
            cls: Type[Device] = Device, **kwargs) -> Device:
        """Attach a named IP instance at `base` with its PeakRDL regmap. `cls`
        may be a Device subclass adding that IP's domain operations (e.g. a
        Pumice with program/perf helpers). Returns the instance."""
        if name in self.devices:
            raise ValueError(f"device {name!r} already on this bus")
        dev = cls(self.bridge, name, regs_base=base, regmap_file=regmap_file,
                  log=self._log, **kwargs)
        self.devices[name] = dev
        return dev

    def device(self, name: str) -> Device:
        return self.devices[name]

    def __getitem__(self, name: str) -> Device:
        return self.devices[name]

    def __contains__(self, name: str) -> bool:
        return name in self.devices

    def names(self):
        return tuple(self.devices)

    def __repr__(self) -> str:
        body = ", ".join(f"{n}@{d.regs.start_address:#x}"
                         for n, d in self.devices.items())
        return f"<DeviceBus [{body}]>"
