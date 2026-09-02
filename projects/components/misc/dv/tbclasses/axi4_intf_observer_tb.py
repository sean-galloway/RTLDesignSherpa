# SPDX-License-Identifier: MIT
# SPDX-FileCopyrightText: 2026 sean galloway
"""Testbench for axi4_intf_{master,slave}_observer.

ONE TB for BOTH observers on purpose. They share obs_regs.rdl, consume an
identical 17-register set and carry identical parameter lists; the only
difference is which monitor flavour they instantiate
(axi4_master_{rd,wr}_mon vs axi4_slave_{rd,wr}_mon). A second TB would be a
second thing to keep in sync, and the register map is exactly what must not
drift between them.

WHY THIS EXISTS AT ALL: until now neither observer had any component-level DV.
Both were exercised only through a 20-minute full-harness simulation in another
project, which is why the following all survived unnoticed:

  - ENABLE_MON_TAPS hardcoded 1'b0, so the monitors were built DISABLED
  - the reporter cones compiled out, so cfg_compl_enable=1 drove nothing
  - N_ADDR_RANGES=0, making ADDR_MATCH packets structurally impossible
  - 26 config inputs tied to constants and reachable from nowhere
  - nothing ever writing the observer's own APB

Every one of those is a register-layer fact this TB can assert in seconds.
"""

import os
import sys
from pathlib import Path

from cocotb.triggers import RisingEdge

from TBClasses.shared.tbbase import TBBase
from CocoTBFramework.components.apb.apb_components import APBMaster
from CocoTBFramework.components.apb.apb_packet import APBPacket


def _regmap_offsets() -> dict:
    """name -> byte offset, from the SAME generated regmap the host tools use.

    Never hardcode an offset here. The regblock is shared with Genesys 2 stream
    and NexysA7 pumice; a pasted constant is how a register move becomes a
    silent readback of the wrong thing.
    """
    here = Path(__file__).resolve()
    gen = here.parents[2] / "rtl" / "regs" / "generated"
    sys.path.insert(0, str(gen))
    import obs_regs_top_regmap as rm  # noqa: E402

    out = {}
    for name, body in rm.top_block.items():
        if not isinstance(body, dict) or body.get("type") != "reg":
            continue
        addr = body.get("address", body.get("offset"))
        out[name] = int(str(addr), 0)
    if not out:
        raise RuntimeError("no register offsets parsed from obs_regs_top_regmap")
    return out


class AXI4IntfObserverTB(TBBase):
    """APB/register-layer TB for either observer flavour."""

    def __init__(self, dut):
        super().__init__(dut)
        self.regs = _regmap_offsets()
        self.apb = APBMaster(
            entity=dut,
            title="OBS APB Master",
            prefix="s_apb_",
            clock=dut.aclk,
            bus_width=32,
            addr_width=12,
            log=self.log,
        )

    # ---- the three mandatory methods -------------------------------------
    async def setup_clocks_and_reset(self):
        await self.start_clock("aclk", freq=10, units="ns")
        await self.assert_reset()
        await self.wait_clocks("aclk", 10)
        await self.deassert_reset()
        await self.wait_clocks("aclk", 5)
        await self.apb.reset_bus()
        # No manual PSTRB drive here on purpose. cocotb_bus binds OPTIONAL
        # signals with a case-SENSITIVE hasattr while required ones are
        # case-insensitive, so on this lowercase DUT PSTRB used to vanish and
        # every write went out with zero byte-strobes. Fixed in the BFM
        # (APBSignalMixin._match_optional_case); this asserts that fix holds.
        for _sig in ("PSTRB", "PPROT", "PSLVERR"):
            bound = self.apb.is_signal_present(_sig)
            self.log.info(f"APB optional signal {_sig} bound: {bound}")
        assert self.apb.is_signal_present("PSTRB"), (
            "PSTRB did not bind. This DUT names its APB ports lowercase; "
            "cocotb_bus gates OPTIONAL signals on a case-sensitive hasattr, so "
            "PSTRB silently disappears and every write carries zero byte-strobes "
            "-- writes are accepted and do nothing.")
        await self.wait_clocks("aclk", 5)

    async def assert_reset(self):
        self.dut.aresetn.value = 0

    async def deassert_reset(self):
        self.dut.aresetn.value = 1

    # ---- register access, BY NAME ----------------------------------------
    def off(self, name: str) -> int:
        if name not in self.regs:
            raise KeyError(f"unknown observer register {name!r}; "
                           f"have {len(self.regs)}: {sorted(self.regs)[:8]}...")
        return self.regs[name]

    async def _xfer(self, pwrite: int, addr: int, data: int = 0) -> int:
        pkt = APBPacket(pwrite=pwrite, paddr=addr, pwdata=data, pstrb=0xF,
                        pprot=0, data_width=32, addr_width=12, strb_width=4)
        pkt.direction = "WRITE" if pwrite else "READ"
        if not hasattr(self.apb, "transmit_coroutine"):
            self.apb.transmit_coroutine = None
        await self.apb.send(pkt)
        for _ in range(100):
            await RisingEdge(self.dut.aclk)
            if (self.dut.s_apb_psel.value and self.dut.s_apb_penable.value
                    and self.dut.s_apb_pready.value):
                break
        rd = int(self.dut.s_apb_prdata.value)
        await RisingEdge(self.dut.aclk)
        return rd

    async def write_reg(self, name: str, value: int):
        await self._xfer(1, self.off(name), value)

    async def read_reg(self, name: str) -> int:
        return await self._xfer(0, self.off(name))
