# SPDX-License-Identifier: MIT
# SPDX-FileCopyrightText: 2026 sean galloway
"""Named, multi-instance host API for STREAM DMA.

One `Stream` object == one STREAM DMA instance, programmed *entirely by register
name* through `TBClasses.harness.UartRegisterMap` (backed by the PeakRDL
`stream_regmap.py`). Several DMAs on one board read as

    stream0 = Stream(bridge, "stream0", regs_base=0x0000_0000, desc_ram_base=0x0002_0000)
    stream1 = Stream(bridge, "stream1", regs_base=0x0010_0000, desc_ram_base=0x0012_0000)
    stream0.load_ext(0, 4096, rd=..., wr=...);  stream0.run(0)
    stream1.load_chain(0, 4, 8192);             stream1.run(0)

No hardcoded register offsets: kick / enable / status all go through named
registers (CHx_CTRL_LOW.DESC_ADDR_LOW, CHANNEL_ENABLE.CH_EN, CHANNEL_IDLE.CH_IDLE).
The same object drives cocotb sim and the FPGA — only the injected bridge's
byte channel differs (see TBClasses.harness).
"""

from __future__ import annotations

import logging
import os
from typing import Optional

from TBClasses.harness.device import Device, DeviceBus
from descriptor_builder import DescriptorBuilder


def _default_regmap() -> str:
    """Locate the generated STREAM regmap by walking up to the repo root."""
    env = os.environ.get("STREAM_REGMAP")
    if env:
        return env
    d = os.path.dirname(os.path.abspath(__file__))
    for _ in range(12):
        cand = os.path.join(d, "projects/components/dmas/stream/rtl/stream_regmap.py")
        if os.path.isfile(cand):
            return cand
        d = os.path.dirname(d)
    raise FileNotFoundError("stream_regmap.py not found; set STREAM_REGMAP")


class Stream(Device):
    """A single STREAM DMA instance, addressed by name.

    Extends the generic `Device` (named register access over an injected bridge)
    with STREAM's descriptor RAM, kick, and channel status/enable operations.
    """

    def __init__(self, bridge, name: str, *, regs_base: int, desc_ram_base: int,
                 regmap_file: Optional[str] = None, data_width: int = 128,
                 src_base: int = 0x8000_0000, dst_base: int = 0x9000_0000,
                 log: Optional[logging.Logger] = None):
        super().__init__(bridge, name, regs_base=regs_base,
                         regmap_file=regmap_file or _default_regmap(), log=log)
        self.desc = DescriptorBuilder(data_width=data_width, src_base=src_base,
                                      dst_base=dst_base, desc_ram_base=desc_ram_base)

    # write/read/field/addr/registers are inherited from Device.

    # ----- channel enable / status by name ---------------------------------
    def enable_channel(self, channel: int, enable: bool = True) -> None:
        cur = self.field("CHANNEL_ENABLE", "CH_EN")
        mask = (cur | (1 << channel)) if enable else (cur & ~(1 << channel))
        self.write("CHANNEL_ENABLE", CH_EN=mask)

    def channel_idle(self, channel: int) -> bool:
        return bool(self.field("CHANNEL_IDLE", "CH_IDLE") & (1 << channel))

    def channel_state(self, channel: int) -> int:
        return self.field(f"CH_STATE{channel}_STATE", "STATE")

    # ----- descriptor programming into this instance's desc RAM ------------
    def _write_desc(self, writes) -> None:
        for addr, data in writes:
            if not self.bridge.write(addr, data):
                raise IOError(f"{self.name}: descriptor write failed @ {addr:#x}")

    def load_chain(self, channel: int, num_descriptors: int,
                   transfer_bytes: int) -> int:
        """Program a legacy descriptor chain; return the kick address."""
        self._write_desc(self.desc.build_chain(channel, num_descriptors, transfer_bytes))
        return self.desc.kick_address(channel)

    def load_ext(self, channel: int, transfer_bytes: int,
                 rd: dict, wr: dict, desc_idx: int = 0) -> int:
        """Program one extended (dma_address_gen) descriptor; return kick addr.

        rd/wr = {s0, s1, inner, w0=0, w1=0}. Requires the DUT built with
        USE_ROW_COL_MAJOR_ADDRESSING=1.
        """
        self._write_desc(self.desc.build_ext(channel, transfer_bytes, rd, wr,
                                              desc_idx=desc_idx))
        return self.desc.kick_address(channel)

    # ----- kick off by name -------------------------------------------------
    def kick(self, channel: int, desc_addr: int) -> None:
        """Kick a channel by writing the descriptor address to CHx_CTRL.

        apbtodescr is a state machine that requires BOTH writes, LOW then HIGH,
        to complete the kick handshake (IDLE -> RESPOND_LOW -> WAIT_HIGH ->
        RESPOND_HIGH -> desc_apb_valid). Always write both, LOW first, even when
        the high word is 0 -- writing only LOW leaves it stuck in WAIT_HIGH and
        the channel never starts."""
        self.write(f"CH{channel}_CTRL_LOW", DESC_ADDR_LOW=desc_addr & 0xFFFF_FFFF)
        self.write(f"CH{channel}_CTRL_HIGH", DESC_ADDR_HIGH=(desc_addr >> 32) & 0xFFFF_FFFF)

    def run(self, channel: int, kick_addr: Optional[int] = None) -> None:
        """Enable + kick a channel (descriptors must already be loaded)."""
        self.enable_channel(channel, True)
        if kick_addr is None:
            kick_addr = self.desc.kick_address(channel)
        self.kick(channel, kick_addr)


# Base addresses of the two register windows in the char-harness bridge map.
STREAM_APB_BASE  = 0x0000_0000   # STREAM controller APB slave (stream_regmap.py)
HARNESS_CSR_BASE = 0x0001_0000   # char-harness control block (harness_csr_regmap.py)


def build_stream_bus(bridge, *, stream_base: int = STREAM_APB_BASE,
                     harness_base: int = HARNESS_CSR_BASE,
                     desc_ram_base: int = 0x0002_0000,
                     log: Optional[logging.Logger] = None) -> DeviceBus:
    """Compose the STREAM char flow's register spaces onto one DeviceBus.

    Each regmap imports on its own as a named Device -- NO hand-merging:
      * bus["stream"]  -> the generated STREAM controller regmap (stream_regmap.py),
                          which already includes the monitor block @0x1000 (the
                          MON regfile is instantiated there by stream_regs.rdl).
                          Typed as `Stream` so it also carries descriptor/kick ops.
      * bus["harness"] -> the char-harness regmap (harness_csr_regmap.py, the one
                          hand-authored CSR map).

    Host tools access everything by name -- bus["stream"].SCHED_CONFIG,
    bus["harness"].KICK_GO.write_word(m) -- over the one injected bridge, so the
    same code drives silicon and cocotb sim.
    """
    from harness_addrs import _default_regmap as _harness_regmap  # sibling module
    bus = DeviceBus(bridge, log=log)
    bus.add("stream", base=stream_base, regmap_file=_default_regmap(),
            cls=Stream, desc_ram_base=desc_ram_base)
    bus.add("harness", base=harness_base, regmap_file=_harness_regmap())
    return bus
