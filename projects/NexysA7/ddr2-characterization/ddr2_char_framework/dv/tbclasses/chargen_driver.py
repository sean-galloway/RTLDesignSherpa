# SPDX-License-Identifier: MIT
# SPDX-FileCopyrightText: 2026 sean galloway
"""Programming interface for the DDR2 characterization traffic generators.

The harness carries sixteen pattern generators -- eight writers and eight
readers, one per DRAM bank -- configured through `chargen_regs`, a generated
PeakRDL block on its own APB slave. This class is how a testbench drives that
block, and it exists so the sim programs the generators over exactly the path
the board does: APB transactions against register names from the generated
regmap, never a poked port and never a hardcoded offset.

That equivalence is the point. The previous single-engine bench set
`dut.cfg_wr_start_addr.value` directly, so the register decode it depended on
was never exercised in simulation -- a register that decoded to the wrong
address could only be discovered on silicon. Sixteen generators multiply that
exposure by sixteen, which is precisely when you stop poking ports.

Names come from `chargen_regs_regmap.py`, regenerated from the RDL by
bin/peakrdl_generate.py. Arrays flatten to `WR_GEN3_START_ADDR`, so a caller
gives an index and this class builds the name.

Usage:

    cg = ChargenDriver(dut, clock=dut.pclk, prefix="s_chargen_apb", log=log)
    for bank in range(4):
        await cg.program_writer(bank, start_addr=bank_base(bank),
                                burst_len=4, txn_count=64, axi_id=bank)
        await cg.program_reader(bank, start_addr=bank_base(bank),
                                burst_len=4, txn_count=64, axi_id=bank)
    await cg.go(wr_mask=0xF, rd_mask=0xF)        # all eight, one cycle
    await cg.wait_done(timeout=1_000_000)
"""

from __future__ import annotations

import logging
import os
from typing import Optional

from cocotb.triggers import RisingEdge

from CocoTBFramework.components.apb.apb_components import APBMaster
from CocoTBFramework.components.apb.apb_packet import APBPacket
from TBClasses.apb.register_map import RegisterMap

_REGMAP_FILE = os.path.join(os.path.dirname(os.path.abspath(__file__)),
                            "chargen_regs_regmap.py")

#: Registers whose reset value the generators treat as "unset". Programming a
#: generator writes every one of them, because a run that inherits a stride or
#: a seed from the previous scenario is the kind of failure that looks like a
#: controller bug for a day.
_WR_FIELDS = ("START_ADDR", "STRIDE_0", "STRIDE_1", "WRAP_MASK_0",
              "WRAP_MASK_1", "BLEN_TXN", "AXI_ATTR", "LFSR_SEED",
              "HASH_SEED0", "HASH_SEED1", "HASH_SEED2")


class ChargenDriver:
    """APB-by-name access to chargen_regs."""

    #: Generators per direction as BUILT. Four, not eight: 8+8 did not fit the
    #: XC7A100T (see chargen_regs.rdl). Read gen_config() to confirm against
    #: the bitstream rather than trusting this constant.
    NUM_GEN = 4

    def __init__(self, dut, clock, prefix: str = "s_chargen_apb",
                 addr_width: int = 12, log=None):
        self.dut = dut
        self.clock = clock
        # Own logger when the caller has none. RegisterMap and APBMaster both
        # call .debug() unconditionally, so a None here is a crash at
        # construction -- and the construction order that produces it (an idle
        # call before the testbench is built) is perfectly reasonable.
        self.log = log if log is not None else logging.getLogger("chargen")
        self.apb = APBMaster(
            entity=dut, title="chargen APB", prefix=prefix,
            clock=clock, bus_width=32, addr_width=addr_width, log=self.log,
        )
        self.reg_map = RegisterMap(
            _REGMAP_FILE, apb_data_width=32, apb_addr_width=addr_width,
            start_address=0x0, log=self.log,
        )
        self.addr_width = addr_width

    # ---- plumbing --------------------------------------------------------

    async def reset(self) -> None:
        await self.apb.reset_bus()

    async def _write_field(self, register: str, field: str, value: int) -> None:
        """One field write, right-justified value.

        RegisterMap.write() applies the field's low-bit shift itself. Do not
        pre-shift here -- doing so pushes the value clear out of the field and
        the masked write stores zero, silently, which is a mistake this repo
        has already paid for once on the pumice CSR path.
        """
        self.reg_map.write(register, field, value)
        for cycle in self.reg_map.generate_apb_cycles():
            await self.apb.busy_send(cycle)
            await RisingEdge(self.clock)

    async def read(self, register: str) -> int:
        """Read one register by name."""
        packet = APBPacket(
            pwrite=0, paddr=self._addr_of(register), pwdata=0, pstrb=0xF, pprot=0,
            data_width=32, addr_width=self.addr_width, strb_width=4,
        )
        await self.apb.busy_send(packet)
        await RisingEdge(self.clock)
        return int(packet.fields.get("prdata", 0))

    def _addr_of(self, register: str) -> int:
        entry = self.reg_map.registers.get(register)
        if entry is None:
            raise KeyError(
                f"no register named {register!r} in chargen_regs -- the regmap "
                f"is generated from chargen_regs.rdl, so a missing name means "
                f"the RDL and this caller disagree, not that the address moved"
            )
        return (self.reg_map.start_address + int(entry["address"], 0)) \
               & self.reg_map.addr_mask

    # ---- programming -----------------------------------------------------

    def _check_index(self, gen: int) -> None:
        if not 0 <= gen < self.NUM_GEN:
            raise IndexError(
                f"generator index {gen} out of range 0..{self.NUM_GEN - 1}. "
                f"The array is sized to NUM_BANKS and the RTL asserts the "
                f"equality at elaboration; an out-of-range index here means "
                f"the test thinks the device has more banks than it does."
            )

    async def _program(self, kind: str, gen: int, *, start_addr: int,
                       stride_0: int, stride_1: int,
                       wrap_mask_0: int, wrap_mask_1: int,
                       burst_len: int, txn_count: int, gap: int,
                       axi_id: int, id_mode: int, axi_size: int,
                       axi_burst: int, data_mode: int, lfsr_seed: int,
                       hash_seed0: int, hash_seed1: int,
                       hash_seed2: int) -> None:
        self._check_index(gen)
        p = f"{kind}_GEN{gen}_"
        await self._write_field(p + "START_ADDR",  "addr",   start_addr)
        await self._write_field(p + "STRIDE_0",    "stride", stride_0 & 0xFFFFFF)
        await self._write_field(p + "STRIDE_1",    "stride", stride_1 & 0xFFFFFF)
        await self._write_field(p + "WRAP_MASK_0", "mask",   wrap_mask_0)
        await self._write_field(p + "WRAP_MASK_1", "mask",   wrap_mask_1)

        await self._write_field(p + "BLEN_TXN", "burst_len", burst_len)
        await self._write_field(p + "BLEN_TXN", "txn_count", txn_count)
        await self._write_field(p + "BLEN_TXN", "gap",       gap)

        await self._write_field(p + "AXI_ATTR", "axi_id",    axi_id)
        await self._write_field(p + "AXI_ATTR", "id_mode",   id_mode)
        await self._write_field(p + "AXI_ATTR", "axi_size",  axi_size)
        await self._write_field(p + "AXI_ATTR", "axi_burst", axi_burst)
        await self._write_field(p + "AXI_ATTR", "data_mode", data_mode)

        await self._write_field(p + "LFSR_SEED",  "seed", lfsr_seed)
        await self._write_field(p + "HASH_SEED0", "seed", hash_seed0)
        await self._write_field(p + "HASH_SEED1", "seed", hash_seed1)
        await self._write_field(p + "HASH_SEED2", "seed", hash_seed2)

    async def program_writer(self, gen: int, *, start_addr: int = 0,
                             stride_0: int = 0, stride_1: int = 0,
                             wrap_mask_0: int = 0, wrap_mask_1: int = 0,
                             burst_len: int = 1, txn_count: int = 1,
                             gap: int = 0, axi_id: int = 0, id_mode: int = 0,
                             axi_size: int = 3, axi_burst: int = 1,
                             data_mode: int = 0, lfsr_seed: int = 0,
                             hash_seed0: int = 0, hash_seed1: int = 0,
                             hash_seed2: int = 0) -> None:
        await self._program("WR", gen, start_addr=start_addr,
                            stride_0=stride_0, stride_1=stride_1,
                            wrap_mask_0=wrap_mask_0, wrap_mask_1=wrap_mask_1,
                            burst_len=burst_len, txn_count=txn_count, gap=gap,
                            axi_id=axi_id, id_mode=id_mode, axi_size=axi_size,
                            axi_burst=axi_burst, data_mode=data_mode,
                            lfsr_seed=lfsr_seed, hash_seed0=hash_seed0,
                            hash_seed1=hash_seed1, hash_seed2=hash_seed2)

    async def program_reader(self, gen: int, **kwargs) -> None:
        """Same signature as :meth:`program_writer`.

        Deliberately identical: writer i and reader i are meant to be a MATCHED
        PAIR over the same address pattern on bank i, and the macro's
        `gen_crc_match` compares them on that assumption. Programming them from
        one set of arguments is what keeps the pair actually matched.
        """
        defaults = dict(start_addr=0, stride_0=0, stride_1=0, wrap_mask_0=0,
                        wrap_mask_1=0, burst_len=1, txn_count=1, gap=0,
                        axi_id=0, id_mode=0, axi_size=3, axi_burst=1,
                        data_mode=0, lfsr_seed=0, hash_seed0=0, hash_seed1=0,
                        hash_seed2=0)
        defaults.update(kwargs)
        await self._program("RD", gen, **defaults)

    async def program_pair(self, gen: int, **kwargs) -> None:
        """Program writer and reader `gen` identically -- the common case."""
        await self.program_writer(gen, **kwargs)
        await self.program_reader(gen, **kwargs)

    # ---- launch ----------------------------------------------------------

    async def go(self, wr_mask: int = 0, rd_mask: int = 0) -> None:
        """Start the selected generators.

        One APB write, so every selected generator starts on the same cycle.
        That is the whole reason GO is a single register: staging is slow and
        happens over many transactions, and if launch were per-generator the
        first would have been running for however long it took to program the
        last. On the rapids characterization that skew was enough to produce
        zero-utilization measurement windows.
        """
        if not (0 <= wr_mask < (1 << self.NUM_GEN)):
            raise ValueError(f"wr_mask {wr_mask:#x} exceeds {self.NUM_GEN} generators")
        if not (0 <= rd_mask < (1 << self.NUM_GEN)):
            raise ValueError(f"rd_mask {rd_mask:#x} exceeds {self.NUM_GEN} generators")

        # GO's bits are sixteen one-bit singlepulse fields (singlepulse is a
        # per-field property and a field must be one bit wide). Build the whole
        # word and send it as ONE transaction -- writing them field by field
        # would put the starts on sixteen different cycles and defeat the point.
        word = (wr_mask & 0xFF) | ((rd_mask & 0xFF) << 8)
        packet = APBPacket(
            pwrite=1, paddr=self._addr_of("GO"), pwdata=word, pstrb=0xF,
            pprot=0, data_width=32, addr_width=self.addr_width, strb_width=4,
        )
        await self.apb.busy_send(packet)
        await RisingEdge(self.clock)

    # ---- status ----------------------------------------------------------

    async def done(self) -> tuple[int, int]:
        """(wr_done_mask, rd_done_mask) from the DONE roll-up."""
        word = await self.read("DONE")
        return word & 0xFF, (word >> 8) & 0xFF

    async def errors(self) -> tuple[int, int]:
        """(wr_bresp_error_mask, rd_any_error_mask) from the ERRORS roll-up."""
        word = await self.read("ERRORS")
        return word & 0xFF, (word >> 8) & 0xFF

    async def crc_pair(self, gen: int) -> tuple[int, int]:
        """(expected, actual) for the matched pair on `gen`."""
        self._check_index(gen)
        return (await self.read(f"WR_GEN{gen}_EXPECTED_CRC"),
                await self.read(f"RD_GEN{gen}_ACTUAL_CRC"))

    async def reader_status(self, gen: int) -> dict:
        """Per-generator reader status, decoded."""
        self._check_index(gen)
        word = await self.read(f"RD_GEN{gen}_STATUS")
        return {
            "done":             bool(word & 0x1),
            "crc_valid":        bool(word & 0x2),
            "data_error":       bool(word & 0x4),
            "rresp_error":      bool(word & 0x8),
            "stray_beat_error": bool(word & 0x10),
            "beats_mismatched": await self.read(f"RD_GEN{gen}_BEATS_MISM"),
            "stray_beats":      await self.read(f"RD_GEN{gen}_STRAY_BEATS"),
        }

    async def gen_config(self) -> dict:
        """Compile-time array shape, read back from the hardware.

        Worth checking rather than assuming: the count the test programs and
        the count that was synthesized are different numbers, and when they
        disagree the run measures something other than what it reports.
        """
        word = await self.read("GEN_CONFIG")
        return {
            "num_wr_gen": word & 0xFF,
            "num_rd_gen": (word >> 8) & 0xFF,
            "num_banks":  (word >> 16) & 0xFF,
        }
