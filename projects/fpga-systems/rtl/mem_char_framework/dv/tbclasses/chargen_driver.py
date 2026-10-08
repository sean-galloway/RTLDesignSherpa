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
    for bank in range(2):
        await cg.program_writer(bank, start_addr=bank_base(bank),
                                burst_len=4, txn_count=64, axi_id=bank)
        await cg.program_reader(bank, start_addr=bank_base(bank),
                                burst_len=4, txn_count=64, axi_id=bank)
    await cg.go(wr_mask=0x3, rd_mask=0x3)        # both generators, one cycle
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
#: controller bug for a day. AXI_ATTR includes hammer_en and FILL_PATTERN is
#: its own register, so both are covered once _program() takes them.
_WR_FIELDS = ("START_ADDR", "STRIDE_0", "STRIDE_1", "WRAP_MASK_0",
              "WRAP_MASK_1", "BLEN_TXN", "AXI_ATTR", "LFSR_SEED",
              "HASH_SEED0", "HASH_SEED1", "HASH_SEED2", "FILL_PATTERN")


class ChargenDriver:
    """APB-by-name access to chargen_regs."""

    #: Generators per direction as BUILT. FOUR, each spanning NUM_BANKS/4 = 2
    #: banks on the MT47H64M16. Measured cost of the step from two: one
    #: write+read pair is 2,043 LUT / 2,022 FF, taking the board build from
    #: 77% to about 87% slice occupancy. Six or eight per direction do not fit
    #: the XC7A100T. Read gen_config() to confirm against the bitstream rather
    #: than trusting this constant.
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
                       hash_seed2: int,
                       max_outstanding: int = 0, hammer_en: int = 0,
                       fill_pattern: int = 0) -> None:
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
        # Rowhammer / aggressor-pair mode: the address index becomes the
        # transaction counter's LSB, so addresses alternate base /
        # base+stride_0 per transaction. Written on EVERY program call so a
        # hammer run never leaks into a later ordinary run through a field
        # the programmer never wrote (hammer_en's reset value is 0, but a
        # previous scenario is not reset).
        await self._write_field(p + "AXI_ATTR", "hammer_en", hammer_en & 0x1)
        # 0 = as built (GEN_MAX_OUTSTANDING). The sweep axis for bandwidth
        # against outstanding transactions; the RTL saturates anything above
        # the built ceiling rather than wrapping it to a small number.
        await self._write_field(p + "AXI_ATTR", "max_outstanding",
                                max_outstanding & 0x3F)

        await self._write_field(p + "LFSR_SEED",  "seed", lfsr_seed)
        await self._write_field(p + "HASH_SEED0", "seed", hash_seed0)
        await self._write_field(p + "HASH_SEED1", "seed", hash_seed1)
        await self._write_field(p + "HASH_SEED2", "seed", hash_seed2)
        await self._write_field(p + "FILL_PATTERN", "pattern",
                                fill_pattern & 0xFFFFFFFF)

    async def program_writer(self, gen: int, *, start_addr: int = 0,
                             stride_0: int = 0, stride_1: int = 0,
                             wrap_mask_0: int = 0, wrap_mask_1: int = 0,
                             burst_len: int = 1, txn_count: int = 1,
                             gap: int = 0, axi_id: int = 0, id_mode: int = 0,
                             axi_size: int = 3, axi_burst: int = 1,
                             data_mode: int = 0, lfsr_seed: int = 0,
                             hash_seed0: int = 0, hash_seed1: int = 0,
                             hash_seed2: int = 0,
                             max_outstanding: int = 0, hammer_en: int = 0,
                             fill_pattern: int = 0) -> None:
        await self._program("WR", gen, start_addr=start_addr,
                            stride_0=stride_0, stride_1=stride_1,
                            wrap_mask_0=wrap_mask_0, wrap_mask_1=wrap_mask_1,
                            burst_len=burst_len, txn_count=txn_count, gap=gap,
                            axi_id=axi_id, id_mode=id_mode, axi_size=axi_size,
                            axi_burst=axi_burst, data_mode=data_mode,
                            lfsr_seed=lfsr_seed, hash_seed0=hash_seed0,
                            hash_seed1=hash_seed1, hash_seed2=hash_seed2,
                            max_outstanding=max_outstanding,
                            hammer_en=hammer_en, fill_pattern=fill_pattern)

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
                        hash_seed2=0, max_outstanding=0, hammer_en=0,
                        fill_pattern=0)
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

    # ---- run control -----------------------------------------------------

    async def wait_done(self, wr_mask: int = 0, rd_mask: int = 0,
                        timeout: int = 1_000_000) -> None:
        """Poll DONE until every selected generator reports done.

        With both masks 0 (the common "I launched everything" case) it waits
        on the full array. `timeout` is in poll iterations -- each poll is one
        APB read, so the bus itself paces the loop; a generator that never
        finishes raises TimeoutError instead of hanging the bench.
        """
        if wr_mask == 0 and rd_mask == 0:
            wr_mask = rd_mask = (1 << self.NUM_GEN) - 1
        wr_done = rd_done = 0
        for _ in range(timeout):
            wr_done, rd_done = await self.done()
            if (wr_done & wr_mask) == wr_mask and \
               (rd_done & rd_mask) == rd_mask:
                return
        raise TimeoutError(
            f"generators never finished: waited wr_mask={wr_mask:#x} "
            f"rd_mask={rd_mask:#x} for {timeout} DONE polls "
            f"(last wr_done={wr_done:#x} rd_done={rd_done:#x})"
        )

    # ---- rowhammer recipe ------------------------------------------------

    async def rowhammer(self, gen: int, *, victim_addr: int, row_pitch: int,
                        hammer_txns: int, aggressor_pattern: int,
                        victim_pattern: int = 0xFFFFFFFF,
                        double_sided: bool = True,
                        axi_size: int = 3, timeout: int = 1_000_000) -> dict:
        """Double-sided rowhammer on one victim row, then victim readback.

        The recipe, matching docs/rowhammer_methodology.md in this framework:

          1. HAMMER -- writer `gen`, hammer_en=1, BL1 (burst_len=1, so one
             ACT per transaction), data_mode=2 (FILL) with
             `aggressor_pattern`. Double-sided: base = victim_addr -
             row_pitch (the row below the victim) and stride_0 = 2 *
             row_pitch, so the address index -- the transaction counter's
             LSB in hammer mode -- ping-pongs between the two aggressor
             rows. Single-sided: base = victim_addr + row_pitch, stride_0 =
             0, so every transaction hits the one aggressor.
          2. READBACK -- reader `gen` walks the victim row in BL1 beats,
             data_mode=2 expecting `victim_pattern`. The caller fills the
             victim with exactly that pattern beforehand (and the
             aggressors, if the campaign wants a specific aggressor image;
             the hammer rewrites both aggressors with `aggressor_pattern`
             on every activation, so a setup fill is about the pattern seen
             DURING the hammer, not after).

        Returns the err_bits summary: the reader's accumulated popcount of
        (actual ^ expected) bits, saturated at all-ones, plus the beat-level
        status. That popcount is the observable -- a bit flipped in the
        victim by the hammer counts exactly one per flipped cell bit.

        `hammer_txns` must be even: the ping-pong spends one transaction on
        each aggressor, and an odd count activates one aggressor once more
        than the other. `victim_addr` must be row-aligned (`row_pitch` is
        the byte stride between rows in the address map the host
        programmed) and `hammer_txns` fits the 16-bit transaction counter.
        `timeout` is in DONE polls per phase, as in :meth:`wait_done`.

        A campaign alternates `aggressor_pattern` between 0x00000000 and
        0xFFFFFFFF on successive passes or victims -- FILL is one constant
        per run by construction, so the "0s on one aggressor, 1s on the
        other" shape lives across passes, not inside one.
        """
        self._check_index(gen)
        beat_bytes = 1 << axi_size
        if row_pitch <= 0 or row_pitch % beat_bytes:
            raise ValueError(
                f"row_pitch={row_pitch} must be a positive multiple of the "
                f"beat size ({beat_bytes} B at axi_size={axi_size}); it is "
                f"the row stride in the programmed address map")
        if victim_addr % row_pitch:
            raise ValueError(
                f"victim_addr={victim_addr:#x} is not row-aligned to "
                f"row_pitch={row_pitch}; a mid-row victim silently measures "
                f"a different row pair than the one reported")
        if not 0 < hammer_txns <= 0xFFFF:
            raise ValueError(
                f"hammer_txns={hammer_txns} out of range 1..{0xFFFF} -- the "
                f"transaction counter is 16 bits")
        if hammer_txns & 1:
            raise ValueError(
                f"hammer_txns={hammer_txns} is odd; the aggressor pair "
                f"ping-pong spends one transaction per aggressor, so an odd "
                f"count hammers one side once more and skews the disturb")
        if double_sided:
            if victim_addr < row_pitch:
                raise ValueError(
                    f"victim row at {victim_addr:#x} has no row below it "
                    f"(row_pitch={row_pitch}) -- double-sided needs both "
                    f"neighbours; use double_sided=False at the device edge")
            if victim_addr + row_pitch >= 1 << 32:
                raise ValueError(
                    f"victim row at {victim_addr:#x} has no row above it "
                    f"inside the 32-bit map (row_pitch={row_pitch}) -- the "
                    f"upper aggressor would wrap")
            aggr_base = victim_addr - row_pitch
            aggr_stride = 2 * row_pitch
        else:
            if victim_addr + row_pitch >= 1 << 32:
                raise ValueError(
                    f"victim row at {victim_addr:#x} has no row above it "
                    f"inside the 32-bit map (row_pitch={row_pitch}) -- use "
                    f"double_sided=False from the other edge")
            aggr_base = victim_addr + row_pitch
            aggr_stride = 0
        # The recipe must survive the CSR fields without truncation: stride_0
        # is a 24-bit signed field and txn_count is 16 bits. A value that
        # doesn't fit would be silently masked by the regmap write, which is
        # exactly the failure this driver exists to prevent.
        if aggr_stride > 0x7F_FFFF:
            raise ValueError(
                f"aggressor stride {aggr_stride:#x} exceeds the signed "
                f"24-bit STRIDE_0 field; row_pitch={row_pitch} is too large "
                f"for this map")
        victim_beats = row_pitch // beat_bytes
        if victim_beats > 0xFFFF:
            raise ValueError(
                f"victim walk needs {victim_beats} beats, more than the "
                f"16-bit txn_count holds; read the victim back in windows")

        # 1. hammer the aggressor pair.
        await self.program_writer(
            gen, start_addr=aggr_base, stride_0=aggr_stride, stride_1=0,
            wrap_mask_0=0, wrap_mask_1=0, burst_len=1,
            txn_count=hammer_txns, gap=0, axi_id=gen, id_mode=0,
            axi_size=axi_size, axi_burst=1, data_mode=2,
            hammer_en=1, fill_pattern=aggressor_pattern)
        await self.go(wr_mask=1 << gen)
        await self.wait_done(wr_mask=1 << gen, timeout=timeout)
        wr_err, _ = await self.errors()
        if (wr_err >> gen) & 1:
            raise RuntimeError(
                f"writer {gen} latched a BRESP error mid-hammer -- the "
                f"recipe addresses are illegal for this map, or the bus "
                f"broke (wr_bresp_error mask {wr_err:#x})")

        # 2. read the victim back and count flipped bits.
        await self.program_reader(
            gen, start_addr=victim_addr, stride_0=beat_bytes, stride_1=0,
            wrap_mask_0=0, wrap_mask_1=0, burst_len=1,
            txn_count=victim_beats, gap=0, axi_id=gen, id_mode=0,
            axi_size=axi_size, axi_burst=1, data_mode=2,
            fill_pattern=victim_pattern)
        await self.go(rd_mask=1 << gen)
        await self.wait_done(rd_mask=1 << gen, timeout=timeout)

        status = await self.reader_status(gen)
        return {
            "gen":              gen,
            "double_sided":     double_sided,
            "aggressor_base":   aggr_base,
            "aggressor_stride": aggr_stride,
            "hammer_txns":      hammer_txns,
            "victim_addr":      victim_addr,
            "victim_beats":     victim_beats,
            # Headline observable: saturating popcount of flipped bits.
            "err_bits":         await self.read(f"RD_GEN{gen}_ERR_BITS"),
            **status,
        }

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
