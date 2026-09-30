# SPDX-License-Identifier: MIT
# SPDX-FileCopyrightText: 2024-2026 sean galloway
"""Host-side driver for the scoria DDR3/LPDDR3 characterization harness.

Adapted from ddr2_char.DDR2CharDriver. Three named Devices over one injectable
bridge, and only ONE of the three is generation-specific:

    self.regs     harness_csr   SHARED (mem_char_framework)   -- unchanged
    self.chargen  chargen_regs  SHARED (mem_char_framework)   -- unchanged
    self.scoria   scoria_csr    scoria                        -- the new part

That split is why this file is short. The framework promotion earlier today
moved harness_csr and chargen_regs out of the pumice board directory precisely
so a DDR3 harness could reuse them, and the register NAMES on both are
identical -- so every engine-programming and status method here talks to the
same blocks pumice does, and a bandwidth number from one is comparable with a
bandwidth number from the other. That comparability IS the point of the A/B.

Registers resolve BY NAME through the PeakRDL-generated regmaps. No hardcoded
offsets: scoria's DDR3 block landed at 0x0C0-0x0E4 and STALL_ZQ at 0x180 only
because 0x17C was taken, and both would move again.

KNOWN DUPLICATION, deliberate for now: the engine/status methods below are
near-identical to DDR2CharDriver's, because both drive the same shared blocks.
The right end state is a MemCharDriver base in mem_char_framework with DDR2 and
DDR3 subclasses. That is a refactor of pumice's live host code, and pumice is a
design at rest whose board results were just re-validated -- so this duplicates
rather than refactoring under it. Filed as the follow-up; do not add a THIRD
copy without doing the extraction first.

NOT YET EXERCISABLE: there is no scoria bitstream. build-scoria does not exist,
so nothing here has talked to hardware. What IS verified is that every register
and field name referenced resolves against scoria_csr_regmap.py, and that the
driver drives the expected register traffic against a mock bridge.
"""
from __future__ import annotations

import os
import sys
from dataclasses import dataclass
from typing import Dict, Optional, Tuple

_HERE = os.path.dirname(os.path.abspath(__file__))
_REPO = os.environ.get("REPO_ROOT") or os.popen(
    "git rev-parse --show-toplevel").read().strip()
sys.path.insert(0, os.path.join(_REPO, "bin"))
sys.path.insert(0, _HERE)

from TBClasses.harness.device import Device            # noqa: E402
from scoria_device import (                            # noqa: E402
    Scoria, SCORIA_REGMAP, SCORIA_APB_BASE,
    HARNESS_CSR_BASE, CHARGEN_APB_BASE,
    MEMTYPE_DDR3, MEMTYPE_LPDDR3,
)

#: Shared framework regmaps. Same files pumice uses -- see the module header.
_FW = os.path.join(_REPO, "projects/fpga-systems/rtl/mem_char_framework")
HARNESS_REGMAP = os.path.join(_FW, "dv/tbclasses/harness_csr_regmap.py")
CHARGEN_REGMAP = os.path.join(_FW, "dv/tbclasses/chargen_regs_regmap.py")

# chargen-level encodings. Shared block, so these are NOT DDR3-specific.
ID_MODE_FIXED, ID_MODE_COUNTER, ID_MODE_LFSR = 0, 1, 2
AXI_SIZE_1, AXI_SIZE_2, AXI_SIZE_4, AXI_SIZE_8, AXI_SIZE_16 = 0, 1, 2, 3, 4
AXI_BURST_FIXED, AXI_BURST_INCR, AXI_BURST_WRAP = 0, 1, 2


@dataclass
class Status:
    init_done: bool
    init_error: bool
    wr_done: int
    rd_done: int
    wr_errors: int
    rd_errors: int


class DDR3CharDriver:
    """Host driver for the scoria DDR3 characterization harness.

    Inject `bridge` (anything with read(addr)->int|None and
    write(addr, val)->bool) to drive the identical register traffic elsewhere:
    a cocotb UART channel in simulation, or a mock for board-less tests. That
    injection is what lets this file be tested before a bitstream exists.
    """

    #: ASCII "DDR3". pumice's harness answers 0x44445232 ("DDR2"), so a driver
    #: pointed at the wrong bitstream fails identity rather than producing
    #: plausible numbers from the wrong controller -- which is the failure the
    #: shared-board near miss would have caused silently.
    BUILD_ID_MAGIC = 0x44445233

    def __init__(self, port: str = "/dev/ttyUSB0", baudrate: int = 115200,
                 timeout: float = 1.0, bridge=None):
        if bridge is None:
            sys.path.insert(0, os.path.join(_REPO, "projects/fpga-systems/bin"))
            from uart_axi_bridge import UARTAxiBridge   # noqa: E402
            bridge = UARTAxiBridge(port=port, baudrate=baudrate,
                                   timeout=timeout)
        self.bridge = bridge

        # Shared blocks: same regmaps, same bases, same names as pumice.
        self.regs = Device(bridge, "harness", regs_base=HARNESS_CSR_BASE,
                           regmap_file=HARNESS_REGMAP)
        self.chargen = Device(bridge, "chargen", regs_base=CHARGEN_APB_BASE,
                              regmap_file=CHARGEN_REGMAP)
        # The generation-specific one.
        self.scoria = Scoria(bridge, "scoria", regs_base=SCORIA_APB_BASE,
                             regmap_file=SCORIA_REGMAP)

        #: AXI beats per DRAM burst. One AXI burst must map to an integer
        #: number of DRAM bursts or the hardware SLVERRs / partial-transfers
        #: and read-back mismatches. DDR3 BL8 on a x16 device pair with a
        #: 64-bit host port gives 32 bytes/DRAM-burst against 8 bytes/AXI-beat
        #: -> 4. Set from the built harness via sync_gen_config(); 1 disables
        #: the guard.
        self.burst_len_multiple = 1

        #: Generators per direction. Conservative default -- call
        #: sync_gen_config() to replace it with what the hardware reports.
        #: pumice carried a stale "1" here for months while the board had two,
        #: so every caller that trusted it drove half the generators it could.
        self.num_gen = 1

    # ===== identity =========================================================

    def build_id(self) -> int:
        return self.regs.read("BUILD_ID")

    def check_build_id(self) -> None:
        """Fail loudly if this is not a scoria harness.

        Cheap, and it is the guard that turns "wrong bitstream on the board"
        from wrong numbers into an error. Worth calling at the top of every
        sequence.
        """
        got = self.build_id()
        if got != self.BUILD_ID_MAGIC:
            raise RuntimeError(
                f"BUILD_ID 0x{got:08X} != expected 0x{self.BUILD_ID_MAGIC:08X} "
                f'("DDR3"). This is not a scoria harness -- pumice answers '
                f'0x44445232 ("DDR2"). Check which bitstream is on the board; '
                f"a shared board can be reprogrammed under a running test.")

    # ===== controller knobs: delegated to the scoria device =================

    def set_memtype(self, memtype: int = MEMTYPE_DDR3) -> None:
        self.regs.write("CTRLR_CFG.memtype", memtype)

    def set_zq(self, **kw) -> None:
        self.scoria.set_zq(**kw)

    def zq_status(self) -> Dict[str, int]:
        return self.scoria.zq_status()

    def set_write_leveling(self, **kw) -> None:
        self.scoria.set_write_leveling(**kw)

    def wrlvl_strobe(self) -> None:
        self.scoria.wrlvl_strobe()

    def wrlvl_status(self) -> Dict[str, int]:
        return self.scoria.wrlvl_status()

    def set_init_timing2(self, **kw) -> None:
        self.scoria.set_init_timing2(**kw)

    def stall_reasons(self) -> Dict[str, int]:
        return self.scoria.stall_reasons()

    def init_restart(self) -> None:
        self.scoria.init_restart()

    def init_done(self) -> bool:
        return self.scoria.init_done()

    def soft_reset(self) -> None:
        """Assert the controller's self-clearing soft reset.

        Invalidates the shadow: soft_reset reverts the CSRs to their RDL
        resets, so a shadow seeded before it would splice pre-reset values
        into the next write.
        """
        self.regs.write("CTRL.soft_reset", 1)
        self.scoria.invalidate_shadow()

    # ===== traffic generators: the SHARED chargen block =====================

    def _program_engine(self, pfx: str, *, start_addr, burst_len, txn_count,
                        stride_0=0, stride_1=0, wrap_mask_0=0, wrap_mask_1=0,
                        gap=0, axi_id=0, id_mode=ID_MODE_FIXED,
                        axi_size=AXI_SIZE_8, axi_burst=AXI_BURST_INCR,
                        data_mode=False, lfsr_seed=0xDEADBEEF,
                        hash_seed0=0, hash_seed1=0, hash_seed2=0,
                        max_outstanding=0, gen=0) -> None:
        """Stage one generator (pfx = WR|RD, gen = 0..num_gen-1).

        STAGING ONLY -- this starts nothing. Launch is go(), which starts every
        selected generator on one cycle. The split matters: staging takes many
        bus transactions and launching must not, or generator 0 runs for however
        long it takes to program generator N.

        max_outstanding caps this generator's bursts in flight; 0 means "as
        built" and is the reset value. This is the sweep axis for bandwidth
        against outstanding transactions -- one bitstream walks the whole curve.
        Values above the built ceiling saturate in RTL rather than wrapping, so
        a too-large request is a flat tail, not a bogus low point.
        """
        if not 0 <= gen < self.num_gen:
            raise IndexError(
                f"generator {gen} out of range 0..{self.num_gen - 1}. The array "
                f"is sized to the device's bank count; read gen_config() for "
                f"what this bitstream was actually built with.")
        q = self.burst_len_multiple
        if q > 1 and (burst_len == 0 or burst_len % q != 0):
            raise ValueError(
                f"{pfx} burst_len={burst_len} must be a nonzero multiple of the "
                f"DRAM-burst quantum ({q} AXI beats/DRAM burst): one AXI burst "
                f"must map to an integer number of DRAM bursts, else the HW "
                f"SLVERRs / partial-transfers. Use a multiple of {q}, or set "
                f"driver.burst_len_multiple=1 to disable this guard.")
        r, n = self.chargen, f"{pfx}_GEN{gen}"
        r.write_word(f"{n}_START_ADDR", start_addr)
        r.write_word(f"{n}_STRIDE_0", stride_0 & 0xFFFFFF)
        r.write_word(f"{n}_STRIDE_1", stride_1 & 0xFFFFFF)
        r.write_word(f"{n}_WRAP_MASK_0", wrap_mask_0)
        r.write_word(f"{n}_WRAP_MASK_1", wrap_mask_1)
        r.write(f"{n}_BLEN_TXN", burst_len=burst_len, txn_count=txn_count,
                gap=gap)
        r.write(f"{n}_AXI_ATTR", axi_id=axi_id, id_mode=id_mode,
                axi_size=axi_size, axi_burst=axi_burst,
                data_mode=1 if data_mode else 0,
                max_outstanding=max_outstanding & 0x3F)
        r.write_word(f"{n}_LFSR_SEED", lfsr_seed)
        r.write_word(f"{n}_HASH_SEED0", hash_seed0)
        r.write_word(f"{n}_HASH_SEED1", hash_seed1)
        r.write_word(f"{n}_HASH_SEED2", hash_seed2)

    def program_wr_engine(self, **kw) -> None:
        self._program_engine("WR", **kw)

    def program_rd_engine(self, **kw) -> None:
        self._program_engine("RD", **kw)

    def go(self, wr_mask: int = 0, rd_mask: int = 0) -> None:
        """Launch the selected generators -- one write, one start edge.

        Masks are bit-per-generator: 0x01 is generator 0, 0xFF is all eight.
        GO's bits are separate FIELDS (wr_go0..3, rd_go0..3) only because a
        singlepulse field must be one bit wide, not because they are separate
        events -- so they go in ONE write. A per-generator start puts the first
        generator minutes ahead of the last over a UART, which is how a
        measurement window ends up describing mostly idle time.
        """
        limit = 1 << self.num_gen
        if not 0 <= wr_mask < limit:
            raise ValueError(
                f"wr_mask 0x{wr_mask:X} exceeds {self.num_gen} generators")
        if not 0 <= rd_mask < limit:
            raise ValueError(
                f"rd_mask 0x{rd_mask:X} exceeds {self.num_gen} generators")
        fields = {}
        for i in range(self.num_gen):
            if wr_mask >> i & 1:
                fields[f"wr_go{i}"] = 1
            if rd_mask >> i & 1:
                fields[f"rd_go{i}"] = 1
        if not fields:
            return
        self.chargen.write("GO", **fields)

    def sync_gen_config(self) -> Dict[str, int]:
        """Replace num_gen / burst_len_multiple with what the HARDWARE reports.

        Read the config register, never default -- if hardware can report it,
        a host-side constant is a guess that goes stale silently. pumice's did.
        """
        # GEN_CONFIG is a CHARGEN register, not a harness one. Reading it off
        # self.regs would not raise on hardware -- it would return whatever the
        # harness block has at that offset, and num_gen would be silently
        # wrong in the direction that drives too many generators.
        n_wr = self.chargen.read("GEN_CONFIG.num_wr_gen")
        n_rd = self.chargen.read("GEN_CONFIG.num_rd_gen")
        n_banks = self.chargen.read("GEN_CONFIG.num_banks")
        self.num_gen = min(n_wr, n_rd) or 1
        if self.num_gen > n_banks:
            raise RuntimeError(
                f"hardware reports {self.num_gen} generators per direction but "
                f"only {n_banks} banks. The RTL invariant is NUM_GEN <= "
                f"NUM_BANKS -- each generator is expected to SPAN "
                f"NUM_BANKS/NUM_GEN banks, so this reading is not consistent "
                f"with any built configuration.")
        return {"num_wr_gen": n_wr, "num_rd_gen": n_rd,
                "num_banks": n_banks, "num_gen": self.num_gen}

    # ===== status ===========================================================

    def gen_done(self) -> Tuple[int, int]:
        """(wr_done_mask, rd_done_mask) -- ONE read, not one per generator."""
        v = self.chargen.read("DONE")
        f = self.chargen.field
        return f("DONE", "wr_done", v), f("DONE", "rd_done", v)

    def gen_errors(self) -> Tuple[int, int]:
        """(writer bresp-error mask, reader any-error mask).

        The reader's is `rd_any_error`, not a bresp mask: a read can fail by
        rresp OR by data mismatch, and collapsing those would report a CRC
        mismatch as a clean run.
        """
        v = self.chargen.read("ERRORS")
        f = self.chargen.field
        return f("ERRORS", "wr_bresp_error", v), f("ERRORS", "rd_any_error", v)

    def status(self) -> Status:
        """Harness + controller status in one object.

        Note which DEVICE each field comes from -- it is not cosmetic. The
        harness STATUS reports `init_fail` (its own view of the controller);
        the controller's own STATUS has `init_error`. They are different
        registers in different blocks with different names, and reading the
        controller's name off the harness Device silently returns whatever the
        harness has at that offset.
        """
        wr_done, rd_done = self.gen_done()
        wr_err, rd_err = self.gen_errors()
        return Status(
            init_done=bool(self.regs.read("STATUS.init_done")),
            init_error=bool(self.regs.read("STATUS.init_fail")),
            wr_done=wr_done, rd_done=rd_done,
            wr_errors=wr_err, rd_errors=rd_err,
        )

    def clear_stats(self) -> None:
        """Pulse CTRL.clear_stats -- zeros the debug_sram write pointer, the
        bus meters and the latency-histogram bins."""
        self.regs.write("CTRL", clear_stats=1)
