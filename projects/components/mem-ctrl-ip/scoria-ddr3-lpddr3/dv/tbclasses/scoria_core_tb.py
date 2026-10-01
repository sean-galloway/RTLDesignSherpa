# SPDX-License-Identifier: MIT
# SPDX-FileCopyrightText: 2026 sean galloway

"""AXI-to-DFI testbench for `scoria_core`, through the real DFI layer.

The macro tier proved the scheduler composes. This proves the DATAPATH does:
AXI4 host traffic in, the real DFI layer and command path out, and a DFI slave
PHY with a backing memory on the far side. It is the boundary the HAS names --
"verification is against the DV repository's DFI bus functional model, in
cocotb. No board is required to verify scoria."

Everything on both edges is a framework BFM, not hand-driven:

    AXI4MasterWrite / AXI4MasterRead   host traffic on s_axi_*
    DFISlavePHY + MemoryModel          the DRAM side, bound to phy_dfi_*
    DramStateModel                     JEDEC policing from the DRAM's view

That last one earns its place by being a DIFFERENT OBSERVATION POINT. The
macro tier's bound `cmd_history_checker` watches the scheduler's output; this
watches the DFI wire, downstream of CMD_DELAY, the CDC and the command path.
Observation point is exactly what made BUG-001 visible -- the same violation
had to be measured at the arbiter to tell an arbiter defect from FIFO
compression -- so having two independent auditors at different depths is the
point, not redundancy.

`peek_memory` is the other reason this tier is worth building. A round trip
through a loopback proves the data came back; it does NOT prove it was stored
where the DRAM thinks it lives. Reading the backing model at the (rank, bank,
row, col) the address SHOULD decode to catches an address-map error that a
write-then-read would hide completely. The addr_mapper FUB suite proves the
decode in isolation; this proves the whole path agrees with it.

Clocks: `aclk` and `dfi_clk` run at the same period, in phase. That is
board-faithful rather than a simplification -- at DFI_RATE 4 the DFI interface
runs at the controller clock and the PHY does the 4x serialisation, so the
Genesys 2 point has sys and DFI both at 100 MHz. The CDC is still in the path;
a frequency-ratio sweep is future work and would need its own case.
"""

from __future__ import annotations

import logging
import os
import subprocess
import sys
from typing import Optional

import cocotb
from cocotb.clock import Clock
from cocotb.triggers import RisingEdge, Timer

_repo_root = subprocess.check_output(
    ['git', 'rev-parse', '--show-toplevel']
).decode().strip()
if _repo_root not in sys.path:
    sys.path.insert(0, _repo_root)
_BIN = os.path.join(_repo_root, "bin")
if _BIN not in sys.path:
    sys.path.insert(0, _BIN)

from CocoTBFramework.components.axi4.axi4_interfaces import (  # noqa: E402
    AXI4MasterRead, AXI4MasterWrite,
)
from CocoTBFramework.components.dfi.dfi_base import DFIBase  # noqa: E402
from CocoTBFramework.components.dfi.dfi_signals import (  # noqa: E402
    DFIVersion, MemoryType,
)
from CocoTBFramework.components.dfi.dfi_slave_phy import DFISlavePHY  # noqa: E402
from CocoTBFramework.components.dfi.dram_state import (  # noqa: E402
    AddressMapping, DramStateModel, ViolationPolicy,
)
from CocoTBFramework.components.dfi.jedec_timings import (  # noqa: E402
    timings_from_params,
)
from CocoTBFramework.components.shared.memory_model import MemoryModel  # noqa: E402

_DV = os.path.abspath(os.path.join(os.path.dirname(__file__), ".."))
if _DV not in sys.path:
    sys.path.insert(0, _DV)
from tbclasses.scoria_dram_configs import (  # noqa: E402
    dram_config, describe, jedec_ns,
)

MEMTYPE_DDR3, MEMTYPE_LPDDR3 = 0, 1
PAGE_OPEN, PAGE_CLOSE = 0, 1


class ScoriaCoreTB:
    def __init__(self, dut, *, config=None, row_width: int = 15,
                 col_width: int = 10, num_banks: int = 8, num_ranks: int = 1,
                 axi_id_width: int = 8, axi_addr_width: int = 32,
                 dram_beat_width: int = 64, dram_device_width: int = 32,
                 cl: int = 6, cwl: int = 5):
        self.dut = dut
        self.log = logging.getLogger("scoria_core_tb")
        self.log.setLevel(logging.INFO)
        self.spacing, self.prog, self.meta = dram_config(config)

        self.num_ranks = num_ranks
        self.num_banks = num_banks
        self.row_width = row_width
        self.col_width = col_width
        self.axi_id_width = axi_id_width
        self.axi_addr_width = axi_addr_width
        self.cl, self.cwl = cl, cwl

        # BEAT and DEVICE are different widths, and conflating them is how a
        # suite validates a configuration the PHY cannot drive.
        #
        #   DEVICE word = the DQ bus              (32 b on this board: 2 x16)
        #   BEAT        = one DFI PHASE's data    (64 b: DDR3 moves TWO
        #                 transfers per CK, so a phase carries 2 device words)
        #
        # Measured, not assumed: the Genesys 2 LiteDRAM core that passes memtest
        # on this board reports SDRAM_PHY_DATABITS 32 and
        # SDRAM_PHY_DFI_DATABITS 64, and LiteDRAM's s7ddrphy sets
        # `dfi_databits = 2*databits` and packs transfer n into phases[n//2].
        #
        # The host AXI width IS the DFI word: scoria_core derives
        # DW = DFI_DATA_WIDTH = DRAM_BEAT_WIDTH * DFI_RATE, so 64 x 4 = 256.
        self.dram_beat_width = dram_beat_width
        self.dram_device_width = dram_device_width
        self.dram_beat_bytes = dram_beat_width // 8
        self.dram_device_bytes = dram_device_width // 8
        self.dfi_rate = self.meta['dfi_rate']
        self.axi_data_width = dram_beat_width * self.dfi_rate
        self.bytes_per_beat = self.axi_data_width // 8
        self.dram_bl = self.meta['dram_bl']

        # ROW_MAJOR, which is bank_lsb == COL_WIDTH and the reset value of
        # ADDR_MAP.bank_lsb. From the LSB the RTL packs [col | bank | row], so
        # the mapping string reads the other way round.
        self.mapping = AddressMapping(
            num_ranks=num_ranks, num_banks=num_banks,
            num_rows=1 << row_width, num_cols=1 << col_width,
            mapping=("rank|row|bank|col" if num_ranks > 1 else "row|bank|col"),
        )
        self.memory = MemoryModel(
            num_lines=num_ranks * num_banks * (1 << row_width) * (1 << col_width),
            bytes_per_line=self.dram_device_bytes, log=self.log,
        )
        # DFI v3.1 + DDR3 is a supported pair; the timings come from the SAME
        # ns table the CSRs are programmed from (scoria_dram_configs), handed
        # over in nanoseconds so the framework does the ns->CK conversion. The
        # agreement between the two views is gated by
        # dv/tests/macro/test_scoria_dram_config_consistency.py.
        self.dfi_base = DFIBase(
            dfi_version=DFIVersion.V3_1,
            memory_type=MemoryType.DDR3,
            timings=timings_from_params(**jedec_ns(config, cl=cl, cwl=cwl)),
            mapping=self.mapping,
            beats_per_burst=self.dram_bl,
        )

        self.axi_wr: Optional[AXI4MasterWrite] = None
        self.axi_rd: Optional[AXI4MasterRead] = None
        self.dfi_slave: Optional[DFISlavePHY] = None

    # ---- bring-up ----------------------------------------------------------
    async def start(self, *, strict_violations: bool = False):
        """Clocks, reset, configuration, then the BFMs.

        The DFI slave is built AFTER reset so it samples a live bus, and the
        configuration ports are driven BEFORE reset is released so the init
        sequencer never sees an undefined timing.
        """
        period = self.meta['mc_ns']
        cocotb.start_soon(Clock(self.dut.aclk, period, units="ns").start())
        cocotb.start_soon(Clock(self.dut.dfi_clk, period, units="ns").start())

        self.dut.aresetn.value = 0
        self.dut.dfi_rstn.value = 0
        self._drive_config()
        self._idle_axi()
        for _ in range(8):
            await RisingEdge(self.dut.aclk)
        self.dut.aresetn.value = 1
        self.dut.dfi_rstn.value = 1
        for _ in range(4):
            await RisingEdge(self.dut.aclk)

        self.axi_wr = AXI4MasterWrite(
            self.dut, self.dut.aclk, prefix="s_axi",
            data_width=self.axi_data_width, id_width=self.axi_id_width,
            addr_width=self.axi_addr_width, log=self.log)
        self.axi_rd = AXI4MasterRead(
            self.dut, self.dut.aclk, prefix="s_axi",
            data_width=self.axi_data_width, id_width=self.axi_id_width,
            addr_width=self.axi_addr_width, log=self.log)

        self.dfi_slave = DFISlavePHY(
            self.dut, self.dut.dfi_clk,
            base=self.dfi_base, memory=self.memory,
            # One DFI PHASE's data slice. The BFM defaults this to the memory
            # line, which is the DEVICE word -- and on this board the two
            # DIFFER (beat 64, device 32), so passing it is what keeps the bus
            # framed at the right granularity. This is the line that was
            # correct in intent and wrong in value until 2026-10-01, when beat
            # and device were still wired equal at 32.
            dfi_phase_bytes=self.dram_beat_bytes,
            log=self.log)
        if not strict_violations:
            # Demote the BFM's HARD violations to SOFT so a case fails on DATA,
            # not on a timing rule, unless it asked for the strict model. The
            # scheduler's own bound checker is the strict auditor today; this
            # one becomes strict when a case turns it on.
            self.dfi_slave.dram = DramStateModel(
                timings=self.dfi_base.timings,
                num_banks=self.mapping.num_banks,
                policy=ViolationPolicy(hard=frozenset()),
            )
        self.log.info("scoria core TB config:\n" + describe(self.meta['name']))
        self.log.info(
            f"AXI {self.axi_data_width}b (= DFI word), DRAM beat "
            f"{self.dram_beat_bytes}B, device {self.dram_device_bytes}B, "
            f"BL{self.dram_bl}, CL{self.cl}/CWL{self.cwl}, "
            f"row {self.row_width}/col {self.col_width}/"
            f"{self.num_banks} banks")

    def _idle_axi(self):
        d = self.dut
        for s in ('s_axi_awvalid', 's_axi_wvalid', 's_axi_bready',
                  's_axi_arvalid', 's_axi_rready'):
            getattr(d, s).value = 0

    def _drive_config(self):
        """Direct config ports: the CSR path is scoria_top's problem."""
        d, p = self.dut, self.prog
        d.memtype_i.value = MEMTYPE_DDR3
        d.page_policy_i.value = PAGE_OPEN
        d.page_mode_i.value = 0
        d.page_tr_init_i.value = 0
        for s in ('sched_order_mode_i', 'sched_row_sel_i', 'sched_col_sel_i',
                  'sched_access_pref_i', 'sched_wr_high_wm_i',
                  'sched_wr_batch_max_i', 'sched_wr_low_wm_i',
                  'sched_prio_sub_i', 'sched_qos_en_i', 'sched_age_thresh_i'):
            getattr(d, s).value = 0
        # ROW_MAJOR, matching the AddressMapping above and ADDR_MAP's reset
        # value. The minimum legal value is log2(DRAM_BL) -- see BUG-022 and
        # the addr_mapper header; COL_WIDTH is the other end of the range.
        d.bank_lsb_i.value = self.col_width
        d.hash_en_i.value = 0
        d.hash_seed_i.value = 0
        d.t_rcd_i.value = p['tRCD']
        d.t_rp_i.value = p['tRP']
        d.t_ras_i.value = p['tRAS']
        d.t_rc_i.value = p['tRC']
        d.t_wr_i.value = p['tWR']
        d.t_rtp_i.value = p['tRTP']
        d.t_faw_i.value = p['tFAW']
        d.t_rrd_i.value = p['tRRD']
        d.t_wtr_i.value = p['tWTR']
        d.t_rtw_i.value = p['tWTR']
        d.t_ccd_i.value = p['tCCD']
        d.t_refi_i.value = p['tREFI']
        d.refi_reload_i.value = 0
        d.t_rfc_i.value = p['tRFC']
        d.refresh_burst_i.value = 1
        d.ref_postpone_i.value = 0
        d.ref_pullin_i.value = 0
        d.ref_mode_i.value = 0
        d.ref_trefi_pb_i.value = p['tREFI']
        d.ref_trfc_pb_i.value = p['tRFC']
        # Init waits collapsed: tINIT is 500 us, which is 50,000 cycles of
        # nothing at this clock. The ORDER is what the init tests check.
        d.t_init_wait_i.value = 4
        d.t_dll_wait_i.value = 4
        d.t_mrd_wait_i.value = 2
        d.t_rp_wait_i.value = 2
        d.t_rfc_wait_i.value = 2
        d.t_xpr_wait_i.value = 4
        d.t_zqinit_wait_i.value = 4
        d.init_restart_i.value = 0
        # MR0 CL field = CL-4 in {A6,A5,A4} with A2 the +8 bit (JESD79-3F
        # Figure 9, measured in test_scoria_mode_register.py); MR2 CWL = value
        # + 5. These must agree with the cl/cwl handed to the DFI slave or the
        # model and the controller describe different parts.
        d.mr0_i.value = ((self.cl - 4) & 0x7) << 4
        d.mr1_i.value = 0
        d.mr2_i.value = ((self.cwl - 5) & 0x7) << 3
        d.mr3_i.value = 0
        d.zq_enable_i.value = 0
        d.zq_interval_i.value = 0
        d.t_zqcs_i.value = 16
        d.wrlvl_strobe_i.value = 0
        d.wrlvl_cs_sel_i.value = 0
        d.t_wldqsen_i.value = 4
        d.t_wlmrd_i.value = 4
        d.t_wlmrd_max_i.value = 0
        d.t_wlo_i.value = 4
        d.t_wloe_i.value = 4
        # NOTE the name: the SCHEDULER calls this wrlvl_prime_dq_i, the CORE
        # calls it dfi_prime_dq_i. Driving the scheduler's name here was the
        # one mismatch in 75 signals, and cocotb caught it by raising rather
        # than by leaving an input at its default -- which is the better
        # failure, and the reason the names are now cross-checked against the
        # wrapper's ports mechanically rather than read off.
        d.dfi_prime_dq_i.value = 0
        d.dfi_phylvl_ack_cs_n_i.value = (1 << max(1, self.num_ranks)) - 1
        # PHY data-phase placement and latencies. rd/wr_phase 0 keeps the
        # command on DFI phase 0; the board tunes these from the CSR.
        d.rd_phase_i.value = 0
        d.wr_phase_i.value = 0
        d.t_phy_wrlat_i.value = 0
        d.t_rddata_en_i.value = 0
        d.gear_i.value = 2            # log2(DFI_RATE) = full rate
        d.bl_i.value = self.dram_bl

    async def complete_init(self, max_cycles=600):
        """Tell the PHY it is ready, then wait for init_done_o.

        `set_init_complete(1)` is required, not optional: the BFM leaves
        dfi_init_complete DELIBERATELY undriven and says so -- "PHY-driven
        status ... call set_init_complete(1) explicitly after construction".
        That is the right default. A BFM that asserted it for free would let a
        test pass with the PHY handshake never modelled, and the first symptom
        here was simply "init never completed", with nothing to say whether the
        sequencer was stuck or nobody had told it the PHY was up.
        """
        self.dfi_slave.set_init_complete(1)
        for _ in range(max_cycles):
            await RisingEdge(self.dut.aclk)
            if int(self.dut.init_done_o.value):
                return True
        return False

    # ---- memory helpers ----------------------------------------------------
    def _model_addr(self, byte_addr: int) -> int:
        """Where the DFI slave stores the device word for this AXI address.

        Not a guess, and not a second address map: the (bank, row, col) comes
        from `decode()` -- the test's independent model of what the RTL should
        do -- and the flattening is the framework's own `tuple_to_flat` scaled
        by the device word, which is exactly `DFISlavePHY._byte_addr()`. So a
        peek lands wherever the slave put the data, and the only thing left
        under test is whether the controller picked the same coordinates.

        The first version of this divided the byte address by the device size
        and handed THAT to `MemoryModel.read()`, which takes a byte address --
        `bytes_per_line` is a dump convenience, not an index unit. The tell was
        a read of 0x0 returning four overlapping copies of the written word,
        each shifted one byte: a stride-1 walk over 4-byte reads. The round
        trips passed throughout, because they never touch this path.
        """
        rank, bank, row, col = self.decode(byte_addr)
        flat = self.mapping.tuple_to_flat(rank, bank, row, col)
        return flat * self.dram_device_bytes

    def peek_memory(self, byte_addr: int, length: int) -> bytes:
        """Read `length` bytes of the backing DRAM at an AXI byte address.

        Walks a device word at a time: consecutive columns are consecutive in
        the flat space, but only within a row -- going through decode() per
        word keeps a peek that straddles a row or bank boundary honest instead
        of running off the end of the row.
        """
        out = bytearray()
        step = self.dram_device_bytes
        for off in range(0, length, step):
            out += bytes(self.memory.read(self._model_addr(byte_addr + off),
                                          step))
        return bytes(out[:length])

    def preload_memory(self, byte_addr: int, data: bytes) -> None:
        """Place bytes in the DRAM model without using the write datapath."""
        step = self.dram_device_bytes
        for off in range(0, len(data), step):
            chunk = bytearray(data[off:off + step])
            self.memory.write(self._model_addr(byte_addr + off), chunk,
                              (1 << len(chunk)) - 1)

    def decode(self, byte_addr: int):
        """(rank, bank, row, col) the RTL should decode a byte address to."""
        word = byte_addr // self.dram_device_bytes
        col = word & ((1 << self.col_width) - 1)
        bank = (word >> self.col_width) % self.num_banks
        row = (word >> (self.col_width + (self.num_banks - 1).bit_length()))
        return (0, bank, row & ((1 << self.row_width) - 1), col)

    def stat(self, name):
        return int(getattr(self.dut, name).value)
