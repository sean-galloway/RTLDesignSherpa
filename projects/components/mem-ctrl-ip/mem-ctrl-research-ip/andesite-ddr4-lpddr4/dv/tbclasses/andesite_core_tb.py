# SPDX-License-Identifier: MIT
# SPDX-FileCopyrightText: 2026 sean galloway

"""AXI-to-DFI testbench for `andesite_core`, through the real DFI 4.0 layer.

Mirrors `scoria_core_tb` for the andesite four-layer stack: AXI4 host traffic
in, the real DFI layer and DFI 4.0 command path out, and a DFI slave PHY with
a backing memory on the far side.
"""

from __future__ import annotations

import logging
import os
import subprocess
import sys
from typing import Optional

import cocotb
from cocotb.clock import Clock
from cocotb.triggers import RisingEdge

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
from CocoTBFramework.components.dfi.dfi_monitor import _CMD_DECODE  # noqa: E402
from CocoTBFramework.components.dfi.dfi_packet import DRAMCommand  # noqa: E402
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
from tbclasses.andesite_dram_configs import (  # noqa: E402
    dram_config, describe, jedec_ns,
)

MEMTYPE_DDR4 = 0b010
PAGE_OPEN = 0


class AndesiteDFISlavePHY(DFISlavePHY):
    """DFISlavePHY variant that decodes DDR4 ACT_n command encodings.

    The stock BFM decodes commands from ``ras_n/cas_n/we_n`` only, which
    misses a DDR4 ACT command (``act_n==0`` with ``ras_n/cas_n/we_n``
    carrying address bits). andesite's formatter follows the DDR4 truth
    table, so the slave must look at ``act_n`` too.
    """

    def _decode_command(self):
        # CA-bus protocols (LPDDR2/3/...) keep the inherited decoder.
        if self._uses_ca_bus():
            return super()._decode_command()

        p = self._active_phase()
        # ``act_n`` is not in the stock BFM's core signal set, so it is
        # not bound as ``self.bus.act_n``; sample it directly from the DUT.
        act_n_sig = getattr(self.entity, "phy_dfi_act_n", None)
        act_n = 1 if act_n_sig is None else (int(act_n_sig.value) >> p) & 1
        ras_n = (int(self.bus.ras_n.value) >> p) & 1
        cas_n = (int(self.bus.cas_n.value) >> p) & 1
        we_n  = (int(self.bus.we_n.value)  >> p) & 1

        if act_n == 0:
            if ras_n == 1 and cas_n == 1 and we_n == 1:
                return DRAMCommand.ACT
            if ras_n == 0 and cas_n == 0 and we_n == 0:
                return DRAMCommand.MRS
            if ras_n == 0 and cas_n == 0 and we_n == 1:
                return DRAMCommand.REF
            return DRAMCommand.NOP

        return _CMD_DECODE.get((ras_n, cas_n, we_n), DRAMCommand.NOP)


class AndesiteCoreTB:
    def __init__(self, dut, *, config=None, row_width: int = 14,
                 col_width: int = 10, num_banks: int = 8, num_bg: int = 4,
                 num_ranks: int = 1, axi_id_width: int = 8,
                 axi_addr_width: int = 32, dram_beat_width: int = 64,
                 dram_device_width: int = 64, cl: int = 11, cwl: int = 9):
        self.dut = dut
        self.log = logging.getLogger("andesite_core_tb")
        self.log.setLevel(logging.INFO)
        self.spacing, self.prog, self.meta = dram_config(config)

        self.num_ranks = num_ranks
        self.num_banks = num_banks
        self.num_bg = num_bg
        self.row_width = row_width
        self.col_width = col_width
        self.axi_id_width = axi_id_width
        self.axi_addr_width = axi_addr_width
        self.cl, self.cwl = cl, cwl

        self.dram_beat_width = dram_beat_width
        self.dram_device_width = dram_device_width
        self.dram_beat_bytes = dram_beat_width // 8
        self.dram_device_bytes = dram_device_width // 8
        self.dfi_rate = self.meta['dfi_rate']
        self.axi_data_width = dram_beat_width * self.dfi_rate
        self.bytes_per_beat = self.axi_data_width // 8
        self.dram_bl = self.meta['dram_bl']

        self.mapping = AddressMapping(
            num_ranks=num_ranks, num_banks=num_banks,
            num_rows=1 << row_width, num_cols=1 << col_width,
            mapping=("rank|row|bank|col" if num_ranks > 1 else "row|bank|col"),
        )
        self.memory = MemoryModel(
            num_lines=num_ranks * num_banks * (1 << row_width) * (1 << col_width),
            bytes_per_line=self.dram_device_bytes, log=self.log,
        )
        self.dfi_base = DFIBase(
            dfi_version=DFIVersion.V4_0,
            memory_type=MemoryType.DDR4,
            timings=timings_from_params(**jedec_ns(config, cl=cl, cwl=cwl)),
            mapping=self.mapping,
            beats_per_burst=self.dram_bl,
        )

        self.axi_wr: Optional[AXI4MasterWrite] = None
        self.axi_rd: Optional[AXI4MasterRead] = None
        self.dfi_slave: Optional[DFISlavePHY] = None

    async def start(self, *, strict_violations: bool = False):
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

        self.dfi_slave = AndesiteDFISlavePHY(
            self.dut, self.dut.dfi_clk,
            base=self.dfi_base, memory=self.memory,
            dfi_phase_bytes=self.dram_beat_bytes,
            log=self.log)
        if not strict_violations:
            self.dfi_slave.dram = DramStateModel(
                timings=self.dfi_base.timings,
                num_banks=self.mapping.num_banks,
                policy=ViolationPolicy(hard=frozenset()),
            )
        self.log.info("andesite core TB config:\n" + describe(self.meta['name']))
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
        d, p = self.dut, self.prog
        d.memtype_i.value = MEMTYPE_DDR4
        d.page_policy_i.value = PAGE_OPEN
        d.page_mode_i.value = 0
        d.page_tr_init_i.value = 0
        for s in ('sched_order_mode_i', 'sched_row_sel_i', 'sched_col_sel_i',
                  'sched_access_pref_i', 'sched_wr_high_wm_i',
                  'sched_wr_batch_max_i', 'sched_wr_low_wm_i',
                  'sched_prio_sub_i', 'sched_qos_en_i', 'sched_age_thresh_i'):
            getattr(d, s).value = 0
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
        d.t_ccd_l_i.value = p['tCCD']
        d.t_ccd_s_i.value = p['tCCD']
        d.t_rrd_l_i.value = p['tRRD']
        d.t_rrd_s_i.value = p['tRRD']
        d.t_refi_i.value = p['tREFI']
        d.refi_reload_i.value = 0
        d.t_rfc_i.value = p['tRFC']
        d.fgr_factor_i.value = 0
        d.t_rfc_2x_i.value = p['tRFC']
        d.t_rfc_4x_i.value = p['tRFC']
        d.refresh_burst_i.value = 1
        d.ref_postpone_i.value = 0
        d.ref_pullin_i.value = 0
        d.ref_mode_i.value = 0
        d.ref_trefi_pb_i.value = p['tREFI']
        d.ref_trfc_pb_i.value = p['tRFC']
        d.t_init_wait_i.value = 4
        d.t_dll_wait_i.value = 4
        d.t_mrd_wait_i.value = 2
        d.t_rp_wait_i.value = 2
        d.t_cke_wait_i.value = 4
        d.t_mod_wait_i.value = 4
        d.t_zqinit_wait_i.value = 4
        d.init_restart_i.value = 0
        # DDR4 MR images: zero means "safe defaults" for the PHY model.
        # A real DDR4 init sequence would program these from the config.
        d.mr0_i.value = 0
        d.mr1_i.value = 0
        d.mr2_i.value = 0
        d.mr3_i.value = 0
        d.mr4_i.value = 0
        d.mr5_i.value = 0
        d.mr6_i.value = 0
        d.zq_enable_i.value = 0
        d.zq_interval_i.value = 0
        d.t_zqcs_i.value = 16
        d.t_zq_i.value = 16
        d.zq_mpc_opcode_i.value = 0
        d.wrlvl_strobe_i.value = 0
        d.wrlvl_cs_sel_i.value = 0
        d.t_wldqsen_i.value = 4
        d.t_wlmrd_i.value = 4
        d.t_wlmrd_max_i.value = 0
        d.t_wlo_i.value = 4
        d.t_wloe_i.value = 4
        d.dfi_prime_dq_i.value = 0
        d.dfi_phylvl_ack_cs_n_i.value = (1 << max(1, self.num_ranks)) - 1
        d.rdlvl_en_i.value = 0
        d.rdlvl_cs_sel_i.value = 0
        d.csr_mr3_mpr_enter_i.value = 0
        d.csr_mr3_mpr_exit_i.value = 0
        d.t_mpr_enter_i.value = 4
        d.t_mpr_exit_i.value = 4
        d.t_mpr_readout_i.value = 4
        d.tmod_i.value = 4
        d.t_rdlvl_timeout_i.value = 0
        d.mpr_pattern_i.value = 0
        d.dfi_phylvl_req_cs_n_i.value = (1 << max(1, self.num_ranks)) - 1
        d.ca_train_en_i.value = 0
        d.wdq_cal_en_i.value = 0
        d.chan_sel_i.value = 0
        d.csr_mpc_ca_enter_i.value = 0
        d.csr_mpc_ca_exit_i.value = 0
        d.csr_mpc_wdq_enter_i.value = 0
        d.csr_mpc_wdq_exit_i.value = 0
        d.t_ca_train_i.value = 4
        d.t_wdq_cal_i.value = 4
        d.t_ca_timeout_i.value = 0
        d.ca_sample_i.value = 0
        d.wdq_sample_i.value = 0
        d.rd_phase_i.value = 0
        d.wr_phase_i.value = 0
        d.t_phy_wrlat_i.value = 0
        d.t_rddata_en_i.value = 0
        d.gear_i.value = 1
        d.bl_i.value = self.dram_bl

    async def complete_init(self, max_cycles=600):
        self.dfi_slave.set_init_complete(1)
        for _ in range(max_cycles):
            await RisingEdge(self.dut.aclk)
            if int(self.dut.init_done_o.value):
                return True
        return False

    def _model_addr(self, byte_addr: int) -> int:
        rank, bank, row, col = self.decode(byte_addr)
        flat = self.mapping.tuple_to_flat(rank, bank, row, col)
        return flat * self.dram_device_bytes

    def peek_memory(self, byte_addr: int, length: int) -> bytes:
        out = bytearray()
        step = self.dram_device_bytes
        for off in range(0, length, step):
            out += bytes(self.memory.read(self._model_addr(byte_addr + off),
                                          step))
        return bytes(out[:length])

    def preload_memory(self, byte_addr: int, data: bytes) -> None:
        step = self.dram_device_bytes
        for off in range(0, len(data), step):
            chunk = bytearray(data[off:off + step])
            self.memory.write(self._model_addr(byte_addr + off), chunk,
                              (1 << len(chunk)) - 1)

    def decode(self, byte_addr: int):
        word = byte_addr // self.dram_device_bytes
        col = word & ((1 << self.col_width) - 1)
        bank_width = max(1, (self.num_banks - 1).bit_length())
        bank = (word >> self.col_width) & ((1 << bank_width) - 1)
        # The RTL addr_mapper places the bank-group field between bank and row.
        bg_width = max(0, (self.num_bg - 1).bit_length())
        row = word >> (self.col_width + bank_width + bg_width)
        return (0, bank, row & ((1 << self.row_width) - 1), col)

    def stat(self, name):
        return int(getattr(self.dut, name).value)
