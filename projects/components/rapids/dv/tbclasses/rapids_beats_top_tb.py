# SPDX-License-Identifier: MIT
# SPDX-FileCopyrightText: 2024-2025 sean galloway
#
# RTL Design Sherpa - Industry-Standard RTL Design and Verification
# https://github.com/sean-galloway/RTLDesignSherpa
#
# Module: RapidsBeatsTopTB
# Purpose: rapids_beats_top (SPLIT core) AXIS datapath integration testbench
#
# Documentation: projects/components/rapids/PRD.md
# Subsystem: rapids_beats_top
#
# Author: sean galloway
# Created: 2026-07-03

"""
rapids_beats_top (SPLIT core) integration testbench.

rapids_beats_top wraps rapids_core_beats (two wholly-independent halves:
SOURCE = memory->AXIS, SINK = AXIS->memory) behind a SINGLE 13-bit APB slave
plus a shared MonBus AXI-Lite group.

This TB is the AXIS-boundary sibling of RapidsCoreBeatsTB. It differs from the
core rig in exactly the two documented ways:

  (a) CONFIG is programmed BY NAME over the APB register chain instead of poking
      raw cfg_* nets. The register file is split SRC/SNK by APB address bit[12],
      so TWO RegisterMap instances (start_address 0x0000 / 0x1000) resolve every
      register name to an absolute APB address (SRC.GLOBAL_CTRL->0x100,
      SNK.GLOBAL_CTRL->0x1100). No hardcoded offsets.

  (b) DESCRIPTOR KICK-OFF goes through the per-half apbtodescr kick windows:
      SRC 0x000-0x03F, SNK 0x1000-0x103F. Each channel is a LOW/HIGH register
      pair (channel = paddr[5:3], paddr[2] = LOW(0)/HIGH(1)); the descriptor
      address is written LOW-then-HIGH and the HIGH write blocks until the
      descriptor engine accepts the kick.

Everything else -- the two 256-bit descriptor AXI read slaves (src/snk), the
512-bit source-read (m_axi_rd) and sink-write (m_axi_wr) memory slaves, the
quiescent Phase-2 control masters, the AXIS master (s_axis, sink ingress) and
the AXIS egress capture (m_axis, source egress) -- is the core rig verbatim,
retargeted to aclk/aresetn.

MonBus egress: the top always instantiates monbus_axil_axil_group, which
consumes the core's single merged MonBus stream (so the core can never stall on
monbus backpressure). The group's bulk-capture AXI-Lite MASTER (m_axil_mon_*)
is backed by a trivial always-accept write responder so any flushed trace record
completes and the group's write FIFO never fills. The 32-bit error-drain slave
(s_axil_err_*) is held quiescent. For these BASIC datapath tests the scheduler /
descriptor AXI monitors are left disabled (register defaults), so the merged
monbus is essentially idle and m_axil_mon stays inactive regardless.
"""

import os
import sys
import random
from typing import Dict, Any, List, Tuple

import cocotb
from cocotb.triggers import RisingEdge

from TBClasses.shared.utilities import get_repo_root
from TBClasses.shared.tbbase import TBBase
from TBClasses.apb.register_map import RegisterMap

from CocoTBFramework.components.shared.memory_model import MemoryModel
from CocoTBFramework.components.axi4.axi4_factories import (
    create_axi4_slave_rd, create_axi4_slave_wr)
from CocoTBFramework.components.axis4.axis_factories import create_axis_master

repo_root = get_repo_root()
sys.path.insert(0, repo_root)

# By-name register description generated from the RAPIDS half regmap. Split-proof:
# a register relocation needs NO TB changes -- only rapids_regmap.py is regenerated.
RAPIDS_REGMAP_PATH = os.path.join(
    repo_root, 'projects/components/rapids/rtl/rapids_regmap.py')

# APB address bit[12] selects the half: SRC config/kick at 0x0000, SNK at 0x1000.
SRC_BASE_ADDR = 0x0000
SNK_BASE_ADDR = 0x1000


class RapidsBeatsTopTB(TBBase):
    """Split-core AXIS datapath testbench for rapids_beats_top."""

    def __init__(self, dut):
        super().__init__(dut)

        self.NUM_CHANNELS = self.convert_to_int(os.environ.get('TEST_NUM_CHANNELS', '8'))
        self.ADDR_WIDTH = self.convert_to_int(os.environ.get('TEST_ADDR_WIDTH', '64'))
        self.DATA_WIDTH = self.convert_to_int(os.environ.get('TEST_DATA_WIDTH', '512'))
        self.AXI_ID_WIDTH = self.convert_to_int(os.environ.get('TEST_AXI_ID_WIDTH', '8'))
        self.CLK_PERIOD = self.convert_to_int(os.environ.get('TEST_CLK_PERIOD', '10'))
        self.apb_addr_width = self.convert_to_int(os.environ.get('TEST_APB_ADDR_WIDTH', '13'))
        self.apb_data_width = self.convert_to_int(os.environ.get('TEST_APB_DATA_WIDTH', '32'))
        self.SEED = self.convert_to_int(os.environ.get('SEED', '12345'))
        random.seed(self.SEED)

        self.DESC_WIDTH = 256
        self.STRB_WIDTH = self.DATA_WIDTH // 8

        # Clock / reset (rapids_beats_top uses aclk / aresetn).
        self.clk = dut.aclk
        self.clk_name = 'aclk'
        self.rst_n = dut.aresetn

        # Address regions (each memory model is 0-based; base_addr translates).
        self.DESC_BASE = 0x3000_0000    # descriptor storage (non-zero: 0 = null ptr)
        self.SRC_BASE = 0x1000_0000     # source data (m_axi_rd)
        self.DST_BASE = 0x2000_0000     # sink data destination (m_axi_wr)
        self.CHANNEL_OFFSET = 0x0010_0000

        bpl = self.DATA_WIDTH // 8
        self.desc_src_mem = MemoryModel(num_lines=4096, bytes_per_line=32, log=self.log)
        self.desc_snk_mem = MemoryModel(num_lines=4096, bytes_per_line=32, log=self.log)
        self.rd_mem = MemoryModel(num_lines=(32 * self.CHANNEL_OFFSET) // bpl,
                                  bytes_per_line=bpl, log=self.log)
        self.wr_mem = MemoryModel(num_lines=(32 * self.CHANNEL_OFFSET) // bpl,
                                  bytes_per_line=bpl, log=self.log)
        # Control-path SEMAPHORE stores. ONE 32-bit MemoryModel per half, SHARED by
        # that half's ctrlrd (read) and ctrlwr (write) masters, so a CTRL_WRITE
        # doorbell to addr X is observable by a later CTRL_READ gate poll of addr X.
        # 16 KiB per half (byte-addressed, 4 bytes/line).
        self.sem_mem = {
            'src': MemoryModel(num_lines=4096, bytes_per_line=4, log=self.log),
            'snk': MemoryModel(num_lines=4096, bytes_per_line=4, log=self.log),
        }
        self.ctrl_mem = {}

        # BFMs (created after reset).
        self.apb_master = None
        self.desc_src_slave = None
        self.desc_snk_slave = None
        self.rd_slave = None
        self.wr_slave = None
        self.axis_master = None       # drives s_axis_* (sink ingress)
        self.ctrl_slaves = []

        # Two by-name register maps: SRC half @ 0x0000, SNK half @ 0x1000.
        self.src_regs = RegisterMap(RAPIDS_REGMAP_PATH, apb_data_width=self.apb_data_width,
                                    apb_addr_width=self.apb_addr_width,
                                    start_address=SRC_BASE_ADDR, log=self.log)
        self.snk_regs = RegisterMap(RAPIDS_REGMAP_PATH, apb_data_width=self.apb_data_width,
                                    apb_addr_width=self.apb_addr_width,
                                    start_address=SNK_BASE_ADDR, log=self.log)
        # get_register_offset_map() returns the RAW (start_address-agnostic) offset,
        # so we add the half base ourselves in reg_abs().
        self._src_off = self.src_regs.get_register_offset_map()
        self._snk_off = self.snk_regs.get_register_offset_map()

        # source-egress capture (background monitor) + m_axil_mon sink control.
        self.captured_axis = {ch: [] for ch in range(self.NUM_CHANNELS)}
        self._mon_active = False
        self.test_errors = []

    # =========================================================================
    # MANDATORY THREE METHODS
    # =========================================================================

    async def setup_clocks_and_reset(self):
        await self.start_clock(self.clk_name, freq=self.CLK_PERIOD, units='ns')
        await self.assert_reset()
        await self.wait_clocks(self.clk_name, 15)
        await self.deassert_reset()
        await self.wait_clocks(self.clk_name, 15)
        self._create_bfms()
        await self.init_apb_master()
        await self._configure_via_apb('src')
        await self._configure_via_apb('snk')

    async def assert_reset(self):
        self.rst_n.value = 0
        d = self.dut

        # Monitor CAM sync-clear.
        d.cam_clear.value = 0

        # APB inputs idle until the APB master takes over (post-reset).
        d.s_apb_psel.value = 0
        d.s_apb_penable.value = 0
        d.s_apb_pwrite.value = 0
        d.s_apb_paddr.value = 0
        d.s_apb_pwdata.value = 0
        d.s_apb_pstrb.value = 0

        # AXIS ingress idle until the master BFM takes over.
        d.s_axis_tvalid.value = 0
        # AXIS egress consumer held ready.
        d.m_axis_tready.value = 1

        # MonBus AXI-Lite group: err-drain slave quiescent, capture-master sink
        # holds ready high (the _axil_mon_sink coroutine completes B responses).
        d.s_axil_err_arvalid.value = 0
        d.s_axil_err_araddr.value = 0
        d.s_axil_err_arprot.value = 0
        d.s_axil_err_rready.value = 1
        d.m_axil_mon_awready.value = 1
        d.m_axil_mon_wready.value = 1
        d.m_axil_mon_bvalid.value = 0
        d.m_axil_mon_bresp.value = 0

        # Monitor group flush window: sane constants (never 0/0, which stalls the
        # master path). With monitors disabled these see no traffic anyway.
        d.cfg_mon_base_addr.value = 0x0000_1000
        d.cfg_mon_limit_addr.value = 0x0000_5000 - 1
        d.cfg_mon_flush_watermark.value = 3

    async def deassert_reset(self):
        self.rst_n.value = 1

    # =========================================================================
    # BFM SETUP
    # =========================================================================

    def _create_bfms(self):
        d = self.dut

        # Descriptor fetch read slaves (256-bit), one per half.
        self.desc_src_slave = create_axi4_slave_rd(
            dut=d, clock=self.clk, prefix="src_m_axi_desc_", log=self.log,
            data_width=self.DESC_WIDTH, id_width=self.AXI_ID_WIDTH,
            addr_width=self.ADDR_WIDTH, user_width=1, multi_sig=True,
            memory_model=self.desc_src_mem, base_addr=self.DESC_BASE)
        self.desc_snk_slave = create_axi4_slave_rd(
            dut=d, clock=self.clk, prefix="snk_m_axi_desc_", log=self.log,
            data_width=self.DESC_WIDTH, id_width=self.AXI_ID_WIDTH,
            addr_width=self.ADDR_WIDTH, user_width=1, multi_sig=True,
            memory_model=self.desc_snk_mem, base_addr=self.DESC_BASE)

        # Source data read slave (memory -> source).
        self.rd_slave = create_axi4_slave_rd(
            dut=d, clock=self.clk, prefix="m_axi_rd_", log=self.log,
            data_width=self.DATA_WIDTH, id_width=self.AXI_ID_WIDTH,
            addr_width=self.ADDR_WIDTH, user_width=1, multi_sig=True,
            memory_model=self.rd_mem, base_addr=self.SRC_BASE)

        # Sink data write slave (sink -> memory).
        self.wr_slave = create_axi4_slave_wr(
            dut=d, clock=self.clk, prefix="m_axi_wr_", log=self.log,
            data_width=self.DATA_WIDTH, id_width=self.AXI_ID_WIDTH,
            addr_width=self.ADDR_WIDTH, user_width=1, multi_sig=True,
            memory_model=self.wr_mem, base_addr=self.DST_BASE)

        # Phase-2 control masters: REAL 32-bit AXI slaves backed by the per-half
        # SEMAPHORE store. Each half's ctrlrd (read) and ctrlwr (write) masters share
        # ONE MemoryModel, so a CTRL_WRITE doorbell (producer) writing addr X is
        # observed by a CTRL_READ gate (consumer) polling addr X on that same half.
        # Non-quiescent, so AR/AW/W always complete and neither half can hang.
        for half, pfx in (('src', 'src_m_axi_ctrlrd_'), ('snk', 'snk_m_axi_ctrlrd_')):
            self.ctrl_slaves.append(create_axi4_slave_rd(
                dut=d, clock=self.clk, prefix=pfx, log=self.log,
                data_width=32, id_width=self.AXI_ID_WIDTH,
                addr_width=self.ADDR_WIDTH, user_width=1, multi_sig=True,
                memory_model=self.sem_mem[half], base_addr=0))
        for half, pfx in (('src', 'src_m_axi_ctrlwr_'), ('snk', 'snk_m_axi_ctrlwr_')):
            self.ctrl_slaves.append(create_axi4_slave_wr(
                dut=d, clock=self.clk, prefix=pfx, log=self.log,
                data_width=32, id_width=self.AXI_ID_WIDTH,
                addr_width=self.ADDR_WIDTH, user_width=1, multi_sig=True,
                memory_model=self.sem_mem[half], base_addr=0))

        # AXIS master drives s_axis_* (sink ingress).
        self.axis_master = create_axis_master(
            dut=d, clock=self.clk, prefix="s_axis_", log=self.log,
            data_width=self.DATA_WIDTH, id_width=8, dest_width=4, user_width=1)

    async def init_apb_master(self):
        """Bring up the framework APB master on s_apb_* (single clock = aclk)."""
        from CocoTBFramework.components.apb.apb_components import APBMaster
        from CocoTBFramework.components.shared.flex_randomizer import FlexRandomizer
        from TBClasses.amba.amba_random_configs import APB_MASTER_RANDOMIZER_CONFIGS

        if not hasattr(self.dut, 's_apb_paddr'):
            raise RuntimeError("DUT has no APB interface (s_apb_paddr missing)")

        self.apb_master = APBMaster(
            entity=self.dut,
            title='RAPIDS APB Master',
            prefix='s_apb',
            clock=self.clk,
            bus_width=self.apb_data_width,
            addr_width=self.apb_addr_width,
            randomizer=FlexRandomizer(APB_MASTER_RANDOMIZER_CONFIGS['fixed']),
            log=self.log,
        )
        await self.apb_master.reset_bus()
        self.log.info("APB master initialized for rapids_beats_top configuration")

    # =========================================================================
    # BY-NAME REGISTER ACCESS (two half maps, base added manually)
    # =========================================================================

    def reg_abs(self, half: str, reg_name: str) -> int:
        """Resolve a register's absolute APB address BY NAME for the given half.

        Raises KeyError (with a count of known regs) on a typo / stale name so a
        regmap regen mismatch fails loudly rather than silently mis-addressing.
        """
        regs = self.src_regs if half == 'src' else self.snk_regs
        offs = self._src_off if half == 'src' else self._snk_off
        try:
            return regs.start_address + offs[reg_name]
        except KeyError:
            raise KeyError(
                f"register '{reg_name}' not in rapids_regmap.py "
                f"(offset map has {len(offs)} regs)") from None

    async def write_reg(self, half: str, reg_name: str, value: int):
        addr = self.reg_abs(half, reg_name)
        await self.write_apb(addr, value, reg_name=f"{half.upper()}.{reg_name}")

    async def write_fields(self, half: str, reg_name: str, **fields: int):
        """Program a register by setting its FIELDS by name (composed at their
        rapids_regmap offsets/widths) rather than a hand-assembled bitmask.
        Unspecified fields default to 0."""
        regs = self.src_regs if half == 'src' else self.snk_regs
        info = regs.registers[reg_name]
        word = 0
        for fname, val in fields.items():
            fld = info.get(fname)
            if not isinstance(fld, dict) or 'offset' not in fld:
                raise KeyError(f"unknown field {reg_name}.{fname}")
            off = fld['offset']
            hi, lo = (int(x) for x in off.split(':')) if ':' in off \
                else (int(off), int(off))
            mask = ((1 << (hi - lo + 1)) - 1) << lo
            word = (word & ~mask) | ((int(val) << lo) & mask)
        await self.write_reg(half, reg_name, word)

    async def read_reg(self, half: str, reg_name: str) -> int:
        addr = self.reg_abs(half, reg_name)
        return await self.read_apb(addr, reg_name=f"{half.upper()}.{reg_name}")

    async def write_apb(self, addr: int, data: int, reg_name=None):
        """APB write using the framework APB master (blocking)."""
        from CocoTBFramework.components.apb.apb_packet import APBPacket
        packet = APBPacket(
            pwrite=1, paddr=addr, pwdata=data, pstrb=0xF, pprot=0,
            data_width=self.apb_data_width, addr_width=self.apb_addr_width,
            strb_width=self.apb_data_width // 8,
        )
        await self.apb_master.busy_send(packet)
        await RisingEdge(self.clk)
        name = reg_name or f"0x{addr:04X}"
        self.log.info(f"APB WRITE: {name} (0x{addr:04X}) = 0x{data:08X}")

    async def read_apb(self, addr: int, reg_name=None) -> int:
        from CocoTBFramework.components.apb.apb_packet import APBPacket
        packet = APBPacket(
            pwrite=0, paddr=addr, pwdata=0, pstrb=0xF, pprot=0,
            data_width=self.apb_data_width, addr_width=self.apb_addr_width,
            strb_width=self.apb_data_width // 8,
        )
        await self.apb_master.busy_send(packet)
        await RisingEdge(self.clk)
        data = int(packet.fields.get('prdata', 0))
        name = reg_name or f"0x{addr:04X}"
        self.log.info(f"APB READ:  {name} (0x{addr:04X}) = 0x{data:08X}")
        return data

    # =========================================================================
    # CONFIG VIA APB (BY NAME, per half)
    # =========================================================================

    async def _configure_via_apb(self, half: str):
        """Program one half's config over APB by NAME. Values mirror
        RapidsCoreBeatsTB._configure() so top behaviour == core.

        Field encodings (verified from rapids_regmap.py):
          SCHED_CONFIG   : SCHED_EN[0] TIMEOUT_EN[1] ERR_EN[2] COMPL_EN[3] PERF_EN[4]
          DESCENG_CONFIG : DESCENG_EN[0] PREFETCH_EN[1] FIFO_THRESH[5:2]
          AXI_XFER_CONFIG: RD_XFER_BEATS[7:0] WR_XFER_BEATS[15:8]
                           ALLOC_SIZE[23:16] DRAIN_SIZE[31:24]
          CTRL_CONFIG    : CTRLRD_MAX_TRY[8:0]
          CHANNEL_ENABLE : CH_EN[NUM_CHANNELS-1:0]
          GLOBAL_CTRL    : GLOBAL_EN[0] GLOBAL_RST[1]
        """
        all_ch = (1 << self.NUM_CHANNELS) - 1

        # --- scheduler --- (timeout + completion monbus OFF for basic tests) ---
        await self.write_fields(half, 'SCHED_TIMEOUT_CYCLES', TIMEOUT_CYCLES=1_000_000)
        await self.write_fields(half, 'SCHED_TIMEOUT_LIMIT', LIMIT=0xFF)
        await self.write_fields(half, 'SCHED_CONFIG', SCHED_EN=1, ERR_EN=1)  # TIMEOUT/COMPL/PERF off

        # --- descriptor engine ---
        await self.write_fields(half, 'DESCENG_CONFIG',
                                DESCENG_EN=1, PREFETCH_EN=1, FIFO_THRESH=4)
        # Address window must cover the descriptor storage region (DESC_BASE).
        await self.write_fields(half, 'DESCENG_ADDR0_BASE',  ADDR0_BASE=0x0000_0000)
        await self.write_fields(half, 'DESCENG_ADDR0_LIMIT', ADDR0_LIMIT=0xFFFF_FFFF)
        await self.write_fields(half, 'DESCENG_ADDR1_BASE',  ADDR1_BASE=0x0000_0000)
        await self.write_fields(half, 'DESCENG_ADDR1_LIMIT', ADDR1_LIMIT=0xFFFF_FFFF)

        # --- AXI burst sizing: RD/WR=8 beats, ALLOC=16, DRAIN=1 (each half uses
        #     only its own fields; writing the full word is harmless). ---
        await self.write_fields(half, 'AXI_XFER_CONFIG',
                                RD_XFER_BEATS=8, WR_XFER_BEATS=8,
                                ALLOC_SIZE=16, DRAIN_SIZE=1)

        # --- Phase-2 control-read retry cap ---
        await self.write_fields(half, 'CTRL_CONFIG', CTRLRD_MAX_TRY=1)

        # --- enable channels, then globally enable last ---
        await self.write_fields(half, 'CHANNEL_ENABLE', CH_EN=all_ch)
        await self.write_fields(half, 'GLOBAL_CTRL', GLOBAL_EN=1)   # avoid RST bit

        await self.wait_clocks(self.clk_name, 10)
        self.log.info(f"rapids_beats_top {half.upper()} half configured via APB (by name)")

    # =========================================================================
    # DESCRIPTOR KICK-OFF VIA APB (per-half kick window, LOW/HIGH pair)
    # =========================================================================

    def _kick_low_addr(self, half: str, channel: int) -> int:
        """apbtodescr LOW offset: base + channel*8 (paddr[2]=0). channel=paddr[5:3]."""
        base = SRC_BASE_ADDR if half == 'src' else SNK_BASE_ADDR
        return base + channel * 0x008

    def _kick_high_addr(self, half: str, channel: int) -> int:
        """apbtodescr HIGH offset: base + channel*8 + 4 (paddr[2]=1)."""
        base = SRC_BASE_ADDR if half == 'src' else SNK_BASE_ADDR
        return base + channel * 0x008 + 0x004

    async def kick_off_channel(self, half: str, channel: int, descriptor_addr: int):
        """Kick a channel by writing the 64-bit descriptor address to its LOW/HIGH
        kickoff register pair. The HIGH write blocks in apbtodescr until the
        descriptor engine has ACCEPTED the kick, so a completed pair == accepted."""
        desc_low = descriptor_addr & 0xFFFF_FFFF
        desc_high = (descriptor_addr >> 32) & 0xFFFF_FFFF
        await self.write_apb(self._kick_low_addr(half, channel), desc_low,
                             reg_name=f"{half.upper()}_CH{channel}_KICK_LOW")
        await self.write_apb(self._kick_high_addr(half, channel), desc_high,
                             reg_name=f"{half.upper()}_CH{channel}_KICK_HIGH")
        self.log.info(f"Kicked {half} ch{channel} via APB, desc @ 0x{descriptor_addr:016X}")

    # =========================================================================
    # DESCRIPTOR + MEMORY HELPERS
    # =========================================================================

    def create_descriptor(self, src_addr, dst_addr, length, gen_irq=False,
                          last=True, channel_id=0, opcode=0) -> int:
        """Pack a 256-bit descriptor. opcode lives at [209:208]:
        0=DATA, 1=CTRL_READ (consumer gate), 2=CTRL_WRITE (producer doorbell).
        For CONTROL descriptors the DATA slots are reinterpreted by the scheduler:
          addr = src_addr[63:0]; data = dst_addr[31:0]; mask = dst_addr[63:32]."""
        desc = 0
        desc |= (src_addr & ((1 << 64) - 1))
        desc |= (dst_addr & ((1 << 64) - 1)) << 64
        desc |= (length & 0xFFFFFFFF) << 128
        desc |= (0 << 160)                        # next_descriptor_ptr
        desc |= (1 << 192)                        # valid
        desc |= ((1 if gen_irq else 0) << 193)
        desc |= ((1 if last else 0) << 194)
        desc |= (0 << 195)                        # error
        desc |= ((channel_id & 0xF) << 196)
        desc |= ((opcode & 0x3) << 208)           # DESC_OPCODE_LO/HI
        return desc

    def create_ctrl_read_descriptor(self, addr, expected, mask, channel_id=0) -> int:
        """CONSUMER GATE (CTRL_READ, opcode=1): poll `addr` on the control-READ
        master until (read_data & mask) == (expected & mask). addr->src_addr[63:0],
        expected->dst_addr[31:0], mask->dst_addr[63:32]. Retry budget comes from
        cfg_ctrlrd_max_try (CTRL_CONFIG)."""
        dst = (expected & 0xFFFF_FFFF) | ((mask & 0xFFFF_FFFF) << 32)
        return self.create_descriptor(src_addr=addr, dst_addr=dst, length=1,
                                      channel_id=channel_id, opcode=1)

    def create_ctrl_write_descriptor(self, addr, data, channel_id=0) -> int:
        """PRODUCER DOORBELL (CTRL_WRITE, opcode=2): write `data` to `addr` on the
        control-WRITE master, then complete. addr->src_addr[63:0],
        data->dst_addr[31:0]."""
        return self.create_descriptor(src_addr=addr, dst_addr=(data & 0xFFFF_FFFF),
                                      length=1, channel_id=channel_id, opcode=2)

    def seed_semaphore(self, half, addr, value):
        """Preload a 32-bit semaphore location in a half's shared control store."""
        self.sem_mem[half].write(addr, bytearray((value & 0xFFFF_FFFF).to_bytes(4, 'little')))

    def read_semaphore(self, half, addr) -> int:
        """Read the current 32-bit semaphore value from a half's control store."""
        return int.from_bytes(bytes(self.sem_mem[half].read(addr, 4)), 'little')

    def register_descriptor(self, mem, desc_addr, desc_data):
        mem.write(desc_addr - self.DESC_BASE, bytearray(desc_data.to_bytes(32, 'little')))

    def preload_source(self, src_addr, beats: List[int]):
        bpl = self.DATA_WIDTH // 8
        off = src_addr - self.SRC_BASE
        for i, val in enumerate(beats):
            self.rd_mem.write(off + i * bpl, bytearray(val.to_bytes(bpl, 'little')))

    def read_sink(self, dst_addr, nbeats) -> List[int]:
        bpl = self.DATA_WIDTH // 8
        off = dst_addr - self.DST_BASE
        out = []
        for i in range(nbeats):
            b = self.wr_mem.read(off + i * bpl, bpl)
            out.append(int.from_bytes(bytes(b), 'little'))
        return out

    # =========================================================================
    # STIMULUS: AXIS send, egress capture, m_axil_mon sink
    # =========================================================================

    async def send_axis_packet(self, channel, beats: List[int]):
        """Drive a sink-ingress packet on s_axis (tid=channel; tlast on final)."""
        axis = self.axis_master['interface']
        n = len(beats)
        for i, val in enumerate(beats):
            pkt = axis.create_packet(
                data=val,
                strb=(1 << self.STRB_WIDTH) - 1,
                id=channel,
                dest=0,
                user=0,
                last=int(i == n - 1),
            )
            await axis.send(pkt)

    async def axis_egress_monitor(self):
        """Background: hold m_axis_tready high, capture source-egress beats."""
        self.dut.m_axis_tready.value = 1
        while self._mon_active:
            await RisingEdge(self.clk)
            try:
                if (int(self.dut.m_axis_tvalid.value) == 1 and
                        int(self.dut.m_axis_tready.value) == 1):
                    tid = int(self.dut.m_axis_tid.value) & (self.NUM_CHANNELS - 1)
                    self.captured_axis.setdefault(tid, []).append(
                        int(self.dut.m_axis_tdata.value))
            except Exception:
                pass

    async def axil_mon_sink(self):
        """Trivial always-accept AXI-Lite write responder on m_axil_mon_* so the
        monbus group's bulk-capture master never backpressures the core. Holds
        aw/w ready high and returns OKAY B responses for matched AW+W pairs."""
        d = self.dut
        d.m_axil_mon_awready.value = 1
        d.m_axil_mon_wready.value = 1
        d.m_axil_mon_bvalid.value = 0
        d.m_axil_mon_bresp.value = 0
        aw_seen = 0
        w_seen = 0
        while self._mon_active:
            await RisingEdge(self.clk)
            try:
                if int(d.m_axil_mon_awvalid.value) and int(d.m_axil_mon_awready.value):
                    aw_seen += 1
                if int(d.m_axil_mon_wvalid.value) and int(d.m_axil_mon_wready.value):
                    w_seen += 1
                if int(d.m_axil_mon_bvalid.value):
                    if int(d.m_axil_mon_bready.value):
                        d.m_axil_mon_bvalid.value = 0
                elif aw_seen > 0 and w_seen > 0:
                    d.m_axil_mon_bvalid.value = 1
                    d.m_axil_mon_bresp.value = 0
                    aw_seen -= 1
                    w_seen -= 1
            except Exception:
                pass

    async def initialize_test(self):
        self._mon_active = True
        cocotb.start_soon(self.axis_egress_monitor())
        cocotb.start_soon(self.axil_mon_sink())
        await self.wait_clocks(self.clk_name, 2)

    def finalize_test(self):
        self._mon_active = False

    # =========================================================================
    # STATUS HELPERS
    # =========================================================================

    async def wait_half_idle(self, half, timeout_cycles=20000) -> bool:
        sig = getattr(self.dut, f'{half}_system_idle')
        for _ in range(timeout_cycles):
            await self.wait_clocks(self.clk_name, 1)
            try:
                if int(sig.value) == 1:
                    return True
            except Exception:
                pass
        return False

    def read_sched_error(self, half) -> int:
        sig = getattr(self.dut, f'{half}_sched_error')
        try:
            return int(sig.value) if sig.value.is_resolvable else -1
        except Exception:
            return -1

    # =========================================================================
    # TEST METHODS
    # =========================================================================

    async def test_source_path(self, channel=0, beats=4) -> Tuple[bool, Dict[str, Any]]:
        """SOURCE: memory -> AXIS. Preload memory, APB-kick SRC, capture m_axis."""
        self.log.info(f"=== SOURCE path: ch{channel}, {beats} beats ===")
        desc_addr = self.DESC_BASE + channel * 0x1000
        src_addr = self.SRC_BASE + channel * self.CHANNEL_OFFSET

        pattern = [(0x5000_0000_0000_0000 + (channel << 40) + i) for i in range(beats)]
        self.preload_source(src_addr, pattern)

        desc = self.create_descriptor(src_addr, 0, beats, channel_id=channel)
        self.register_descriptor(self.desc_src_mem, desc_addr, desc)

        await self.kick_off_channel('src', channel, desc_addr)

        for _ in range(4000):
            await self.wait_clocks(self.clk_name, 1)
            if len(self.captured_axis.get(channel, [])) >= beats:
                break
        await self.wait_clocks(self.clk_name, 50)

        got = self.captured_axis.get(channel, [])
        errors = list(self.test_errors)
        if len(got) < beats:
            errors.append(f"source ch{channel}: captured {len(got)}/{beats} beats")
        else:
            mism = sum(1 for a, b in zip(got[:beats], pattern) if a != b)
            if mism:
                errors.append(f"source ch{channel}: {mism}/{beats} beat mismatches")
                for i, (a, b) in enumerate(zip(got[:beats], pattern)):
                    if a != b:
                        self.log.error(f"  beat[{i}] got=0x{a:X} exp=0x{b:X}")
        se = self.read_sched_error('src')
        if se not in (0, -1) and se != 0:
            errors.append(f"src_sched_error=0x{se:X}")
        stats = {'captured': len(got), 'expected': beats, 'errors': errors}
        if errors:
            for e in errors:
                self.log.error(f"  SCOREBOARD: {e}")
        else:
            self.log.info(f"  SCOREBOARD: source verified ({beats} beats)")
        return (len(errors) == 0), stats

    async def test_sink_path(self, channel=0, beats=4) -> Tuple[bool, Dict[str, Any]]:
        """SINK: AXIS -> memory. APB-kick SNK, stream s_axis, verify wr_mem."""
        self.log.info(f"=== SINK path: ch{channel}, {beats} beats ===")
        desc_addr = self.DESC_BASE + channel * 0x1000
        dst_addr = self.DST_BASE + channel * self.CHANNEL_OFFSET

        pattern = [(0xA000_0000_0000_0000 + (channel << 40) + i) for i in range(beats)]

        desc = self.create_descriptor(0, dst_addr, beats, channel_id=channel)
        self.register_descriptor(self.desc_snk_mem, desc_addr, desc)

        # Stream AXIS data into SRAM FIRST (buffers per-channel), then kick drain.
        await self.send_axis_packet(channel, pattern)
        await self.wait_clocks(self.clk_name, 20)
        await self.kick_off_channel('snk', channel, desc_addr)

        await self.wait_half_idle('snk', timeout_cycles=20000)
        await self.wait_clocks(self.clk_name, 200)

        got = self.read_sink(dst_addr, beats)
        errors = list(self.test_errors)
        if got != pattern:
            mism = sum(1 for a, b in zip(got, pattern) if a != b)
            errors.append(f"sink ch{channel} @0x{dst_addr:X}: {mism}/{beats} beats mismatch")
            for i, (a, b) in enumerate(zip(got, pattern)):
                if a != b:
                    self.log.error(f"  beat[{i}] got=0x{a:X} exp=0x{b:X}")
        se = self.read_sched_error('snk')
        if se not in (0, -1) and se != 0:
            errors.append(f"snk_sched_error=0x{se:X}")
        stats = {'errors': errors}
        if errors:
            for e in errors:
                self.log.error(f"  SCOREBOARD: {e}")
        else:
            self.log.info(f"  SCOREBOARD: sink verified ({beats} beats)")
        return (len(errors) == 0), stats

    async def test_control_path(self, half='src', gate_ch=0,
                                doorbell_ch=1) -> Tuple[bool, Dict[str, Any]]:
        """PRODUCER/CONSUMER control path end-to-end through the split TOP.

        Real 32-bit semaphore memory backs the half's ctrlrd + ctrlwr masters
        (shared MemoryModel), so a CTRL_WRITE doorbell and a CTRL_READ gate on the
        same half rendezvous through the DUT's real control masters.

        Scenario (single half, two independent schedulers):
          1. Pre-seed semaphore addr with a NON-matching value.
          2. CONSUMER (gate_ch): kick a CTRL_READ GATE polling the semaphore. Prove
             it is HELD OFF -- the half never goes idle while the value mismatches,
             and the ctrlrd master is actually polled (paced by tick_1us).
          3. PRODUCER (doorbell_ch): kick a CTRL_WRITE DOORBELL writing the matching
             value to the SAME addr through the ctrlwr master.
          4. Prove the gate RELEASES -- the half returns idle, and the doorbell
             value is present in the shared semaphore store.
        """
        self.log.info(f"=== CONTROL path: {half} consumer=ch{gate_ch} "
                      f"producer=ch{doorbell_ch} ===")
        errors = []
        desc_mem = self.desc_src_mem if half == 'src' else self.desc_snk_mem

        SEM_ADDR = 0x0000_0100        # 4-byte aligned, non-zero (avoid null-addr)
        MASK = 0x0000_FFFF
        EXPECTED = 0x0000_ABCD        # (EXPECTED & MASK) is the release condition
        NONMATCH = 0x0000_0000        # (NONMATCH & MASK) != (EXPECTED & MASK)
        DOORBELL_DATA = 0x0000_ABCD   # (DOORBELL_DATA & MASK) == (EXPECTED & MASK)

        # Big retry budget so the gate does NOT error out before the producer fires.
        await self.write_fields(half, 'CTRL_CONFIG', CTRLRD_MAX_TRY=511)

        # Pre-seed the semaphore to a NON-matching value.
        self.seed_semaphore(half, SEM_ADDR, NONMATCH)
        pre = self.read_semaphore(half, SEM_ADDR)
        self.log.info(f"  seeded sem[0x{SEM_ADDR:X}]=0x{pre:08X} (non-matching)")

        idle_sig = getattr(self.dut, f'{half}_system_idle')
        ar_v = getattr(self.dut, f'{half}_m_axi_ctrlrd_arvalid')
        ar_r = getattr(self.dut, f'{half}_m_axi_ctrlrd_arready')

        # Background: count ctrlrd AR handshakes -> proves the gate actually polls.
        poll_count = [0]
        poll_active = [True]

        async def poll_monitor():
            while poll_active[0]:
                await RisingEdge(self.clk)
                try:
                    if int(ar_v.value) == 1 and int(ar_r.value) == 1:
                        poll_count[0] += 1
                except Exception:
                    pass
        cocotb.start_soon(poll_monitor())

        # ---- CONSUMER GATE (CTRL_READ) ------------------------------------
        gate_desc_addr = self.DESC_BASE + gate_ch * 0x1000
        gate_desc = self.create_ctrl_read_descriptor(SEM_ADDR, EXPECTED, MASK,
                                                     channel_id=gate_ch)
        self.register_descriptor(desc_mem, gate_desc_addr, gate_desc)
        await self.kick_off_channel(half, gate_ch, gate_desc_addr)

        # Let the gate spin up and issue its first poll(s).
        await self.wait_clocks(self.clk_name, 50)

        # Prove HELD OFF: half must NOT go idle across the whole window while the
        # semaphore mismatches.
        held_off = True
        for _ in range(800):
            await self.wait_clocks(self.clk_name, 1)
            try:
                if int(idle_sig.value) == 1:
                    held_off = False
                    break
            except Exception:
                pass
        polls_before = poll_count[0]
        if not held_off:
            errors.append("gate did NOT hold off: half went idle before producer fired")
        if polls_before == 0:
            errors.append("gate never polled the ctrlrd master (no AR handshakes)")
        self.log.info(f"  HELD-OFF confirmed: {half}_system_idle=0 across 800 cyc, "
                      f"{polls_before} ctrlrd polls issued")

        # ---- PRODUCER DOORBELL (CTRL_WRITE) -------------------------------
        db_desc_addr = self.DESC_BASE + doorbell_ch * 0x1000
        db_desc = self.create_ctrl_write_descriptor(SEM_ADDR, DOORBELL_DATA,
                                                    channel_id=doorbell_ch)
        self.register_descriptor(desc_mem, db_desc_addr, db_desc)
        self.log.info(f"  PRODUCER: ringing doorbell ch{doorbell_ch} -> "
                      f"sem[0x{SEM_ADDR:X}]=0x{DOORBELL_DATA:08X}")
        await self.kick_off_channel(half, doorbell_ch, db_desc_addr)

        # ---- RELEASE: gate must now complete; half returns idle. -----------
        released = await self.wait_half_idle(half, timeout_cycles=20000)
        polls_after = poll_count[0]
        poll_active[0] = False
        await self.wait_clocks(self.clk_name, 5)

        if not released:
            errors.append("gate did NOT release: half never returned idle after doorbell")
        else:
            self.log.info(f"  RELEASED: {half}_system_idle=1 after doorbell "
                          f"(total {polls_after} ctrlrd polls)")

        # Doorbell must have landed in the shared semaphore store.
        stored = self.read_semaphore(half, SEM_ADDR)
        if (stored & MASK) != (DOORBELL_DATA & MASK):
            errors.append(f"doorbell not in store: sem[0x{SEM_ADDR:X}]=0x{stored:08X} "
                          f"exp masked 0x{DOORBELL_DATA & MASK:04X}")
        else:
            self.log.info(f"  DOORBELL landed: sem[0x{SEM_ADDR:X}]=0x{stored:08X}")

        se = self.read_sched_error(half)
        if se not in (0, -1):
            errors.append(f"{half}_sched_error=0x{se:X}")

        stats = {'polls_before': polls_before, 'polls_after': polls_after,
                 'held_off': held_off, 'released': released, 'stored': stored,
                 'errors': errors}
        if errors:
            for e in errors:
                self.log.error(f"  SCOREBOARD: {e}")
        else:
            self.log.info("  SCOREBOARD: control path verified "
                          "(gate held off, doorbell released it)")
        return (len(errors) == 0), stats
