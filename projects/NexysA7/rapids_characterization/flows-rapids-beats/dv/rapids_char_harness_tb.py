# SPDX-License-Identifier: MIT
# SPDX-FileCopyrightText: 2026 sean galloway
#
# RTL Design Sherpa - Industry-Standard RTL Design and Verification
# https://github.com/sean-galloway/RTLDesignSherpa
#
# Module: RapidsCharHarnessTB
# Purpose: cocotb testbench for the RAPIDS beats characterization harness
#          (rapids_char_harness). Drives the harness exactly the way the host
#          will and verifies the on-chip self-check end-to-end (per-channel CRC).
#
# Documentation: projects/NexysA7/rapids_characterization/flows-rapids-beats/
# Subsystem: rapids_char_harness
#
# Author: sean galloway
# Created: 2026-07-03

"""
rapids_char_harness testbench.

The harness wraps rapids_beats_top (split SOURCE + SINK beats DMA) and provides
the on-chip stimulus / checkers / memories:

  - axis4_master_pattern_gen  -> DUT s_axis  (SINK ingress stimulus, per channel)
  - axis4_slave_pattern_check <- DUT m_axis  (SOURCE egress check, per channel)
  - axi4_slave_rd_pattern_gen  backs m_axi_rd (512b SOURCE data, per-arid LFSR)
  - axi4_slave_wr_crc_check    backs m_axi_wr (512b SINK data CRC, per-awid)
  - sdpram_slave_axi4_axi4 x2  descriptor RAM per half (DUT reads port A;
                               host writes descriptors on the port-B boundary)
  - sdpram_slave_axi4_axi4 x2  control semaphore RAM per half (unused here)

There are therefore NO AXIS / data-AXI BFMs in this TB -- those paths are all
on-chip. The TB drives ONLY the control surface:

  (a) CONFIG is programmed BY NAME over the 13-bit APB register chain using TWO
      RegisterMap instances (SRC @ 0x0000, SNK @ 0x1000), exactly like
      rapids_beats_top_tb.py.
  (b) DESCRIPTORS are loaded into the per-half descriptor RAM through the exposed
      host write port (desc_src_* / desc_snk_*, 256-bit AXI4 write master BFM);
      the DUT fetches them from the same byte address when kicked.
  (c) KICK-OFF goes through the per-half apbtodescr kick windows (SRC 0x000, SNK
      0x1000); channel = paddr[5:3]; LOW/HIGH = paddr[2]; addr written LOW-HIGH.
  (d) AXIS gen / chk and the data-memory CRC engines are driven / read over their
      dedicated harness control/status ports.

Consistency invariant being verified (the point of the harness): all four on-chip
blocks share identical LFSR (0xDEADBEEF, taps {32,22,2,1}) + CRC-32 params, so
per channel:
  SINK  : o_gen_expected_crc[ch] (what the AXIS gen sent) == wr_crc_value[ch]
          (what the sink wrote to m_axi_wr, CRC'd)   -- s_axis -> sink -> m_axi_wr
  SOURCE: rd_crc_value[ch] (what m_axi_rd served)     == o_chk_actual_crc[ch]
          (what the AXIS checker received on m_axis), with o_data_error == 0
          -- m_axi_rd -> source -> m_axis

Per-channel demux is off the AXI ID / tid: the read pattern gen demuxes off
s_axi_arid[CIW-1:0], the write CRC check off s_axi_awid[CIW-1:0], and the AXIS
gen/chk off tid. This only lines up per channel if the DUT tags m_axi_rd arid /
m_axi_wr awid / m_axis tid with the channel index -- which the passing
multi-channel result below demonstrates it does.
"""

import os
import sys

import cocotb
from cocotb.triggers import RisingEdge

from TBClasses.shared.utilities import get_repo_root
from TBClasses.shared.tbbase import TBBase
from TBClasses.apb.register_map import RegisterMap

from CocoTBFramework.components.axi4.axi4_factories import create_axi4_master_wr

repo_root = get_repo_root()
sys.path.insert(0, repo_root)

# Independent, bit-exact software reference model of the on-chip LFSR->CRC-32
# pattern (host/rapids_char_golden.py). Used to validate the CRC in sim against
# a reference that shares NO logic with the RTL, on both sink and source paths.
_HOST_DIR = os.path.join(
    os.path.dirname(os.path.abspath(__file__)), '..', 'host')
sys.path.insert(0, os.path.abspath(_HOST_DIR))
from rapids_char_golden import golden_crc  # noqa: E402

# By-name register description generated from the RAPIDS half regmap (split-proof).
RAPIDS_REGMAP_PATH = os.path.join(
    repo_root, 'projects/components/rapids/rtl/rapids_regmap.py')

# APB address bit[12] selects the half: SRC config/kick at 0x0000, SNK at 0x1000.
SRC_BASE_ADDR = 0x0000
SNK_BASE_ADDR = 0x1000


class RapidsCharHarnessTB(TBBase):
    """Control-surface testbench for the RAPIDS beats characterization harness."""

    def __init__(self, dut):
        super().__init__(dut)

        self.NUM_CHANNELS = self.convert_to_int(os.environ.get('TEST_NUM_CHANNELS', '8'))
        self.NUM_ACTIVE = self.convert_to_int(os.environ.get('TEST_NUM_ACTIVE', '4'))
        self.NUM_BEATS = self.convert_to_int(os.environ.get('TEST_NUM_BEATS', '8'))
        self.ADDR_WIDTH = self.convert_to_int(os.environ.get('TEST_ADDR_WIDTH', '64'))
        self.DATA_WIDTH = self.convert_to_int(os.environ.get('TEST_DATA_WIDTH', '512'))
        self.AXI_ID_WIDTH = self.convert_to_int(os.environ.get('TEST_AXI_ID_WIDTH', '8'))
        self.CLK_PERIOD = self.convert_to_int(os.environ.get('TEST_CLK_PERIOD', '10'))
        self.apb_addr_width = self.convert_to_int(os.environ.get('TEST_APB_ADDR_WIDTH', '13'))
        self.apb_data_width = self.convert_to_int(os.environ.get('TEST_APB_DATA_WIDTH', '32'))

        self.DESC_WIDTH = 256

        # Clock / reset (harness uses aclk / aresetn).
        self.clk = dut.aclk
        self.clk_name = 'aclk'
        self.rst_n = dut.aresetn

        # Address regions. Descriptor storage lands in the on-chip descriptor RAM
        # (sdpram_core: line = addr[15:5], no base offset), so the host-write
        # address MUST equal the DUT fetch address -- we use the same value for
        # both. Non-zero base: 0 is a null descriptor pointer.
        self.DESC_BASE = 0x3000_0000
        self.SRC_BASE = 0x1000_0000       # source data (m_axi_rd) - addr agnostic
        self.DST_BASE = 0x2000_0000       # sink data dest (m_axi_wr) - addr agnostic
        self.CHANNEL_OFFSET = 0x0010_0000

        # BFMs (created after reset).
        self.apb_master = None
        self.desc_src_master = None
        self.desc_snk_master = None

        # Two by-name register maps: SRC half @ 0x0000, SNK half @ 0x1000.
        self.src_regs = RegisterMap(RAPIDS_REGMAP_PATH, apb_data_width=self.apb_data_width,
                                    apb_addr_width=self.apb_addr_width,
                                    start_address=SRC_BASE_ADDR, log=self.log)
        self.snk_regs = RegisterMap(RAPIDS_REGMAP_PATH, apb_data_width=self.apb_data_width,
                                    apb_addr_width=self.apb_addr_width,
                                    start_address=SNK_BASE_ADDR, log=self.log)
        self._src_off = self.src_regs.get_register_offset_map()
        self._snk_off = self.snk_regs.get_register_offset_map()

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

        # APB idle until the APB master takes over (post-reset).
        d.s_apb_psel.value = 0
        d.s_apb_penable.value = 0
        d.s_apb_pwrite.value = 0
        d.s_apb_paddr.value = 0
        d.s_apb_pwdata.value = 0
        d.s_apb_pstrb.value = 0

        # Descriptor-RAM host write ports idle until the master BFMs take over.
        for pfx in ('desc_src', 'desc_snk'):
            getattr(d, f'{pfx}_awvalid').value = 0
            getattr(d, f'{pfx}_awid').value = 0
            getattr(d, f'{pfx}_awaddr').value = 0
            getattr(d, f'{pfx}_awlen').value = 0
            getattr(d, f'{pfx}_awsize').value = 0
            getattr(d, f'{pfx}_awburst').value = 0
            getattr(d, f'{pfx}_wvalid').value = 0
            getattr(d, f'{pfx}_wdata').value = 0
            getattr(d, f'{pfx}_wstrb').value = 0
            getattr(d, f'{pfx}_wlast').value = 0
            getattr(d, f'{pfx}_bready').value = 1

        # AXIS pattern generator (sink stimulus) idle.
        d.cfg_gen_start.value = 0
        d.cfg_gen_lfsr_seed.value = 0
        d.cfg_gen_num_beats.value = 0
        d.cfg_gen_beats_per_pkt.value = 0
        d.cfg_gen_channel_mask.value = 0
        d.cfg_gen_tdest.value = 0

        # AXIS pattern checker (source egress) idle.
        d.chk_cfg_start.value = 0
        d.chk_cfg_lfsr_seed.value = 0
        d.chk_ready_en.value = 0

        # Data-memory CRC engines idle.
        d.rd_crc_lfsr_reset.value = 0
        d.wr_crc_reset.value = 0

        # Monitor egress window: sane constants (never 0/0, which stalls the path).
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
        # 256-bit AXI4 write masters onto the exposed descriptor-RAM host ports.
        self.desc_src_master = create_axi4_master_wr(
            dut=d, clock=self.clk, prefix="desc_src_", log=self.log,
            data_width=self.DESC_WIDTH, id_width=self.AXI_ID_WIDTH,
            addr_width=self.ADDR_WIDTH, user_width=1, multi_sig=True)
        self.desc_snk_master = create_axi4_master_wr(
            dut=d, clock=self.clk, prefix="desc_snk_", log=self.log,
            data_width=self.DESC_WIDTH, id_width=self.AXI_ID_WIDTH,
            addr_width=self.ADDR_WIDTH, user_width=1, multi_sig=True)

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
        self.log.info("APB master initialized for rapids_char_harness configuration")

    # =========================================================================
    # BY-NAME REGISTER ACCESS (two half maps, base added manually)
    # =========================================================================

    def reg_abs(self, half: str, reg_name: str) -> int:
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

    async def write_apb(self, addr: int, data: int, reg_name=None):
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

    # =========================================================================
    # CONFIG VIA APB (BY NAME, per half) -- mirrors rapids_beats_top_tb
    # =========================================================================

    async def _configure_via_apb(self, half: str):
        """Program one half's config over APB by NAME (values mirror the split-top
        basic-datapath config: sched EN, timeout OFF, descriptor engine EN,
        RD/WR=8 beats, ALLOC=16, wide-open address windows, all channels EN)."""
        all_ch = (1 << self.NUM_CHANNELS) - 1

        await self.write_reg(half, 'SCHED_TIMEOUT_CYCLES', 1_000_000)
        await self.write_reg(half, 'SCHED_TIMEOUT_LIMIT', 0xFF)
        # SCHED_EN[0] | ERR_EN[2]  (TIMEOUT_EN/COMPL_EN/PERF_EN off)
        await self.write_reg(half, 'SCHED_CONFIG', (1 << 0) | (1 << 2))

        # DESCENG_EN | PREFETCH_EN | FIFO_THRESH=4
        await self.write_reg(half, 'DESCENG_CONFIG', 0x1 | 0x2 | (4 << 2))
        await self.write_reg(half, 'DESCENG_ADDR0_BASE', 0x0000_0000)
        await self.write_reg(half, 'DESCENG_ADDR0_LIMIT', 0xFFFF_FFFF)
        await self.write_reg(half, 'DESCENG_ADDR1_BASE', 0x0000_0000)
        await self.write_reg(half, 'DESCENG_ADDR1_LIMIT', 0xFFFF_FFFF)

        # RD/WR=8 beats, ALLOC=16, DRAIN=1.
        axi_xfer = (1 << 24) | (16 << 16) | (8 << 8) | (8 << 0)
        await self.write_reg(half, 'AXI_XFER_CONFIG', axi_xfer)

        await self.write_reg(half, 'CTRL_CONFIG', 0x1)

        await self.write_reg(half, 'CHANNEL_ENABLE', all_ch)
        await self.write_reg(half, 'GLOBAL_CTRL', 0x1)   # GLOBAL_EN (avoid RST bit)

        await self.wait_clocks(self.clk_name, 10)
        self.log.info(f"rapids_char_harness {half.upper()} half configured via APB")

    # =========================================================================
    # DESCRIPTOR KICK-OFF VIA APB (per-half kick window, LOW/HIGH pair)
    # =========================================================================

    def _kick_low_addr(self, half: str, channel: int) -> int:
        base = SRC_BASE_ADDR if half == 'src' else SNK_BASE_ADDR
        return base + channel * 0x008

    def _kick_high_addr(self, half: str, channel: int) -> int:
        base = SRC_BASE_ADDR if half == 'src' else SNK_BASE_ADDR
        return base + channel * 0x008 + 0x004

    async def kick_off_channel(self, half: str, channel: int, descriptor_addr: int):
        """Kick a channel by writing the 64-bit descriptor address to its LOW/HIGH
        kickoff register pair (HIGH write blocks until the descriptor engine
        accepts the kick)."""
        desc_low = descriptor_addr & 0xFFFF_FFFF
        desc_high = (descriptor_addr >> 32) & 0xFFFF_FFFF
        await self.write_apb(self._kick_low_addr(half, channel), desc_low,
                             reg_name=f"{half.upper()}_CH{channel}_KICK_LOW")
        await self.write_apb(self._kick_high_addr(half, channel), desc_high,
                             reg_name=f"{half.upper()}_CH{channel}_KICK_HIGH")
        self.log.info(f"Kicked {half} ch{channel} via APB, desc @ 0x{descriptor_addr:016X}")

    # =========================================================================
    # DESCRIPTOR PACK + LOAD (into on-chip descriptor RAM via host write port)
    # =========================================================================

    def create_descriptor(self, src_addr, dst_addr, length, gen_irq=False,
                          last=True, channel_id=0, opcode=0) -> int:
        """Pack a 256-bit descriptor (opcode 0=DATA at [209:208])."""
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
        desc |= ((opcode & 0x3) << 208)
        return desc

    async def load_descriptor(self, half: str, descriptor_addr: int, desc_data: int):
        """Write a single 256-bit descriptor beat into the half's descriptor RAM
        through the exposed host write port. The sdpram maps line = addr[15:5], so
        writing at descriptor_addr lands where the DUT will fetch it when kicked."""
        master = self.desc_src_master if half == 'src' else self.desc_snk_master
        # size=5 => 32 bytes (256-bit) per beat; single-beat burst (awlen=0).
        await master['interface'].write_transaction(
            address=descriptor_addr, data=desc_data, burst_len=1, size=5, burst_type=1, id=0)
        self.log.info(f"Loaded {half} descriptor @ 0x{descriptor_addr:016X} = 0x{desc_data:064X}")

    # =========================================================================
    # PER-CHANNEL PACKED-ARRAY STATUS READERS
    # =========================================================================

    def _read_ch_word(self, sig, ch) -> int:
        """Read element ch (32-bit) from a packed [NC-1:0][31:0] output."""
        try:
            val = int(sig.value)
        except Exception:
            return -1
        return (val >> (ch * 32)) & 0xFFFF_FFFF

    def _read_ch_bit(self, sig, ch) -> int:
        """Read bit ch from a packed [NC-1:0] output."""
        try:
            val = int(sig.value)
        except Exception:
            return -1
        return (val >> ch) & 0x1

    def _read_u32(self, sig) -> int:
        try:
            return int(sig.value)
        except Exception:
            return -1

    async def _pulse(self, sig, cycles=1):
        sig.value = 1
        await self.wait_clocks(self.clk_name, cycles)
        sig.value = 0
        await self.wait_clocks(self.clk_name, 1)

    async def _wait_for(self, cond, timeout_cycles) -> bool:
        for _ in range(timeout_cycles):
            await self.wait_clocks(self.clk_name, 1)
            try:
                if cond():
                    return True
            except Exception:
                pass
        return False

    # =========================================================================
    # TEST: SINK self-check  (AXIS gen -> sink -> m_axi_wr CRC)
    # =========================================================================

    async def run_sink_selfcheck(self, active_channels, beats):
        self.log.info(f"=== SINK self-check: channels={active_channels}, "
                      f"{beats} beats/channel ===")
        d = self.dut
        n_active = len(active_channels)
        mask = 0
        for ch in active_channels:
            mask |= (1 << ch)

        # 1. Load a SINK DATA descriptor per active channel into the SNK desc RAM.
        for ch in active_channels:
            desc_addr = self.DESC_BASE + ch * 0x1000
            dst_addr = self.DST_BASE + ch * self.CHANNEL_OFFSET
            desc = self.create_descriptor(0, dst_addr, beats, channel_id=ch)
            await self.load_descriptor('snk', desc_addr, desc)

        # 2. Reset the sink-write CRC checker.
        await self._pulse(d.wr_crc_reset)

        # 3. Program + start the AXIS pattern generator (cfg_start reseeds/clears
        #    its per-channel LFSR + expected CRC).
        d.cfg_gen_lfsr_seed.value = 0            # 0 => DEADBEEF param
        d.cfg_gen_num_beats.value = beats        # beats PER CHANNEL
        d.cfg_gen_beats_per_pkt.value = 0        # 0 => one packet per channel
        d.cfg_gen_channel_mask.value = mask
        d.cfg_gen_tdest.value = 0
        await self._pulse(d.cfg_gen_start)

        # Let the generator push some beats into the sink SRAM before draining.
        await self.wait_clocks(self.clk_name, 20)

        # 4. Kick each channel's SINK descriptor over APB (drains SRAM -> m_axi_wr).
        for ch in active_channels:
            desc_addr = self.DESC_BASE + ch * 0x1000
            await self.kick_off_channel('snk', ch, desc_addr)

        # 5. Wait for the sink to go idle AND for all beats to be CRC'd.
        expected_total = beats * n_active
        ok_idle = await self._wait_for(
            lambda: (int(d.snk_system_idle.value) == 1 and
                     self._read_u32(d.wr_beat_count_total) == expected_total),
            timeout_cycles=60000)

        await self.wait_clocks(self.clk_name, 50)

        # 6. Per-channel scoreboard: wr_crc_value[ch] == o_gen_expected_crc[ch].
        errors = []
        results = {}
        wr_total = self._read_u32(d.wr_beat_count_total)
        if not ok_idle:
            errors.append(f"timeout: snk_system_idle={int(d.snk_system_idle.value)} "
                          f"wr_beat_count_total={wr_total} (expected {expected_total})")
        if wr_total != expected_total:
            errors.append(f"wr_beat_count_total={wr_total} != expected {expected_total}")

        for ch in active_channels:
            exp_crc = self._read_ch_word(d.o_gen_expected_crc, ch)
            act_crc = self._read_ch_word(d.wr_crc_value, ch)
            gold_crc = golden_crc(ch, beats)
            exp_valid = self._read_ch_bit(d.o_gen_expected_crc_valid, ch)
            act_valid = self._read_ch_bit(d.wr_crc_value_valid if hasattr(d, 'wr_crc_value_valid')
                                          else d.wr_crc_valid, ch)
            results[ch] = (exp_crc, act_crc)
            if not exp_valid:
                errors.append(f"ch{ch}: gen expected_crc_valid=0")
            if not act_valid:
                errors.append(f"ch{ch}: wr_crc_valid=0")
            if exp_crc != act_crc:
                errors.append(f"ch{ch}: SINK CRC mismatch gen=0x{exp_crc:08X} "
                              f"wr=0x{act_crc:08X}")
            # Validate BOTH the gen's expected CRC and the sink-written data's CRC
            # against the independent golden reference (not just gen==wr).
            if exp_crc != gold_crc:
                errors.append(f"ch{ch}: SINK gen CRC 0x{exp_crc:08X} != "
                              f"golden 0x{gold_crc:08X}")
            if act_crc != gold_crc:
                errors.append(f"ch{ch}: SINK wr CRC 0x{act_crc:08X} != "
                              f"golden 0x{gold_crc:08X}")
            if exp_crc == act_crc == gold_crc:
                self.log.info(f"  ch{ch}: SINK CRC match 0x{act_crc:08X} "
                              f"(gen==wr==golden, valid)")

        se = self._read_u32(d.snk_sched_error)
        if se not in (0, -1):
            errors.append(f"snk_sched_error=0x{se:X}")

        if errors:
            for e in errors:
                self.log.error(f"  SCOREBOARD: {e}")
        else:
            self.log.info(f"  SCOREBOARD: SINK self-check PASSED for "
                          f"{n_active} channels ({beats} beats each)")
        return (len(errors) == 0), {'errors': errors, 'results': results,
                                    'wr_beat_count_total': wr_total}

    # =========================================================================
    # TEST: SOURCE self-check  (m_axi_rd LFSR -> source -> m_axis chk)
    # =========================================================================

    async def run_source_selfcheck(self, active_channels, beats):
        self.log.info(f"=== SOURCE self-check: channels={active_channels}, "
                      f"{beats} beats/channel ===")
        d = self.dut
        n_active = len(active_channels)

        # 1. Reset the source-read LFSR/CRC pattern generator.
        await self._pulse(d.rd_crc_lfsr_reset)

        # 2. Arm the AXIS pattern checker (seed 0 => DEADBEEF, matches rd gen).
        d.chk_cfg_lfsr_seed.value = 0
        d.chk_ready_en.value = 1
        await self._pulse(d.chk_cfg_start)

        # 3. Load a SOURCE DATA descriptor per active channel into the SRC desc RAM.
        for ch in active_channels:
            desc_addr = self.DESC_BASE + ch * 0x1000
            src_addr = self.SRC_BASE + ch * self.CHANNEL_OFFSET
            desc = self.create_descriptor(src_addr, 0, beats, channel_id=ch)
            await self.load_descriptor('src', desc_addr, desc)

        # 4. Kick each channel's SOURCE descriptor over APB.
        for ch in active_channels:
            desc_addr = self.DESC_BASE + ch * 0x1000
            await self.kick_off_channel('src', ch, desc_addr)

        # 5. Wait for the source to go idle AND for all beats to be checked.
        expected_total = beats * n_active
        ok_idle = await self._wait_for(
            lambda: (int(d.src_system_idle.value) == 1 and
                     self._read_u32(d.o_chk_beat_count_total) == expected_total),
            timeout_cycles=60000)

        await self.wait_clocks(self.clk_name, 50)

        # 6. Per-channel scoreboard: o_chk_actual_crc[ch] == rd_crc_value[ch].
        errors = []
        results = {}
        chk_total = self._read_u32(d.o_chk_beat_count_total)
        data_error = self._read_u32(d.o_data_error)
        if not ok_idle:
            errors.append(f"timeout: src_system_idle={int(d.src_system_idle.value)} "
                          f"o_chk_beat_count_total={chk_total} (expected {expected_total})")
        if chk_total != expected_total:
            errors.append(f"o_chk_beat_count_total={chk_total} != expected {expected_total}")
        if data_error not in (0,):
            errors.append(f"o_data_error asserted (0x{data_error:X})")

        for ch in active_channels:
            exp_crc = self._read_ch_word(d.rd_crc_value, ch)
            act_crc = self._read_ch_word(d.o_chk_actual_crc, ch)
            gold_crc = golden_crc(ch, beats)
            src_valid = self._read_ch_bit(d.rd_crc_valid, ch)
            chk_valid = self._read_ch_bit(d.o_chk_actual_crc_valid, ch)
            results[ch] = (exp_crc, act_crc)
            if not src_valid:
                errors.append(f"ch{ch}: rd_crc_valid=0")
            if not chk_valid:
                errors.append(f"ch{ch}: o_chk_actual_crc_valid=0")
            if exp_crc != act_crc:
                errors.append(f"ch{ch}: SOURCE CRC mismatch rd=0x{exp_crc:08X} "
                              f"chk=0x{act_crc:08X}")
            # Validate BOTH the read-served CRC and the AXIS checker's actual CRC
            # against the independent golden reference.
            if exp_crc != gold_crc:
                errors.append(f"ch{ch}: SOURCE rd CRC 0x{exp_crc:08X} != "
                              f"golden 0x{gold_crc:08X}")
            if act_crc != gold_crc:
                errors.append(f"ch{ch}: SOURCE chk CRC 0x{act_crc:08X} != "
                              f"golden 0x{gold_crc:08X}")
            if exp_crc == act_crc == gold_crc:
                self.log.info(f"  ch{ch}: SOURCE CRC match 0x{act_crc:08X} "
                              f"(rd==chk==golden, valid)")

        se = self._read_u32(d.src_sched_error)
        if se not in (0, -1):
            errors.append(f"src_sched_error=0x{se:X}")

        if errors:
            for e in errors:
                self.log.error(f"  SCOREBOARD: {e}")
        else:
            self.log.info(f"  SCOREBOARD: SOURCE self-check PASSED for "
                          f"{n_active} channels ({beats} beats each)")
        return (len(errors) == 0), {'errors': errors, 'results': results,
                                    'o_chk_beat_count_total': chk_total,
                                    'o_data_error': data_error}
