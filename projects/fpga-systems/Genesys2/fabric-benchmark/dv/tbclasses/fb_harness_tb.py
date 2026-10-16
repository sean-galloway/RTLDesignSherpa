# SPDX-License-Identifier: MIT
# SPDX-FileCopyrightText: 2026 sean galloway
"""fb_harness testbench: the board's own host program, over the sim UART.

K0 gate (PRD section 6): fabric-only mode (W2) in sim -- STREAM moves data from
the LFSR source (S2) to the CRC sink (S3) through the data fabric under test,
driven by the Genesys 2 STREAM characterization runner, unchanged, over a
cocotb UART channel. The runner is the class the board's host program builds;
the only thing this harness gives it is a DescriptorBuilder for the fabric's
data map:

    sources       0x9000_0000 + ch x 32 MB   (S2, channel = address bits [27:25])
    destinations  0xA000_0000 + ch x 32 MB   (S3)
    descriptors   preloaded at 0x0002_0000 over the configuration bridge,
                  fetched by STREAM at 0x8000_0000 over the data fabric (S1)

S0 (DDR3) is answered by framework AXI4 slave BFMs over a MemoryModel; nothing
in W2 touches it. K3's DDR3 workloads (W1-F2, W1-F1, W4) run as the
CRC-checked chain of bin/fb_workloads.py, the same code the board runs.

A pass means, per run: the runner's verdict is pass, the on-chip run timer
finished with PASS, and every active channel is in both the CRC valid and
match masks (and no other channel is).
"""
from __future__ import annotations

import os
import sys

import cocotb
from cocotb._bridge import bridge

from CocoTBFramework.components.axi4.axi4_factories import create_axi4_slave_rd, create_axi4_slave_wr
from CocoTBFramework.components.shared.memory_model import MemoryModel
from TBClasses.harness.cocotb_axil_bridge import make_uart_channel
from TBClasses.shared.tbbase import TBBase
from TBClasses.shared.utilities import get_repo_root

# The data map is shared with the board program: bin/fb_map.py.
_AREA_BIN = os.path.join(get_repo_root(), 'projects/fpga-systems/Genesys2/fabric-benchmark/bin')
if _AREA_BIN not in sys.path:
    sys.path.insert(0, _AREA_BIN)
import fb_map  # noqa: E402
fb_map.stream_host_path()
from uart_axi_bridge import UARTAxiBridge  # noqa: E402
from descriptor_builder import CharConfig  # noqa: E402
from fb_slave_meters import read_slave_side  # noqa: E402
import fb_workloads  # noqa: E402

DDR_BYTES = 0x10000                  # modelled span of S0 when no chain runs


class FbHarnessTB(TBBase):
    def __init__(self, dut, ddr_bytes: int = DDR_BYTES):
        super().__init__(dut)
        self.aclk_ns = float(os.environ.get('ACLK_PERIOD_NS', '10'))
        self.ep_ns = float(os.environ.get('EP_PERIOD_NS', '8'))
        fpga_clk_hz = int(os.environ.get('FPGA_CLK_HZ', '100000000'))
        uart_baud = int(os.environ.get('UART_BAUD', '25000000'))
        self.clks_per_bit = fpga_clk_hz // uart_baud
        self.channel = make_uart_channel(dut, dut.aclk, self.clks_per_bit,
                                         rx_signal='i_uart_rx', tx_signal='o_uart_tx',
                                         log=self.log)
        self.bridge = UARTAxiBridge(channel=self.channel)
        self.builder = fb_map.make_builder()
        self.ddr = MemoryModel(num_lines=max(ddr_bytes, DDR_BYTES) // 16, bytes_per_line=16,
                               log=self.log)
        kw = dict(dut=dut, clock=dut.aclk, prefix='ddr', log=self.log, id_width=10,
                  addr_width=32, data_width=128, user_width=1, memory_model=self.ddr,
                  base_addr=0)
        self.ddr_rd = create_axi4_slave_rd(**kw)
        self.ddr_wr = create_axi4_slave_wr(**kw)
        self._runner = None
        self.results: list[dict] = []
        self.errors: list[str] = []

    # ---- mandatory ----------------------------------------------------------
    async def setup_clocks_and_reset(self):
        self.dut.i_uart_rx.value = 1
        # Board status for fb_ctl STATUS: the sim's S0 model is always ready.
        self.dut.i_ddr_init_done.value = 1
        self.dut.i_ddr_init_error.value = 0
        self.dut.i_ddr_pll_locked.value = 1
        self.dut.i_ep_mmcm_locked.value = 1
        await self.start_clock('aclk', self.aclk_ns, 'ns')
        await self.start_clock('ep_clk', self.ep_ns, 'ns')
        await self.assert_reset()
        await self.wait_clocks('aclk', 20)
        await self.deassert_reset()
        await self.wait_clocks('aclk', 20)

    async def assert_reset(self):
        self.dut.aresetn.value = 0
        self.dut.ep_aresetn.value = 0

    async def deassert_reset(self):
        self.dut.aresetn.value = 1
        self.dut.ep_aresetn.value = 1

    # ---- the board's runner -------------------------------------------------
    @property
    def runner(self):
        if self._runner is None:
            from characterization import CharacterizationRunner
            self._runner = CharacterizationRunner(
                self.bridge, data_width=128, builder=self.builder,
                verbose=os.environ.get('CHAR_VERBOSE', '0') == '1')
            self._runner.log = lambda msg, _l=self.log: _l.info(f"  [runner] {msg}")
        return self._runner

    async def ping(self) -> bool:
        ok = await bridge(self.runner.ping)()
        if not ok:
            self.errors.append("ping failed (UART link, harness_csr SCRATCH or BUILD_ID)")
        return bool(ok)

    async def run(self, num_channels: int, descriptors: int, transfer_bytes: int) -> dict:
        cfg = CharConfig(name=f"w2_{num_channels}ch_{descriptors}desc_{transfer_bytes // 1024}KB",
                         num_channels=num_channels, descriptors_per_channel=descriptors,
                         transfer_bytes=transfer_bytes)
        runner = self.runner
        res = await bridge(lambda: runner.run_config(cfg))()
        self.results.append(res)
        crc = res.get('crc') or {}
        active = (1 << num_channels) - 1
        if not res.get('pass'):
            self.errors.append(f"{cfg.name}: runner verdict FAIL ({res.get('error')})")
        if crc.get('valid_mask') != active or crc.get('match_mask') != active:
            self.errors.append(f"{cfg.name}: crc valid 0x{crc.get('valid_mask', 0):X} "
                               f"match 0x{crc.get('match_mask', 0):X}, want 0x{active:X}")
        # Slave-side observer (the fabric's output): every beat crosses the
        # fabric once at the same width, so over the shared window its
        # productive count must equal the master side's AND the transfer size
        # in beats. A dead or mis-wired observer cannot pass this.
        slv = await bridge(lambda: read_slave_side(self.bridge))()
        met = res.get('metrics') or {}
        want_beats = num_channels * descriptors * transfer_bytes // (fb_map.DATA_WIDTH // 8)
        for side, key in (('r', 'r_aggregate'), ('w', 'w_aggregate')):
            m_prod = (met.get(key) or {}).get('productive')
            s_prod = slv[side]['productive']
            if not (m_prod == s_prod == want_beats):
                self.errors.append(f"{cfg.name}: {side} productive beats master {m_prod}, "
                                   f"slave {s_prod}, want {want_beats}")
        res['slave_side'] = slv
        self.log.info(f"{cfg.name}: pass={res.get('pass')} "
                      f"cycles={res.get('bus_cycles_total')} "
                      f"bus_mbps={res.get('bus_throughput_mbps')} "
                      f"valid=0x{crc.get('valid_mask', 0):X} match=0x{crc.get('match_mask', 0):X} "
                      f"util m r/w {met.get('datapath_utilization_r')}/{met.get('datapath_utilization_w')} "
                      f"s r/w {slv['r_util']:.4f}/{slv['w_util']:.4f}")
        return res

    async def chain(self, num_channels: int, descriptors: int, transfer_bytes: int) -> list:
        """The DDR3 workload chain (fb_workloads.CHAIN) on one config."""
        cfg = CharConfig(name=f"k3_{num_channels}ch_{descriptors}desc_{transfer_bytes // 1024}KB",
                         num_channels=num_channels, descriptors_per_channel=descriptors,
                         transfer_bytes=transfer_bytes)
        runner = self.runner
        steps = await bridge(lambda: fb_workloads.run_chain(
            runner, self.bridge, cfg, log=lambda m: self.log.info(f"{cfg.name}{m}")))()
        for r in steps:
            self.results.append(r)
            if not r['verdict']:
                self.errors.append(f"{cfg.name} {r['step']}: {'; '.join(r['why'])}")
        if len(steps) != len(fb_workloads.CHAIN):
            self.errors.append(f"{cfg.name}: {len(steps)} of {len(fb_workloads.CHAIN)} steps ran")
        return steps

    def report(self) -> bool:
        for e in self.errors:
            self.log.error(e)
        return not self.errors
