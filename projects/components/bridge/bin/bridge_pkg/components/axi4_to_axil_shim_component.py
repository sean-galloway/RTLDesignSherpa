#!/usr/bin/env python3
# SPDX-License-Identifier: MIT
# SPDX-FileCopyrightText: 2024-2025 sean galloway
#
# Typed component wrapper for axi4_to_axil{4,5}_{wr,rd} instantiations.
#
# Mirrors Axi4ToApbShim. The crossbar always carries full AXI4 across the
# fabric; at the slave boundary AXIL-protocol slaves get a shim that
# burst-decomposes AXI4 transactions into AXIL4 single-beat transactions.
# Read and write are separate converter modules in
# projects/components/converters/rtl/, so the rw case instantiates both
# side-by-side.
#
# The class keeps the parameter list, port list, and tie-off widths in
# one place so call sites can't mistype a port name or pick the wrong
# tie-off width (the bug that bit Axi4ToApbShim before this typing).

from typing import List, Optional
from rtl_generators.verilog.module import Module


class Axi4ToAxilShim:
    """Generate `axi4_to_axil{4,5}_wr` and/or `_rd` instantiations.

    `protocol` selects which: 'axil4' emits the AXI4-Lite converters, 'axil5'
    emits the AXI5-Lite ones. The AXI5-Lite modules WRAP the AXI4-Lite ones,
    so the AXI4 (crossbar-facing) and AXI4-Lite (slave-facing) port lists are
    identical between the two -- the only difference is the module name, the
    ENABLE_*/width parameters, and the sideband ports appended at the end.

    Usage (rw):
        shim = Axi4ToAxilShim(
            instance_base='u_dma_axil',
            id_width=4, addr_width=32, data_width=32,
            has_write=True, has_read=True,
        )
        shim.connect_clocks_and_resets()
        shim.connect_axi_write_channel(
            crossbar_prefix='xbar_dma_axil_axi_',
            bvalid_intercept='converter_bvalid',
            bready_intercept='converter_bready',
        )
        shim.connect_axi_read_channel(
            crossbar_prefix='xbar_dma_axil_axi_',
            rvalid_intercept='converter_rvalid',
            rready_intercept='converter_rready',
            rlast_intercept='converter_rlast',
        )
        shim.connect_axil_master(prefix='dma_axil_')
        for line in shim.generate_lines():
            ...
    """

    def __init__(
        self,
        instance_base: str,
        id_width: int,
        addr_width: int,
        data_width: int,
        has_write: bool,
        has_read: bool,
        skid_depth_aw: int = 2,
        skid_depth_w: int = 4,
        skid_depth_b: int = 4,
        skid_depth_ar: int = 2,
        skid_depth_r: int = 4,
        axi_user_width: int = 1,
        protocol: str = 'axil4',
        axi5_features=None,
        loop_width: int = 1,
    ):
        assert has_write or has_read, "shim must carry at least one channel"
        if protocol not in ('axil4', 'axil5'):
            raise ValueError(f"Axi4ToAxilShim: unsupported protocol {protocol!r}")
        if protocol != 'axil5' and axi5_features:
            raise ValueError("axi5_features passed but protocol is not 'axil5'")
        self.protocol = protocol
        self.axi5_features = list(axi5_features or ())
        # The AXI5-Lite USER width matches the fabric's AXI4 USER width: USER
        # is the only address-channel group with an AXI4 source, so widening
        # it here would only pad zeros.
        self.user_width = axi_user_width
        self.loop_width = loop_width
        self.instance_base = instance_base
        self.id_width = id_width
        self.addr_width = addr_width
        self.data_width = data_width
        self.axi_user_width = axi_user_width
        self.has_write = has_write
        self.has_read = has_read

        # Per-channel skid depths
        self._skid_depth_aw = skid_depth_aw
        self._skid_depth_w = skid_depth_w
        self._skid_depth_b = skid_depth_b
        self._skid_depth_ar = skid_depth_ar
        self._skid_depth_r = skid_depth_r

        # Per-converter section storage. The wr and rd converters are
        # separate SV modules, so they each get their own
        # parameter/port grouping. Each entry is:
        #   {'kind': 'wr'|'rd', 'instance_name': ..., 'sections': [...]}
        # where sections is a list of (section_comment, [(port, conn), ...]).
        self._converters: List[dict] = []

    # --- connection helpers --------------------------------------------

    def connect_clocks_and_resets(self, aclk: str = 'aclk', aresetn: str = 'aresetn') -> None:
        """Add clock/reset section to every converter we'll emit."""
        self._aclk = aclk
        self._aresetn = aresetn
        # Lazily build entries on the first channel-connect call; clock
        # ties are appended via _ensure_converter().

    def _ensure_converter(self, kind: str) -> dict:
        for entry in self._converters:
            if entry['kind'] == kind:
                return entry
        entry = {
            'kind': kind,
            'instance_name': f"{self.instance_base}_{kind}",
            'sections': [(
                "Clocks and resets",
                [('aclk', getattr(self, '_aclk', 'aclk')),
                 ('aresetn', getattr(self, '_aresetn', 'aresetn'))],
            )],
        }
        self._converters.append(entry)
        return entry

    def connect_axi_write_channel(self, crossbar_prefix: str,
                                  bvalid_intercept: Optional[str] = None,
                                  bready_intercept: Optional[str] = None) -> None:
        """Wire AW/W from the crossbar and route B through the intercepts.
        Mirror of Axi4ToApbShim.connect_axi_write_channel -- the
        bridge_id-tracking FIFO needs to see B at the shim's s_axi side,
        not after it's been wired back to the crossbar."""
        if not self.has_write:
            raise RuntimeError("Axi4ToAxilShim: cannot connect write channel when has_write=False")
        pfx = crossbar_prefix
        pairs = [
            # AW from crossbar
            ('s_axi_awid', f'{pfx}awid'),
            ('s_axi_awaddr', f'{pfx}awaddr'),
            ('s_axi_awlen', f'{pfx}awlen'),
            ('s_axi_awsize', f'{pfx}awsize'),
            ('s_axi_awburst', f'{pfx}awburst'),
            ('s_axi_awlock', f'{pfx}awlock'),
            ('s_axi_awcache', f'{pfx}awcache'),
            ('s_axi_awprot', f'{pfx}awprot'),
            ('s_axi_awqos', f'{pfx}awqos'),
            ('s_axi_awregion', f'{pfx}awregion'),
            ('s_axi_awuser', f'{pfx}awuser'),
            ('s_axi_awvalid', f'{pfx}awvalid'),
            ('s_axi_awready', f'{pfx}awready'),
            # W from crossbar
            ('s_axi_wdata', f'{pfx}wdata'),
            ('s_axi_wstrb', f'{pfx}wstrb'),
            ('s_axi_wlast', f'{pfx}wlast'),
            ('s_axi_wuser', f'{pfx}wuser'),
            ('s_axi_wvalid', f'{pfx}wvalid'),
            ('s_axi_wready', f'{pfx}wready'),
            # B back to crossbar -- routed via intercepts so the
            # bridge_id-tracking FIFO can hook the shim's response side.
            ('s_axi_bid', f'{pfx}bid'),
            ('s_axi_bresp', f'{pfx}bresp'),
            ('s_axi_buser', f'{pfx}buser'),
            ('s_axi_bvalid', bvalid_intercept if bvalid_intercept else f'{pfx}bvalid'),
            ('s_axi_bready', bready_intercept if bready_intercept else f'{pfx}bready'),
        ]
        entry = self._ensure_converter('wr')
        entry['sections'].append(("AXI4 write channels (from crossbar)", pairs))

    def connect_axi_read_channel(self, crossbar_prefix: str,
                                 rvalid_intercept: Optional[str] = None,
                                 rready_intercept: Optional[str] = None,
                                 rlast_intercept: Optional[str] = None) -> None:
        if not self.has_read:
            raise RuntimeError("Axi4ToAxilShim: cannot connect read channel when has_read=False")
        pfx = crossbar_prefix
        pairs = [
            # AR from crossbar
            ('s_axi_arid', f'{pfx}arid'),
            ('s_axi_araddr', f'{pfx}araddr'),
            ('s_axi_arlen', f'{pfx}arlen'),
            ('s_axi_arsize', f'{pfx}arsize'),
            ('s_axi_arburst', f'{pfx}arburst'),
            ('s_axi_arlock', f'{pfx}arlock'),
            ('s_axi_arcache', f'{pfx}arcache'),
            ('s_axi_arprot', f'{pfx}arprot'),
            ('s_axi_arqos', f'{pfx}arqos'),
            ('s_axi_arregion', f'{pfx}arregion'),
            ('s_axi_aruser', f'{pfx}aruser'),
            ('s_axi_arvalid', f'{pfx}arvalid'),
            ('s_axi_arready', f'{pfx}arready'),
            # R back to crossbar -- routed via intercepts.
            ('s_axi_rid', f'{pfx}rid'),
            ('s_axi_rdata', f'{pfx}rdata'),
            ('s_axi_rresp', f'{pfx}rresp'),
            ('s_axi_rlast', rlast_intercept if rlast_intercept else f'{pfx}rlast'),
            ('s_axi_ruser', f'{pfx}ruser'),
            ('s_axi_rvalid', rvalid_intercept if rvalid_intercept else f'{pfx}rvalid'),
            ('s_axi_rready', rready_intercept if rready_intercept else f'{pfx}rready'),
        ]
        entry = self._ensure_converter('rd')
        entry['sections'].append(("AXI4 read channels (from crossbar)", pairs))

    def connect_axil_master(self, prefix: str) -> None:
        """Wire the m_axil_* outputs to the external AXIL slave port.
        `prefix` is the slave's external prefix (e.g., 'dma_axil_'), and
        the shim's lowercase AXIL signal names are appended to it."""
        if self.has_write:
            pairs_wr = [
                ('m_axil_awaddr',  f'{prefix}awaddr'),
                ('m_axil_awprot',  f'{prefix}awprot'),
                ('m_axil_awvalid', f'{prefix}awvalid'),
                ('m_axil_awready', f'{prefix}awready'),
                ('m_axil_wdata',   f'{prefix}wdata'),
                ('m_axil_wstrb',   f'{prefix}wstrb'),
                ('m_axil_wvalid',  f'{prefix}wvalid'),
                ('m_axil_wready',  f'{prefix}wready'),
                ('m_axil_bresp',   f'{prefix}bresp'),
                ('m_axil_bvalid',  f'{prefix}bvalid'),
                ('m_axil_bready',  f'{prefix}bready'),
            ]
            entry = self._ensure_converter('wr')
            entry['sections'].append((
                "AXI4-Lite master write interface (to external slave)", pairs_wr))
        if self.has_read:
            pairs_rd = [
                ('m_axil_araddr',  f'{prefix}araddr'),
                ('m_axil_arprot',  f'{prefix}arprot'),
                ('m_axil_arvalid', f'{prefix}arvalid'),
                ('m_axil_arready', f'{prefix}arready'),
                ('m_axil_rdata',   f'{prefix}rdata'),
                ('m_axil_rresp',   f'{prefix}rresp'),
                ('m_axil_rvalid',  f'{prefix}rvalid'),
                ('m_axil_rready',  f'{prefix}rready'),
            ]
            entry = self._ensure_converter('rd')
            entry['sections'].append((
                "AXI4-Lite master read interface (to external slave)", pairs_rd))

        if self.protocol == 'axil5':
            self._connect_axil5_sideband(prefix)

    def _connect_axil5_sideband(self, prefix: str) -> None:
        """Wire every AXI5-Lite sideband port straight out to the boundary.

        Every field in the table is connected, enabled or not: the converter
        drives a disabled group to 0 rather than leaving it dangling, so the
        external surface has the same shape in every build. Leaving a port
        unconnected instead would read as PINMISSING and float on the slave.
        """
        from ..axil5_sideband import sideband_ports, WRITE_CHANNELS

        channels = ('rw' if (self.has_write and self.has_read)
                    else 'wr' if self.has_write else 'rd')
        write_bases = {base for base, _w, _d in sideband_ports('wr')}

        wr_pairs, rd_pairs = [], []
        for base, _width_key, _direction in sideband_ports(channels):
            pair = (f'm_axil_{base}', f'{prefix}{base}')
            (wr_pairs if base in write_bases else rd_pairs).append(pair)

        if wr_pairs:
            self._ensure_converter('wr')['sections'].append((
                "AXI5-Lite write sideband (to external slave)", wr_pairs))
        if rd_pairs:
            self._ensure_converter('rd')['sections'].append((
                "AXI5-Lite read sideband (to external slave)", rd_pairs))

    def _axil5_param_suffix(self) -> str:
        """ENABLE_* and sideband widths, appended to the base parameter list."""
        from ..axil5_sideband import (enable_params, MPAM_WIDTH, MECID_WIDTH,
                                      NSAID_WIDTH)
        parts = [f"parameter bit {name} = {value}"
                 for name, value in enable_params(self.axi5_features)]
        parts += [
            f"parameter int USER_WIDTH  = {self.user_width}",
            f"parameter int LOOP_WIDTH  = {self.loop_width}",
            f"parameter int MPAM_WIDTH  = {MPAM_WIDTH}",
            f"parameter int MECID_WIDTH = {MECID_WIDTH}",
            f"parameter int NSAID_WIDTH = {NSAID_WIDTH}",
        ]
        return ", " + ", ".join(parts)

    # --- formatting ----------------------------------------------------

    def _format_param_str_wr(self) -> str:
        return (
            f"parameter int AXI_ID_WIDTH     = {self.id_width}, "
            f"parameter int AXI_ADDR_WIDTH   = {self.addr_width}, "
            f"parameter int AXI_DATA_WIDTH   = {self.data_width}, "
            f"parameter int AXI_USER_WIDTH   = {self.axi_user_width}"
            # axi4_to_axil4_wr declares NO skid-depth parameters. It used to take
            # SKID_DEPTH_AW/W/B; passing them now is an elaboration error in every
            # generated bridge. The write path buffers internally, so there is
            # nothing left to size from here.
        )

    def _format_param_str_rd(self) -> str:
        return (
            f"parameter int AXI_ID_WIDTH     = {self.id_width}, "
            f"parameter int AXI_ADDR_WIDTH   = {self.addr_width}, "
            f"parameter int AXI_DATA_WIDTH   = {self.data_width}, "
            f"parameter int AXI_USER_WIDTH   = {self.axi_user_width}"
            # ALL skid-depth parameters are gone from axi4_to_axil4_rd/wr --
            # the modules never contained a skid buffer, and the parameter
            # surface was removed with the false header claims. SKID_DEPTH_R
            # briefly survived that cleanup (it was the last parameter, no
            # trailing comma) and is now gone too.
        )

    def generate_lines(self) -> List[str]:
        """Emit one multi-line instantiation block per converter."""
        if not self._converters:
            raise RuntimeError("Axi4ToAxilShim: nothing to instantiate")

        lines: List[str] = []
        # Emit wr first then rd if both present, for stable ordering.
        ordered = sorted(self._converters, key=lambda e: 0 if e['kind'] == 'wr' else 1)
        for entry in ordered:
            kind = entry['kind']
            instance_name = entry['instance_name']
            family = 'axil5' if self.protocol == 'axil5' else 'axil4'
            module_name = f"axi4_to_{family}_{kind}"
            param_str = (self._format_param_str_wr() if kind == 'wr'
                         else self._format_param_str_rd())
            if self.protocol == 'axil5':
                param_str += self._axil5_param_suffix()
            module = Module(module_name=module_name, instance_name=instance_name)
            module.params.add_param_string(param_str)

            all_pairs = []
            for _, pairs in entry['sections']:
                all_pairs.extend(pairs)

            lines.append(f"    {module_name} #(")
            param_inst = module.params.create_param_instance()
            param_parts = [p.strip() for p in param_inst.split(',') if p.strip()]
            for i, p in enumerate(param_parts):
                sep = "," if i < len(param_parts) - 1 else ""
                lines.append(f"        {p}{sep}")
            lines.append(f"    ) {instance_name} (")

            last_idx = len(all_pairs) - 1
            running = 0
            for section_comment, pairs in entry['sections']:
                if section_comment:
                    lines.append(f"        // {section_comment}")
                for port, connector in pairs:
                    is_last = (running == last_idx)
                    sep = "" if is_last else ","
                    lines.append(f"        .{port}({connector}){sep}")
                    running += 1
                lines.append("")
            if lines and lines[-1] == "":
                lines.pop()
            lines.append("    );")
            lines.append("")
        return lines
