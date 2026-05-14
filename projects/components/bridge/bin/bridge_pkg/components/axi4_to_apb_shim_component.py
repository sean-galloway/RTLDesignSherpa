#!/usr/bin/env python3
# SPDX-License-Identifier: MIT
# SPDX-FileCopyrightText: 2024-2025 sean galloway
#
# Typed component wrapper for axi4_to_apb_shim instantiation.
#
# Centralises the shim's parameter list, port list, tie-off widths, and
# multi-line formatting so callers can't mistype a port name or pick the
# wrong tie-off width. Previously every call site emitted ~140 lines of
# `lines.append(f"...")` -- which is exactly where this session's
# 32b/64b AXI_DATA_WIDTH mismatch and `8'b0` tie-off width bugs lived.
#
# The class uses rtl_generators.verilog.Module for typed parameter
# storage and a small in-class formatter for grouped multi-line output
# (Module.instantiate() itself emits single-line, which is unreadable
# for a 50-port shim).

from typing import List, Optional
from rtl_generators.verilog.module import Module


class Axi4ToApbShim:
    """Generate an `axi4_to_apb_shim` instantiation block.

    Usage:
        shim = Axi4ToApbShim(
            instance_name='u_apb_periph_apb_converter',
            id_width=4, addr_width=32,
            axi_data_width=32, apb_data_width=32,
            has_write=True, has_read=True,
        )
        shim.connect_clocks_and_resets()  # defaults to aclk/aresetn
        shim.connect_axi_write_channel(
            crossbar_prefix='xbar_apb_periph_axi_',
            bvalid_intercept='converter_bvalid',
            bready_intercept='converter_bready',
        )
        shim.connect_axi_read_channel(
            crossbar_prefix='xbar_apb_periph_axi_',
            rvalid_intercept='converter_rvalid',
            rready_intercept='converter_rready',
            rlast_intercept='converter_rlast',
        )
        shim.connect_apb_master(prefix='apb_periph_')
        for line in shim.generate_lines():
            ...
    """

    def __init__(
        self,
        instance_name: str,
        id_width: int,
        addr_width: int,
        axi_data_width: int,
        apb_data_width: int,
        has_write: bool,
        has_read: bool,
        depth_aw: int = 2,
        depth_w: int = 4,
        depth_b: int = 2,
        depth_ar: int = 2,
        depth_r: int = 4,
        side_depth: int = 4,
        apb_cmd_depth: int = 4,
        apb_rsp_depth: int = 4,
        axi_user_width: int = 1,
    ):
        assert has_write or has_read, "shim must carry at least one channel"
        self.instance_name = instance_name
        self.id_width = id_width
        self.addr_width = addr_width
        self.axi_data_width = axi_data_width
        self.apb_data_width = apb_data_width
        self.axi_user_width = axi_user_width
        self.has_write = has_write
        self.has_read = has_read

        self.module = Module(module_name='axi4_to_apb_shim',
                             instance_name=instance_name)
        param_str = (
            f"parameter int DEPTH_AW         = {depth_aw}, "
            f"parameter int DEPTH_W          = {depth_w}, "
            f"parameter int DEPTH_B          = {depth_b}, "
            f"parameter int DEPTH_AR         = {depth_ar}, "
            f"parameter int DEPTH_R          = {depth_r}, "
            f"parameter int SIDE_DEPTH       = {side_depth}, "
            f"parameter int APB_CMD_DEPTH    = {apb_cmd_depth}, "
            f"parameter int APB_RSP_DEPTH    = {apb_rsp_depth}, "
            f"parameter int AXI_ID_WIDTH     = {id_width}, "
            f"parameter int AXI_ADDR_WIDTH   = {addr_width}, "
            f"parameter int AXI_DATA_WIDTH   = {axi_data_width}, "
            f"parameter int AXI_USER_WIDTH   = {axi_user_width}, "
            f"parameter int APB_ADDR_WIDTH   = {addr_width}, "
            f"parameter int APB_DATA_WIDTH   = {apb_data_width}"
        )
        self.module.params.add_param_string(param_str)

        # Grouped (port, connector) tuples by section. The formatter
        # walks these in order and emits a section comment + the
        # contents of each group.
        self._sections: List[tuple] = []  # list of (section_comment, [(port, connector), ...])

    # --- connection helpers --------------------------------------------

    def connect_clocks_and_resets(self, aclk: str = 'aclk', aresetn: str = 'aresetn',
                                  pclk: Optional[str] = None, presetn: Optional[str] = None) -> None:
        pclk = pclk if pclk is not None else aclk
        presetn = presetn if presetn is not None else aresetn
        self._sections.append((
            "Clocks and resets (single clock domain by default)",
            [('aclk', aclk), ('aresetn', aresetn),
             ('pclk', pclk), ('presetn', presetn)],
        ))

    def connect_axi_write_channel(self, crossbar_prefix: str,
                                  bvalid_intercept: Optional[str] = None,
                                  bready_intercept: Optional[str] = None,
                                  bid_intercept: Optional[str] = None,
                                  bresp_intercept: Optional[str] = None) -> None:
        """Wire AW/W to the crossbar and B to either the crossbar or
        the supplied intercept signals (typically the adapter's
        `converter_bvalid` / `converter_bready` so the bridge_id-tracking
        FIFO can monitor the shim's response side directly)."""
        if not self.has_write:
            raise RuntimeError("Axi4ToApbShim: cannot connect write channel when has_write=False")
        pfx = crossbar_prefix
        pairs = [
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
            ('s_axi_wdata', f'{pfx}wdata'),
            ('s_axi_wstrb', f'{pfx}wstrb'),
            ('s_axi_wlast', f'{pfx}wlast'),
            ('s_axi_wuser', f'{pfx}wuser'),
            ('s_axi_wvalid', f'{pfx}wvalid'),
            ('s_axi_wready', f'{pfx}wready'),
            ('s_axi_bid', bid_intercept if bid_intercept else f'{pfx}bid'),
            ('s_axi_bresp', bresp_intercept if bresp_intercept else f'{pfx}bresp'),
            ('s_axi_buser', f'{pfx}buser'),
            ('s_axi_bvalid', bvalid_intercept if bvalid_intercept else f'{pfx}bvalid'),
            ('s_axi_bready', bready_intercept if bready_intercept else f'{pfx}bready'),
        ]
        self._sections.append(("AXI4 write channels (from crossbar)", pairs))

    def tie_off_axi_write_channel(self) -> None:
        """Tie all write-side AXI ports to zero. Tie-off widths are
        derived from the shim's parameters -- callers can't pick the
        wrong width by hand."""
        strb_width = self.axi_data_width // 8
        pairs = [
            ('s_axi_awid', f"{self.id_width}'b0"),
            ('s_axi_awaddr', f"{self.addr_width}'b0"),
            ('s_axi_awlen', "8'b0"),
            ('s_axi_awsize', "3'b0"),
            ('s_axi_awburst', "2'b0"),
            ('s_axi_awlock', "1'b0"),
            ('s_axi_awcache', "4'b0"),
            ('s_axi_awprot', "3'b0"),
            ('s_axi_awqos', "4'b0"),
            ('s_axi_awregion', "4'b0"),
            ('s_axi_awuser', "1'b0"),
            ('s_axi_awvalid', "1'b0"),
            ('s_axi_awready', ""),  # unconnected output
            ('s_axi_wdata', f"{self.axi_data_width}'b0"),
            ('s_axi_wstrb', f"{strb_width}'b0"),
            ('s_axi_wlast', "1'b0"),
            ('s_axi_wuser', "1'b0"),
            ('s_axi_wvalid', "1'b0"),
            ('s_axi_wready', ""),
            ('s_axi_bid', ""),
            ('s_axi_bresp', ""),
            ('s_axi_buser', ""),
            ('s_axi_bvalid', ""),
            ('s_axi_bready', "1'b0"),
        ]
        self._sections.append(("AXI4 write channels (tied off — read-only bridge)", pairs))

    def connect_axi_read_channel(self, crossbar_prefix: str,
                                 rvalid_intercept: Optional[str] = None,
                                 rready_intercept: Optional[str] = None,
                                 rlast_intercept: Optional[str] = None) -> None:
        if not self.has_read:
            raise RuntimeError("Axi4ToApbShim: cannot connect read channel when has_read=False")
        pfx = crossbar_prefix
        pairs = [
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
            ('s_axi_rid', f'{pfx}rid'),
            ('s_axi_rdata', f'{pfx}rdata'),
            ('s_axi_rresp', f'{pfx}rresp'),
            ('s_axi_rlast', rlast_intercept if rlast_intercept else f'{pfx}rlast'),
            ('s_axi_ruser', f'{pfx}ruser'),
            ('s_axi_rvalid', rvalid_intercept if rvalid_intercept else f'{pfx}rvalid'),
            ('s_axi_rready', rready_intercept if rready_intercept else f'{pfx}rready'),
        ]
        self._sections.append(("AXI4 read channels (from crossbar)", pairs))

    def tie_off_axi_read_channel(self) -> None:
        pairs = [
            ('s_axi_arid', f"{self.id_width}'b0"),
            ('s_axi_araddr', f"{self.addr_width}'b0"),
            ('s_axi_arlen', "8'b0"),
            ('s_axi_arsize', "3'b0"),
            ('s_axi_arburst', "2'b0"),
            ('s_axi_arlock', "1'b0"),
            ('s_axi_arcache', "4'b0"),
            ('s_axi_arprot', "3'b0"),
            ('s_axi_arqos', "4'b0"),
            ('s_axi_arregion', "4'b0"),
            ('s_axi_aruser', "1'b0"),
            ('s_axi_arvalid', "1'b0"),
            ('s_axi_arready', ""),
            ('s_axi_rid', ""),
            ('s_axi_rdata', ""),
            ('s_axi_rresp', ""),
            ('s_axi_rlast', ""),
            ('s_axi_ruser', ""),
            ('s_axi_rvalid', ""),
            ('s_axi_rready', "1'b0"),
        ]
        self._sections.append(("AXI4 read channels (tied off — write-only bridge)", pairs))

    def connect_apb_master(self, prefix: str) -> None:
        """Wire the m_apb_* outputs to the external APB slave port.
        `prefix` is the slave's external prefix (e.g., 'apb_periph_'),
        and the shim's uppercase APB signal names are appended to it."""
        pairs = [
            ('m_apb_PSEL', f'{prefix}PSEL'),
            ('m_apb_PADDR', f'{prefix}PADDR'),
            ('m_apb_PENABLE', f'{prefix}PENABLE'),
            ('m_apb_PWRITE', f'{prefix}PWRITE'),
            ('m_apb_PWDATA', f'{prefix}PWDATA'),
            ('m_apb_PSTRB', f'{prefix}PSTRB'),
            ('m_apb_PPROT', f'{prefix}PPROT'),
            ('m_apb_PRDATA', f'{prefix}PRDATA'),
            ('m_apb_PSLVERR', f'{prefix}PSLVERR'),
            ('m_apb_PREADY', f'{prefix}PREADY'),
        ]
        self._sections.append(("APB master interface (to external slave)", pairs))

    # --- formatting ----------------------------------------------------

    def generate_lines(self) -> List[str]:
        """Emit a multi-line SystemVerilog instantiation block."""
        # Collect all port connections in declaration order across
        # sections so we can decide where to drop the trailing comma.
        all_pairs = []
        for _, pairs in self._sections:
            all_pairs.extend(pairs)
        if not all_pairs:
            raise RuntimeError("Axi4ToApbShim: nothing to instantiate")

        lines: List[str] = []
        lines.append("    axi4_to_apb_shim #(")
        # Parameter override list for the instantiation -- comes from
        # Module.params.create_param_instance() which emits the
        # `.NAME(VALUE)` form (NOT `parameter int NAME = VALUE`).
        param_inst = self.module.params.create_param_instance()
        # Split on the comma boundary so we can put one per line.
        # `create_param_instance` returns ".A(1),.B(2),.C(3)" so we
        # walk it manually to preserve any commas inside values.
        param_parts = [p.strip() for p in param_inst.split(',') if p.strip()]
        for i, p in enumerate(param_parts):
            sep = "," if i < len(param_parts) - 1 else ""
            lines.append(f"        {p}{sep}")
        lines.append(f"    ) {self.instance_name} (")

        # Track which pair is the last so we omit its trailing comma.
        last_idx = len(all_pairs) - 1
        running = 0
        for section_comment, pairs in self._sections:
            if section_comment:
                lines.append(f"        // {section_comment}")
            for port, connector in pairs:
                is_last = (running == last_idx)
                sep = "" if is_last else ","
                lines.append(f"        .{port}({connector}){sep}")
                running += 1
            lines.append("")
        # Drop the trailing blank line before the closing paren.
        if lines and lines[-1] == "":
            lines.pop()
        lines.append("    );")
        lines.append("")
        return lines
