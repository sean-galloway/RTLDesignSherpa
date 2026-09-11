#!/usr/bin/env python3
# SPDX-License-Identifier: MIT
# SPDX-FileCopyrightText: 2026 sean galloway
"""Typed instantiation of `axi4_to_wb4` (BRIDGE-019).

The AXI4 side is the same five-channel slave face `axi4_to_apb4_shim` has,
so the channel wiring, the BRIDGE-011 not-full gate and the converter_*
intercepts are inherited from Axi4ToApbShim unchanged. What differs is the
module (a composition of the AXI4-Lite decomposers and axil4_to_wb4), its
parameter list, a single clock domain, and the Wishbone requester surface,
which comes from bridge_pkg/wb4_signals so it cannot drift from the port
list the adapter declares.
"""

from typing import List
from rtl_generators.verilog.module import Module
from .axi4_to_apb4_shim_component import Axi4ToApbShim


class Axi4ToWb4Shim(Axi4ToApbShim):

    def __init__(self, instance_name: str, id_width: int, addr_width: int,
                 data_width: int, has_write: bool, has_read: bool,
                 axi_user_width: int = 1, skid_depth: int = 2,
                 cmd_depth: int = 4, rsp_depth: int = 4, side_depth: int = 8,
                 classic: int = 0):
        assert has_write or has_read, "shim must carry at least one channel"
        self.instance_name = instance_name
        self.id_width = id_width
        self.addr_width = addr_width
        self.axi_data_width = data_width
        self.apb_data_width = data_width      # unused by WB4; kept for the base class
        self.axi_user_width = axi_user_width
        self.has_write = has_write
        self.has_read = has_read
        self.protocol = 'wb4'
        self.module = Module(module_name='axi4_to_wb4', instance_name=instance_name)
        self.module.params.add_param_string(
            f"parameter int AXI_ID_WIDTH   = {id_width}, "
            f"parameter int AXI_ADDR_WIDTH = {addr_width}, "
            f"parameter int AXI_DATA_WIDTH = {data_width}, "
            f"parameter int AXI_USER_WIDTH = {axi_user_width}, "
            f"parameter int SKID_DEPTH_AW  = {skid_depth}, "
            f"parameter int SKID_DEPTH_W   = {skid_depth}, "
            f"parameter int SKID_DEPTH_B   = {skid_depth}, "
            f"parameter int SKID_DEPTH_AR  = {skid_depth}, "
            f"parameter int SKID_DEPTH_R   = {skid_depth}, "
            f"parameter int CMD_DEPTH      = {cmd_depth}, "
            f"parameter int RSP_DEPTH      = {rsp_depth}, "
            f"parameter int SIDE_DEPTH     = {side_depth}, "
            f"parameter int CLASSIC        = {classic}"
        )
        self._sections: List[tuple] = []

    def connect_clocks_and_resets(self, aclk: str = 'aclk', aresetn: str = 'aresetn',
                                  pclk=None, presetn=None) -> None:
        # One clock domain: the Wishbone side runs on aclk.
        self._sections.append(("Clock and reset", [('aclk', aclk), ('aresetn', aresetn)]))

    def connect_apb4_master(self, prefix: str) -> None:  # pragma: no cover
        raise RuntimeError("Axi4ToWb4Shim has no APB side; use connect_wb4_master")

    def connect_wb4_master(self, prefix: str) -> None:
        """Wire m_wb_* to the external Wishbone completer port, in the
        shared table's order."""
        from ..wb4_signals import wb4_names
        pairs = [(f'm_wb_{base}', f'{prefix}{base}') for base in wb4_names()]
        self._sections.append(("Wishbone B4 requester interface (to external completer)", pairs))

    def generate_lines(self) -> List[str]:
        all_pairs = [pair for _c, pairs in self._sections for pair in pairs]
        if not all_pairs:
            raise RuntimeError("Axi4ToWb4Shim: nothing to instantiate")
        lines: List[str] = ["    axi4_to_wb4 #("]
        param_parts = [p.strip() for p in self.module.params.create_param_instance().split(',') if p.strip()]
        for i, p in enumerate(param_parts):
            lines.append(f"        {p}{',' if i < len(param_parts) - 1 else ''}")
        lines.append(f"    ) {self.instance_name} (")
        last = len(all_pairs) - 1
        running = 0
        for comment, pairs in self._sections:
            if comment:
                lines.append(f"        // {comment}")
            for port, connector in pairs:
                lines.append(f"        .{port}({connector}){'' if running == last else ','}")
                running += 1
            lines.append("")
        if lines[-1] == "":
            lines.pop()
        lines.append("    );")
        lines.append("")
        return lines
