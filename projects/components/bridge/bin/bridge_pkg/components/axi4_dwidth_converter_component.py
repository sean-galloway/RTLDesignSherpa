#!/usr/bin/env python3
# SPDX-License-Identifier: MIT
# SPDX-FileCopyrightText: 2024-2025 sean galloway
#
# Typed component wrapper for axi4_dwidth_converter_{rd,wr} instantiation.
#
# Encapsulates the converter's parameter list and port list so that
# call sites can't mistype a port name, swap S_/M_ data widths, or
# forget to attach an intercept signal. Used by the master-adapter
# generator for the per-width converter instances that bridge a master's
# native width to a slave's native width.

from typing import List, Optional
from rtl_generators.verilog.module import Module


class Axi4DwidthConverter:
    """Generate an `axi4_dwidth_converter_{rd,wr}` instantiation block.

    The converter sits in the master adapter between the wrapper's
    `fub_axi_*` side (s_axi -- master's native width) and the per-width
    crossbar input (`<master>_<W>b_*` -- slave's native width). The
    component handles BOTH directions (read or write) -- pass
    `direction='rd'` or `direction='wr'` at construction.
    """

    DIRECTIONS = ('rd', 'wr')

    def __init__(
        self,
        direction: str,
        instance_name: str,
        s_data_width: int,
        m_data_width: int,
        id_width: int,
        addr_width: int = 32,
        user_width: int = 1,
        skid_depth_ax: int = 2,    # SKID_DEPTH_AW or SKID_DEPTH_AR
        skid_depth_data: int = 4,  # SKID_DEPTH_W or SKID_DEPTH_R
        skid_depth_resp: int = 2,  # SKID_DEPTH_B (write only)
    ):
        if direction not in self.DIRECTIONS:
            raise ValueError(f"direction must be one of {self.DIRECTIONS}")
        self.direction = direction
        self.instance_name = instance_name
        self.s_data_width = s_data_width
        self.m_data_width = m_data_width
        self.id_width = id_width
        self.addr_width = addr_width
        self.user_width = user_width

        module_name = f'axi4_dwidth_converter_{direction}'
        self.module = Module(module_name=module_name,
                             instance_name=instance_name)
        if direction == 'wr':
            param_str = (
                f"parameter int S_AXI_DATA_WIDTH = {s_data_width}, "
                f"parameter int M_AXI_DATA_WIDTH = {m_data_width}, "
                f"parameter int AXI_ID_WIDTH     = {id_width}, "
                f"parameter int AXI_ADDR_WIDTH   = {addr_width}, "
                f"parameter int AXI_USER_WIDTH   = {user_width}, "
                f"parameter int SKID_DEPTH_AW    = {skid_depth_ax}, "
                f"parameter int SKID_DEPTH_W     = {skid_depth_data}, "
                f"parameter int SKID_DEPTH_B     = {skid_depth_resp}"
            )
        else:  # rd
            param_str = (
                f"parameter int S_AXI_DATA_WIDTH = {s_data_width}, "
                f"parameter int M_AXI_DATA_WIDTH = {m_data_width}, "
                f"parameter int AXI_ID_WIDTH     = {id_width}, "
                f"parameter int AXI_ADDR_WIDTH   = {addr_width}, "
                f"parameter int AXI_USER_WIDTH   = {user_width}, "
                f"parameter int SKID_DEPTH_AR    = {skid_depth_ax}, "
                f"parameter int SKID_DEPTH_R     = {skid_depth_data}"
            )
        self.module.params.add_param_string(param_str)
        self._sections: List[tuple] = []

    # --- connection helpers --------------------------------------------

    def connect_clocks_and_resets(self, aclk: str = 'aclk', aresetn: str = 'aresetn') -> None:
        self._sections.append((
            None,
            [('aclk', aclk), ('aresetn', aresetn)],
        ))

    def connect_s_axi_write(self,
                            fub_prefix: str,
                            aw_valid_gate: str,
                            w_valid_gate: str,
                            b_intercept_prefix: str) -> None:
        """Wire the s_axi-side write channels.
        - AW/W signals come directly from `fub_prefix` (e.g. 'fub_axi_').
        - awvalid is gated by `aw_valid_gate` (an expression like
          'fub_axi_awvalid && aw_path_active_32b').
        - wvalid is gated by `w_valid_gate` (separate from AW because
          W beats follow the FIFO-tracked path-active rather than the
          combinational AW decode -- see adapter_generator).
        - awready / wready / b* are pulled off into intercept signals
          (`<intercept>_awready`, `<intercept>_wready`, `<intercept>_bid`,
          etc.) so the response MUX in the adapter can read them via
          the FIFO-tracked r/b_slave_select.
        """
        if self.direction != 'wr':
            raise RuntimeError("connect_s_axi_write requires direction='wr'")
        pairs = [
            ('s_axi_awid', f'{fub_prefix}awid'),
            ('s_axi_awaddr', f'{fub_prefix}awaddr'),
            ('s_axi_awlen', f'{fub_prefix}awlen'),
            ('s_axi_awsize', f'{fub_prefix}awsize'),
            ('s_axi_awburst', f'{fub_prefix}awburst'),
            ('s_axi_awlock', f'{fub_prefix}awlock'),
            ('s_axi_awcache', f'{fub_prefix}awcache'),
            ('s_axi_awprot', f'{fub_prefix}awprot'),
            ('s_axi_awqos', "4'b0"),
            ('s_axi_awregion', "4'b0"),
            ('s_axi_awuser', "1'b0"),
            ('s_axi_awvalid', aw_valid_gate),
            ('s_axi_awready', f'{b_intercept_prefix}_awready'),
            ('s_axi_wdata', f'{fub_prefix}wdata'),
            ('s_axi_wstrb', f'{fub_prefix}wstrb'),
            ('s_axi_wlast', f'{fub_prefix}wlast'),
            ('s_axi_wuser', "1'b0"),
            ('s_axi_wvalid', w_valid_gate),
            ('s_axi_wready', f'{b_intercept_prefix}_wready'),
            ('s_axi_bid', f'{b_intercept_prefix}_bid'),
            ('s_axi_bresp', f'{b_intercept_prefix}_bresp'),
            ('s_axi_buser', ""),
            ('s_axi_bvalid', f'{b_intercept_prefix}_bvalid'),
            ('s_axi_bready', f'{fub_prefix}bready'),
        ]
        self._sections.append((
            "Slave side (from wrapper) - BROADCAST requests; ready/B intercepted for FIFO",
            pairs,
        ))

    def connect_s_axi_read(self,
                           fub_prefix: str,
                           ar_valid_gate: str,
                           r_intercept_prefix: str) -> None:
        """Wire the s_axi-side read channels.
        AR signals come from `fub_prefix`; arvalid is gated by
        `ar_valid_gate`. Arready/R signals are pulled off into
        `<intercept>_arready` / `<intercept>_rid` / `_rdata` / `_rresp`
        / `_rlast` / `_rvalid` so the response MUX can read them via
        the FIFO-tracked r_slave_select.
        """
        if self.direction != 'rd':
            raise RuntimeError("connect_s_axi_read requires direction='rd'")
        pairs = [
            ('s_axi_arid', f'{fub_prefix}arid'),
            ('s_axi_araddr', f'{fub_prefix}araddr'),
            ('s_axi_arlen', f'{fub_prefix}arlen'),
            ('s_axi_arsize', f'{fub_prefix}arsize'),
            ('s_axi_arburst', f'{fub_prefix}arburst'),
            ('s_axi_arlock', f'{fub_prefix}arlock'),
            ('s_axi_arcache', f'{fub_prefix}arcache'),
            ('s_axi_arprot', f'{fub_prefix}arprot'),
            ('s_axi_arqos', "4'b0"),
            ('s_axi_arregion', "4'b0"),
            ('s_axi_aruser', "1'b0"),
            ('s_axi_arvalid', ar_valid_gate),
            ('s_axi_arready', f'{r_intercept_prefix}_arready'),
            ('s_axi_rid', f'{r_intercept_prefix}_rid'),
            ('s_axi_rdata', f'{r_intercept_prefix}_rdata'),
            ('s_axi_rresp', f'{r_intercept_prefix}_rresp'),
            ('s_axi_rlast', f'{r_intercept_prefix}_rlast'),
            ('s_axi_ruser', ""),
            ('s_axi_rvalid', f'{r_intercept_prefix}_rvalid'),
            ('s_axi_rready', f'{fub_prefix}rready'),
        ]
        self._sections.append((
            "Slave side (from wrapper) - BROADCAST requests; arready/R intercepted for FIFO",
            pairs,
        ))

    def connect_m_axi_write(self, struct_prefix: str,
                            valid_signal: str, ready_signal: str,
                            bvalid_signal: str, bready_signal: str) -> None:
        """Wire the m_axi-side write channels to the per-width crossbar
        input. `struct_prefix` is the path that owns `.id`/.addr` etc.
        (e.g. 'cpu_master_256b_aw' -- the AW struct -- and similarly
        '_w' / '_b' substituted internally). `valid_signal` /
        `ready_signal` are the scalar valid/ready going to the xbar."""
        if self.direction != 'wr':
            raise RuntimeError("connect_m_axi_write requires direction='wr'")
        aw = struct_prefix.replace('_aw', '_aw')   # alias, kept readable
        # struct_prefix is e.g. 'cpu_master_256b'
        # the AW struct is f'{struct_prefix}_aw'
        # the W struct is f'{struct_prefix}_w'
        # the B struct is f'{struct_prefix}_b'
        sp = struct_prefix
        pairs = [
            ('m_axi_awid', f'{sp}_aw.id'),
            ('m_axi_awaddr', f'{sp}_aw.addr'),
            ('m_axi_awlen', f'{sp}_aw.len'),
            ('m_axi_awsize', f'{sp}_aw.size'),
            ('m_axi_awburst', f'{sp}_aw.burst'),
            ('m_axi_awlock', f'{sp}_aw.lock'),
            ('m_axi_awcache', f'{sp}_aw.cache'),
            ('m_axi_awprot', f'{sp}_aw.prot'),
            ('m_axi_awqos', f'{sp}_aw.qos'),
            ('m_axi_awregion', f'{sp}_aw.region'),
            ('m_axi_awuser', f'{sp}_aw.user'),
            ('m_axi_awvalid', valid_signal),
            ('m_axi_awready', ready_signal),
            ('m_axi_wdata', f'{sp}_w.data'),
            ('m_axi_wstrb', f'{sp}_w.strb'),
            ('m_axi_wlast', f'{sp}_w.last'),
            ('m_axi_wuser', f'{sp}_w.user'),
            ('m_axi_wvalid', f'{sp}_wvalid'),
            ('m_axi_wready', f'{sp}_wready'),
            ('m_axi_bid', f'{sp}_b.id'),
            ('m_axi_bresp', f'{sp}_b.resp'),
            ('m_axi_buser', f'{sp}_b.user'),
            ('m_axi_bvalid', bvalid_signal),
            ('m_axi_bready', bready_signal),
        ]
        self._sections.append(("Master side (to crossbar)", pairs))

    def connect_m_axi_read(self, struct_prefix: str,
                           arvalid_signal: str, arready_signal: str,
                           rvalid_signal: str, rready_signal: str) -> None:
        if self.direction != 'rd':
            raise RuntimeError("connect_m_axi_read requires direction='rd'")
        sp = struct_prefix
        pairs = [
            ('m_axi_arid', f'{sp}_ar.id'),
            ('m_axi_araddr', f'{sp}_ar.addr'),
            ('m_axi_arlen', f'{sp}_ar.len'),
            ('m_axi_arsize', f'{sp}_ar.size'),
            ('m_axi_arburst', f'{sp}_ar.burst'),
            ('m_axi_arlock', f'{sp}_ar.lock'),
            ('m_axi_arcache', f'{sp}_ar.cache'),
            ('m_axi_arprot', f'{sp}_ar.prot'),
            ('m_axi_arqos', f'{sp}_ar.qos'),
            ('m_axi_arregion', f'{sp}_ar.region'),
            ('m_axi_aruser', f'{sp}_ar.user'),
            ('m_axi_arvalid', arvalid_signal),
            ('m_axi_arready', arready_signal),
            ('m_axi_rid', f'{sp}_r.id'),
            ('m_axi_rdata', f'{sp}_r.data'),
            ('m_axi_rresp', f'{sp}_r.resp'),
            ('m_axi_rlast', f'{sp}_r.last'),
            ('m_axi_ruser', f'{sp}_r.user'),
            ('m_axi_rvalid', rvalid_signal),
            ('m_axi_rready', rready_signal),
        ]
        self._sections.append(("Master side (to crossbar)", pairs))

    # --- formatting ----------------------------------------------------

    def generate_lines(self) -> List[str]:
        all_pairs: List[tuple] = []
        for _, pairs in self._sections:
            all_pairs.extend(pairs)
        if not all_pairs:
            raise RuntimeError("Axi4DwidthConverter: nothing to instantiate")

        lines: List[str] = []
        lines.append(f"    axi4_dwidth_converter_{self.direction} #(")
        param_inst = self.module.params.create_param_instance()
        param_parts = [p.strip() for p in param_inst.split(',') if p.strip()]
        for i, p in enumerate(param_parts):
            sep = "," if i < len(param_parts) - 1 else ""
            lines.append(f"        {p}{sep}")
        lines.append(f"    ) {self.instance_name} (")

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
        if lines and lines[-1] == "":
            lines.pop()
        lines.append("    );")
        lines.append("")
        return lines
