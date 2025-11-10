#!/usr/bin/env python3
# SPDX-License-Identifier: MIT
# SPDX-FileCopyrightText: 2024-2025 sean galloway
#
# Interface Wrapper Generator for Bridge Crossbars
# Generates axi4_master/slave_rd/wr wrapper instantiations

from typing import List
from ..config import BridgeConfig, PortSpec


class InterfaceWrapperGenerator:
    """Generates AXI4 interface wrapper instantiations for timing closure"""

    def __init__(self, config: BridgeConfig):
        self.config = config

    def get_wrapper_module_name(self, is_master_side: bool, channel_type: str) -> str:
        """
        Get wrapper module name based on side and monitoring

        Args:
            is_master_side: True for master-side (bridge accepts), False for slave-side (bridge issues)
            channel_type: 'rd', 'wr'

        Returns:
            Module name (e.g., 'axi4_slave_rd', 'axi4_master_wr_mon')
        """
        # Master-side uses slave wrappers (bridge accepts commands)
        # Slave-side uses master wrappers (bridge issues commands)
        direction = 'slave' if is_master_side else 'master'

        # Add _mon suffix if monitoring enabled
        mon_suffix = '_mon' if self.config.enable_monitoring else ''

        return f"axi4_{direction}_{channel_type}{mon_suffix}"

    def generate_master_wrapper(self, master: PortSpec, master_idx: int) -> str:
        """Generate wrapper instantiation(s) for external master interface"""
        wrappers = []

        if master.has_read_channels():
            wrappers.append(self._generate_master_rd_wrapper(master, master_idx))

        if master.has_write_channels():
            wrappers.append(self._generate_master_wr_wrapper(master, master_idx))

        return '\n\n'.join(wrappers)

    def _generate_master_rd_wrapper(self, master: PortSpec, master_idx: int) -> str:
        """Generate read wrapper for external master"""
        module_name = self.get_wrapper_module_name(is_master_side=True, channel_type='rd')
        instance_name = f"u_m{master_idx}_rd_wrap"

        # External prefix (raw AXI at boundary)
        ext_prefix = master.prefix.rstrip('_')

        # Internal prefix (fub signals to crossbar)
        int_prefix = f"m{master_idx}_fub_axi"

        code = f"""// Master {master_idx} ({master.port_name}) - Read wrapper
{module_name} #(
    .SKID_DEPTH_AR({self.config.skid_depth_ar}),
    .SKID_DEPTH_R({self.config.skid_depth_r}),
    .AXI_ID_WIDTH({master.id_width}),
    .AXI_ADDR_WIDTH({master.addr_width}),
    .AXI_DATA_WIDTH({master.data_width}),
    .AXI_USER_WIDTH(1)
) {instance_name} (
    .aclk(aclk),
    .aresetn(aresetn),

    // External boundary (s_axi_* → bridge ports)
    .s_axi_arid({ext_prefix}_arid),
    .s_axi_araddr({ext_prefix}_araddr),
    .s_axi_arlen({ext_prefix}_arlen),
    .s_axi_arsize({ext_prefix}_arsize),
    .s_axi_arburst({ext_prefix}_arburst),
    .s_axi_arlock({ext_prefix}_arlock),
    .s_axi_arcache({ext_prefix}_arcache),
    .s_axi_arprot({ext_prefix}_arprot),
    .s_axi_arqos({ext_prefix}_arqos),
    .s_axi_arregion({ext_prefix}_arregion),
    .s_axi_aruser({ext_prefix}_aruser),
    .s_axi_arvalid({ext_prefix}_arvalid),
    .s_axi_arready({ext_prefix}_arready),

    .s_axi_rid({ext_prefix}_rid),
    .s_axi_rdata({ext_prefix}_rdata),
    .s_axi_rresp({ext_prefix}_rresp),
    .s_axi_rlast({ext_prefix}_rlast),
    .s_axi_ruser({ext_prefix}_ruser),
    .s_axi_rvalid({ext_prefix}_rvalid),
    .s_axi_rready({ext_prefix}_rready),

    // Internal crossbar (fub_axi_* → crossbar)
    .fub_axi_arid({int_prefix}_arid),
    .fub_axi_araddr({int_prefix}_araddr),
    .fub_axi_arlen({int_prefix}_arlen),
    .fub_axi_arsize({int_prefix}_arsize),
    .fub_axi_arburst({int_prefix}_arburst),
    .fub_axi_arlock({int_prefix}_arlock),
    .fub_axi_arcache({int_prefix}_arcache),
    .fub_axi_arprot({int_prefix}_arprot),
    .fub_axi_arqos({int_prefix}_arqos),
    .fub_axi_arregion({int_prefix}_arregion),
    .fub_axi_aruser({int_prefix}_aruser),
    .fub_axi_arvalid({int_prefix}_arvalid),
    .fub_axi_arready({int_prefix}_arready),

    .fub_axi_rid({int_prefix}_rid),
    .fub_axi_rdata({int_prefix}_rdata),
    .fub_axi_rresp({int_prefix}_rresp),
    .fub_axi_rlast({int_prefix}_rlast),
    .fub_axi_ruser({int_prefix}_ruser),
    .fub_axi_rvalid({int_prefix}_rvalid),
    .fub_axi_rready({int_prefix}_rready)"""

        # Add monitoring ports if enabled
        if self.config.enable_monitoring:
            code += f""",

    // Monitoring interface
    .monbus_pkt_valid(m{master_idx}_rd_mon_valid),
    .monbus_pkt_ready(m{master_idx}_rd_mon_ready),
    .monbus_pkt_data(m{master_idx}_rd_mon_data),

    // Monitor configuration
    .cfg_error_enable(cfg_mon_error_enable),
    .cfg_compl_enable(cfg_mon_compl_enable),
    .cfg_timeout_enable(cfg_mon_timeout_enable),
    .cfg_perf_enable(cfg_mon_perf_enable)"""

        code += "\n);"
        return code

    def _generate_master_wr_wrapper(self, master: PortSpec, master_idx: int) -> str:
        """Generate write wrapper for external master"""
        module_name = self.get_wrapper_module_name(is_master_side=True, channel_type='wr')
        instance_name = f"u_m{master_idx}_wr_wrap"

        ext_prefix = master.prefix.rstrip('_')
        int_prefix = f"m{master_idx}_fub_axi"

        code = f"""// Master {master_idx} ({master.port_name}) - Write wrapper
{module_name} #(
    .SKID_DEPTH_AW({self.config.skid_depth_aw}),
    .SKID_DEPTH_W({self.config.skid_depth_w}),
    .SKID_DEPTH_B({self.config.skid_depth_b}),
    .AXI_ID_WIDTH({master.id_width}),
    .AXI_ADDR_WIDTH({master.addr_width}),
    .AXI_DATA_WIDTH({master.data_width}),
    .AXI_USER_WIDTH(1)
) {instance_name} (
    .aclk(aclk),
    .aresetn(aresetn),

    // External boundary (s_axi_* → bridge ports)
    .s_axi_awid({ext_prefix}_awid),
    .s_axi_awaddr({ext_prefix}_awaddr),
    .s_axi_awlen({ext_prefix}_awlen),
    .s_axi_awsize({ext_prefix}_awsize),
    .s_axi_awburst({ext_prefix}_awburst),
    .s_axi_awlock({ext_prefix}_awlock),
    .s_axi_awcache({ext_prefix}_awcache),
    .s_axi_awprot({ext_prefix}_awprot),
    .s_axi_awqos({ext_prefix}_awqos),
    .s_axi_awregion({ext_prefix}_awregion),
    .s_axi_awuser({ext_prefix}_awuser),
    .s_axi_awvalid({ext_prefix}_awvalid),
    .s_axi_awready({ext_prefix}_awready),

    .s_axi_wdata({ext_prefix}_wdata),
    .s_axi_wstrb({ext_prefix}_wstrb),
    .s_axi_wlast({ext_prefix}_wlast),
    .s_axi_wuser({ext_prefix}_wuser),
    .s_axi_wvalid({ext_prefix}_wvalid),
    .s_axi_wready({ext_prefix}_wready),

    .s_axi_bid({ext_prefix}_bid),
    .s_axi_bresp({ext_prefix}_bresp),
    .s_axi_buser({ext_prefix}_buser),
    .s_axi_bvalid({ext_prefix}_bvalid),
    .s_axi_bready({ext_prefix}_bready),

    // Internal crossbar (fub_axi_* → crossbar)
    .fub_axi_awid({int_prefix}_awid),
    .fub_axi_awaddr({int_prefix}_awaddr),
    .fub_axi_awlen({int_prefix}_awlen),
    .fub_axi_awsize({int_prefix}_awsize),
    .fub_axi_awburst({int_prefix}_awburst),
    .fub_axi_awlock({int_prefix}_awlock),
    .fub_axi_awcache({int_prefix}_awcache),
    .fub_axi_awprot({int_prefix}_awprot),
    .fub_axi_awqos({int_prefix}_awqos),
    .fub_axi_awregion({int_prefix}_awregion),
    .fub_axi_awuser({int_prefix}_awuser),
    .fub_axi_awvalid({int_prefix}_awvalid),
    .fub_axi_awready({int_prefix}_awready),

    .fub_axi_wdata({int_prefix}_wdata),
    .fub_axi_wstrb({int_prefix}_wstrb),
    .fub_axi_wlast({int_prefix}_wlast),
    .fub_axi_wuser({int_prefix}_wuser),
    .fub_axi_wvalid({int_prefix}_wvalid),
    .fub_axi_wready({int_prefix}_wready),

    .fub_axi_bid({int_prefix}_bid),
    .fub_axi_bresp({int_prefix}_bresp),
    .fub_axi_buser({int_prefix}_buser),
    .fub_axi_bvalid({int_prefix}_bvalid),
    .fub_axi_bready({int_prefix}_bready)"""

        if self.config.enable_monitoring:
            code += f""",

    // Monitoring interface
    .monbus_pkt_valid(m{master_idx}_wr_mon_valid),
    .monbus_pkt_ready(m{master_idx}_wr_mon_ready),
    .monbus_pkt_data(m{master_idx}_wr_mon_data),

    // Monitor configuration
    .cfg_error_enable(cfg_mon_error_enable),
    .cfg_compl_enable(cfg_mon_compl_enable),
    .cfg_timeout_enable(cfg_mon_timeout_enable),
    .cfg_perf_enable(cfg_mon_perf_enable)"""

        code += "\n);"
        return code

    def generate_slave_wrapper(self, slave: PortSpec, slave_idx: int) -> str:
        """Generate wrapper instantiation(s) for external slave interface"""
        wrappers = []

        if slave.has_read_channels():
            wrappers.append(self._generate_slave_rd_wrapper(slave, slave_idx))

        if slave.has_write_channels():
            wrappers.append(self._generate_slave_wr_wrapper(slave, slave_idx))

        return '\n\n'.join(wrappers)

    def _generate_slave_rd_wrapper(self, slave: PortSpec, slave_idx: int) -> str:
        """Generate read wrapper for external slave"""
        module_name = self.get_wrapper_module_name(is_master_side=False, channel_type='rd')
        instance_name = f"u_s{slave_idx}_rd_wrap"

        ext_prefix = slave.prefix.rstrip('_')
        int_prefix = f"s{slave_idx}_fub_axi"

        code = f"""// Slave {slave_idx} ({slave.port_name}) - Read wrapper
{module_name} #(
    .SKID_DEPTH_AR({self.config.skid_depth_ar}),
    .SKID_DEPTH_R({self.config.skid_depth_r}),
    .AXI_ID_WIDTH({slave.id_width}),
    .AXI_ADDR_WIDTH({slave.addr_width}),
    .AXI_DATA_WIDTH({slave.data_width}),
    .AXI_USER_WIDTH(1)
) {instance_name} (
    .aclk(aclk),
    .aresetn(aresetn),

    // Internal crossbar (fub_axi_* ← crossbar)
    .fub_axi_arid({int_prefix}_arid),
    .fub_axi_araddr({int_prefix}_araddr),
    .fub_axi_arlen({int_prefix}_arlen),
    .fub_axi_arsize({int_prefix}_arsize),
    .fub_axi_arburst({int_prefix}_arburst),
    .fub_axi_arlock({int_prefix}_arlock),
    .fub_axi_arcache({int_prefix}_arcache),
    .fub_axi_arprot({int_prefix}_arprot),
    .fub_axi_arqos({int_prefix}_arqos),
    .fub_axi_arregion({int_prefix}_arregion),
    .fub_axi_aruser({int_prefix}_aruser),
    .fub_axi_arvalid({int_prefix}_arvalid),
    .fub_axi_arready({int_prefix}_arready),

    .fub_axi_rid({int_prefix}_rid),
    .fub_axi_rdata({int_prefix}_rdata),
    .fub_axi_rresp({int_prefix}_rresp),
    .fub_axi_rlast({int_prefix}_rlast),
    .fub_axi_ruser({int_prefix}_ruser),
    .fub_axi_rvalid({int_prefix}_rvalid),
    .fub_axi_rready({int_prefix}_rready),

    // External boundary (m_axi_* ← bridge ports)
    .m_axi_arid({ext_prefix}_arid),
    .m_axi_araddr({ext_prefix}_araddr),
    .m_axi_arlen({ext_prefix}_arlen),
    .m_axi_arsize({ext_prefix}_arsize),
    .m_axi_arburst({ext_prefix}_arburst),
    .m_axi_arlock({ext_prefix}_arlock),
    .m_axi_arcache({ext_prefix}_arcache),
    .m_axi_arprot({ext_prefix}_arprot),
    .m_axi_arqos({ext_prefix}_arqos),
    .m_axi_arregion({ext_prefix}_arregion),
    .m_axi_aruser({ext_prefix}_aruser),
    .m_axi_arvalid({ext_prefix}_arvalid),
    .m_axi_arready({ext_prefix}_arready),

    .m_axi_rid({ext_prefix}_rid),
    .m_axi_rdata({ext_prefix}_rdata),
    .m_axi_rresp({ext_prefix}_rresp),
    .m_axi_rlast({ext_prefix}_rlast),
    .m_axi_ruser({ext_prefix}_ruser),
    .m_axi_rvalid({ext_prefix}_rvalid),
    .m_axi_rready({ext_prefix}_rready)"""

        if self.config.enable_monitoring:
            code += f""",

    // Monitoring interface
    .monbus_pkt_valid(s{slave_idx}_rd_mon_valid),
    .monbus_pkt_ready(s{slave_idx}_rd_mon_ready),
    .monbus_pkt_data(s{slave_idx}_rd_mon_data),

    // Monitor configuration
    .cfg_error_enable(cfg_mon_error_enable),
    .cfg_compl_enable(cfg_mon_compl_enable),
    .cfg_timeout_enable(cfg_mon_timeout_enable),
    .cfg_perf_enable(cfg_mon_perf_enable)"""

        code += "\n);"
        return code

    def _generate_slave_wr_wrapper(self, slave: PortSpec, slave_idx: int) -> str:
        """Generate write wrapper for external slave"""
        module_name = self.get_wrapper_module_name(is_master_side=False, channel_type='wr')
        instance_name = f"u_s{slave_idx}_wr_wrap"

        ext_prefix = slave.prefix.rstrip('_')
        int_prefix = f"s{slave_idx}_fub_axi"

        code = f"""// Slave {slave_idx} ({slave.port_name}) - Write wrapper
{module_name} #(
    .SKID_DEPTH_AW({self.config.skid_depth_aw}),
    .SKID_DEPTH_W({self.config.skid_depth_w}),
    .SKID_DEPTH_B({self.config.skid_depth_b}),
    .AXI_ID_WIDTH({slave.id_width}),
    .AXI_ADDR_WIDTH({slave.addr_width}),
    .AXI_DATA_WIDTH({slave.data_width}),
    .AXI_USER_WIDTH(1)
) {instance_name} (
    .aclk(aclk),
    .aresetn(aresetn),

    // Internal crossbar (fub_axi_* ← crossbar)
    .fub_axi_awid({int_prefix}_awid),
    .fub_axi_awaddr({int_prefix}_awaddr),
    .fub_axi_awlen({int_prefix}_awlen),
    .fub_axi_awsize({int_prefix}_awsize),
    .fub_axi_awburst({int_prefix}_awburst),
    .fub_axi_awlock({int_prefix}_awlock),
    .fub_axi_awcache({int_prefix}_awcache),
    .fub_axi_awprot({int_prefix}_awprot),
    .fub_axi_awqos({int_prefix}_awqos),
    .fub_axi_awregion({int_prefix}_awregion),
    .fub_axi_awuser({int_prefix}_awuser),
    .fub_axi_awvalid({int_prefix}_awvalid),
    .fub_axi_awready({int_prefix}_awready),

    .fub_axi_wdata({int_prefix}_wdata),
    .fub_axi_wstrb({int_prefix}_wstrb),
    .fub_axi_wlast({int_prefix}_wlast),
    .fub_axi_wuser({int_prefix}_wuser),
    .fub_axi_wvalid({int_prefix}_wvalid),
    .fub_axi_wready({int_prefix}_wready),

    .fub_axi_bid({int_prefix}_bid),
    .fub_axi_bresp({int_prefix}_bresp),
    .fub_axi_buser({int_prefix}_buser),
    .fub_axi_bvalid({int_prefix}_bvalid),
    .fub_axi_bready({int_prefix}_bready),

    // External boundary (m_axi_* ← bridge ports)
    .m_axi_awid({ext_prefix}_awid),
    .m_axi_awaddr({ext_prefix}_awaddr),
    .m_axi_awlen({ext_prefix}_awlen),
    .m_axi_awsize({ext_prefix}_awsize),
    .m_axi_awburst({ext_prefix}_awburst),
    .m_axi_awlock({ext_prefix}_awlock),
    .m_axi_awcache({ext_prefix}_awcache),
    .m_axi_awprot({ext_prefix}_awprot),
    .m_axi_awqos({ext_prefix}_awqos),
    .m_axi_awregion({ext_prefix}_awregion),
    .m_axi_awuser({ext_prefix}_awuser),
    .m_axi_awvalid({ext_prefix}_awvalid),
    .m_axi_awready({ext_prefix}_awready),

    .m_axi_wdata({ext_prefix}_wdata),
    .m_axi_wstrb({ext_prefix}_wstrb),
    .m_axi_wlast({ext_prefix}_wlast),
    .m_axi_wuser({ext_prefix}_wuser),
    .m_axi_wvalid({ext_prefix}_wvalid),
    .m_axi_wready({ext_prefix}_wready),

    .m_axi_bid({ext_prefix}_bid),
    .m_axi_bresp({ext_prefix}_bresp),
    .m_axi_buser({ext_prefix}_buser),
    .m_axi_bvalid({ext_prefix}_bvalid),
    .m_axi_bready({ext_prefix}_bready)"""

        if self.config.enable_monitoring:
            code += f""",

    // Monitoring interface
    .monbus_pkt_valid(s{slave_idx}_wr_mon_valid),
    .monbus_pkt_ready(s{slave_idx}_wr_mon_ready),
    .monbus_pkt_data(s{slave_idx}_wr_mon_data),

    // Monitor configuration
    .cfg_error_enable(cfg_mon_error_enable),
    .cfg_compl_enable(cfg_mon_compl_enable),
    .cfg_timeout_enable(cfg_mon_timeout_enable),
    .cfg_perf_enable(cfg_mon_perf_enable)"""

        code += "\n);"
        return code

    def generate_all_wrappers(self) -> str:
        """Generate all interface wrapper instantiations"""
        if not self.config.enable_interface_wrappers:
            return "// Interface wrappers disabled (direct RTL connections)\n"

        sections = []

        # Header
        sections.append("""
//=============================================================================
// Interface Wrappers (Timing Closure + Optional Monitoring)
//=============================================================================
// External masters use axi4_slave_rd/wr (bridge accepts commands)
// External slaves use axi4_master_rd/wr (bridge issues commands)
// fub_axi_* signals are INTERNAL (between wrapper and crossbar)
""")

        # Master wrappers
        sections.append("// Master-side interface wrappers")
        for idx, master in enumerate(self.config.masters):
            sections.append(self.generate_master_wrapper(master, idx))

        # Slave wrappers
        sections.append("\n// Slave-side interface wrappers")
        for idx, slave in enumerate(self.config.slaves):
            sections.append(self.generate_slave_wrapper(slave, idx))

        return '\n'.join(sections)

    def generate_monitor_aggregation(self) -> str:
        """Generate monitor bus aggregation logic (if monitoring enabled)"""
        if not self.config.enable_monitoring:
            return ""

        # Count total monitor outputs
        mon_count = 0
        for m in self.config.masters:
            if m.has_read_channels(): mon_count += 1
            if m.has_write_channels(): mon_count += 1
        for s in self.config.slaves:
            if s.has_read_channels(): mon_count += 1
            if s.has_write_channels(): mon_count += 1

        # Build arrays
        valids = []
        datas = []
        readys = []

        for idx, m in enumerate(self.config.masters):
            if m.has_read_channels():
                valids.append(f"m{idx}_rd_mon_valid")
                datas.append(f"m{idx}_rd_mon_data")
                readys.append(f"m{idx}_rd_mon_ready")
            if m.has_write_channels():
                valids.append(f"m{idx}_wr_mon_valid")
                datas.append(f"m{idx}_wr_mon_data")
                readys.append(f"m{idx}_wr_mon_ready")

        for idx, s in enumerate(self.config.slaves):
            if s.has_read_channels():
                valids.append(f"s{idx}_rd_mon_valid")
                datas.append(f"s{idx}_rd_mon_data")
                readys.append(f"s{idx}_rd_mon_ready")
            if s.has_write_channels():
                valids.append(f"s{idx}_wr_mon_valid")
                datas.append(f"s{idx}_wr_mon_data")
                readys.append(f"s{idx}_wr_mon_ready")

        code = f"""
//=============================================================================
// Monitor Bus Aggregation (combines all monitor outputs)
//=============================================================================

arbiter_rr_monbus #(
    .N({mon_count}),
    .DATA_WIDTH(64)
) u_mon_arbiter (
    .i_clk(aclk),
    .i_rst_n(aresetn),
    .i_request({{
        {', '.join(valids)}
    }}),
    .i_data({{
        {', '.join(datas)}
    }}),
    .o_grant({{
        {', '.join(readys)}
    }}),
    .o_valid(bridge_monbus_valid),
    .o_data(bridge_monbus_data)
);

// External monitoring output (aggregate)
assign bridge_monbus_ready = 1'b1;  // TODO: Connect to downstream consumer
"""
        return code
