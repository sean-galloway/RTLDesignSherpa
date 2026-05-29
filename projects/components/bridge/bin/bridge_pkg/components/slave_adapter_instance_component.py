#!/usr/bin/env python3
# SPDX-License-Identifier: MIT
# SPDX-FileCopyrightText: 2024-2025 sean galloway
#
# Typed component wrapper for instantiating a generated <slave>_adapter
# module from the bridge top. The adapter itself is emitted by
# SlaveAdapterGenerator; this class encapsulates the matching port-list
# conventions so the bridge top can't drift out of sync with the
# generator's output.
#
# The port list depends on slave.protocol:
#   axi4 / axil : crossbar-side AXI4 + external-side full AXI4 +
#                 bridge_id_aw/ar + bid_*/rid_*
#   apb         : crossbar-side AXI4 + APB master ports + bridge_id_*
#
# Channels are pruned by `has_write` / `has_read` (the adapter only
# wires the channels actually used).

from typing import List
from rtl_generators.verilog.module import Module


# Shared per-channel AXI4 base port name lists.
_AXI4_AW_PORTS = (
    'awid', 'awaddr', 'awlen', 'awsize', 'awburst',
    'awlock', 'awcache', 'awprot', 'awqos', 'awregion',
    'awuser', 'awvalid', 'awready',
)
_AXI4_W_PORTS = ('wdata', 'wstrb', 'wlast', 'wuser', 'wvalid', 'wready')
_AXI4_B_PORTS = ('bid', 'bresp', 'buser', 'bvalid', 'bready')
_AXI4_AR_PORTS = (
    'arid', 'araddr', 'arlen', 'arsize', 'arburst',
    'arlock', 'arcache', 'arprot', 'arqos', 'arregion',
    'aruser', 'arvalid', 'arready',
)
_AXI4_R_PORTS = ('rid', 'rdata', 'rresp', 'rlast', 'ruser', 'rvalid', 'rready')

_APB_PORTS = (
    'PADDR', 'PSEL', 'PENABLE', 'PWRITE', 'PWDATA',
    'PSTRB', 'PPROT', 'PRDATA', 'PSLVERR', 'PREADY',
)

# AXI4-Lite has none of AXI4's id/len/size/burst/lock/cache/qos/region/
# user/last signals on AW/AR/W/B/R -- only the bare minimum needed for
# single-beat transactions. Used by the axil branch of
# connect_external_interface() so the bridge top's AXIL slave ports
# match the adapter module's _generate_axil_external_ports output.
_AXIL_WRITE_PORTS = (
    'awaddr', 'awprot', 'awvalid', 'awready',
    'wdata', 'wstrb', 'wvalid', 'wready',
    'bresp', 'bvalid', 'bready',
)
_AXIL_READ_PORTS = (
    'araddr', 'arprot', 'arvalid', 'arready',
    'rdata', 'rresp', 'rvalid', 'rready',
)


class SlaveAdapterInstance:
    """Instantiate a generated <slave>_adapter module from the bridge
    top. Keeps the bridge top's connection list in lockstep with the
    adapter generator -- if the adapter's port set changes, only the
    component needs updating, not every call site.
    """

    def __init__(self, slave_name: str, slave_prefix: str, protocol: str,
                 has_write: bool, has_read: bool):
        if protocol not in ('axi4', 'apb', 'axil'):
            raise ValueError(f"unsupported protocol: {protocol!r}")
        if not (has_write or has_read):
            raise ValueError("adapter must carry at least one channel")
        self.slave_name = slave_name
        self.slave_prefix = slave_prefix
        self.protocol = protocol
        self.has_write = has_write
        self.has_read = has_read
        self.module = Module(module_name=f"{slave_name}_adapter",
                             instance_name=f"u_{slave_name}_adapter")
        self._sections: List[tuple] = []

    # --- connection helpers --------------------------------------------

    def connect_clocks_and_resets(self, aclk: str = 'aclk', aresetn: str = 'aresetn') -> None:
        self._sections.append((None,
                               [('aclk', aclk), ('aresetn', aresetn)]))

    def connect_xbar_interface(self) -> None:
        """Wire the crossbar-facing AXI4 ports. The xbar always exports
        full AXI4 regardless of slave protocol; the adapter's wrapper
        is what does any conversion."""
        xbar_prefix = f"xbar_{self.slave_name}_axi_"
        pairs: List[tuple] = []
        if self.has_write:
            for base in _AXI4_AW_PORTS:
                pairs.append((f'{xbar_prefix}{base}', f'{xbar_prefix}{base}'))
            for base in _AXI4_W_PORTS:
                pairs.append((f'{xbar_prefix}{base}', f'{xbar_prefix}{base}'))
            for base in _AXI4_B_PORTS:
                pairs.append((f'{xbar_prefix}{base}', f'{xbar_prefix}{base}'))
        if self.has_read:
            for base in _AXI4_AR_PORTS:
                pairs.append((f'{xbar_prefix}{base}', f'{xbar_prefix}{base}'))
            for base in _AXI4_R_PORTS:
                pairs.append((f'{xbar_prefix}{base}', f'{xbar_prefix}{base}'))
        self._sections.append((
            f"Crossbar interface (xbar_{self.slave_name}_axi_*)", pairs))

    def connect_external_interface(self) -> None:
        """Wire the external slave-facing ports. Layout depends on
        slave protocol:
          - apb : uppercase PADDR/PSEL/... ten-signal APB master
          - axil: AXI4-Lite (no id/len/burst/etc.)
          - axi4: full AXI4 channel set
        Each branch must match what the adapter module declares in its
        own _generate_*_external_ports method, or the bridge top won't
        compile against the adapter."""
        if self.protocol == 'apb':
            pairs = [(f'{self.slave_prefix}{sig}', f'{self.slave_prefix}{sig}')
                     for sig in _APB_PORTS]
            self._sections.append((
                f"External APB interface ({self.slave_prefix}*)", pairs))
        elif self.protocol == 'axil':
            pairs: List[tuple] = []
            if self.has_write:
                for base in _AXIL_WRITE_PORTS:
                    pairs.append((f'{self.slave_prefix}{base}',
                                  f'{self.slave_prefix}{base}'))
            if self.has_read:
                for base in _AXIL_READ_PORTS:
                    pairs.append((f'{self.slave_prefix}{base}',
                                  f'{self.slave_prefix}{base}'))
            self._sections.append((
                f"External AXI4-Lite interface ({self.slave_prefix}*)", pairs))
        else:  # axi4
            pairs: List[tuple] = []
            if self.has_write:
                for base in _AXI4_AW_PORTS:
                    pairs.append((f'{self.slave_prefix}{base}',
                                  f'{self.slave_prefix}{base}'))
                for base in _AXI4_W_PORTS:
                    pairs.append((f'{self.slave_prefix}{base}',
                                  f'{self.slave_prefix}{base}'))
                for base in _AXI4_B_PORTS:
                    pairs.append((f'{self.slave_prefix}{base}',
                                  f'{self.slave_prefix}{base}'))
            if self.has_read:
                for base in _AXI4_AR_PORTS:
                    pairs.append((f'{self.slave_prefix}{base}',
                                  f'{self.slave_prefix}{base}'))
                for base in _AXI4_R_PORTS:
                    pairs.append((f'{self.slave_prefix}{base}',
                                  f'{self.slave_prefix}{base}'))
            self._sections.append((
                f"External AXI4 interface ({self.slave_prefix}*)", pairs))

    def connect_monitor(self, wrappers) -> None:
        """Wire the AXI4 slave adapter's monbus + cfg ports. `wrappers`
        is a list of MonitoredWrapper entries belonging to this slave;
        each contributes one channel-suffixed monbus trio plus its 15
        cfg inputs. Only meaningful when the adapter generator emitted
        the matching ports (use_monitor=true + protocol=axi4)."""
        from .axi4_timing_wrapper_component import Axi4TimingWrapper

        if self.protocol != 'axi4':
            raise RuntimeError(
                f"connect_monitor() on non-axi4 slave {self.slave_name!r}: "
                f"the converter shims have no monitor ports today."
            )
        pairs: List[tuple] = []
        ordered = sorted(wrappers, key=lambda w: 0 if w.channel == 'wr' else 1)
        # Single shared free-running monitor-time net (driven by the
        # bridge top's monbus_axil_group.mon_time_out). Same connector
        # name as declared in BridgeModuleGenerator._generate_monitor_internal_signals.
        pairs.append(('i_mon_time', 'mon_time_w'))
        for w in ordered:
            pairs.append((f'monbus_{w.channel}_valid',     w.monbus_valid))
            pairs.append((f'monbus_{w.channel}_ready',     w.monbus_ready))
            pairs.append((f'monbus_{w.channel}_packet',    w.monbus_packet))
            pairs.append((f'monbus_{w.channel}_timestamp', w.monbus_timestamp))
            for sig in Axi4TimingWrapper.MONITOR_CFG_SIGNALS:
                base = sig[len('cfg_'):]
                adapter_port = f'cfg_{w.channel}_{base}'
                pairs.append((adapter_port, w.cfg_signal(base)))
        self._sections.append(("Monitor side-band", pairs))

    def connect_bridge_id_tracking(self) -> None:
        """Wire the xbar_bridge_id_{ar,aw} and bid_*/rid_* signals that
        the response MUX in the xbar uses to route B/R back to the
        originating master."""
        pairs: List[tuple] = []
        if self.has_write:
            pairs.extend([
                ('xbar_bridge_id_aw', f'{self.slave_name}_axi_bridge_id_aw'),
                ('bid_bridge_id', f'{self.slave_name}_axi_bid_bridge_id'),
                ('bid_valid', f'{self.slave_name}_axi_bid_valid'),
            ])
        if self.has_read:
            pairs.extend([
                ('xbar_bridge_id_ar', f'{self.slave_name}_axi_bridge_id_ar'),
                ('rid_bridge_id', f'{self.slave_name}_axi_rid_bridge_id'),
                ('rid_valid', f'{self.slave_name}_axi_rid_valid'),
            ])
        self._sections.append(("Bridge ID tracking", pairs))

    # --- formatting ----------------------------------------------------

    def generate_lines(self) -> List[str]:
        all_pairs: List[tuple] = []
        for _, pairs in self._sections:
            all_pairs.extend(pairs)
        if not all_pairs:
            raise RuntimeError("SlaveAdapterInstance: nothing to instantiate")

        lines: List[str] = []
        lines.append(f"    // {self.slave_name} adapter "
                     f"({self.protocol.upper()}, crossbar → external slave)")
        lines.append(f"    {self.module.module_name} {self.module.instance_name} (")

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
