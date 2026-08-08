#!/usr/bin/env python3
# SPDX-License-Identifier: MIT
# SPDX-FileCopyrightText: 2024-2025 sean galloway
"""
Shared SystemVerilog emission helpers for the bridge generators.

Home for port-list emission that must stay byte-identical between the
master-side AdapterGenerator and the slave-side SlaveAdapterGenerator —
the bridge top wires both with the same connector-naming scheme, so any
divergence breaks instantiation.
"""

from typing import List


def generate_monitor_ports(channels_mode: str) -> List[str]:
    """Per-wrapper monbus output + cfg input ports for an adapter.

    Shared by AdapterGenerator (master side, channels from
    self.master.channels) and SlaveAdapterGenerator (slave side,
    channels from self.channels) so the bridge top can wire
    master/slave adapters with the same connector-naming scheme.

    Names use the adapter-local channel suffix (`_wr` / `_rd`) -- the
    bridge top binds them to {port_name}_{port_idx}-prefixed nets so
    each monbus stream and cfg group is uniquely identifiable.

    After the 64->128-bit packet widening, every channel also gets a
    64-bit `monbus_<chan>_timestamp` side-band output (paired with
    the packet). A single shared `i_mon_time` input is declared once
    per adapter (not per channel) because every wrapper instance
    consumes the same free-running counter from monbus_axil_group's
    `mon_time_out`.

    Args:
        channels_mode: "wr", "rd", or "rw" — which channels the adapter has.

    Returns:
        Port declaration lines (no trailing comma after the final port).
    """
    # Lazy imports: adapter_generator imports this module at top level,
    # so pulling _MONITOR_CFG_WIDTHS at call time avoids an import cycle.
    from .components.axi4_timing_wrapper_component import Axi4TimingWrapper
    from .generators.adapter_generator import _MONITOR_CFG_WIDTHS

    lines: List[str] = []
    channels: List[str] = []
    if channels_mode in ("wr", "rw"):
        channels.append("wr")
    if channels_mode in ("rd", "rw"):
        channels.append("rd")

    # Shared free-running monitor-time -- one input shared by every
    # internal wrapper instance. Always emit when monitoring is
    # enabled, regardless of which channel(s) are present.
    if channels:
        lines.append("    // Shared free-running monitor-time (from monbus_axil_group.mon_time_out)")
        lines.append("    input  monitor_common_pkg::monbus_timestamp_t i_mon_time,")
        lines.append("")

    last_chan = channels[-1] if channels else None
    for chan in channels:
        lines.append(f"    // Monitor side-band: {chan} wrapper")
        lines.append(f"    output logic                                  monbus_{chan}_valid,")
        lines.append(f"    input  logic                                  monbus_{chan}_ready,")
        lines.append(f"    output monitor_common_pkg::monitor_packet_t   monbus_{chan}_packet,")
        lines.append(f"    output monitor_common_pkg::monbus_timestamp_t monbus_{chan}_timestamp,")
        lines.append("")
        for i, sig in enumerate(Axi4TimingWrapper.MONITOR_CFG_SIGNALS):
            is_final_cfg = (chan == last_chan and i == len(Axi4TimingWrapper.MONITOR_CFG_SIGNALS) - 1)
            width = _MONITOR_CFG_WIDTHS[sig]
            width_decl = "       " if width == 1 else f"[{width-1}:0]"
            base = sig[len("cfg_"):]
            sep = "" if is_final_cfg else ","
            lines.append(f"    input  logic {width_decl} cfg_{chan}_{base}{sep}")
        if chan != last_chan:
            lines.append("")
    return lines
