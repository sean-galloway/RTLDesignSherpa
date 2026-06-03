#!/usr/bin/env python3
# SPDX-License-Identifier: MIT
# SPDX-FileCopyrightText: 2024-2025 sean galloway
#
# Typed component wrapper for the AXI4 timing-isolation wrappers
# (axi4_master_{wr,rd} and axi4_slave_{wr,rd}).
#
# Both wrappers expose two AXI4 sides:
#   axi4_master_*: fub_axi (from inside the bridge) -> m_axi (to ext slave)
#   axi4_slave_*:  s_axi   (from ext master)        -> fub_axi (to inside bridge)
#
# The slave-side adapter uses axi4_master_* (the bridge is a master to
# the external slave). The master-side adapter uses axi4_slave_* (the
# bridge is a slave to the external master). The component takes a
# `side` and `channel` arg and emits the appropriate module name and
# port names.

from typing import List, Optional
from rtl_generators.verilog.module import Module


class Axi4TimingWrapper:
    """Generate an axi4_{master,slave}_{wr,rd} instantiation block.

    Construct with:
        Axi4TimingWrapper(side='master'|'slave', channel='wr'|'rd', ...)

    `side` picks the SV module: side='master' -> axi4_master_*,
    side='slave' -> axi4_slave_*. `channel` picks 'wr' or 'rd'. The
    `mon` flag swaps in the `_mon` variant.
    """

    def __init__(
        self,
        side: str,
        channel: str,
        instance_name: str,
        id_width: int,
        addr_width: int,
        data_width: int,
        user_width: int = 1,
        mon: bool = False,
        # Skid-depth args -- pass as Python expression strings so the
        # caller can reference top-level parameters (e.g. 'SKID_DEPTH_AW').
        skid_depth_ax: str = '2',
        skid_depth_data: str = '4',
        skid_depth_resp: str = '2',
        # Monitor identity -- only honoured when mon=True. Both override
        # the SV module's hard-coded defaults so every per-port wrapper
        # instance puts a traceable {UNIT_ID, AGENT_ID} tuple in its
        # monbus packets. Leaving them None falls back to the SV defaults,
        # which is fine for non-monitored builds.
        unit_id: Optional[int] = None,
        agent_id: Optional[int] = None,
        # use_monitor -- per-instance USE_MONITOR override on the _mon
        # variant. Only meaningful when mon=True AND use_monitor_param
        # is None (the legacy hardcoded-bake path). When False here,
        # the wrapper emits `.USE_MONITOR(1'b0)` directly -- monitor
        # omitted at synth, monbus outputs tied to safe defaults.
        use_monitor: bool = True,
        # use_monitor_param -- preferred mode for production. When set
        # to a parameter-name string (e.g. 'USE_MONITOR_WR'), the
        # wrapper emits `.USE_MONITOR(<param_name>)` instead of a
        # hardcoded literal, so the *enclosing* module (typically the
        # per-port adapter) owns the parameter and the *outer* enclosing
        # module (bridge top) can override it at instantiation. Lets
        # production builds flip monitor enables at integration time
        # without regenerating the bridge.
        use_monitor_param: Optional[str] = None,
    ):
        if side not in ('master', 'slave'):
            raise ValueError(f"side must be 'master' or 'slave', got {side!r}")
        if channel not in ('wr', 'rd'):
            raise ValueError(f"channel must be 'wr' or 'rd', got {channel!r}")
        self.side = side
        self.channel = channel
        self.instance_name = instance_name
        self.id_width = id_width
        self.addr_width = addr_width
        self.data_width = data_width
        self.user_width = user_width

        module_name = f"axi4_{side}_{channel}{'_mon' if mon else ''}"
        self.module = Module(module_name=module_name,
                             instance_name=instance_name)
        if channel == 'wr':
            param_str = (
                f"parameter int SKID_DEPTH_AW   = {skid_depth_ax}, "
                f"parameter int SKID_DEPTH_W    = {skid_depth_data}, "
                f"parameter int SKID_DEPTH_B    = {skid_depth_resp}, "
                f"parameter int AXI_ID_WIDTH    = {id_width}, "
                f"parameter int AXI_ADDR_WIDTH  = {addr_width}, "
                f"parameter int AXI_DATA_WIDTH  = {data_width}, "
                f"parameter int AXI_USER_WIDTH  = {user_width}"
            )
        else:  # rd
            param_str = (
                f"parameter int SKID_DEPTH_AR   = {skid_depth_ax}, "
                f"parameter int SKID_DEPTH_R    = {skid_depth_data}, "
                f"parameter int AXI_ID_WIDTH    = {id_width}, "
                f"parameter int AXI_ADDR_WIDTH  = {addr_width}, "
                f"parameter int AXI_DATA_WIDTH  = {data_width}, "
                f"parameter int AXI_USER_WIDTH  = {user_width}"
            )
        # When the monitored variant is used, the caller can override the
        # SV module's hard-coded UNIT_ID / AGENT_ID defaults so monbus
        # packets identify exactly which per-port wrapper produced them.
        # Skip on non-monitored variants -- those modules don't declare
        # the parameters and would lint-fail on an override.
        if mon and unit_id is not None and agent_id is not None:
            param_str += (
                f", parameter int UNIT_ID         = {unit_id}, "
                f"parameter int AGENT_ID        = {agent_id}"
            )
        # Per-instance USE_MONITOR override (only on _mon variants -- the
        # non-mon modules don't declare the parameter). Two modes:
        #   - use_monitor_param set: emit a parameter-name reference so
        #     the enclosing adapter owns the parameter and the bridge
        #     top can override it at instantiation. Preferred for
        #     production builds.
        #   - use_monitor_param None, use_monitor=False: hardcoded
        #     `1'b0` override (legacy bake path). For tests or one-off
        #     bridges with no expected reconfig at integration time.
        if mon:
            if use_monitor_param is not None:
                param_str += (
                    f", parameter bit USE_MONITOR     = {use_monitor_param}"
                )
            elif not use_monitor:
                param_str += (
                    ", parameter bit USE_MONITOR     = 1'b0"
                )
        self.module.params.add_param_string(param_str)
        self._sections: List[tuple] = []

        # Per-side, per-channel port name layouts. These mirror the SV
        # module declarations -- centralised so call sites can't typo.
        if channel == 'wr':
            self._req1_ports = (
                'awid', 'awaddr', 'awlen', 'awsize', 'awburst',
                'awlock', 'awcache', 'awprot', 'awqos', 'awregion',
                'awuser', 'awvalid', 'awready',
            )
            self._req2_ports = (
                'wdata', 'wstrb', 'wlast', 'wuser', 'wvalid', 'wready',
            )
            self._resp_ports = (
                'bid', 'bresp', 'buser', 'bvalid', 'bready',
            )
            self._req1_label = "AW channel"
            self._req2_label = "W channel"
            self._resp_label = "B channel"
        else:
            self._req1_ports = (
                'arid', 'araddr', 'arlen', 'arsize', 'arburst',
                'arlock', 'arcache', 'arprot', 'arqos', 'arregion',
                'aruser', 'arvalid', 'arready',
            )
            self._req2_ports = ()
            self._resp_ports = (
                'rid', 'rdata', 'rresp', 'rlast', 'ruser', 'rvalid', 'rready',
            )
            self._req1_label = "AR channel"
            self._req2_label = None
            self._resp_label = "R channel"

    # --- side identification -------------------------------------------

    @property
    def _bridge_internal_prefix(self) -> str:
        """Port prefix on the bridge-internal side of the wrapper."""
        # Both axi4_master_* and axi4_slave_* use 'fub_axi_' for the
        # internal-facing side (their slave/master orientation differs).
        return 'fub_axi_'

    @property
    def _external_prefix(self) -> str:
        """Port prefix on the external-facing side."""
        # axi4_master_* exposes m_axi_* to the external slave.
        # axi4_slave_* exposes s_axi_* to the external master.
        return 'm_axi_' if self.side == 'master' else 's_axi_'

    # --- connection helpers --------------------------------------------

    def connect_clocks_and_resets(self, aclk: str = 'aclk', aresetn: str = 'aresetn') -> None:
        self._sections.append((None, [('aclk', aclk), ('aresetn', aresetn)]))

    def connect_bridge_internal(self,
                                connector_prefix: str,
                                qos_connector: Optional[str] = None,
                                region_connector: Optional[str] = None,
                                user_connector: Optional[str] = None,
                                wuser_connector: Optional[str] = None,
                                buser_connector: Optional[str] = None,
                                ruser_connector: Optional[str] = None) -> None:
        """Wire the bridge-internal (fub_axi_*) side. `connector_prefix`
        is appended in front of each base port name (e.g.
        `xbar_ddr_axi_` or `fub_axi_`). When the connector for qos /
        region / user / etc. is None, defaults are applied:
          - For axi4_slave_* (master adapter): qos/region/user/wuser/
            buser are tied or left open per the original hand-written
            convention (`buser(1'b0)`, others empty).
          - For axi4_master_* (slave adapter): qos/region/user pass
            through with the prefix.
        Override any of them with a keyword if needed."""
        prefix = self._bridge_internal_prefix
        defaults = self._fub_default_connectors(connector_prefix)
        # User-supplied kwargs only override when non-None. Leaving a
        # connector at None means "use the side-default (which may be
        # empty / 1'b0) or fall through to connector_prefix+base".
        explicit = {
            'awqos': qos_connector,
            'awregion': region_connector,
            'awuser': user_connector,
            'wuser': wuser_connector,
            'buser': buser_connector,
            'arqos': qos_connector,
            'arregion': region_connector,
            'aruser': user_connector,
            'ruser': ruser_connector,
        }
        for k, v in explicit.items():
            if v is not None:
                defaults[k] = v
        pairs = self._build_section_pairs(prefix, connector_prefix, defaults)
        self._sections.append((
            f"Bridge-internal side ({prefix.rstrip('_')})",
            pairs,
        ))

    def connect_external(self, connector_prefix: str) -> None:
        """Wire the external (m_axi_* or s_axi_*) side to the bridge's
        top-level port with `connector_prefix` (e.g. 'ddr_s_axi_' for
        a slave or 'cpu_rd_axi_' for a master)."""
        prefix = self._external_prefix
        defaults = self._external_default_connectors(connector_prefix)
        pairs = self._build_section_pairs(prefix, connector_prefix, defaults)
        self._sections.append((
            f"External side ({prefix.rstrip('_')})",
            pairs,
        ))

    def add_status(self, busy_connector: str = "") -> None:
        """Attach the wrapper's .busy() status output (default unconnected).
        ALSO emits tie-offs for the other status outputs the wrapper
        exposes -- active_transactions, error_count, transaction_count,
        cfg_conflict_error -- because Verilator (and good practice)
        require every port to be explicitly bound. Without these binds
        the cocotb sim flow errors on PINMISSING even though Vivado
        tolerates it (which is what masked a UART-silence bug for a
        full bitstream cycle once)."""
        pairs = [('busy', busy_connector)]
        # Monitor-only status outputs (only present on _mon variants).
        if '_mon' in self.module.module_name:
            pairs.extend([
                ('active_transactions', ''),
                ('error_count',         ''),
                ('transaction_count',   ''),
                ('cfg_conflict_error',  ''),
            ])
        self._sections.append(
            ("Status (empty connector = unconnected tie-off)", pairs))

    def add_addr_range_tieoff(self) -> None:
        """Bind the address-range checker config inputs to 0. With the
        SV module's N_ADDR_RANGES=0 default the checker is disabled,
        but the input ports still exist and Verilator errors on
        PINMISSING if they aren't bound. Until the bridge cfg
        subsystem (PeakRDL regblock) wires these to runtime knobs,
        tie them off explicitly."""
        if '_mon' not in self.module.module_name:
            return
        self._sections.append(("Address-range checker (disabled at N_ADDR_RANGES=0)", [
            ('cfg_addr_check_enable', "1'b0"),
            ('cfg_addr_range_enable', "1'b0"),
            ('cfg_addr_range_low',    "{32{1'b0}}"),
            ('cfg_addr_range_high',   "{32{1'b0}}"),
        ]))

    # --- monitor-only port groups (only valid when mon=True) -----------

    # The 15 cfg_* signal names every axi4_{master,slave}_{wr,rd}_mon
    # variant exposes. Centralised here so adapter generators and bridge
    # top can iterate the same list when surfacing per-port cfg inputs.
    MONITOR_CFG_SIGNALS = (
        'cfg_monitor_enable',
        'cfg_error_enable',
        'cfg_timeout_enable',
        'cfg_perf_enable',
        'cfg_timeout_cycles',
        'cfg_latency_threshold',
        'cfg_axi_pkt_mask',
        'cfg_axi_err_select',
        'cfg_axi_error_mask',
        'cfg_axi_timeout_mask',
        'cfg_axi_compl_mask',
        'cfg_axi_thresh_mask',
        'cfg_axi_perf_mask',
        'cfg_axi_addr_mask',
        'cfg_axi_debug_mask',
    )

    def connect_monbus(self, valid: str, ready: str, packet: str,
                       timestamp: str, mon_time: str = 'mon_time_w') -> None:
        """Wire the wrapper's monitor-bus output set. Only meaningful
        on `_mon` variants -- non-mon modules have no such ports.

        After the 64->128-bit packet widening, every `_mon` wrapper also
        gets a 64-bit `monbus_timestamp` side-band output (captured by
        the arbiter alongside the packet) and an `i_mon_time` input that
        carries the free-running time from monbus_axil_group's
        `mon_time_out`. The default `mon_time_w` matches the shared net
        declared by BridgeModuleGenerator._generate_monitor_internal_signals().
        """
        if '_mon' not in self.module.module_name:
            raise RuntimeError(
                f"connect_monbus() called on non-mon wrapper "
                f"{self.module.module_name!r}; caller must gate on mon=True."
            )
        self._sections.append(("Monitor bus output", [
            ('i_mon_time',       mon_time),
            ('monbus_valid',     valid),
            ('monbus_ready',     ready),
            ('monbus_packet',    packet),
            ('monbus_timestamp', timestamp),
        ]))

    def connect_cfg(self, connector_prefix: str) -> None:
        """Wire the wrapper's 15 cfg_* inputs. `connector_prefix` is
        prepended to each base cfg signal name -- e.g. passing 'cfg_wr_'
        yields .cfg_monitor_enable(cfg_wr_monitor_enable), etc. Only
        valid on `_mon` variants."""
        if '_mon' not in self.module.module_name:
            raise RuntimeError(
                f"connect_cfg() called on non-mon wrapper "
                f"{self.module.module_name!r}; caller must gate on mon=True."
            )
        pairs = []
        for sig in self.MONITOR_CFG_SIGNALS:
            # The SV module's port name is the bare cfg_* signal; the
            # adapter-level connector is f"{prefix}{stripped}" where we
            # strip the leading 'cfg_' to avoid 'cfg_wr_cfg_monitor_...'.
            base = sig[len('cfg_'):]
            pairs.append((sig, f"{connector_prefix}{base}"))
        self._sections.append(("Monitor cfg inputs", pairs))

    # --- internals -----------------------------------------------------

    def _fub_default_connectors(self, connector_prefix: str) -> dict:
        """Defaults for the bridge-internal (fub_axi_*) connectors.
        On the master-adapter side (axi4_slave_*) we drop the qos/
        region/user signals because the master adapter has no place
        to route them; on the slave-adapter side (axi4_master_*) they
        pass through with the prefix."""
        d = {}
        if self.side == 'slave':
            # axi4_slave_* on the master-adapter -- match the hand-written
            # convention: open qos/region/user outputs, tie buser to 0,
            # ruser=1'b0 too.
            for name in ('awqos', 'awregion', 'awuser',
                         'wuser', 'buser',
                         'arqos', 'arregion', 'aruser', 'ruser'):
                d[name] = ""
            d['buser'] = "1'b0"
            d['ruser'] = "1'b0"
        return d

    def _external_default_connectors(self, connector_prefix: str) -> dict:
        # External-side connectors pass through with the prefix unless
        # callers override. No special defaults required today.
        return {}

    def _build_section_pairs(self, port_prefix: str,
                             connector_prefix: str,
                             overrides: dict) -> List[tuple]:
        """Construct (port, connector) tuples for a channel side."""
        pairs: List[tuple] = []
        groups = [self._req1_ports, self._req2_ports, self._resp_ports]
        labels = [self._req1_label, self._req2_label, self._resp_label]
        for group, _label in zip(groups, labels):
            if not group:
                continue
            for base in group:
                port_name = f"{port_prefix}{base}"
                if base in overrides:
                    connector = overrides[base]
                else:
                    connector = f"{connector_prefix}{base}"
                pairs.append((port_name, connector))
        return pairs

    # --- formatting ----------------------------------------------------

    def generate_lines(self) -> List[str]:
        all_pairs: List[tuple] = []
        for _, pairs in self._sections:
            all_pairs.extend(pairs)
        if not all_pairs:
            raise RuntimeError("Axi4TimingWrapper: nothing to instantiate")

        mon = '_mon' if 'mon' in self.module.module_name else ''
        # The module name was set in __init__; re-derive from instance
        # to avoid double-bookkeeping.
        module_name = self.module.module_name
        lines: List[str] = []
        lines.append(f"    {module_name} #(")
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
