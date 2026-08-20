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


# ---------------------------------------------------------------------------
# AXI5 feature tables (BRIDGE-002 phases A5-1 / A5-2 slice 1).
#
# The axi5_{slave,master}_{wr,rd} modules declare every feature port
# unconditionally; ENABLE_<FEATURE> parameters gate the logic. The
# tables below mirror the SV declarations
# (rtl/amba/axi5/axi5_{slave,master}_{wr,rd}.sv -- both families use
# identical feature-port base names) so instantiation can bind every
# pin: enabled-feature externals connect through, disabled-feature
# external INPUTS tie to '0 and OUTPUTS get empty connectors; on the fub
# (fabric) side every feature port terminates (outputs open, inputs '0)
# because the fabric behind the wrapper is plain AXI4.
#
# Tuple format: (port_base_name, feature, req_direction)
#   req_direction == True  -> the signal flows in the REQUEST direction
#     (upstream master toward downstream slave). On axi5_slave_* that
#     makes s_axi_<name> a wrapper INPUT (fub output); on axi5_master_*
#     it makes m_axi_<name> a wrapper OUTPUT (fub input). b/r-side
#     extras (req_direction=False) flow the other way.
# ---------------------------------------------------------------------------

# ENABLE_* parameter per feature. wr has no CHUNKING; rd has no ATOMIC.
AXI5_FEATURE_ENABLE_PARAM = {
    'atomic':   'ENABLE_ATOMIC',
    'nsaid':    'ENABLE_NSAID',
    'trace':    'ENABLE_TRACE',
    'mpam':     'ENABLE_MPAM',
    'mecid':    'ENABLE_MECID',
    'unique':   'ENABLE_UNIQUE',
    'chunking': 'ENABLE_CHUNKING',
    'mte':      'ENABLE_MTE',
    'poison':   'ENABLE_POISON',
}
_AXI5_WR_FEATURE_ORDER = (
    'atomic', 'nsaid', 'trace', 'mpam', 'mecid', 'unique', 'mte', 'poison')
_AXI5_RD_FEATURE_ORDER = (
    'nsaid', 'trace', 'mpam', 'mecid', 'unique', 'chunking', 'mte', 'poison')

# wr-channel extras, grouped to match the SV declaration order.
_AXI5_WR_REQ1_EXTRAS = (            # AW-side (after awready)
    ('awatop',   'atomic', True),
    ('awnsaid',  'nsaid',  True),
    ('awtrace',  'trace',  True),
    ('awmpam',   'mpam',   True),
    ('awmecid',  'mecid',  True),
    ('awunique', 'unique', True),
    ('awtagop',  'mte',    True),
    ('awtag',    'mte',    True),
)
_AXI5_WR_REQ2_EXTRAS = (            # W-side (after wready)
    ('wpoison',    'poison', True),
    ('wtag',       'mte',    True),
    ('wtagupdate', 'mte',    True),
)
_AXI5_WR_RESP_EXTRAS = (            # B-side (after bready)
    ('btrace',    'trace', False),
    ('btag',      'mte',   False),
    ('btagmatch', 'mte',   False),
)

# rd-channel extras.
_AXI5_RD_REQ1_EXTRAS = (            # AR-side (after arready)
    ('arnsaid',   'nsaid',    True),
    ('artrace',   'trace',    True),
    ('armpam',    'mpam',     True),
    ('armecid',   'mecid',    True),
    ('arunique',  'unique',   True),
    ('archunken', 'chunking', True),
    ('artagop',   'mte',      True),
)
_AXI5_RD_RESP_EXTRAS = (            # R-side (after rready)
    ('rtrace',     'trace',    False),
    ('rpoison',    'poison',   False),
    ('rchunkv',    'chunking', False),
    ('rchunknum',  'chunking', False),
    ('rchunkstrb', 'chunking', False),
    ('rtag',       'mte',      False),
    ('rtagmatch',  'mte',      False),
)

# External-surface declarations for the interop sideband feature set,
# keyed by AXI channel. Only enabled features' signals are exposed on
# the bridge top / per-port adapter; the widths mirror the axi5_* SV
# parameter defaults (AXI_NSAID_WIDTH=4, AXI_MPAM_WIDTH=11,
# AXI_MECID_WIDTH=16; trace/unique are scalars -- identical across the
# slave and master wrapper families).
# Tuple: (name, width_bits, feature, req_direction). req_direction=True
# means the signal flows master->slave: on an AXI5 MASTER port (bridge
# is the slave) it is a bridge-top INPUT; on an AXI5 SLAVE port (bridge
# is the master) it is a bridge-top OUTPUT.
AXI5_SIDEBAND_EXT_SIGNALS = {
    'aw': (
        ('awnsaid',  4,  'nsaid',  True),
        ('awtrace',  1,  'trace',  True),
        ('awmpam',   11, 'mpam',   True),
        ('awmecid',  16, 'mecid',  True),
        ('awunique', 1,  'unique', True),
        ('awatop',   6,  'atomic', True),
    ),
    'w': (
        ('wpoison', 1, 'poison', True),
    ),
    'b': (
        ('btrace', 1, 'trace', False),
    ),
    'ar': (
        ('arnsaid',  4,  'nsaid',  True),
        ('artrace',  1,  'trace',  True),
        ('armpam',   11, 'mpam',   True),
        ('armecid',  16, 'mecid',  True),
        ('arunique', 1,  'unique', True),
    ),
    'r': (
        ('rtrace', 1, 'trace', False),
        ('rpoison', 1, 'poison', False),
    ),
}


def axi5_exposed_ext_signals(channel_key: str, features) -> List[tuple]:
    """The (name, width, req_direction) triples an AXI5 port with
    `features` enabled exposes on AXI channel `channel_key`
    ('aw'/'w'/'b'/'ar'/'r'), in declaration order. req_direction=True
    signals flow master->slave (bridge-top INPUT on an AXI5 master
    port, bridge-top OUTPUT on an AXI5 slave port)."""
    feats = set(features or ())
    return [(name, width, ext_in)
            for name, width, feat, ext_in
            in AXI5_SIDEBAND_EXT_SIGNALS[channel_key]
            if feat in feats]


class Axi4TimingWrapper:
    """Generate an {axi4,axi5}_{master,slave}_{wr,rd} instantiation block.

    Construct with:
        Axi4TimingWrapper(side='master'|'slave', channel='wr'|'rd', ...)

    `side` picks the SV module: side='master' -> <protocol>_master_*,
    side='slave' -> <protocol>_slave_*. `channel` picks 'wr' or 'rd'.
    The `mon` flag swaps in the `_mon` variant.

    `protocol` (default 'axi4') picks the module family. With
    protocol='axi5', the instantiated module is
    axi5_{slave,master}_{wr,rd}[_mon] -- side='slave' for the
    master-adapter boundary (A5-1), side='master' for the slave-adapter
    boundary (A5-2 slice 1). In both cases:
      - the base port set drops aw/arregion (AXI5 removed REGION),
      - every AXI5 feature port is bound: features named in
        `axi5_features` connect through on the external side, the rest
        tie ('0 inputs / open outputs),
      - ENABLE_<FEATURE> parameter overrides are emitted for every
        feature the module declares (1'b1 when enabled, else 1'b0),
      - the fub (fabric) side terminates ALL feature ports -- the
        fabric behind the wrapper stays AXI4.
    The class name keeps its historical `Axi4` prefix; renaming is out
    of scope for the A5 interop slices.
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
        # Reporter sub-block enables -- dict keyed by cone name
        # (error/timeout/compl/threshold/perf) with bool values. Each
        # becomes a `.ENABLE_<NAME>_LOGIC(1'b<x>)` parameter override
        # on the _mon variant so the genvar-if inside the reporter
        # actually drops the cone at synthesis. Only meaningful when
        # mon=True. Pass None to leave the SV defaults in place (all 1).
        mon_enables: Optional[dict] = None,
        # protocol -- module family selector: 'axi4' (default, unchanged
        # behaviour) or 'axi5' (axi5_slave_* boundary wrappers on
        # master-adapter ports (A5-1), axi5_master_* on slave-adapter
        # ports (A5-2 slice 1)). See class docstring.
        protocol: str = 'axi4',
        # axi5_features -- feature names whose external signals connect
        # through (the rest tie off). Only meaningful when
        # protocol='axi5'. Upstream validation (validate_axi5) restricts
        # this to the interop sideband set.
        axi5_features: Optional[List[str]] = None,
        # native_sideband -- A5-2 slice 2. When True, the fub (fabric)
        # side of each ENABLED feature's sideband port binds to
        # <connector_prefix><base> (e.g. fub_axi_awnsaid) instead of
        # terminating, so the enclosing adapter can ride the sideband
        # on the fabric structs. Disabled features and the
        # non-native extras (atomic/mte/chunking ports) still terminate.
        native_sideband: bool = False,
    ):
        if side not in ('master', 'slave'):
            raise ValueError(f"side must be 'master' or 'slave', got {side!r}")
        if channel not in ('wr', 'rd'):
            raise ValueError(f"channel must be 'wr' or 'rd', got {channel!r}")
        if protocol not in ('axi4', 'axi5'):
            raise ValueError(
                f"protocol must be 'axi4' or 'axi5', got {protocol!r}")
        if protocol != 'axi5' and axi5_features:
            raise ValueError(
                "axi5_features passed but protocol is not 'axi5'")
        self.side = side
        self.channel = channel
        self.protocol = protocol
        self.axi5_features = tuple(axi5_features or ())
        self.native_sideband = bool(native_sideband)
        self.instance_name = instance_name
        self.id_width = id_width
        self.addr_width = addr_width
        self.data_width = data_width
        self.user_width = user_width

        module_name = f"{protocol}_{side}_{channel}{'_mon' if mon else ''}"
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
        # AXI5 feature-enable overrides. The SV defaults are all-enabled
        # (ENABLE_*=1), so every feature parameter the module declares is
        # driven explicitly -- 1'b1 for features in axi5_features, 1'b0
        # for the rest -- ensuring disabled logic is dropped at synthesis.
        if protocol == 'axi5':
            feature_order = (_AXI5_WR_FEATURE_ORDER if channel == 'wr'
                             else _AXI5_RD_FEATURE_ORDER)
            for feat in feature_order:
                fparam = AXI5_FEATURE_ENABLE_PARAM[feat]
                fval = "1'b1" if feat in self.axi5_features else "1'b0"
                param_str += f", parameter bit {fparam}    = {fval}"

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
            # Reporter sub-block ENABLE_*_LOGIC overrides. Drives the
            # genvar-if inside axi_monitor_reporter (committed in
            # 657e00b3) so the unused cones are gone at synthesis.
            if mon_enables is not None:
                cone_to_param = (
                    ('error',     'ENABLE_ERROR_LOGIC'),
                    ('timeout',   'ENABLE_TIMEOUT_LOGIC'),
                    ('compl',     'ENABLE_COMPL_LOGIC'),
                    ('threshold', 'ENABLE_THRESHOLD_LOGIC'),
                    ('perf',      'ENABLE_PERF_LOGIC'),
                    ('debug',     'ENABLE_DEBUG_LOGIC'),
                )
                for cone, param in cone_to_param:
                    val = "1'b1" if mon_enables.get(cone, True) else "1'b0"
                    param_str += f", parameter bit {param} = {val}"
        self.module.params.add_param_string(param_str)
        self._sections: List[tuple] = []

        # Per-side, per-channel port name layouts. These mirror the SV
        # module declarations -- centralised so call sites can't typo.
        #
        # AXI5 differences (axi5_{slave,master}_{wr,rd}.sv -- both
        # families declare the same base + feature port names): the base
        # set drops aw/arregion (AXI5 removed REGION), and every feature
        # port is appended to its channel group so instantiation binds
        # all pins. Feature-extra tuples carry (name, feature,
        # req_direction); the connector-default helpers turn them into
        # pass-through / tie-off connectors per side.
        is_axi5 = (protocol == 'axi5')
        if channel == 'wr':
            self._req1_ports = (
                'awid', 'awaddr', 'awlen', 'awsize', 'awburst',
                'awlock', 'awcache', 'awprot', 'awqos',
            ) + (() if is_axi5 else ('awregion',)) + (
                'awuser', 'awvalid', 'awready',
            )
            self._req2_ports = (
                'wdata', 'wstrb', 'wlast', 'wuser', 'wvalid', 'wready',
            )
            self._resp_ports = (
                'bid', 'bresp', 'buser', 'bvalid', 'bready',
            )
            self._req1_extras = _AXI5_WR_REQ1_EXTRAS if is_axi5 else ()
            self._req2_extras = _AXI5_WR_REQ2_EXTRAS if is_axi5 else ()
            self._resp_extras = _AXI5_WR_RESP_EXTRAS if is_axi5 else ()
            self._req1_label = "AW channel"
            self._req2_label = "W channel"
            self._resp_label = "B channel"
        else:
            self._req1_ports = (
                'arid', 'araddr', 'arlen', 'arsize', 'arburst',
                'arlock', 'arcache', 'arprot', 'arqos',
            ) + (() if is_axi5 else ('arregion',)) + (
                'aruser', 'arvalid', 'arready',
            )
            self._req2_ports = ()
            self._resp_ports = (
                'rid', 'rdata', 'rresp', 'rlast', 'ruser', 'rvalid', 'rready',
            )
            self._req1_extras = _AXI5_RD_REQ1_EXTRAS if is_axi5 else ()
            self._req2_extras = ()
            self._resp_extras = _AXI5_RD_RESP_EXTRAS if is_axi5 else ()
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

    def add_perfmon_tieoff(self) -> None:
        """Bind the Stage A (window control) and Stage B (cycle bucket
        + counter) ports added in f4542a9d / ca2d2334. With perfmon off
        the cfg inputs are all dead-event selectors (3'b111) and the
        triggers are 0; outputs are left unconnected. When the bridge
        cfg subsystem (PeakRDL regblock) lands, replace this tie-off
        with real per-port cfg routing -- but only when the integrator
        actually plans to drive a window. Until then, PINMISSING-safe."""
        if '_mon' not in self.module.module_name:
            return
        self._sections.append(("Perfmon Stage A/B (tied off -- no window driven)", [
            ('cfg_start_event_sel',    "3'b111"),  # never-fire
            ('cfg_end_event_sel',      "3'b111"),
            ('cfg_start_trigger',      "1'b0"),
            ('cfg_end_trigger',        "1'b0"),
            ('cfg_window_force_close', "1'b0"),
            # Stage A status + Stage B counters: outputs, left open.
            ('window_active',          ""),
            ('window_cycles',          ""),
            ('perf_prod_cycles',       ""),
            ('perf_bp_cycles',         ""),
            ('perf_starv_cycles',      ""),
            ('perf_idle_cycles',       ""),
            ('perf_beat_count',        ""),
            ('perf_byte_count',        ""),
            ('perf_burst_count',       ""),
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
        # New dedicated cfg ports (#114). Bridge top exposes these as
        # adapter inputs so the bridge cfg subsystem (#90) can route
        # them per-port when it lands; until then the integrator ties
        # them off (compl/threshold follow legacy aliases via the
        # bridge top, debug stays 0).
        'cfg_compl_enable',
        'cfg_threshold_enable',
        'cfg_debug_enable',
        'cfg_timeout_cycles',
        'cfg_freq_sel',
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
        # AXI5 feature ports terminate at the wrapper on the fabric side
        # regardless of enablement -- the fabric behind is plain AXI4.
        # Tie-off follows the wrapper's fub-port direction, which depends
        # on `side`:
        #   side='slave'  (axi5_slave_*, master adapter): req-direction
        #     extras are fub OUTPUTS (leave open); b/r-side extras are
        #     fub INPUTS driven INTO the wrapper (tie '0).
        #   side='master' (axi5_master_*, slave adapter): req-direction
        #     extras arrive FROM the fabric as fub INPUTS (tie '0 -- the
        #     AXI4 fabric has nothing to drive them); b/r-side extras
        #     are fub OUTPUTS (leave open).
        from bridge_pkg.sideband import SIDEBAND_FIELDS
        native_bases = {base for _ch, _f, _w, _feat, base in SIDEBAND_FIELDS}
        for name, feat, req_dir in self._all_axi5_extras():
            if (self.native_sideband and feat in self.axi5_features
                    and name in native_bases):
                # A5-2 slice 2: fall through to connector_prefix+base so
                # the adapter's fub_axi_<base> sideband wires bind here.
                continue
            fub_is_input = req_dir if self.side == 'master' else not req_dir
            d[name] = "'0" if fub_is_input else ""
        return d

    def _external_default_connectors(self, connector_prefix: str) -> dict:
        # External-side connectors pass through with the prefix unless
        # callers override. Base signals need no special defaults; AXI5
        # feature signals of DISABLED features are not exposed on the
        # enclosing module, so tie unexposed wrapper INPUTS to '0 and
        # leave unexposed OUTPUTS with empty connectors (house style).
        # Which extras are wrapper inputs depends on `side`:
        #   side='slave'  (s_axi face): req-direction extras are inputs.
        #   side='master' (m_axi face): b/r-side extras are inputs (they
        #     come back FROM the external slave).
        # Enabled features fall through to the prefix+base pass-through.
        d = {}
        for name, feat, req_dir in self._all_axi5_extras():
            if feat not in self.axi5_features:
                ext_is_input = (req_dir if self.side == 'slave'
                                else not req_dir)
                d[name] = "'0" if ext_is_input else ""
        return d

    def _all_axi5_extras(self):
        """Every AXI5 feature-extra tuple across all channel groups
        (empty for protocol='axi4')."""
        return (tuple(self._req1_extras) + tuple(self._req2_extras)
                + tuple(self._resp_extras))

    def _build_section_pairs(self, port_prefix: str,
                             connector_prefix: str,
                             overrides: dict) -> List[tuple]:
        """Construct (port, connector) tuples for a channel side. Each
        channel group emits its base ports first, then its AXI5 feature
        extras (empty on the axi4 family) in SV-declaration order."""
        pairs: List[tuple] = []
        groups = [self._req1_ports, self._req2_ports, self._resp_ports]
        extras = [self._req1_extras, self._req2_extras, self._resp_extras]
        labels = [self._req1_label, self._req2_label, self._resp_label]
        for group, group_extras, _label in zip(groups, extras, labels):
            if not group and not group_extras:
                continue
            base_names = tuple(group) + tuple(
                name for name, _f, _d in group_extras)
            for base in base_names:
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
