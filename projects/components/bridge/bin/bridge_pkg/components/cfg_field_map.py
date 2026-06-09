# SPDX-License-Identifier: MIT
# SPDX-FileCopyrightText: 2026 sean galloway
"""
Map from cfg-net basenames (as used by the bridge generator's
MONITOR_CFG_SIGNALS) to the corresponding RDL register/field pair
in the peakrdl-generated regblock (90.2).

Used by the bridge top emit (90.3) to wire each internal
`cfg_<port>_<idx>_<chan>_<base>` net to
`hwif_out.<NAME>_<IDX>_<CHAN>_<REG>.<base>.value`.

The schema mirrors bridge_cfg.rdl.j2 (per-direction CTRL + LATENCY
+ MASKS_A..E for the per-monitor cluster; MON_GROUP_*_* for the
shared cluster). Keep the two in lockstep.
"""

# Per-monitor cfg field: base -> (reg_suffix, field_name)
PER_MON_FIELD_MAP = {
    'monitor_enable':    ('CTRL',    'monitor_enable'),
    'error_enable':      ('CTRL',    'error_enable'),
    'timeout_enable':    ('CTRL',    'timeout_enable'),
    'perf_enable':       ('CTRL',    'perf_enable'),
    'compl_enable':      ('CTRL',    'compl_enable'),
    'threshold_enable':  ('CTRL',    'threshold_enable'),
    'debug_enable':      ('CTRL',    'debug_enable'),
    'timeout_cycles':    ('CTRL',    'timeout_cycles'),
    'latency_threshold': ('LATENCY', 'latency_threshold'),
    'axi_pkt_mask':      ('MASKS_A', 'axi_pkt_mask'),
    'axi_err_select':    ('MASKS_A', 'axi_err_select'),
    'axi_error_mask':    ('MASKS_B', 'axi_error_mask'),
    'axi_timeout_mask':  ('MASKS_B', 'axi_timeout_mask'),
    'axi_compl_mask':    ('MASKS_C', 'axi_compl_mask'),
    'axi_thresh_mask':   ('MASKS_C', 'axi_thresh_mask'),
    'axi_perf_mask':     ('MASKS_D', 'axi_perf_mask'),
    'axi_addr_mask':     ('MASKS_D', 'axi_addr_mask'),
    'axi_debug_mask':    ('MASKS_E', 'axi_debug_mask'),
}

# Group cfg (mon_group_*) is data-driven from the bridge generator's
# _MON_GROUP_CFG tuple. The layout is:
#   - 32-bit fields (base_addr, limit_addr) each get their own reg
#     named MON_GROUP_<BASE>.
#   - 16-bit mask fields are packed two per register, named
#     MON_GROUP_PACK_<N> where N is the pack index.
# `build_group_field_map(mon_group_cfg)` returns the dict; the
# matching Jinja template iterates the same list.

def build_group_field_map(mon_group_cfg):
    """Build {base -> (reg_name, field_name)} from the _MON_GROUP_CFG
    tuple list. Mirrors the layout the Jinja template emits."""
    mapping = {}
    pack_idx = 0
    pending = None  # (base, width) waiting for a low-half partner
    for base, width in mon_group_cfg:
        if width == 32:
            reg = f"MON_GROUP_{base.upper()}"
            mapping[base] = (reg, base)
            # If a 16-bit was pending, flush it as a solo low-half pack.
            if pending is not None:
                solo_reg = f"MON_GROUP_PACK_{pack_idx}"
                mapping[pending[0]] = (solo_reg, pending[0])
                pack_idx += 1
                pending = None
        elif width == 16:
            if pending is None:
                pending = (base, width)
            else:
                reg = f"MON_GROUP_PACK_{pack_idx}"
                mapping[pending[0]] = (reg, pending[0])
                mapping[base]       = (reg, base)
                pack_idx += 1
                pending = None
        else:
            raise NotImplementedError(
                f"mon_group field {base!r} has unsupported width {width}"
            )
    if pending is not None:
        reg = f"MON_GROUP_PACK_{pack_idx}"
        mapping[pending[0]] = (reg, pending[0])
    return mapping


# Built lazily when first needed; callers pass mon_group_cfg explicitly
# to keep the dependency direction clean.


def per_mon_hwif_ref(port_prefix: str, base: str) -> str:
    """Build the hwif_out.<REG>.<field>.value expression for a per-monitor
    cfg signal. `port_prefix` is e.g. 'host_0_wr'."""
    reg_suffix, field = PER_MON_FIELD_MAP[base]
    reg = f"{port_prefix.upper()}_{reg_suffix}"
    return f"hwif_out.{reg}.{field}.value"


def group_hwif_ref(base: str, mon_group_cfg) -> str:
    """Build the hwif_out.<REG>.<field>.value expression for a group cfg
    signal (cfg_mon_group_<base>). `mon_group_cfg` is the bridge
    generator's _MON_GROUP_CFG tuple."""
    reg, field = build_group_field_map(mon_group_cfg)[base]
    return f"hwif_out.{reg}.{field}.value"
