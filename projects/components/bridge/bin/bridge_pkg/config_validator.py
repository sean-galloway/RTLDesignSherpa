#!/usr/bin/env python3
# SPDX-License-Identifier: MIT
# SPDX-FileCopyrightText: 2024-2025 sean galloway
#
# Configuration Validator for Bridge Generator
# Purpose: Validate YAML bridge configurations and detect illegal combinations

"""
Configuration Validator

Validates bridge configurations to detect:
1. Invalid channel specifications (not in ['rw', 'rd', 'wr'])
2. Invalid protocol specifications (see validate_protocol for the set)
3. Illegal master-slave channel combinations (incompatible channels)
4. APB-specific constraints (must be 'rw', specific data widths)
5. AXI4-Lite specific constraints
6. Missing required fields
7. Semantic errors (slaves shouldn't specify channels - derived from masters)

Usage:
    from bridge_pkg.config_validator import validate_config, ValidationError

    try:
        validate_config(masters, slaves, connectivity)
    except ValidationError as e:
        print(f"Configuration error: {e}")
        sys.exit(1)
"""

from typing import List, Dict, Set
from .config import PortSpec


class ValidationError(Exception):
    """Exception raised for configuration validation errors."""
    pass


def validate_channels(channels: str, port_name: str) -> None:
    """
    Validate channels field value.

    Args:
        channels: Channel specification ('rw', 'rd', 'wr')
        port_name: Port name for error messages

    Raises:
        ValidationError: If channels value is invalid
    """
    valid_channels = {'rw', 'rd', 'wr'}
    if channels not in valid_channels:
        raise ValidationError(
            f"Invalid channels '{channels}' for port '{port_name}'. "
            f"Must be one of {valid_channels}"
        )


def validate_protocol(protocol: str, port_name: str) -> None:
    """
    Validate protocol field value.

    Args:
        protocol: Protocol specification -- see valid_protocols below
        port_name: Port name for error messages

    Raises:
        ValidationError: If protocol value is invalid
    """
    # 'axil5' is an AXI5-Lite slave boundary: AXI4-Lite transfers plus the
    # optional sideband groups, converted by axi4_to_axil5_{rd,wr}.
    valid_protocols = {'axi4', 'axi5', 'apb', 'apb5', 'axil', 'axil5'}
    if protocol not in valid_protocols:
        raise ValidationError(
            f"Invalid protocol '{protocol}' for port '{port_name}'. "
            f"Must be one of {valid_protocols}"
        )


# ---------------------------------------------------------------------------
# AXI5 (BRIDGE-002 phases A5-1 / A5-2 slice 1) — AXI5 ports on the AMBA4
# fabric, interop mode.
#
# A bridge MASTER port with protocol="axi5" gets axi5_slave_{wr,rd}
# boundary wrappers exposing an AXI5 external interface (A5-1); a bridge
# SLAVE port with protocol="axi5" gets axi5_master_{wr,rd} boundary
# wrappers driving an external AXI5 slave (A5-2 slice 1). In both cases
# the fabric behind/between stays AXI4. Only pure-sideband features can
# be exposed in interop mode (they terminate safely at the wrapper).
# Features that change data semantics or need response routing are
# phase-gated below.
# ---------------------------------------------------------------------------

# Features legal in interop mode: pure sideband, terminated at the AXI4
# fabric.
AXI5_ALLOWED_FEATURES = ('nsaid', 'trace', 'mpam', 'mecid', 'unique')

# Features that exist in the axi5 wrappers but are NOT deliverable on an
# AXI4 fabric without more work. Maps feature -> the phase that lands it.
# 'poison' left this set in A5-2 slice 2: it is legal under the
# connectivity rule below (validate_axi5_poison_connectivity).
AXI5_PHASED_FEATURES = {
    'mte':      'deferred (per-beat tag fields; revisit after poison)',
    'chunking': 'deferred (R-channel re-framing through converters)',
}

# Legal ONLY when every connected path carries it natively end-to-end
# (A5-2 slice 2): both ends protocol="axi5" with the feature enabled and
# width-matched (per-beat sideband cannot traverse the dwidth-converter
# IP, and unlike the droppable sideband set, silently dropping POISON
# would turn corrupted data into trusted data).
# 'atomic' (A5-3a): store-class atomics ride the structs natively;
# the master boundary's axi5_atomic_filter DECERRs read-return classes
# (AtomicLoad/Swap/Compare), which this fabric cannot route.
AXI5_CONNECTIVITY_GATED_FEATURES = ('poison', 'atomic')


def validate_axi5(masters: List[PortSpec], slaves: List[PortSpec]) -> None:
    """
    Validate AXI5 usage per the interop scope (A5-1 masters + A5-2
    slice-1 slaves).

    Rules:
    1. axi5_features on a non-axi5 port is rejected.
    2. Feature entries on any axi5 port (master or slave) must be in
       AXI5_ALLOWED_FEATURES; features in AXI5_PHASED_FEATURES are
       rejected naming the delivering phase; anything else is an unknown
       feature name.

    Raises:
        ValidationError: on any violation.
    """
    for port in list(masters) + list(slaves):
        feats = getattr(port, 'axi5_features', []) or []
        if feats and port.protocol not in ('axi5', 'axil5'):
            raise ValidationError(
                f"Port '{port.port_name}': 'axi5_features' is only legal "
                f"on protocol=\"axi5\"/\"axil5\" ports (got protocol="
                f"'{port.protocol}')"
            )

    validate_axil5_features(list(masters) + list(slaves))

    for port in list(masters) + list(slaves):
        if port.protocol != 'axi5':
            continue
        kind = 'master' if port.direction == 'master' else 'slave'
        feats = getattr(port, 'axi5_features', []) or []
        seen = set()
        for f in feats:
            if f in seen:
                raise ValidationError(
                    f"AXI5 {kind} '{port.port_name}': duplicate "
                    f"axi5_features entry '{f}'"
                )
            seen.add(f)
            if f in AXI5_ALLOWED_FEATURES:
                continue
            if f in AXI5_CONNECTIVITY_GATED_FEATURES:
                # Accepted here; validate_axi5_poison_connectivity
                # enforces the every-path-native rule.
                continue
            if f in AXI5_PHASED_FEATURES:
                raise ValidationError(
                    f"AXI5 {kind} '{port.port_name}': feature '{f}' is "
                    f"not supported in interop mode; it lands with "
                    f"{AXI5_PHASED_FEATURES[f]}."
                )
            raise ValidationError(
                f"AXI5 {kind} '{port.port_name}': unknown axi5_features "
                f"entry '{f}'. Allowed in interop mode: "
                f"{list(AXI5_ALLOWED_FEATURES)}; connectivity-gated: "
                f"{list(AXI5_CONNECTIVITY_GATED_FEATURES)}; phase-gated: "
                f"{sorted(AXI5_PHASED_FEATURES)}"
            )


# AXI5-Lite features that actually do something on an AXI4 fabric. Only these
# two have an AXI4 source to forward, so only these two are gates in
# axi4_to_axil5_{rd,wr}. The rest of the AXI5-Lite sideband is exposed on the
# boundary and tied to zero either way -- naming one in axi5_features would
# suggest it does something, so it is rejected rather than quietly ignored.
AXIL5_FORWARDABLE_FEATURES = ('user', 'exclusive')

# Named separately from the unknown-name case so the message can say WHY: a
# reader who asked for mpam on an AXI4 fabric has a design question, not a
# typo.
AXIL5_TIED_FEATURES = ('trace', 'loop', 'mpam', 'mecid', 'nsaid', 'poison')


def validate_axil5_features(ports: List[PortSpec]) -> None:
    """Only the forwardable groups may be named on an axil5 port.

    Masters and slaves alike (BRIDGE-014): on a master port the same two
    groups are the only ones with an AXI4 destination -- 'exclusive' rides
    awlock/arlock and 'user' the 1-bit USER fields; the rest is exposed on
    the boundary and terminated at the bridge top."""
    for port in ports:
        if port.protocol != 'axil5':
            continue
        kind = 'master' if port.direction == 'master' else 'slave'
        seen = set()
        for f in getattr(port, 'axi5_features', []) or []:
            if f in seen:
                raise ValidationError(
                    f"AXI5-Lite {kind} '{port.port_name}': duplicate "
                    f"axi5_features entry '{f}'")
            seen.add(f)
            if f in AXIL5_FORWARDABLE_FEATURES:
                continue
            if f in AXIL5_TIED_FEATURES:
                where = ("the converter ties it to zero" if kind == 'slave'
                         else "the bridge top terminates it")
                raise ValidationError(
                    f"AXI5-Lite {kind} '{port.port_name}': feature '{f}' has "
                    f"no AXI4 {'source' if kind == 'slave' else 'destination'}, "
                    f"so {where} whether or not it is named here. Its port is "
                    f"exposed on the boundary regardless -- remove it from "
                    f"axi5_features. Forwardable: "
                    f"{list(AXIL5_FORWARDABLE_FEATURES)}")
            raise ValidationError(
                f"AXI5-Lite {kind} '{port.port_name}': unknown axi5_features "
                f"entry '{f}'. Legal on an axil5 port: "
                f"{list(AXIL5_FORWARDABLE_FEATURES)}")


def _axi5_connected_pairs(masters: List[PortSpec], slaves: List[PortSpec],
                          connectivity) -> List[tuple]:
    """(master, slave) PortSpec pairs that are connected per the
    connectivity dict (master_name -> collection of slave names)."""
    pairs = []
    for m in masters:
        connected = connectivity.get(m.port_name, set()) if connectivity else set()
        for s in slaves:
            if s.port_name in connected:
                pairs.append((m, s))
    return pairs


def validate_axi5_poison_connectivity(masters: List[PortSpec],
                                      slaves: List[PortSpec],
                                      connectivity) -> None:
    """A5-2 slice 2: 'poison' is legal on a port ONLY when every
    connected path carries it natively end-to-end — both ends
    protocol="axi5" with poison enabled, and data widths matched (no
    dwidth converter on the path). Unlike the droppable sideband set,
    a silently-dropped POISON bit would let corrupted data read back
    as trusted data, so any non-native path is a config error."""
    def has_feat(p, feat):
        return (p.protocol == 'axi5'
                and feat in (getattr(p, 'axi5_features', None) or []))

    pairs = _axi5_connected_pairs(masters, slaves, connectivity)
    for feature in AXI5_CONNECTIVITY_GATED_FEATURES:
      for port in list(masters) + list(slaves):
        if not has_feat(port, feature):
            continue
        if port.direction == 'master':
            others = [s for m, s in pairs if m.port_name == port.port_name]
            other_kind = 'slave'
        else:
            others = [m for m, s in pairs if s.port_name == port.port_name]
            other_kind = 'master'
        for other in others:
            # The subtractive catch-all is not a data path. It never services
            # a transaction -- it REJECTS one, with DECERR, because no slave
            # claimed the address. An AXI5 feature has nothing to be carried
            # natively THROUGH: poison, atomics and the rest describe how a
            # request is to be honoured, and this one is not being honoured.
            # Requiring it to be AXI5 would force every AXI5 bridge to give
            # its error terminator sideband it can never use.
            if getattr(other, 'internal', False):
                continue
            problems = []
            if other.protocol != 'axi5':
                problems.append(f"protocol '{other.protocol}' (needs axi5)")
            elif feature not in (getattr(other, 'axi5_features', None) or []):
                problems.append(f"no '{feature}' in axi5_features")
            if other.data_width != port.data_width:
                problems.append(
                    f"data width {other.data_width} != {port.data_width} "
                    f"(dwidth converters cannot carry per-beat sideband)")
            if problems:
                raise ValidationError(
                    f"AXI5 port '{port.port_name}' enables '{feature}' but "
                    f"connected {other_kind} '{other.port_name}' cannot "
                    f"carry it natively: {'; '.join(problems)}. Every "
                    f"connected path must be AXI5-both-ends, "
                    f"{feature}-enabled, and width-matched."
                )


def validate_axi5_atomic_read_return(masters: List[PortSpec],
                                     slaves: List[PortSpec],
                                     connectivity) -> None:
    """BRIDGE-002 A5-3b. An rw AXI5 master that enables 'atomic' forwards
    read-return atomics (AtomicLoad/Swap/Compare) natively -- there is no
    boundary filter on such a port -- and they answer on the READ data
    channel with the AW's ID. Every connected atomic slave must therefore be
    able to return read data ('rw'). The per-ID return tracker sits beside
    whichever read tracker the slave uses (in-order FIFO or, with enable_ooo,
    the CAM). A write-only atomic master keeps the A5-3a filter and is not
    subject to this rule."""
    for m, s in _axi5_connected_pairs(masters, slaves, connectivity):
        if not (m.protocol == 'axi5'
                and 'atomic' in (getattr(m, 'axi5_features', None) or [])
                and m.channels == 'rw'):
            continue
        if getattr(s, 'internal', False):
            continue
        if s.channels != 'rw':
            raise ValidationError(
                f"AXI5 master '{m.port_name}' is 'rw' with 'atomic', so its "
                f"read-return atomics forward natively and answer on R -- but "
                f"connected slave '{s.port_name}' has channels '{s.channels}' "
                f"and cannot return read data. Give the slave 'rw', or make "
                f"the master write-only (which keeps the boundary filter and "
                f"answers read-return classes with DECERR)."
            )


def validate_slave_id_widths(masters: List[PortSpec], slaves: List[PortSpec]) -> None:
    """BRIDGE-016. Inside the fabric every transaction ID is {master index,
    master id}, so a slave sees the widest master's id_width plus
    $clog2(NUM_MASTERS) bits (zero for one master). The slave's declared
    id_width is the width of its external port and must be at least that, or
    the prefix would be truncated and two masters could alias again."""
    from bridge_pkg.width_utils import xbar_id_width, id_prefix_width, master_id_width
    need = xbar_id_width(masters)
    if id_prefix_width(masters) == 0:
        return
    for s in slaves:
        if getattr(s, 'internal', False):
            continue
        if s.protocol not in ('axi4', 'axi5'):
            continue
        if (s.id_width or 0) < need:
            raise ValidationError(
                f"Slave '{s.port_name}' declares id_width {s.id_width}, but with "
                f"{len(list(masters))} masters the fabric prepends {id_prefix_width(masters)} "
                f"master-index bit(s) to the {master_id_width(masters)}-bit master ID, so "
                f"every AXI slave port carries {need}-bit IDs. Set id_width = {need} "
                f"(or wider) on this slave, and size whatever it connects to accordingly."
            )


def warn_axi5_dropped_sideband(masters: List[PortSpec],
                               slaves: List[PortSpec],
                               connectivity) -> None:
    """Generation-time warnings for droppable sideband that will NOT
    propagate on some connected path (other end not axi5 / feature
    missing / width mismatch). Dropping is legal for these features —
    the warning just makes the termination visible in the build log."""
    droppable = set(AXI5_ALLOWED_FEATURES)
    for m, s in _axi5_connected_pairs(masters, slaves, connectivity):
        m_feats = (set(getattr(m, 'axi5_features', None) or [])
                   if m.protocol == 'axi5' else set())
        s_feats = (set(getattr(s, 'axi5_features', None) or [])
                   if s.protocol == 'axi5' else set())
        for f in sorted((m_feats | s_feats) & droppable):
            reasons = []
            if f not in m_feats:
                reasons.append(f"master '{m.port_name}' does not carry it")
            if f not in s_feats:
                reasons.append(
                    f"slave '{s.port_name}' is not axi5/{f}-enabled")
            if m.data_width != s.data_width:
                reasons.append(
                    f"width {m.data_width}->{s.data_width} converter "
                    f"drops sideband")
            if reasons:
                print(f"  WARNING: AXI5 sideband '{f}' terminates on path "
                      f"{m.port_name} -> {s.port_name}: "
                      f"{'; '.join(reasons)}")


def validate_apb_constraints(port: PortSpec) -> None:
    """
    Validate APB-specific constraints.

    APB constraints:
    1. Must support both read and write (channels = 'rw')
    2. Data width must be 32 bits (APB4 standard)
    3. Address width typically 32 bits
    4. No ID width (APB has no transaction IDs)

    Args:
        port: Port specification to validate

    Raises:
        ValidationError: If APB constraints are violated
    """
    if port.protocol not in ('apb', 'apb5'):
        return  # Not APB/APB5, skip (apb5 shares APB4's transfer
        # protocol, so the same rw-only/32-bit constraints apply)

    # APB must be read-write
    if port.channels != 'rw':
        raise ValidationError(
            f"APB port '{port.port_name}' must have channels='rw' "
            f"(APB protocol requires both read and write support). "
            f"Got channels='{port.channels}'"
        )

    # APB data width is 32 bits (APB4 standard)
    if port.data_width not in [8, 16, 32]:
        raise ValidationError(
            f"APB port '{port.port_name}' has non-standard data width {port.data_width}. "
            f"APB4 standard data widths are 8, 16, or 32 bits. "
            f"Consider using 32-bit width for standard compliance."
        )

    # APB has no transaction IDs
    if port.id_width != 0:
        raise ValidationError(
            f"APB port '{port.port_name}' must have id_width=0 "
            f"(APB protocol has no transaction IDs). "
            f"Got id_width={port.id_width}"
        )


def validate_master_slave_compatibility(
    master: PortSpec,
    slave: PortSpec,
    connectivity: Dict[str, Set[str]]
) -> None:
    """
    Validate that connected masters and slaves have compatible channels.

    Compatibility rules:
    1. Write-only master (wr) can ONLY connect to slaves supporting write (wr or rw)
    2. Read-only master (rd) can ONLY connect to slaves supporting read (rd or rw)
    3. Full RW master (rw) can connect to any slave (rw, wr, or rd)
    4. APB slaves MUST be 'rw' (validated separately)

    Args:
        master: Master port specification
        slave: Slave port specification
        connectivity: Connectivity dictionary

    Raises:
        ValidationError: If master-slave channel combination is illegal
    """
    # Check if master connects to this slave
    if slave.port_name not in connectivity.get(master.port_name, set()):
        return  # Not connected, skip validation

    master_channels = master.channels
    slave_channels = slave.channels

    # Write-only master
    if master_channels == 'wr':
        if slave_channels == 'rd':
            raise ValidationError(
                f"Illegal connection: Write-only master '{master.port_name}' "
                f"cannot connect to read-only slave '{slave.port_name}'. "
                f"Master has channels='wr' (AW, W, B), "
                f"slave has channels='rd' (AR, R) - no compatible channels!"
            )

    # Read-only master
    elif master_channels == 'rd':
        if slave_channels == 'wr':
            raise ValidationError(
                f"Illegal connection: Read-only master '{master.port_name}' "
                f"cannot connect to write-only slave '{slave.port_name}'. "
                f"Master has channels='rd' (AR, R), "
                f"slave has channels='wr' (AW, W, B) - no compatible channels!"
            )

    # Full RW master can connect to any slave (no error case)


def validate_slave_channels_explicit(slaves: List[PortSpec]) -> None:
    """
    Validate that slaves have explicit channel specifications.

    IMPORTANT: Slaves MUST explicitly specify channels in YAML - no defaults, no guessing.
    This ensures the configuration is self-documenting and the user's intent is clear.

    Slaves should specify the channels they SUPPORT, not necessarily what they REQUIRE.
    The crossbar will only generate channels actually needed by connecting masters.

    Args:
        slaves: List of slave port specifications

    Raises:
        ValidationError: If any slave doesn't explicitly specify channels
    """
    for slave in slaves:
        # Check if channels was explicitly set (not just defaulted)
        # Note: This assumes config_loader sets channels during parsing
        # We validate it's one of the valid values
        if not slave.channels:
            raise ValidationError(
                f"Configuration error: Slave '{slave.port_name}' missing 'channels' field. "
                f"Slaves MUST explicitly specify channels ('rw', 'rd', or 'wr'). "
                f"This documents the slave's supported operations.\n"
                f"\n"
                f"Example:\n"
                f"  slaves:\n"
                f"    - name: {slave.port_name}\n"
                f"      channels: rw  # Supports both read and write\n"
                f"\n"
                f"Note: The crossbar will only generate channels actually needed by "
                f"connecting masters, but the slave must declare what it supports."
            )


def validate_required_fields(port: PortSpec) -> None:
    """
    Validate that all required fields are present and non-zero where appropriate.

    Args:
        port: Port specification to validate

    Raises:
        ValidationError: If required fields are missing or invalid
    """
    # All ports need these
    if not port.port_name:
        raise ValidationError("Port missing 'name' field")

    if not port.prefix:
        raise ValidationError(f"Port '{port.port_name}' missing 'prefix' field")

    if port.data_width <= 0:
        raise ValidationError(f"Port '{port.port_name}' has invalid data_width={port.data_width}")

    if port.addr_width <= 0:
        raise ValidationError(f"Port '{port.port_name}' has invalid addr_width={port.addr_width}")

    # AXI4 masters need ID width
    if port.direction == 'master' and port.protocol == 'axi4':
        if port.id_width <= 0:
            raise ValidationError(
                f"AXI4 master '{port.port_name}' must have id_width > 0. "
                f"Got id_width={port.id_width}"
            )

    # Lite requesters carry no ID: the adapter's internal face uses a
    # placeholder sized by the bridge (fub_id_width) and the fabric prepends
    # the master index. A non-zero id_width here would size ports that do
    # not exist on the boundary.
    if port.direction == 'master' and port.protocol in ('axil', 'axil5'):
        if port.id_width:
            raise ValidationError(
                f"AXI-Lite master '{port.port_name}' must have id_width=0 "
                f"(AXI4-Lite/AXI5-Lite have no transaction IDs). "
                f"Got id_width={port.id_width}"
            )

    # An APB requester supplies the full fabric address: PADDR is the
    # 32-bit AXI address, not a window offset the way an APB slave port's
    # PADDR is. (APB slave ports are windowed by base_addr; masters are not.)
    if port.direction == 'master' and port.protocol in ('apb', 'apb5'):
        if port.addr_width != 32:
            raise ValidationError(
                f"APB master '{port.port_name}' must have addr_width=32 "
                f"(the requester addresses the whole fabric). "
                f"Got addr_width={port.addr_width}"
            )

    # Slaves need address mapping
    if port.direction == 'slave':
        if port.base_addr is None:
            raise ValidationError(f"Slave '{port.port_name}' missing 'base_addr' field")

        if port.addr_range is None or port.addr_range <= 0:
            raise ValidationError(
                f"Slave '{port.port_name}' has invalid addr_range={port.addr_range}"
            )

        # 4K page-alignment rule. Every slave hanging off the bridge
        # needs a 4K-multiple addressable space and a 4K-aligned base.
        # This matches what every real bus / MMU / address-decoder
        # expects: sub-4K agents create decode gaps and tooling
        # assumptions break (e.g. linker scripts, page-table mappers,
        # config-register layout helpers).
        page = 0x1000
        if port.base_addr & (page - 1):
            raise ValidationError(
                f"Slave '{port.port_name}' base_addr 0x{port.base_addr:08X} "
                f"is not 4K-aligned. Real bus agents must sit on a 4K page boundary."
            )
        if port.addr_range & (page - 1):
            raise ValidationError(
                f"Slave '{port.port_name}' addr_range 0x{port.addr_range:X} "
                f"is not a multiple of 4K (0x1000). Real bus agents must "
                f"occupy whole 4K pages -- bump it up to at least 0x1000."
            )


def validate_address_map(slaves: List[PortSpec]) -> None:
    """
    Validate slave address map for overlaps.

    Args:
        slaves: List of slave port specifications

    Raises:
        ValidationError: If slave address ranges overlap
    """
    # A SUBTRACTIVE slave overlaps everything by definition -- it claims the
    # addresses no positively-decoded slave claimed, which is expressible only
    # as the full span plus last-place in the decode chain. Comparing it for
    # overlap asks the wrong question: the decode is if/else-if/else, so an
    # address that matched an earlier arm never reaches it.
    positional = [sl for sl in slaves if not sl.internal]

    for i, slave1 in enumerate(positional):
        addr1_start = slave1.base_addr
        addr1_end = slave1.base_addr + slave1.addr_range - 1

        for slave2 in positional[i+1:]:
            addr2_start = slave2.base_addr
            addr2_end = slave2.base_addr + slave2.addr_range - 1

            # Check for overlap
            if not (addr1_end < addr2_start or addr2_end < addr1_start):
                raise ValidationError(
                    f"Address overlap detected:\n"
                    f"  Slave '{slave1.port_name}': 0x{addr1_start:08X} - 0x{addr1_end:08X}\n"
                    f"  Slave '{slave2.port_name}': 0x{addr2_start:08X} - 0x{addr2_end:08X}\n"
                    f"Slave address ranges must not overlap!"
                )


def validate_config(
    masters: List[PortSpec],
    slaves: List[PortSpec],
    connectivity: Dict[str, Set[str]]
) -> None:
    """
    Comprehensive validation of bridge configuration.

    Validates:
    1. Required fields presence
    2. Valid channels and protocols
    3. APB-specific constraints
    4. Master-slave channel compatibility
    5. Slave channel semantic correctness
    6. Address map overlaps

    Args:
        masters: List of master port specifications
        slaves: List of slave port specifications
        connectivity: Connectivity dictionary (master_name -> set of slave_names)

    Raises:
        ValidationError: If any validation check fails
    """
    # Validate each master
    for master in masters:
        validate_required_fields(master)
        validate_channels(master.channels, master.port_name)
        validate_protocol(master.protocol, master.port_name)
        validate_apb_constraints(master)

    # Validate each slave
    for slave in slaves:
        validate_required_fields(slave)
        validate_channels(slave.channels, slave.port_name)
        validate_protocol(slave.protocol, slave.port_name)
        validate_apb_constraints(slave)

    # Validate explicit channel specification for slaves
    validate_slave_channels_explicit(slaves)

    # Validate AXI5 scope (interop mode: sideband features only, on
    # masters (A5-1) and slaves (A5-2 slice 1) alike)
    validate_axi5(masters, slaves)

    # A5-2 slice 2: poison needs every connected path native; the
    # droppable sideband set gets visibility warnings when it will
    # terminate mid-path.
    validate_axi5_poison_connectivity(masters, slaves, connectivity)
    validate_axi5_atomic_read_return(masters, slaves, connectivity)
    validate_slave_id_widths(masters, slaves)
    warn_axi5_dropped_sideband(masters, slaves, connectivity)

    # Validate address map
    validate_address_map(slaves)

    # Validate master-slave compatibility
    for master in masters:
        for slave in slaves:
            validate_master_slave_compatibility(master, slave, connectivity)

    print("✓ Configuration validation passed")
