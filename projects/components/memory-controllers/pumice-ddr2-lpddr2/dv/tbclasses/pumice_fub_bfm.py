# SPDX-License-Identifier: MIT
# SPDX-FileCopyrightText: 2026 sean galloway
#
# Module: pumice_fub_bfm
# Purpose: GAXI BFMs for pumice's FUB-INTERNAL valid/ready interfaces, so
#          the fub TBs never hand-drive a handshake or its payload.

"""GAXI master/slave BFMs for pumice's fub-internal valid/ready ports.

PUMICE-014's rule is not AXI-specific: "None of the environments should
EVER hand poke on any standard interface or valid ready interface." The
fub TBs drive interfaces like `aw_push_*`, `wdata_*`, `snarf_rd_*` and
`dfi_rd_*` -- plain valid/ready handshakes with side-band payload, not an
AXI port -- so the AXI4 master BFMs do not apply. The framework's GAXI
components are the generic valid/ready driver, and they cover these.

**And they drive the PAYLOAD too, not just the handshake.** The point of
using a BFM is that the test sets no signals at all; a half-port that
takes the handshake from a BFM while still poking the data fields keeps
every problem hand-driving has.

## Signal mapping

pumice names its fub ports with direction suffixes (`aw_push_bank_o`,
`snarf_rd_data_i`), which do not match GAXI's auto-discovery patterns
(`{prefix}{bus_name}{pkt_prefix}{field_name}`). So these use an explicit
`signal_map`, which accepts `valid`, `ready`, and -- in multi_sig mode --
one entry per field name. Explicit beats contorting the RTL names to suit
discovery, and it fails loudly when a port is renamed instead of silently
binding to nothing.

## Which side is which

Read the port direction on the DUT, not the signal's role name:

  * DUT drives `*_valid_o` and reads `*_ready_i`  -> DUT produces
    -> the TB CONSUMES -> `fub_consumer()` (GAXISlave, drives ready)
  * DUT reads `*_valid_i` and drives `*_ready_o`  -> DUT consumes
    -> the TB PRODUCES -> `fub_producer()` (GAXIMaster, drives valid+payload)

## Timing

Profiles come from `TBClasses.amba.amba_random_configs`
(`GAXI_RANDOMIZER_CONFIGS`), the same common valid/ready timing source the
AXI side uses, with the same nested `master`/`slave` shape. The default is
`backtoback`; pass a backpressure profile to a consumer to prove the DUT
tolerates a stalled downstream -- which a constant `ready = 1` never did.

## Valid-only strobes are NOT this

Some fub inputs (`wr_done_valid_i` + id/resp) have NO ready at all. They
are strobes, not handshakes, so there is nothing for a BFM to pace against
and `fub_producer` cannot model them. Those stay as small named driver
methods on the TB; the rule is about valid/ready interfaces, and a
valid-only pulse is not one.
"""

from __future__ import annotations

from typing import Dict, Mapping, Optional, Sequence, Tuple

from CocoTBFramework.components.gaxi.gaxi_factories import (create_gaxi_master,
                                                            create_gaxi_slave)
from CocoTBFramework.components.shared.field_config import (FieldConfig,
                                                            FieldDefinition)
from CocoTBFramework.components.shared.flex_randomizer import FlexRandomizer
from TBClasses.amba.amba_random_configs import GAXI_RANDOMIZER_CONFIGS

DEFAULT_PROFILE = "backtoback"


def make_field_config(fields: Mapping[str, int]) -> FieldConfig:
    """FieldConfig from {field_name: width_bits}, in declaration order."""
    fc = FieldConfig()
    for name, bits in fields.items():
        fc.add_field(FieldDefinition(name=name, bits=bits))
    return fc


def _signal_map(valid: str, ready: str,
                field_signals: Mapping[str, str]) -> Dict[str, str]:
    m = {'valid': valid, 'ready': ready}
    m.update(field_signals)
    return m


def _randomizer(profile: str, side: str) -> FlexRandomizer:
    return FlexRandomizer(GAXI_RANDOMIZER_CONFIGS[profile][side])


def fub_consumer(dut, title: str, clock, *, valid: str, ready: str,
                 fields: Mapping[str, Tuple[str, int]],
                 profile: str = DEFAULT_PROFILE,
                 ready_policy: str = "always", log=None):
    """GAXISlave on a DUT-produces interface: the BFM drives `ready`.

    `ready_policy` defaults to `"always"`: ready is asserted up front and
    held, independent of valid, so valid and ready coincide on the same
    cycle. That is what these TBs previously modelled with a constant 1,
    and it matters -- GAXISlave's default `valid_first` policy waits for
    valid on a CLOCKED loop, so ready lands one cycle LATE even at
    ready_delay 0 (measured on pumice's cmd port as "10 11": valid alone
    for a cycle, then the handshake). On a DUT that gates its next pick on
    downstream ready, that extra cycle shifts every subsequent decision.

    Pass `ready_policy="valid_first"` with a backpressure profile when the
    point of the test IS to stall the producer.

    `fields` maps field name -> (dut_signal_name, width_bits).

        aw_push = fub_consumer(dut, "aw_push", dut.aclk,
                               valid="aw_push_valid_o",
                               ready="aw_push_ready_i",
                               fields={'bank': ("aw_push_bank_o", 3),
                                       'row':  ("aw_push_row_o", 14)})

    Received packets land on `aw_push.received_queue` -- so the TB's old
    hand-rolled monitor coroutine goes away with the hand-driven ready.
    """
    fc = make_field_config({n: w for n, (_, w) in fields.items()})
    return create_gaxi_slave(
        dut, title, "", clock, field_config=fc, multi_sig=True,
        signal_map=_signal_map(valid, ready,
                               {n: sig for n, (sig, _) in fields.items()}),
        randomizer=_randomizer(profile, "slave"),
        ready_policy=ready_policy,
        log=log if log is not None else dut._log)


def fub_producer(dut, title: str, clock, *, valid: str, ready: str,
                 fields: Mapping[str, Tuple[str, int]],
                 profile: str = DEFAULT_PROFILE, log=None):
    """GAXIMaster on a DUT-consumes interface: the BFM drives `valid` AND
    every payload field, and honours the DUT's `ready`.

        dfi_rd = fub_producer(dut, "dfi_rd", dut.aclk,
                              valid="dfi_rd_valid_i",
                              ready="dfi_rd_ready_o",
                              fields={'data': ("dfi_rd_data_i", 128),
                                      'last': ("dfi_rd_last_i", 1)})
        await dfi_rd.send(dfi_rd.create_packet(data=0xdead, last=1))
    """
    fc = make_field_config({n: w for n, (_, w) in fields.items()})
    return create_gaxi_master(
        dut, title, "", clock, field_config=fc, multi_sig=True,
        signal_map=_signal_map(valid, ready,
                               {n: sig for n, (sig, _) in fields.items()}),
        randomizer=_randomizer(profile, "master"),
        log=log if log is not None else dut._log)


def fub_pulse_producer(dut, title: str, clock, *, valid: str, ready: str,
                       profile: str = DEFAULT_PROFILE, log=None):
    """GAXIMaster on a PAYLOAD-LESS valid/ready request port.

    Some fub request ports are just `x_valid_i` / `x_ready_o` with no data
    at all (pumice_dfi_rd_aligner's `op_*` is one: the aligner needs to know
    a read was issued, nothing more). They are still handshakes -- the DUT
    can backpressure -- so they are in scope for PUMICE-014, but there is no
    payload to map.

    Modelled as a single 1-bit field bound to the VALID signal itself. The
    BFM drives valid, honours ready, and the field write is a harmless
    re-assert of the bit the handshake already sets.
    """
    fc = make_field_config({'req': 1})
    return create_gaxi_master(
        dut, title, "", clock, field_config=fc, multi_sig=True,
        signal_map=_signal_map(valid, ready, {'req': valid}),
        randomizer=_randomizer(profile, "master"),
        log=log if log is not None else dut._log)


def set_profile(component, profile: str, side: str) -> None:
    """Retime a GAXI component. `side` is 'master' (valid_delay, a
    producer) or 'slave' (ready_delay, a consumer)."""
    component.randomizer = _randomizer(profile, side)
