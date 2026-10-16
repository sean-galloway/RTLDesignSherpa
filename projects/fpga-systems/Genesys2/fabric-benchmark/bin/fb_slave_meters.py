# SPDX-License-Identifier: MIT
# SPDX-FileCopyrightText: 2026 sean galloway
"""Read the slave-side observer (the fabric's output, S2 reads / S3 writes).

fb_harness instantiates the same observer at slvmon_apb (0x0018_0000) as the
master-side one at obs_apb (0x0019_0000), sharing its measurement window. The
register layout is identical, so this reads it with obs_addrs' names rebased
onto SLAVE_OBS_APB_BASE and bus_meters' selector packing -- nothing new to keep
in step. Master-side utilization minus slave-side utilization is what the
fabric itself costs.
"""
import fb_map

METRICS = ('productive', 'backpressure', 'starvation', 'idle')


def read_buckets(bridge, is_write: int) -> dict:
    fb_map.stream_host_path()
    from obs_addrs import O, SLAVE_OBS_APB_BASE
    from bus_meters import _stat_sel, _STAT_METRIC
    out = {}
    for m in METRICS:
        bridge.write(O("OBS_STAT_SEL", SLAVE_OBS_APB_BASE), _stat_sel(_STAT_METRIC[m], is_write))
        out[m] = (bridge.read(O("OBS_STAT_DATA", SLAVE_OBS_APB_BASE)) or 0) & 0xFFFF_FFFF
    return out


def utilization(b: dict) -> float:
    total = sum(b[m] for m in METRICS)
    return b['productive'] / total if total else 0.0


def read_slave_side(bridge) -> dict:
    """{'r': buckets, 'w': buckets, 'r_util': float, 'w_util': float}."""
    r, w = read_buckets(bridge, 0), read_buckets(bridge, 1)
    return {'r': r, 'w': w, 'r_util': utilization(r), 'w_util': utilization(w)}
