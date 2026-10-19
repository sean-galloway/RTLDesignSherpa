"""Per-master lanes into a multi-master slave on its own clock (bridge W9).

A `cdc = true` AXI4 slave that two or more masters reach is arbitrated on its
own clock: the crossbar hands each master's AW / W / AR to the slave adapter
on a lane of its own, and bridge_cdc_slave_arb crosses every lane and picks
among them on s_aclk. B and R keep the ordinary single-slave ports.

The crossbar, the bridge top and the slave adapter all size and order the
lanes from here, so the three cannot disagree.
"""

from typing import List, Sequence

# Fixed AXI4 address-channel fields after id and addr:
# len 8, size 3, burst 2, lock 1, cache 4, prot 3, qos 4, region 4, user 1.
_AX_FIXED = 8 + 3 + 2 + 1 + 4 + 3 + 4 + 4 + 1


def is_lane_slave(slave, idx: int, masters: Sequence) -> bool:
    """True for a cdc AXI4 slave (slave index `idx`) that two or more
    masters reach."""
    if not getattr(slave, 'cdc', False) or getattr(slave, 'protocol', 'axi4') != 'axi4':
        return False
    return len(lane_masters(idx, masters)) >= 2


def lane_masters(idx: int, masters: Sequence) -> List:
    """The masters that reach slave `idx`, in master order: lane i is the
    i-th. A master without a write (read) channel has its AW/W (AR) lane
    tied off."""
    return [m for m in masters if idx in m.slave_connections]


def ax_width(id_w: int, addr_w: int) -> int:
    """AW / AR lane payload: {id, addr, len, size, burst, lock, cache, prot,
    qos, region, user}."""
    return id_w + addr_w + _AX_FIXED


def w_width(data_w: int) -> int:
    """W lane payload: {data, strb, last, user}."""
    return data_w + data_w // 8 + 1 + 1


def b_width(id_w: int) -> int:
    """B crossing payload: {id, resp, user}."""
    return id_w + 2 + 1


def r_width(id_w: int, data_w: int) -> int:
    """R crossing payload: {id, data, resp, last, user}."""
    return id_w + data_w + 2 + 1 + 1


AX_FIELDS = ('id', 'addr', 'len', 'size', 'burst', 'lock', 'cache', 'prot',
             'qos', 'region', 'user')
W_FIELDS = ('data', 'strb', 'last', 'user')
