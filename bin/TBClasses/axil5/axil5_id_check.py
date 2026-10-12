# SPDX-License-Identifier: MIT
# SPDX-FileCopyrightText: 2026 sean galloway
#
# RTL Design Sherpa - Industry-Standard RTL Design and Verification
# https://github.com/sean-galloway/RTLDesignSherpa
#
# Module: axil5_id_check
# Purpose: Give every AXIL5 test transaction an ID and check it comes back
#
# Subsystem: framework

"""AXI5-Lite ID reflection, checked on every transaction a testbench issues.

AXI5-Lite carries AWID/BID and ARID/RID (IHI 0022 Issue L, Table B2.2, code
YS: optional on a Manager, mandatory on a Subordinate), and a Subordinate
reflects the request's ID on its response (A5.1.1). The ``rtl/amba/axil5``
modules are skid-buffer pass-throughs, so for them "reflects" means the ID a
Manager put on AWID/ARID crosses the module, reaches the Subordinate behind
it, and the BID/RID that Subordinate returns crosses back unchanged.

The inherited AXI4-Lite phases never name an ID, so left alone every beat
would carry ID 0 -- the reset value, and the value an unconnected port reads.
A module that dropped the ID would pass all of them. :func:`install` wraps the
Manager-side BFM so each transaction that does not pick its own ID gets the
next one from a rotating non-zero sequence (all bit patterns of the width are
used), and the response's ID is compared with it before the phase sees the
result. A mismatch raises, so the phase records a failed transaction.

The slave BFM on the other side reflects the ID it was given (see
``reflected_id`` in the AXI-Lite interfaces), so a mismatch here is the DUT.
"""

#: Must equal the RTL default ``ID_WIDTH`` of the rtl/amba/axil5 modules.
#: The BFM binds AWID/ARID/BID/RID by name; a different width would truncate
#: rather than fail to bind.
AXIL5_TB_ID_WIDTH = 4


class AXIL5IdReflectionCheck:
    """Wraps one AXI5-Lite Manager BFM interface; counts and checks IDs."""

    def __init__(self, iface, id_width, log):
        if id_width < 1:
            raise ValueError("ID reflection needs an ID of at least one bit")
        self.iface = iface
        self.log = log
        self.max_id = (1 << id_width) - 1
        self._next = 1
        self.checked = 0
        self.mismatches = []

    def _next_id(self):
        """1, 2, ... max_id, 1, ...: never 0, and every bit toggles."""
        tid = self._next
        self._next = 1 if tid >= self.max_id else tid + 1
        return tid

    def _check(self, what, sent, packet):
        got = getattr(packet, 'id', None) if packet is not None else None
        self.checked += 1
        if got != sent:
            msg = (f"{what} = {got!r}, expected {sent!r} reflected from the "
                   f"request ID")
            self.mismatches.append(msg)
            self.log.error(f"AXIL5 ID reflection: {msg}")
            raise AssertionError(f"AXIL5 ID reflection failed: {msg}")
        if self.checked in (1, 10, 100, 1000):
            self.log.info(f"AXIL5 ID reflection: {self.checked} responses "
                          f"checked, last {what}={got} (sent {sent}), "
                          f"0 mismatches")

    def wrap_read(self):
        orig = self.iface.read_transaction

        async def read_transaction(address, **kwargs):
            if 'arid' in kwargs:
                return await orig(address, **kwargs)
            tid = self._next_id()
            try:
                result = await orig(address, arid=tid, **kwargs)
            except RuntimeError:
                # An error RESPONSE (SLVERR/DECERR) still arrived and still
                # carries the RID of the request it answers. A timeout is not
                # a RuntimeError and is left to propagate unchecked.
                self._check('RID', tid, self.iface.last_r_packet)
                raise
            self._check('RID', tid, self.iface.last_r_packet)
            return result

        self.iface.read_transaction = read_transaction

    def wrap_write(self):
        orig = self.iface.write_transaction

        async def write_transaction(address, data, *args, **kwargs):
            if 'awid' in kwargs:
                return await orig(address, data, *args, **kwargs)
            tid = self._next_id()
            try:
                result = await orig(address, data, *args, awid=tid, **kwargs)
            except RuntimeError:
                self._check('BID', tid, self.iface.last_b_packet)
                raise
            self._check('BID', tid, self.iface.last_b_packet)
            return result

        self.iface.write_transaction = write_transaction

    def summary(self):
        return {'checked': self.checked, 'mismatches': len(self.mismatches)}


def install(iface, log, id_width=AXIL5_TB_ID_WIDTH):
    """Wrap whichever of read/write ``iface`` implements. Returns the checker.

    Only call this for a BFM built with ``id_width``: without an ``id`` field
    the transaction would reject ``arid=``/``awid=`` as undeclared.
    """
    chk = AXIL5IdReflectionCheck(iface, id_width, log)
    log.info(f"AXIL5 ID reflection check installed on {type(iface).__name__} "
             f"(id_width={id_width})")
    if hasattr(iface, 'read_transaction'):
        chk.wrap_read()
    if hasattr(iface, 'write_transaction'):
        chk.wrap_write()
    return chk


#: The BFM configuration that matches an rtl/amba/axil5 module elaborated with
#: its default parameters: ID_WIDTH=4, USER_WIDTH=4, ENABLE_USER/TRACE/POISON=1.
#: A BFM configured wider or narrower than the DUT truncates or fails to bind,
#: so change one side and the other must follow.
AXIL5_RTL_DEFAULT_COMPONENT_KWARGS = {
    'id_width': AXIL5_TB_ID_WIDTH,   # ID_WIDTH  (AWID/BID, ARID/RID)
    'user_width': 4,                 # USER_WIDTH, ENABLE_USER
    'trace': True,                   # ENABLE_TRACE
    'poison': True,                  # ENABLE_POISON
}
